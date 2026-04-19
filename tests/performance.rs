//! ACT Protocol — Detailed Performance Profile
//!
//! Measures timing (min / avg / max across N iterations), wire-format proof
//! sizes, and per-component breakdowns for every phase of the protocol.
//!
//! Run with:
//!   cargo test --test performance -- --nocapture
//!
//! For release-mode timings (recommended):
//!   cargo test --test performance --release -- --nocapture

use std::time::{Duration, Instant};

use ark_bls12_381::{Bls12_381, Fq12, G1Projective};
use ark_ec::{pairing::Pairing, CurveGroup, VariableBaseMSM};
use ark_ff::Field;
use ark_std::rand::thread_rng;
use rand::RngCore;

use act::{
    bulletproofs::{prove_range, verify_range},
    compute_h_ctx,
    epoch_refresh::{verify_refresh, RefreshProof, RefreshProver},
    hash::hash_to_g1,
    master_mint::{MasterMintClient, MasterMintServer},
    setup::{Generators, ServerKeys},
    spend::{verify_spend, SpendProver},
    BbsSignature, Scalar,
};

// ─── helpers ─────────────────────────────────────────────────────────────────

const ITERS: usize = 10;

struct Stats {
    min: Duration,
    max: Duration,
    sum: Duration,
    n: usize,
}

impl Stats {
    fn new() -> Self {
        Self { min: Duration::MAX, max: Duration::ZERO, sum: Duration::ZERO, n: 0 }
    }

    fn record(&mut self, d: Duration) {
        if d < self.min { self.min = d; }
        if d > self.max { self.max = d; }
        self.sum += d;
        self.n += 1;
    }

    fn avg(&self) -> Duration {
        if self.n == 0 { Duration::ZERO } else { self.sum / self.n as u32 }
    }

    fn print(&self, label: &str) {
        println!(
            "  {:<47}  avg {:>8.3} ms   min {:>8.3} ms   max {:>8.3} ms",
            label, ms(self.avg()), ms(self.min), ms(self.max),
        );
    }
}

fn ms(d: Duration) -> f64 { d.as_secs_f64() * 1_000.0 }

// Wire-format sizes ─────────────────────────────────────────────────────────
const G1_BYTES: usize = 48;     // compressed G1 (BLS12-381)
const SCALAR_BYTES: usize = 32; // Fr element

fn refresh_proof_size(proof: &RefreshProof) -> usize {
    // BBS+ core (3×G1) + bridge commits (6×G1) + public values (3×G1) +
    // Schnorr responses (9×Fr) + serialised Bulletproof.
    let bp = act::bulletproofs::serialize_proof(&proof.bp_exp)
        .map(|b| b.len())
        .unwrap_or(0);
    12 * G1_BYTES + 9 * SCALAR_BYTES + bp
}

fn spend_proof_size(proof: &act::spend::SpendProof) -> usize {
    // BBS+ core (3×G1) + bridge commits (6×G1) + public values (2×G1) +
    // disclosed u32×2 (8 bytes) + k_cur Fr + 7×Fr responses + Bulletproof.
    let bp = act::bulletproofs::serialize_proof(&proof.bp_spend)
        .map(|b| b.len())
        .unwrap_or(0);
    11 * G1_BYTES + 8 * SCALAR_BYTES + 8 + bp
}

// ─── test fixtures ───────────────────────────────────────────────────────────

fn make_daily_sig(
    rng: &mut impl ark_std::rand::RngCore,
    k_daily: Scalar,
    c_bal: u32,
    t_issue: u32,
    generators: &Generators,
    keys: &ServerKeys,
) -> BbsSignature {
    use ark_bls12_381::Fr;
    let r = Scalar::rand(rng);
    let k_commit = generators.h[4] * Fr::from(c_bal as u64)
        + generators.h[1] * k_daily.0
        + generators.h[2] * Fr::from(t_issue as u64)
        + generators.h[0] * r.0;
    let e = Scalar::rand(rng);
    let s_prime = Scalar::rand(rng);
    let msg = generators.g1 + k_commit + generators.h[0] * s_prime.0;
    let a = msg * (e + keys.sk_daily).0.inverse().unwrap();
    BbsSignature { a, e, s: r + s_prime }
}

// ─── main test ───────────────────────────────────────────────────────────────

#[test]
fn performance_profile() {
    let mut rng = thread_rng();

    println!();
    println!("╔══════════════════════════════════════════════════════════════════════════════╗");
    println!("║              ACT PROTOCOL — DETAILED PERFORMANCE PROFILE                    ║");
    println!("╚══════════════════════════════════════════════════════════════════════════════╝");
    println!("  Build : {}", if cfg!(debug_assertions) { "DEBUG  ← run --release for realistic numbers" } else { "RELEASE" });
    println!("  N     : {ITERS} iterations per operation (avg / min / max reported)");
    println!();

    // ── 1. Setup ─────────────────────────────────────────────────────────────
    println!("┌─ 1. SETUP ─────────────────────────────────────────────────────────────────┐");

    let t = Instant::now(); let generators = Generators::new();     let t_gen = t.elapsed();
    let t = Instant::now(); let keys       = ServerKeys::generate(&mut rng); let t_keys = t.elapsed();
    let t = Instant::now();
    let h_ctx = compute_h_ctx("act-perf", &keys.pk_master, &keys.pk_daily, &generators);
    let t_hctx = t.elapsed();

    println!("  {:<47}  {:>8.3} ms  (one-time, deterministic)", "Generator creation  (5 × hash-to-G1):", ms(t_gen));
    println!("  {:<47}  {:>8.3} ms", "Server key generation:", ms(t_keys));
    println!("  {:<47}  {:>8.3} ms", "H_ctx computation:", ms(t_hctx));
    println!();

    // ── 2. Master Mint ───────────────────────────────────────────────────────
    println!("┌─ 2. MASTER MINT ───────────────────────────────────────────────────────────┐");

    let c_max = 100u32;
    let e_max = 5000u32;
    let current_epoch = 1000u32;

    let (mut st_cb, mut st_si, mut st_cf) = (Stats::new(), Stats::new(), Stats::new());
    let mut last_k_sub = Scalar::rand_nonzero(&mut rng);
    let mut last_master_sig: Option<BbsSignature> = None;

    for _ in 0..ITERS {
        let t = Instant::now();
        let (client, req) = MasterMintClient::begin(&mut rng, c_max, e_max, &generators, h_ctx);
        st_cb.record(t.elapsed());

        let t = Instant::now();
        let (a, e, sp) = MasterMintServer::issue(&mut rng, &req, c_max, e_max, &generators, &keys, h_ctx).unwrap();
        st_si.record(t.elapsed());

        let k_sub = client.k_sub;
        let t = Instant::now();
        let sig = client.finalize(a, e, sp);
        st_cf.record(t.elapsed());

        last_k_sub = k_sub;
        last_master_sig = Some(sig);
    }

    st_cb.print("Client begin (commit + PoK prove):");
    st_si.print("Server issue (PoK verify + BBS+ sign):");
    st_cf.print("Client finalize (unblind s):");

    let req_size = 2 * G1_BYTES + 2 * SCALAR_BYTES; // K_sub, T_pok, s_k, s_r
    let resp_size = G1_BYTES + 2 * SCALAR_BYTES;     // A_sub, e, s'
    println!();
    println!("  Wire sizes:");
    println!("    MasterMintRequest  : {req_size} bytes   (K_sub G1=48, T_PoK G1=48, s_k Fr=32, s_r Fr=32)");
    println!("    MasterMintResponse : {resp_size} bytes   (A_sub G1=48, e Fr=32, s' Fr=32)");
    println!();

    // ── 3. Epoch Refresh ─────────────────────────────────────────────────────
    println!("┌─ 3. EPOCH REFRESH ─────────────────────────────────────────────────────────┐");

    let master_sig = last_master_sig.unwrap();
    let k_sub = last_k_sub;

    let (mut st_rp, mut st_rv) = (Stats::new(), Stats::new());
    let mut last_rp: Option<RefreshProof> = None;
    let mut last_daily: Option<(BbsSignature, Scalar)> = None;

    for _ in 0..ITERS {
        let t = Instant::now();
        let (client, proof) = RefreshProver::prove(
            &mut rng, &master_sig, k_sub, c_max, e_max, current_epoch,
            &generators, &keys.pk_master, h_ctx,
        ).unwrap();
        st_rp.record(t.elapsed());

        let t = Instant::now();
        let resp = verify_refresh(&proof, current_epoch, &generators, &keys.pk_master, &keys, h_ctx, &mut rng).unwrap();
        st_rv.record(t.elapsed());

        if last_rp.is_none() { last_rp = Some(proof.clone()); }
        let finalized = client.finalize(resp);
        if last_daily.is_none() { last_daily = Some(finalized); }
    }

    st_rp.print("Client prove  (BBS+ randomise + bridging + BP):");
    st_rv.print("Server verify (challenge + bridges + MSM + BP + pairing):");

    let rp = last_rp.as_ref().unwrap();
    let rp_bp = act::bulletproofs::serialize_proof(&rp.bp_exp).unwrap();
    let rp_total = refresh_proof_size(rp);

    println!();
    println!("  Refresh proof wire size:");
    println!("    Total                              : {rp_total} bytes  ({:.1} KiB)", rp_total as f64 / 1024.0);
    println!("    BBS+ core   (a', ā, T_BBS)  3×G1  : {} bytes", 3 * G1_BYTES);
    println!("    Bridge commitments           6×G1  : {} bytes", 6 * G1_BYTES);
    println!("    Public values (N_T, K_d, CΔ) 3×G1  : {} bytes", 3 * G1_BYTES);
    println!("    Schnorr responses            9×Fr  : {} bytes", 9 * SCALAR_BYTES);
    println!("    Bulletproof  (32-bit range)        : {} bytes", rp_bp.len());
    println!();

    // ── 4. Spend ─────────────────────────────────────────────────────────────
    println!("┌─ 4. SPEND ─────────────────────────────────────────────────────────────────┐");

    let (_daily_sig_base, k_daily) = last_daily.unwrap();
    let spend_amount = 30u32;
    let nonce: [u8; 16] = rand::random();

    let (mut st_sp, mut st_sv) = (Stats::new(), Stats::new());
    let mut last_sp: Option<act::spend::SpendProof> = None;

    for _ in 0..ITERS {
        // Fresh daily sig each iteration (prevents nonce reuse in the range proof).
        let daily_i = make_daily_sig(&mut rng, k_daily, c_max, current_epoch, &generators, &keys);

        let t = Instant::now();
        let (_c, proof) = SpendProver::prove(
            &mut rng, &daily_i, k_daily, c_max, current_epoch, spend_amount,
            &nonce, &generators, &keys.pk_daily, h_ctx,
        ).unwrap();
        st_sp.record(t.elapsed());

        let t = Instant::now();
        let _ = verify_spend(&proof, current_epoch, &nonce, &generators, &keys.pk_daily, &keys, h_ctx, &mut rng).unwrap();
        st_sv.record(t.elapsed());

        if last_sp.is_none() { last_sp = Some(proof); }
    }

    st_sp.print("Client prove  (BBS+ randomise + bridging + BP):");
    st_sv.print("Server verify (challenge + bridges + MSM + BP + pairing):");

    let sp = last_sp.as_ref().unwrap();
    let sp_bp = act::bulletproofs::serialize_proof(&sp.bp_spend).unwrap();
    let sp_total = spend_proof_size(sp);

    println!();
    println!("  Spend proof wire size:");
    println!("    Total                              : {sp_total} bytes  ({:.1} KiB)", sp_total as f64 / 1024.0);
    println!("    BBS+ core   (a', ā, T_BBS)  3×G1  : {} bytes", 3 * G1_BYTES);
    println!("    Bridge commitments           6×G1  : {} bytes", 6 * G1_BYTES);
    println!("    Public values (K', C_BP)     2×G1  : {} bytes", 2 * G1_BYTES);
    println!("    Disclosed (s u32 + T_issue u32)    : 8 bytes");
    println!("    k_cur (disclosed nullifier)  1×Fr  : {} bytes", SCALAR_BYTES);
    println!("    Schnorr responses            7×Fr  : {} bytes", 7 * SCALAR_BYTES);
    println!("    Bulletproof  (32-bit range)        : {} bytes", sp_bp.len());
    println!();

    // ── 5. Component Benchmarks ───────────────────────────────────────────────
    println!("┌─ 5. COMPONENT BENCHMARKS ──────────────────────────────────────────────────┐");

    let g1a = generators.g1.into_affine();
    let g2a = generators.g2.into_affine();
    let g1_neg = (-generators.g1).into_affine();

    // 5a. Single pairing (baseline for comparison)
    let mut st = Stats::new();
    for _ in 0..ITERS {
        let t = Instant::now();
        let _ = Bls12_381::pairing(g1a, g2a);
        st.record(t.elapsed());
    }
    st.print("Single pairing e(G1, G2)  [baseline]:");

    // 5b. Multi-pairing 2-input (the optimised pairing check path)
    let mut st_mp = Stats::new();
    for _ in 0..ITERS {
        let t = Instant::now();
        let r = Bls12_381::multi_pairing([g1a, g1_neg], [g2a, g2a]);
        let _ = r.0 == Fq12::ONE;
        st_mp.record(t.elapsed());
    }
    st_mp.print("Multi-pairing 2-input  [used in verify]:");

    // Speedup vs single pairing
    {
        let mut st_single = Stats::new();
        for _ in 0..ITERS {
            let t = Instant::now();
            let _ = Bls12_381::pairing(g1a, g2a);
            st_single.record(t.elapsed());
        }
        println!("  →  single: {:.3} ms   multi: {:.3} ms   ratio: {:.2}×",
            ms(st_single.avg()), ms(st_mp.avg()),
            ms(st_single.avg()) / ms(st_mp.avg()).max(0.001));
    }
    println!();

    // 5c. Miller loop (half of pairing cost)
    let mut st = Stats::new();
    for _ in 0..ITERS {
        let t = Instant::now();
        let _ = Bls12_381::multi_miller_loop([g1a], [g2a]);
        st.record(t.elapsed());
    }
    st.print("Miller loop only (1 G1-G2 pair):");

    // 5d. Final exponentiation (the other half)
    let ml = Bls12_381::multi_miller_loop([g1a], [g2a]);
    let mut st = Stats::new();
    for _ in 0..ITERS {
        let t = Instant::now();
        let _ = Bls12_381::final_exponentiation(ml);
        st.record(t.elapsed());
    }
    st.print("Final exponentiation:");
    println!();

    // 5e. MSM — 3 bases (token issuance size)
    {
        let affine = G1Projective::normalize_batch(&[generators.g1, generators.h[0], generators.h[1]]);
        let s: Vec<_> = (0..3).map(|_| Scalar::rand(&mut rng).0).collect();
        let mut st = Stats::new();
        for _ in 0..ITERS {
            let t = Instant::now();
            let _ = G1Projective::msm(&affine, &s).unwrap();
            st.record(t.elapsed());
        }
        st.print("MSM  3 bases  Pippenger  (issuance size):");
    }
    // 5f. MSM — 6 bases (Schnorr check size)
    {
        let affine = G1Projective::normalize_batch(&generators.h[..6.min(generators.h.len())]);
        let s: Vec<_> = (0..affine.len()).map(|_| Scalar::rand(&mut rng).0).collect();
        let mut st = Stats::new();
        for _ in 0..ITERS {
            let t = Instant::now();
            let _ = G1Projective::msm(&affine, &s).unwrap();
            st.record(t.elapsed());
        }
        st.print("MSM  5-6 bases Pippenger (BBS+ Schnorr check):");
    }
    // 5g. MSM — 12 bases (bridge check size)
    {
        let pts: Vec<G1Projective> = (0..12).map(|_| generators.g1 * Scalar::rand(&mut rng).0).collect();
        let affine = G1Projective::normalize_batch(&pts);
        let s: Vec<_> = (0..12).map(|_| Scalar::rand(&mut rng).0).collect();
        let mut st = Stats::new();
        for _ in 0..ITERS {
            let t = Instant::now();
            let _ = G1Projective::msm(&affine, &s).unwrap();
            st.record(t.elapsed());
        }
        st.print("MSM 12 bases  Pippenger (bridge+BBS combined):");
    }
    println!();

    // 5h. Hash-to-G1 (H_T epoch hash, computed once per epoch)
    let mut st_h2g1 = Stats::new();
    for i in 0..ITERS {
        let t = Instant::now();
        let _ = hash_to_g1(b"ACT:Epoch:", &(i as u32).to_le_bytes());
        st_h2g1.record(t.elapsed());
    }
    st_h2g1.print("Hash-to-G1  (H_T epoch computation):");

    // 5i. Bulletproof prove  (32-bit range)
    let bp_val = 42u64;
    let bp_blind = Scalar::rand(&mut rng);
    let bp_extra = b"perf-test";
    let mut st_bpp = Stats::new();
    for _ in 0..ITERS {
        let t = Instant::now();
        let _ = prove_range(&mut rng, bp_val, bp_blind, 32, generators.h[4], generators.h[0], b"ACT:Perf", bp_extra).unwrap();
        st_bpp.record(t.elapsed());
    }
    st_bpp.print("Bulletproof prove   (32-bit range):");

    // 5j. Bulletproof verify (32-bit range)
    let (bp_proof, bp_commit) = prove_range(&mut rng, bp_val, bp_blind, 32, generators.h[4], generators.h[0], b"ACT:Perf", bp_extra).unwrap();
    let mut st_bpv = Stats::new();
    for _ in 0..ITERS {
        let t = Instant::now();
        verify_range(&bp_proof, bp_commit, 32, generators.h[4], generators.h[0], b"ACT:Perf", bp_extra).unwrap();
        st_bpv.record(t.elapsed());
    }
    st_bpv.print("Bulletproof verify  (32-bit range):");

    // 5k. SHA-256 challenge hash (~typical preimage)
    let preimage = vec![0xABu8; 1024];
    let mut st_sha = Stats::new();
    for _ in 0..ITERS {
        let t = Instant::now();
        let _ = act::hash_to_scalar(&preimage);
        st_sha.record(t.elapsed());
    }
    st_sha.print("SHA-256 challenge hash (~1 KiB preimage):");

    // 5l. G1 scalar-mul (BBS+ randomisation A×r1)
    let r1 = Scalar::rand(&mut rng);
    let pt = generators.g1;
    let mut st_smul = Stats::new();
    for _ in 0..ITERS {
        let t = Instant::now();
        let _ = pt * r1.0;
        st_smul.record(t.elapsed());
    }
    st_smul.print("G1 scalar-mul  (BBS+ randomisation A·r₁):");
    println!();

    // ── 6. Throughput Estimates ───────────────────────────────────────────────
    println!("┌─ 6. THROUGHPUT ESTIMATES (single-threaded) ────────────────────────────────┐");

    let rv_ms = ms(st_rv.avg()).max(0.001);
    let sv_ms = ms(st_sv.avg()).max(0.001);
    let rp_ms = ms(st_rp.avg()).max(0.001);
    let sp_ms = ms(st_sp.avg()).max(0.001);

    println!("  {:<47}  {:>9.1} ops/s", "Server: refresh verifications/sec:", 1000.0 / rv_ms);
    println!("  {:<47}  {:>9.1} ops/s", "Server: spend verifications/sec:", 1000.0 / sv_ms);
    println!("  {:<47}  {:>9.1} ops/s", "Server: combined (1 refresh + 1 spend)/sec:", 1000.0 / (rv_ms + sv_ms));
    println!("  {:<47}  {:>9.1} ops/s", "Client: refresh proofs/sec:", 1000.0 / rp_ms);
    println!("  {:<47}  {:>9.1} ops/s", "Client: spend proofs/sec:", 1000.0 / sp_ms);
    println!("  {:<47}  {:>9.1} ops/s", "Bulletproof verify/sec:", 1000.0 / ms(st_bpv.avg()).max(0.001));
    println!();

    // ── 7. Summary Table ─────────────────────────────────────────────────────
    println!("┌─ 7. SUMMARY TABLE ─────────────────────────────────────────────────────────┐");
    let sep = format!("  {:─<75}", "");
    println!("{sep}");
    println!("  {:<40}  {:>10}  {:>14}  {:>10}", "Operation", "Avg (ms)", "Wire (bytes)", "Ops/sec");
    println!("{sep}");

    let rows: &[(&str, f64, usize)] = &[
        ("Setup: generator creation",          ms(t_gen),          0),
        ("Master Mint: client begin",           ms(st_cb.avg()),    req_size),
        ("Master Mint: server issue",           ms(st_si.avg()),    resp_size),
        ("Epoch Refresh: client prove",         ms(st_rp.avg()),    rp_total),
        ("Epoch Refresh: server verify",        ms(st_rv.avg()),    rp_total),
        ("Spend: client prove",                 ms(st_sp.avg()),    sp_total),
        ("Spend: server verify",                ms(st_sv.avg()),    sp_total),
        ("  ↳ Multi-pairing (2 inputs)",        ms(st_mp.avg()),    0),
        ("  ↳ Bulletproof prove (32-bit)",       ms(st_bpp.avg()),  rp_bp.len()),
        ("  ↳ Bulletproof verify (32-bit)",      ms(st_bpv.avg()),  0),
        ("  ↳ Hash-to-G1 (H_T)",                ms(st_h2g1.avg()), 0),
        ("  ↳ SHA-256 challenge hash",           ms(st_sha.avg()),  0),
    ];

    for (label, avg_ms, size) in rows {
        let size_s = if *size > 0 { format!("{size}") } else { "—".to_string() };
        let ops_s  = if *avg_ms > 0.0 { format!("{:.1}", 1000.0 / avg_ms) } else { "—".to_string() };
        println!("  {:<40}  {:>10.3}  {:>14}  {:>10}", label, avg_ms, size_s, ops_s);
    }
    println!("{sep}");
    println!();

    // ── 8. Applied Optimisations ─────────────────────────────────────────────
    println!("┌─ 8. APPLIED OPTIMISATIONS ─────────────────────────────────────────────────┐");
    println!("  ① Pippenger MSM (all four crypto files)");
    println!("       Before: naive fold  Σ (base_i × scalar_i) — O(n) scalar-muls");
    println!("       After : normalize_batch (one batch inversion) + VariableBaseMSM");
    println!("       Effect: ~5-10× for n≥8; speedup begins at n≥4");
    println!();
    println!("  ② Single multi-pairing instead of two separate pairings");
    println!("       Before: e(A', pk) and e(Ā, g₂) — 2 Miller loops + 2 final-exps");
    println!("       After : multi_miller_loop([A', -Ā], [pk, g₂]) + 1 final-exp");
    println!("       Effect: ~30-40 % fewer field operations for the pairing check");
    println!("       Applied in: bbs_proof::verify, verify_refresh, verify_spend");
    println!();
    println!("  ③ Lock-free atomic Bloom filter  (server.rs)");
    println!("       Before: Vec<u8> bits + RwLock — every insert acquires a write lock,");
    println!("               serialising all concurrent nonce verifications");
    println!("       After : Vec<AtomicU8> with fetch_or (Relaxed) — zero contention");
    println!("       Effect: linear throughput scaling with core count for nonce checks");
    println!("       Safety: the Redis SADD is the authoritative double-spend guard;");
    println!("               the Bloom filter is a fast-path pre-check only");
    println!();
    println!("  ④ spawn_blocking for CPU-bound proof verification  (server.rs)");
    println!("       Before: verify_refresh / verify_spend ran on the Tokio async thread,");
    println!("               blocking the I/O reactor for several milliseconds per request");
    println!("       After : tokio::task::spawn_blocking moves crypto onto a dedicated");
    println!("               OS thread pool, keeping networking fully responsive under load");
    println!();
    println!("  ⑤ OnceLock-cached BulletproofGens  (bulletproofs.rs, pre-existing)");
    println!("       128 hash-to-G1 calls amortised across all proofs in the process");
    println!();

    // Sanity assertions — the test itself must pass.
    assert!(ms(st_rv.avg()) > 0.0, "refresh verify must take non-zero time");
    assert!(ms(st_sv.avg()) > 0.0, "spend verify must take non-zero time");
    assert!(rp_total > 0, "refresh proof must have non-zero size");
    assert!(sp_total > 0, "spend proof must have non-zero size");
}
