//! Server‑side logic for the ACT protocol.
//!
//! This module provides:
//! - Nullifier set management using Redis for atomic operations.
//! - Idempotency caching to handle retried requests safely.
//! - Nonce verification with support for both standard (direct) and high‑privacy
//!   (Merkle‑inclusion) modes.
//!
//! The server is designed to be integrated into an HTTP API (e.g., using Axum).
//! All database operations are atomic to prevent race conditions and double‑spending.

extern crate alloc;
use alloc::vec::Vec;
use ark_std::vec;
#[cfg(feature = "server")]
use redis::{AsyncCommands, Client};
#[cfg(feature = "server")]
use crate::error::{ActError, Result};
#[cfg(feature = "server")]
use crate::types::{CompressedG1, Scalar};
#[cfg(feature = "server")]
use sha2::{Digest, Sha256};
#[cfg(feature = "server")]
use std::collections::HashSet;
#[cfg(feature = "server")]
use std::sync::Arc;
#[cfg(feature = "server")]
use tokio::sync::RwLock;
#[cfg(feature = "server")]
use ark_serialize::CanonicalSerialize;
#[cfg(feature = "server")]
use rand::RngCore;

// ============================================================================
// Server Configuration
// ============================================================================

#[cfg(feature = "server")]
#[derive(Clone)]
pub struct ServerConfig {
    /// Redis connection URL.
    pub redis_url: String,
    /// Current epoch (set by the server, typically updated via cron).
    pub current_epoch: u32,
    /// Grace period in seconds after epoch rollover during which the previous
    /// epoch's spend nullifiers are still accepted.
    pub epoch_grace_period_secs: u64,
    /// TTL for idempotency cache entries (seconds).
    pub idempotency_ttl_secs: u64,
    /// TTL for nonce cache entries (standard mode) (seconds).
    pub nonce_ttl_secs: u64,
    /// Number of nonces to publish in each high‑privacy batch.
    pub high_privacy_batch_size: usize,
    /// False‑positive rate for the high‑privacy Bloom filter.
    pub bloom_filter_fp_rate: f64,
}

impl Default for ServerConfig {
    fn default() -> Self {
        Self {
            redis_url: "redis://127.0.0.1:6379".to_string(),
            current_epoch: 0,
            epoch_grace_period_secs: 300, // 5 minutes
            idempotency_ttl_secs: 60,
            nonce_ttl_secs: 60,
            high_privacy_batch_size: 10000,
            bloom_filter_fp_rate: 0.001,
        }
    }
}

// ============================================================================
// Nullifier Manager
// ============================================================================

#[cfg(feature = "server")]
#[derive(Clone)]
pub struct NullifierManager {
    client: Client,
    config: ServerConfig,
}

#[cfg(feature = "server")]
impl NullifierManager {
    pub fn new(client: Client, config: ServerConfig) -> Self {
        Self { client, config }
    }

    pub async fn check_epoch_nullifier(&self, n_t: &CompressedG1) -> Result<bool> {
        let mut conn = self.client.get_async_connection().await?;
        let key = format!("act:epoch:{}:nullifiers", self.config.current_epoch);
        let added: u64 = conn.sadd(&key, n_t.0.as_slice()).await?;
        let ttl = self.config.epoch_grace_period_secs + 86400;
        let _: () = conn.expire(&key, ttl as i64).await?;
        Ok(added == 1)
    }

    pub async fn check_spend_nullifier(&self, k_cur: Scalar, t_issue: u32) -> Result<bool> {
        let epoch_key = if t_issue == self.config.current_epoch {
            self.config.current_epoch
        } else if t_issue == self.config.current_epoch - 1 {
            self.config.current_epoch - 1
        } else {
            return Err(ActError::VerificationFailed("Epoch mismatch".into()));
        };
        let mut conn = self.client.get_async_connection().await?;
        let key = format!("act:spend:{}:nullifiers", epoch_key);
        let added: u64 = conn.sadd(&key, k_cur.to_bytes().as_slice()).await?;
        let ttl = self.config.epoch_grace_period_secs + 86400;
        let _: () = conn.expire(&key, ttl as i64).await?;
        Ok(added == 1)
    }
}

// ============================================================================
// Idempotency Cache
// ============================================================================

#[cfg(feature = "server")]
#[derive(Clone)]
pub struct IdempotencyCache {
    client: Client,
    ttl_secs: u64,
}

#[cfg(feature = "server")]
impl IdempotencyCache {
    pub fn new(client: Client, ttl_secs: u64) -> Self {
        Self { client, ttl_secs }
    }

    pub fn compute_key(proof_bytes: &[u8], nonce: &[u8]) -> String {
        let mut hasher = Sha256::new();
        hasher.update(proof_bytes);
        hasher.update(nonce);
        let digest = hasher.finalize();
        format!("act:idem:{}", hex::encode(digest))
    }

    pub fn compute_key_no_nonce(proof_bytes: &[u8]) -> String {
        let digest = Sha256::digest(proof_bytes);
        format!("act:idem:{}", hex::encode(digest))
    }

    pub async fn store(&self, key: &str, value: &[u8]) -> Result<()> {
        let mut conn = self.client.get_async_connection().await?;
        let _: () = conn.set_ex(key, value, self.ttl_secs as usize).await?;
        Ok(())
    }

    pub async fn get(&self, key: &str) -> Result<Option<Vec<u8>>> {
        let mut conn = self.client.get_async_connection().await?;
        let res: Option<Vec<u8>> = conn.get(key).await?;
        Ok(res)
    }
}

// ============================================================================
// Merkle Tree for High‑Privacy Nonces
// ============================================================================

#[cfg(feature = "server")]
#[derive(Clone, Debug)]
pub struct MerkleProof {
    pub leaf: [u8; 16],
    pub siblings: Vec<[u8; 32]>,
    pub index: usize,
}

#[cfg(feature = "server")]
impl MerkleProof {
    pub fn verify(&self, root: &[u8; 32]) -> bool {
        let mut current = Sha256::digest(&self.leaf);
        let mut idx = self.index;
        for sibling in &self.siblings {
            let mut hasher = Sha256::new();
            if idx % 2 == 0 {
                hasher.update(current);
                hasher.update(sibling);
            } else {
                hasher.update(sibling);
                hasher.update(current);
            }
            current = hasher.finalize();
            idx /= 2;
        }
        current.as_slice() == root.as_slice()
    }
}

#[cfg(feature = "server")]
pub struct MerkleTree {
    leaves: Vec<[u8; 16]>,
    root: [u8; 32],
}

#[cfg(feature = "server")]
impl MerkleTree {
    pub fn build(mut nonces: Vec<[u8; 16]>) -> Self {
        let original_len = nonces.len();
        let next_pow2 = original_len.next_power_of_two();
        nonces.resize(next_pow2, [0u8; 16]);

        let mut hashes: Vec<[u8; 32]> = nonces
            .iter()
            .map(|leaf| {
                let mut h = [0u8; 32];
                h.copy_from_slice(Sha256::digest(leaf).as_slice());
                h
            })
            .collect();

        let mut level_size = next_pow2;
        while level_size > 1 {
            for i in 0..(level_size / 2) {
                let mut hasher = Sha256::new();
                hasher.update(hashes[2 * i]);
                hasher.update(hashes[2 * i + 1]);
                let digest = hasher.finalize();
                hashes[i].copy_from_slice(digest.as_slice());
            }
            level_size /= 2;
        }

        let root = hashes[0];
        Self {
            leaves: nonces[..original_len].to_vec(),
            root,
        }
    }

    pub fn root(&self) -> [u8; 32] {
        self.root
    }

    pub fn prove(&self, index: usize) -> Option<MerkleProof> {
        if index >= self.leaves.len() {
            return None;
        }
        let padded_len = self.leaves.len().next_power_of_two();
        let mut hashes: Vec<[u8; 32]> = ark_std::iter::repeat([0u8; 16])
            .take(padded_len - self.leaves.len())
            .chain(self.leaves.iter().copied())
            .map(|leaf| {
                let mut h = [0u8; 32];
                h.copy_from_slice(Sha256::digest(&leaf).as_slice());
                h
            })
            .collect();

        let mut siblings = Vec::new();
        let mut idx = index;
        let mut level_size = padded_len;
        while level_size > 1 {
            let sibling_idx = if idx % 2 == 0 { idx + 1 } else { idx - 1 };
            siblings.push(hashes[sibling_idx]);
            let parent_idx = idx / 2;
            let mut hasher = Sha256::new();
            if idx % 2 == 0 {
                hasher.update(hashes[idx]);
                hasher.update(hashes[sibling_idx]);
            } else {
                hasher.update(hashes[sibling_idx]);
                hasher.update(hashes[idx]);
            }
            hashes[parent_idx].copy_from_slice(hasher.finalize().as_slice());
            idx = parent_idx;
            level_size /= 2;
        }

        Some(MerkleProof {
            leaf: self.leaves[index],
            siblings,
            index,
        })
    }
}

// ============================================================================
// Bloom Filter for High‑Privacy Nonce Reuse Detection
// ============================================================================

#[cfg(feature = "server")]
pub struct BloomFilter {
    bits: Vec<u8>,
    num_hashes: usize,
}

#[cfg(feature = "server")]
impl BloomFilter {
    pub fn new(capacity: usize, fp_rate: f64) -> Self {
        let m = (-(capacity as f64) * fp_rate.ln() / (2.0f64.ln().powi(2))).ceil() as usize;
        let k = ((m as f64 / capacity as f64) * 2.0f64.ln()).ceil() as usize;
        Self {
            bits: vec![0u8; (m + 7) / 8],
            num_hashes: k.max(1),
        }
    }

    fn hash(&self, data: &[u8], seed: u64) -> usize {
        use ark_std::collections::hash_map::DefaultHasher;
        use ark_std::hash::{Hash, Hasher};
        let mut hasher = DefaultHasher::new();
        data.hash(&mut hasher);
        seed.hash(&mut hasher);
        (hasher.finish() as usize) % (self.bits.len() * 8)
    }

    pub fn insert(&mut self, item: &[u8]) {
        for i in 0..self.num_hashes {
            let bit = self.hash(item, i as u64);
            let byte = bit / 8;
            let mask = 1 << (bit % 8);
            self.bits[byte] |= mask;
        }
    }

    pub fn contains(&self, item: &[u8]) -> bool {
        for i in 0..self.num_hashes {
            let bit = self.hash(item, i as u64);
            let byte = bit / 8;
            let mask = 1 << (bit % 8);
            if self.bits[byte] & mask == 0 {
                return false;
            }
        }
        true
    }
}

// ============================================================================
// Nonce Manager
// ============================================================================

#[cfg(feature = "server")]
#[derive(Clone)]
pub struct NonceManager {
    client: Client,
    ttl_secs: u64,
    inner: Arc<RwLock<NonceManagerInner>>,
}

#[cfg(feature = "server")]
struct NonceManagerInner {
    current_root: Option<[u8; 32]>,
    current_tree: Option<MerkleTree>,
    bloom_filter: BloomFilter,
}

#[cfg(feature = "server")]
impl NonceManager {
    pub fn new(client: Client, ttl_secs: u64, config: &ServerConfig) -> Self {
        Self {
            client,
            ttl_secs,
            inner: Arc::new(RwLock::new(NonceManagerInner {
                current_root: None,
                current_tree: None,
                bloom_filter: BloomFilter::new(
                    config.high_privacy_batch_size,
                    config.bloom_filter_fp_rate,
                ),
            })),
        }
    }

    pub async fn generate_nonce(&self) -> Result<[u8; 16]> {
        let mut rng = rand::thread_rng();
        let mut nonce = [0u8; 16];
        rng.fill_bytes(&mut nonce);
        let mut conn = self.client.get_async_connection().await?;
        let key = format!("act:nonce:{}", hex::encode(nonce));
        let _: () = conn.set_ex(&key, b"1", self.ttl_secs as usize).await?;
        Ok(nonce)
    }

    pub async fn verify_and_consume(&self, nonce: &[u8; 16]) -> Result<bool> {
        let mut conn = self.client.get_async_connection().await?;
        let key = format!("act:nonce:{}", hex::encode(nonce));
        let script = redis::Script::new(
            r#"
            local key = KEYS[1]
            local ttl = ARGV[1]
            local exists = redis.call('EXISTS', key)
            if exists == 1 then
                return 0
            end
            redis.call('SETEX', key, ttl, '1')
            return 1
            "#,
        );
        let result: u32 = script
            .key(&key)
            .arg(self.ttl_secs)
            .invoke_async(&mut conn)
            .await?;
        Ok(result == 1)
    }

    pub async fn publish_high_privacy_batch(&self, count: usize) -> Result<([u8; 32], usize)> {
        let mut rng = rand::thread_rng();
        let mut nonces = Vec::with_capacity(count);
        for _ in 0..count {
            let mut nonce = [0u8; 16];
            rng.fill_bytes(&mut nonce);
            nonces.push(nonce);
        }
        let tree = MerkleTree::build(nonces);
        let root = tree.root();

        let mut inner = self.inner.write().await;
        inner.current_root = Some(root);
        inner.current_tree = Some(tree);

        Ok((root, count))
    }

    pub async fn get_current_root(&self) -> Option<[u8; 32]> {
        self.inner.read().await.current_root
    }

    pub async fn verify_merkle_nonce(
        &self,
        nonce: &[u8; 16],
        merkle_proof: &MerkleProof,
        expected_root: &[u8; 32],
    ) -> Result<bool> {
        let inner = self.inner.read().await;

        if !merkle_proof.verify(expected_root) {
            return Ok(false);
        }

        if &merkle_proof.leaf != nonce {
            return Ok(false);
        }

        if inner.bloom_filter.contains(nonce) {
            return Ok(false);
        }

        drop(inner);
        let mut inner = self.inner.write().await;
        inner.bloom_filter.insert(nonce);

        Ok(true)
    }

    pub async fn verify_merkle_nonce_bytes(
        &self,
        nonce: &[u8; 16],
        proof_bytes: &[u8],
        root: &[u8; 32],
    ) -> Result<bool> {
        let _ = (nonce, proof_bytes, root);
        Err(ActError::ProtocolError("Binary Merkle proof decoding not available".into()))
    }
}

// ============================================================================
// Server API Handlers
// ============================================================================

#[cfg(feature = "server")]
pub mod handlers {
    use super::*;
    use crate::epoch_refresh::{RefreshProof, RefreshResponse, verify_refresh};
    use crate::master_mint::{MasterMintRequest, MasterMintServer};
    use crate::spend::{SpendProof, SpendResponse, verify_spend};
    use crate::setup::{Generators, ServerKeys};
    use crate::types::{CompressedG1, Scalar};
    use crate::hash::compute_h_ctx;
    use ark_ec::CurveGroup;
    use ark_std::rand::thread_rng;
    use ark_serialize::CanonicalSerialize;

    pub struct AppState {
        pub generators: Generators,
        pub keys: ServerKeys,
        pub h_ctx: Scalar,
        pub nullifier_mgr: NullifierManager,
        pub idempotency_cache: IdempotencyCache,
        pub nonce_mgr: NonceManager,
        pub config: ServerConfig,
    }

    impl AppState {
        pub fn new(redis_client: Client, config: ServerConfig, keys: ServerKeys) -> Self {
            let generators = Generators::new();
            let h_ctx = compute_h_ctx(
                "act-service",
                &keys.pk_master,
                &keys.pk_daily,
                &generators,
            );
            Self {
                generators,
                keys,
                h_ctx,
                nullifier_mgr: NullifierManager::new(redis_client.clone(), config.clone()),
                idempotency_cache: IdempotencyCache::new(redis_client.clone(), config.idempotency_ttl_secs),
                nonce_mgr: NonceManager::new(redis_client, config.nonce_ttl_secs, &config),
                config,
            }
        }
    }

    pub async fn handle_master_mint(
        state: &AppState,
        request: MasterMintRequest,
        c_max: u32,
        e_max: u32,
    ) -> Result<(CompressedG1, Scalar, Scalar)> {
        let mut rng = thread_rng();
        let (a_sub, e_sub, s_prime) = MasterMintServer::issue(
            &mut rng,
            &request,
            c_max,
            e_max,
            &state.generators,
            &state.keys,
            state.h_ctx,
        )?;
        Ok((CompressedG1::from_affine(a_sub.into_affine()), e_sub, s_prime))
    }

    pub async fn handle_refresh(
        state: &AppState,
        proof: RefreshProof,
    ) -> Result<RefreshResponse> {
        // 1. Idempotency check for refresh (cache for remainder of epoch)
        let proof_bytes = format!("{proof:?}").into_bytes();
        let idem_key = IdempotencyCache::compute_key_no_nonce(&proof_bytes);

        // 2. Check epoch nullifier
        let n_t_compressed = CompressedG1::from_affine(proof.n_t.into_affine());
        if !state.nullifier_mgr.check_epoch_nullifier(&n_t_compressed).await? {
            return Err(ActError::VerificationFailed("Epoch nullifier already used".into()));
        }

        // 3. Verify the proof
        let mut rng = thread_rng();
        let response = verify_refresh(
            &proof,
            state.config.current_epoch,
            &state.generators,
            &state.keys.pk_master,
            &state.keys,
            state.h_ctx,
            &mut rng,
        )?;

        // 4. Cache the response for idempotency (TTL = remainder of epoch)
        // We can set a long TTL because the epoch is long-lived.
        state.idempotency_cache.store(&idem_key, b"ok").await?;

        Ok(response)
    }

    pub async fn handle_spend(
        state: &AppState,
        proof: SpendProof,
        nonce: &[u8; 16],
        merkle_proof: Option<MerkleProof>,
        merkle_root: Option<[u8; 32]>,
    ) -> Result<SpendResponse> {
        // 1. Idempotency check
        let proof_bytes = format!("{proof:?}").into_bytes();
        let idem_key = IdempotencyCache::compute_key(&proof_bytes, nonce);

        // 2. Explicitly reject k_cur == 0
        if proof.k_cur.is_zero() {
            return Err(ActError::VerificationFailed("k_cur is zero".into()));
        }

        // 3. Verify nonce freshness
        if let (Some(proof), Some(root)) = (merkle_proof, merkle_root) {
            // High‑privacy mode: verify Merkle inclusion proof
            if !state.nonce_mgr.verify_merkle_nonce(nonce, &proof, &root).await? {
                return Err(ActError::VerificationFailed("Invalid or reused nonce".into()));
            }
        } else {
            // Standard mode: direct nonce verification
            if !state.nonce_mgr.verify_and_consume(nonce).await? {
                return Err(ActError::VerificationFailed("Nonce already used".into()));
            }
        }

        // 4. Check spend nullifier
        if !state.nullifier_mgr.check_spend_nullifier(proof.k_cur, proof.t_issue).await? {
            return Err(ActError::VerificationFailed("Spend nullifier already used".into()));
        }

        // 5. Verify the proof
        let mut rng = thread_rng();
        let response = verify_spend(
            &proof,
            state.config.current_epoch,
            nonce,
            &state.generators,
            &state.keys.pk_daily,
            &state.keys,
            state.h_ctx,
            &mut rng,
        )?;

        // 6. Cache the response for idempotency
        state.idempotency_cache.store(&idem_key, b"ok").await?;

        Ok(response)
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(all(test, feature = "server"))]
mod tests {
    use super::*;
    use redis::Client;

    #[tokio::test]
    async fn merkle_tree_proof_verification() {
        let nonces: Vec<[u8; 16]> = (0..10)
            .map(|i| {
                let mut n = [0u8; 16];
                n[0..8].copy_from_slice(&(i as u64).to_le_bytes());
                n
            })
            .collect();
        let tree = MerkleTree::build(nonces.clone());
        let root = tree.root();
        let proof = tree.prove(3).unwrap();
        assert!(proof.verify(&root));
        assert_eq!(proof.leaf, nonces[3]);

        let mut bad_proof = proof.clone();
        bad_proof.leaf[0] ^= 1;
        assert!(!bad_proof.verify(&root));
    }

    #[tokio::test]
    async fn bloom_filter_basics() {
        let mut bf = BloomFilter::new(1000, 0.01);
        let item1 = b"test1";
        let item2 = b"test2";
        assert!(!bf.contains(item1));
        bf.insert(item1);
        assert!(bf.contains(item1));
        assert!(!bf.contains(item2));
    }

    #[tokio::test]
    async fn high_privacy_nonce_flow() {
        let config = ServerConfig::default();
        let client = Client::open("redis://127.0.0.1:6379").unwrap();
        let mgr = NonceManager::new(client, 60, &config);
        let (root, count) = mgr.publish_high_privacy_batch(100).await.unwrap();
        assert_eq!(count, 100);

        let inner = mgr.inner.read().await;
        let tree = inner.current_tree.as_ref().unwrap();
        let nonce = tree.leaves[42];
        let proof = tree.prove(42).unwrap();
        drop(inner);

        assert!(mgr.verify_merkle_nonce(&nonce, &proof, &root).await.unwrap());
        assert!(!mgr.verify_merkle_nonce(&nonce, &proof, &root).await.unwrap());
    }
}
