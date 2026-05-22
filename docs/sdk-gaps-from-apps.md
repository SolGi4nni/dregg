# SDK Gaps Identified from bounty-board and compute-exchange

## 1. Duplicated Proof Verification Infrastructure

Both apps reimplemented qualification/proof verification from scratch (bounty-board `qualification.rs` ~280 LOC, compute-exchange `qualification.rs` ~300 LOC). The logic is structurally identical: parse proof header bytes, check attribute hash binding, validate threshold, verify predicate type byte, then stub out the actual STARK call.

**Proposed:** `pyana-sdk::verify` should expose:
```rust
pub fn verify_predicate_proof(proof: &[u8], attribute: &str, threshold: u64, predicate_type: PredicateType, federation_root: [u8; 32]) -> Result<bool, ProofError>
pub fn verify_membership_proof(proof: &[u8], federation_root: [u8; 32]) -> Result<bool, ProofError>
pub fn verify_ivc_standing(proof: &[u8], min_steps: u64) -> Result<bool, ProofError>
```
**Where:** `sdk/src/verify.rs` (already exists, add these). ~120 LOC.

## 2. Identical State Management Pattern (Arc<RwLock<HashMap>>)

Both apps build `Arc<RwLock<Inner>>` with `HashMap<[u8;32], T>` stores, current_height tracking, and nearly identical CRUD async methods. bounty-board `state.rs` is 227 LOC, compute-exchange `state.rs` is 250 LOC.

**Proposed:** A generic `ContentStore<T>` in a new crate:
```rust
pub struct ContentStore<T: Clone> { /* Arc<RwLock<HashMap<[u8;32], T>>> */ }
impl<T: Clone> ContentStore<T> {
    pub async fn insert(&self, id: [u8; 32], item: T);
    pub async fn get(&self, id: &[u8; 32]) -> Option<T>;
    pub async fn update<F: FnOnce(&mut T)>(&self, id: &[u8; 32], f: F) -> bool;
    pub async fn filter<F: Fn(&T) -> bool>(&self, f: F) -> Vec<T>;
}
```
**Where:** New `pyana-app-framework` crate. ~80 LOC.

## 3. Hex Encode/Decode Utilities Copied Verbatim

Both apps have identical `hex_encode`, `hex_decode`, `hex_decode_32`, `hex_nibble`, `bounty_id_hex`, `bounty_id_from_hex` functions (~50 LOC each).

**Proposed:** `pyana-types` should export `hex::encode(&[u8]) -> String` and `hex::decode_32(&str) -> Option<[u8;32]>`. ~30 LOC.

## 4. Escrow Construction Built from Raw Primitives

bounty-board `payment.rs` (300 LOC) manually assembles `Action`, `Effect::Transfer`, `Turn`, `CallForest`, `TurnReceipt` structs. compute-exchange `settlement.rs` builds `EscrowRecord` + `Effect::CreateEscrow` manually.

**Proposed SDK methods:**
```rust
impl PyanaEngine {
    pub fn create_escrow(&mut self, from: CellId, to: CellId, amount: u64, condition: EscrowCondition, timeout: u64) -> Result<[u8;32], EmbedError>;
    pub fn release_escrow(&mut self, escrow_id: [u8;32], proof: &[u8]) -> Result<TurnReceipt, EmbedError>;
    pub fn refund_escrow(&mut self, escrow_id: [u8;32]) -> Result<TurnReceipt, EmbedError>;
}
```
**Where:** `sdk/src/embed.rs`. ~100 LOC.

## 5. Commit-Reveal Protocol Wiring

compute-exchange wraps `pyana_intent::commit_reveal_fulfillment::FulfillmentRegistry` but has to manually thread it through state, map error types, and coordinate the two-phase flow. This should be a managed flow.

**Proposed:**
```rust
pub struct CommitRevealFlow { /* wraps FulfillmentRegistry + timing */ }
impl CommitRevealFlow {
    pub fn commit(&mut self, id: [u8;32], secret: &[u8;32], now: u64) -> Result<[u8;32], FlowError>;
    pub fn reveal(&self, id: &[u8;32], secret: &[u8;32], now: u64) -> Result<(), FlowError>;
    pub fn is_expired(&self, id: &[u8;32], now: u64) -> bool;
}
```
**Where:** `sdk/src/embed.rs` or new `sdk/src/flows.rs`. ~60 LOC.

## 6. Missing Axum Middleware for Proof-Gated Endpoints

Both apps verify proofs inline in handlers. The SDK's embed doc even shows a code example of an axum handler verifying proofs, but never ships it as a reusable extractor/layer.

**Proposed:**
```rust
pub struct PyanaProofLayer { engine: Arc<RwLock<PyanaEngine>> }
pub struct VerifiedProof { pub federation_root: [u8;32] }
// axum::FromRequestParts impl that extracts X-Pyana-Proof header, verifies, rejects 403
```
**Where:** New `pyana-app-framework` crate (feature-gated behind `axum`). ~80 LOC.

## 7. Direct Imports Below SDK Abstraction

- bounty-board imports `pyana_circuit::PredicateType` directly
- bounty-board imports `pyana_turn::action::{Action, Authorization, Effect, ...}` directly
- compute-exchange imports `pyana_intent::FillConstraints`, `pyana_intent::partial_fill::*`
- compute-exchange imports `pyana_turn::escrow::EscrowRecord`

**Fix:** Re-export `PredicateType`, `FillConstraints`, `EscrowCondition`, `EscrowRecord` from `pyana-sdk` root. ~10 LOC of `pub use` lines.

## Summary Table

| Gap | Location | Est. LOC |
|-----|----------|----------|
| Unified proof verification helpers | `sdk/src/verify.rs` | 120 |
| Generic async ContentStore | `pyana-app-framework` | 80 |
| Hex utilities | `pyana-types` | 30 |
| Escrow lifecycle on PyanaEngine | `sdk/src/embed.rs` | 100 |
| CommitRevealFlow managed wrapper | `sdk/src/flows.rs` | 60 |
| Axum proof middleware | `pyana-app-framework` | 80 |
| Re-exports of sub-crate types | `sdk/src/lib.rs` | 10 |
| **Total** | | **~480** |
