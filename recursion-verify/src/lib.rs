//! `dregg-recursion-verify`: the **VERIFY-ONLY** half of the dregg recursion tower.
//!
//! There is no prover here. No witness generation, no circuit construction, no
//! `build_and_prove_next_layer`, no GPU backend, no descriptor interpretation. What is here is
//! the four things a consumer needs to make a recursion root MEAN something:
//!
//! 1. [`config::DreggRecursionConfig`] — the STARK config the tower runs at (**the** one; not a
//!    verify-side copy — `dregg-circuit-prove` re-exports these items from
//!    `plonky3_recursion_impl::recursive`).
//! 2. [`verify::recursion_vk_fingerprint`] — *which circuit is this root a proof of*.
//! 3. [`verify::verify_recursive_batch_proof_with_config`] — *does it verify*.
//! 4. [`chain_root`] — reading the Mina phase-2 chain fold's exposed claim.
//!
//! # ⚑ WHY A CRATE AND NOT A CARGO FEATURE
//!
//! Because a feature is a hidden boundary and a crate is a real one. A `#[cfg(feature = …)]` arm
//! is off in one resolve and on in another, so a shape change compiles green until some consumer
//! four crates away selects the other arm — the class
//! `docs/reference/TURN-PROVER-CRATE-EXTRACTION-DESIGN.md` §0 was written to close, and the
//! reason `dregg-turn-prover` exists as a crate with **no `[features]` section at all**. This
//! crate is that same move on the verify side: it is always compiled as itself, so a consumer
//! that wants recursion verification takes an EDGE, and the edge is visible in
//! `cargo tree`.
//!
//! # ⚑ WHAT THE `dregg-turn` FIREWALL ACTUALLY REQUIRES — measured 2026-08-05, at source
//!
//! `turn/Cargo.toml:17-25` forbids the `dregg-circuit-prove` edge and justifies it with two
//! things. Both were checked, and neither is what the firewall buys:
//!
//! * **"the seL4 verifier-PD floor."** The seL4 verifier PDs build **no dregg crate at all**.
//!   `sel4/dregg-pd/verifier/Cargo.toml`'s entire `[dependencies]` is `sel4-microkit`;
//!   `sel4/dregg-pd/verifier-stark/` carries a *vendored copy* of `circuit/src/{field,stark}.rs`
//!   rather than a path dep. The one scaffold that does name a dregg crate
//!   (`sel4/verifier-pd/Cargo.toml` → `dregg-verifier`) is marked `STATUS: SCAFFOLD … not built
//!   here` — and `dregg-verifier` itself pulls `dregg-turn-prover` **unconditionally**
//!   (`verifier/Cargo.toml:35`), which pulls `dregg-circuit-prove`. So the recursion tower is
//!   already inside the very crate the seL4 floor would link. That justification is spent.
//! * **"the wasm/zkvm card."** `wasm/Cargo.toml` already declares `dregg-circuit-prove` AND
//!   `dregg-turn-prover` as normal deps, on purpose (the light-client-in-a-tab verifies the
//!   recursive IVC aggregate); `circuit-prove` compiles for `wasm32-unknown-unknown` and has a
//!   `[target.'cfg(target_arch = "wasm32")']` block to prove it. The only real zkvm guest,
//!   `circuit/sp1-guest/`, does not depend on `dregg-turn` at all.
//!
//! **And nothing enforces the edge.** There is no `deny.toml` in the repo, no `[bans]` section,
//! no `cargo tree` / `cargo metadata` gate naming these two crates, and none of
//! `scripts/local-gates.sh`'s ~90 gates touches it. The extraction design named that gate as its
//! own acceptance criterion (§5 PR1: *"`cargo build -p dregg-turn` is now prover-free and has no
//! `dregg-circuit-prove` edge"*) and it was never written. It is written now:
//! `tests/tests/recursion_verify_closure.rs`.
//!
//! What IS real, and is the reason to keep the edge out of `dregg-turn` anyway, is the
//! cfg-brittleness argument (§0) plus dependency weight for the ~50 consumers that inherit
//! `turn`. Neither is an argument against a consumer that WANTS verification taking this edge
//! explicitly — which is the whole design: `dregg-node` depends on this crate and injects the
//! backend; `dregg-turn` does not, and **fails the effect closed when nothing is injected**.
//!
//! ⚠ One correction to the firewall's own wording while we are here: `p3-circuit` is ALREADY in
//! `dregg-turn`'s normal graph (`dregg-turn → dregg-circuit → p3-poseidon2-circuit-air →
//! p3-circuit`). "Recursion-free" means precisely *no `p3-recursion` and no `p3-circuit-prover`*,
//! not "nothing from the recursion fork".
//!
//! # The dependency closure, stated plainly
//!
//! This crate pulls `p3-circuit-prover`, `p3-circuit` and `p3-recursion` at rev `fc3c6df` — see
//! `Cargo.toml` for why all three are unavoidable for VERIFICATION (the orphan rule forces the
//! `FriRecursionConfig` impl to sit with the type). It does **not** pull `dregg-circuit-prove`,
//! and therefore not the IVC tower, the shielded prover, the custom proof-bind engine, the
//! `wgpu`/`pollster`/`bytemuck` GPU backend, `dregg-lean-ffi`, `dregg-cell`, `dregg-commit`,
//! `dregg-p3-pasta` or `p3-bn254`. `tests/dependency_closure.rs` asserts both poles.

pub mod chain_root;
pub mod config;
pub mod verify;

pub use chain_root::{
    ChainClaim, chain_root_config, read_chain_claim_from_proof, verify_chain_root_bytes,
};
pub use config::{DreggRecursionConfig, create_recursion_config, ir2_leaf_wrap_config};
pub use verify::{
    RecursionVk, recursion_vk_fingerprint, verify_recursive_batch_proof,
    verify_recursive_batch_proof_with_config,
};
