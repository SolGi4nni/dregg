//! `dregg-circuit`: Zero-knowledge proof circuits for dregg authorization token chains.
//!
//! # ⚠️ dregg1 hand-written AIRs vs the verified dregg2 descriptor path
//!
//! Most AIRs in this crate are **hand-written, UNVERIFIED dregg1 circuits**.
//! They are NOT the source of truth. The verified circuit semantics live in
//! Lean under `metatheory/Dregg2/Circuit/` — 52 per-effect descriptor
//! instances (`Inst/*.lean`), each with a full-state soundness keystone over
//! ALL kernel-state fields, grounded on the single named `Poseidon2SpongeCR`
//! hypothesis (kernel-clean: `lake build` green, `#assert_namespace_axioms`
//! whitelisting only `{propext, Classical.choice, Quot.sound}`).
//!
//! The Lean is verified at the **digest / state-transition layer**; it
//! abstracts Poseidon2 / Merkle / selector-dispatch as a hypothesis. The
//! hand-written AIRs here (`effect_vm/`, `note_spending_witness`, `poseidon2_air`,
//! `effect_action_air`) are the layer that actually computes those hashes /
//! Merkle paths in-circuit — a DIFFERENT abstraction layer, not a competing
//! implementation. They retire one FRONTIER at a time as the Lean-emitted
//! descriptor interpreter (`lean_descriptor_air`) gains hash / limb / dispatch
//! gates. Do NOT duplicate or hand-extend a circuit without checking whether the
//! verified Lean descriptor already covers the statement; see
//! `metatheory/docs/rebuild/_RUST-CIRCUIT-CONSOLIDATION.md` and
//! `_DREGG1-DREGG2-UNIFICATION-LEDGER.md`. Dead/duplicate AIRs get deleted, not
//! kept (already gone: `effect_interp`, `garbled_air_p3`).
//!
//! # Trust Model
//!
//! This crate operates at the **TRUSTLESS** trust level.
//!
//! - **Soundness**: All proofs are independently verifiable by any party with access to
//!   the public inputs and verification key. A valid proof guarantees that the prover
//!   knows a witness satisfying the circuit constraints, up to the FRI soundness error
//!   ledgered below.
//! - **Assumptions**: Cryptographic hardness of the hash function (BLAKE3/Poseidon2),
//!   correct circuit constraint encoding, and honest verifier randomness (Fiat-Shamir).
//!   No trust in any federation member, operator, or third party.
//! - **Verifiable by**: Anyone. Proofs are publicly verifiable with O(log n) verification
//!   time. Light clients, external auditors, and cross-federation peers can all verify
//!   independently.
//!
//! ## The FRI soundness ledger — the deployed numbers
//!
//! There is no `2^{-128}` here — and there is no single per-fold number for this system
//! either. The ledger is **PARAMETRIC and LEAN-OWNED**: `Dregg2.Circuit.FriLedger.friLedger
//! : FriParams → Ledger` is a computable Lean function, `@[export dregg_fri_ledger]`-ed, and
//! `circuit-prove/tests/fri_params_soundness_budget.rs` CALLS it for each of the **7**
//! shipped configs. Rust derives none of these figures — it marshals knobs in and reports
//! columns out. (Its predecessor re-typed the formulas in Rust; that twin is deleted.)
//!
//! One parametric theorem justifies every row — `FriLedgerSound.ledger_perFold_soundness`,
//! instantiating `FriArityTransfer.good_card_le_of_phase_injective` at each config's arity
//! `m = 2^max_log_arity` and folded domain `|κ| = 2^log_blowup`. The three columns:
//!
//! - **per-fold bits — PROVEN, and per-config.** The proximity-gap error exponent:
//!   `|Good| ≤ (m−1)·C(|κ|,2)` over the challenge field `|F| = babyBearP^ext_deg ≈ 2^123.6`.
//!   It is **structure-specific and config-specific** — not a bound on FRI in general, and
//!   not one number for the system:
//!   * `ir2_config` — **the DEPLOYED wrap** — folds at arity **8**: `|Good| ≤ 7·C(64,2) =
//!     14112`, giving **109 bits** (`FriArityTransfer.arity8_perFold_soundness`). The
//!     often-quoted ~112.6 is proved for a 2-to-1 fold the deployed prover does NOT run;
//!     `log₂ 7 ≈ 2.807` bits is the price of the arity-8 moment curve.
//!   * `ir2_leaf_wrap_config` (arity 2 at `log_blowup 6`) is the ONE shipped config ~112.6
//!     describes: `|Good| ≤ C(64,2) = 2016` ⇒ **112 bits**.
//!   * v1 `create_config` / `create_zk_config`: **116**. `create_outer_config` (**the config
//!     the gnark ETH-wrap verifies**) / its GPU twin / `create_recursion_config`: **118**.
//!   ⚑ per-fold RISES as `log_blowup` FALLS, and that is NOT an upgrade — a smaller folded
//!   domain has fewer pairs, hence fewer good challenges. The rate is paid for in the QUERY
//!   ledger below. The columns are independent (`query_ledger_does_not_determine_perFold`):
//!   never multiply them into one figure.
//!   ⚑ Every per-fold number rests on the `M = 1` fiber bound, carried as the per-config
//!   HYPOTHESIS `hΦ` by the arity-generic count. It is now DISCHARGED from farness at ALL
//!   six shipped configs by `Dregg2.Circuit.FriArityFiberDischarge.phase_injective_of_far`
//!   (deployed arity 8: `arity8_phase_injective`, `dOut ≥ 496`), which builds the
//!   arity-`2^k` rate-`2^(−b)` RS setups the tree previously lacked. `#assert_axioms` is
//!   blind to hypotheses — the discharge is a theorem, not an axiom-check result.
//!   ⚑ **These numbers are claims about NEAR-CAPACITY words, not about the operating
//!   radius.** The `hΦ` discharge fires only for words `dOut ≥ |L| − 2·arity`-far — `496` of
//!   `512` = **96.9%** at the deployed wrap — while FRI's proven argument runs at the
//!   **Johnson radius** `1 − √ρ` = **87.5%** (`dOut = 448`). `M = 1` is **FALSE** in the band
//!   `[448, 496)`: `Dregg2.Circuit.FriJohnsonRadiusGap.deployed_M1_false_at_johnson` exhibits
//!   a `448`-far word with a non-injective phase map, and `deployed_discharge_threshold_tight`
//!   shows `496` cannot be weakened by even one. So `109` is TRUE and NON-VACUOUS about
//!   `96.9%`-far words and does not cover the operating regime. At the Johnson radius the
//!   fiber bound is `M ≤ 7` and the honest count is `arity8_johnson_good_card_le`'s `3528` ⟹
//!   **~111 bits** — HIGHER only because it is a WEAKER claim (it bounds the `dIn = 56`
//!   challenge family, not the larger `dIn = 62` one). Different objects; neither dominates.
//! - **Johnson bits — the QUERY column, proven for any code.** The list-decoding-to-√rate
//!   figure, `num_queries × log_blowup / 2 + query_pow_bits`. `73` on six shipped configs;
//!   **`71` on `create_recursion_config`**, whose `14` query-PoW bits make it the weakest
//!   shipped config and set the gate's floor (`recursion_config_is_the_weakest_link`).
//!   ⚑ **This column is the `m → ∞` IDEALISATION and it DROPS `ε_C`.** `log_blowup/2` is
//!   `−log₂ α` in the limit of BCIKS20's `α = √ρ·(1 + 1/2m)` (eprint 2020/654, Lemma 8.2 /
//!   Thm 8.3, printed pp. 40–41); the paper's actual bound is `ε_FRI = ε_C + α^s`. The
//!   dropped commit-phase term is `FriLedger.friCommitLedger`'s `commitBits`, and at the
//!   deployed wrap it BINDS: `71` at `|D⁽⁰⁾| = 2^12`. Composing them as ethSTARK eq. (20)
//!   does (`λ ≥ min{−log₂ ε_C, ζ − s·log₂ α} − 1`) reads **~70**, not `73`. Read `73` as the
//!   query ledger it is — never as "the proven soundness".
//! - **capacity bits — REFUTED; a knob-drift baseline, NOT a security claim.** The
//!   up-to-`1−ρ` arithmetic `num_queries × log_blowup + query_pow_bits` that production
//!   STARKs historically quote. The conjecture it rests on is **refuted**: Crites–Stewart
//!   (eprint 2025/2046, *On Reed–Solomon Proximity Gaps Conjectures*) disprove it by
//!   reduction, and Kambiré (arXiv 2604.09724, *Proximity Gaps Conjecture Fails Near
//!   Capacity over Prime Fields*) exhibits a counterexample over prime fields. The gate's
//!   `≥ 128` check is a conservative ENGINEERING MARGIN on this refuted arithmetic — drift
//!   detection only, not a proof and not a claim that 128 bits are achieved. `130` on six
//!   configs; **exactly `128` — zero headroom — on `create_recursion_config`**.
//! - **Caps.** All figures are additionally capped by the degree-4 BabyBear extension
//!   (~2^124 challenge space) and the Poseidon2 commitment hash. Every figure sits under it.
//!
//! The v1 and IR-v2 configs share a QUERY ledger, and the gate asserts that parity: v1
//! [`plonky3_prover::create_config`] at `(log_blowup 3, 38 queries, 16 PoW)` and IR-v2
//! `descriptor_ir2::ir2_config` at `(6, 19, 16)` each give capacity `130` / Johnson `73`
//! (proved: `FriLedgerSound.wrap_prodV1_query_ledger_parity`). The `(6, 19)` pin is the
//! measured size-optimal point AT that parity. ⚑ They do NOT share a per-fold posture
//! (109 vs 116) — the parity is a fact about two columns, not about "the ledger".
//!
//! ⚑ No published counterexample instantiates at BabyBear — and that is NOT a defence.
//! Kambiré's Thm 1 picks the prime AFTER the block length ("there exist infinitely many block
//! lengths `n` … there exists a prime `p < n^A` with `p ≡ 1 (mod n)`", via a quantitative
//! Linnik theorem), so `p` GROWS with `n` while dregg runs a FIXED 31-bit prime
//! (`p = 2³¹ − 2²⁷ + 1`); and his radius `δ = (1−ρ) − Ω(1/log n)` sits vanishingly close to
//! CAPACITY, far above the Johnson radius this system runs at. Also refuting, none reaching
//! us: Diamond–Gruen (eprint 2025/2010, rate → 0 only) and BCHKS (ECCC TR25-169 Thm 1.6,
//! constant rate — `ρ = 1/64` exactly at `τ = 4` — but characteristic 2 and a random
//! `F₂`-subspace domain, where ours is an odd-characteristic multiplicative coset).
//! A conjecture refuted in general is not a security basis for anyone, whatever the
//! field-cardinality technicality — which is exactly why the capacity column is carried only
//! as a drift canary and every claim here stands on the Johnson and per-fold columns.
//!
//! All code in this crate MUST maintain the property that a valid proof implies a valid
//! witness. Bugs here break the entire trust model -- a soundness bug allows forged
//! authorization tokens.
//!
//! This crate implements the circuit layer for the dregg ZK token system,
//! proving: "I hold a valid attenuated token chain whose final state authorizes
//! action X" without revealing the chain or capabilities.
//!
//! # Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────────┐
//! │                     Presentation Proof                               │
//! │                                                                     │
//! │  ┌──────────────┐   ┌──────────────┐         ┌──────────────┐     │
//! │  │  Fold AIR #1 │──▶│  Fold AIR #2 │──▶ ... ─▶│  Fold AIR #N │     │
//! │  │  (attenuation)│   │  (attenuation)│         │  (attenuation)│     │
//! │  └──────────────┘   └──────────────┘         └──────────────┘     │
//! │         │                                            │             │
//! │         │           initial_root                 final_root        │
//! │         │                                            │             │
//! │         ▼                                            ▼             │
//! │  ┌──────────────┐                          ┌──────────────┐      │
//! │  │ Merkle AIR   │                          │Derivation AIR│      │
//! │  │ (issuer key) │                          │(authorization)│      │
//! │  └──────────────┘                          └──────────────┘      │
//! │         │                                                         │
//! │         ▼                                                         │
//! │  federation_root                                                  │
//! └─────────────────────────────────────────────────────────────────────┘
//!
//! Public Inputs: [federation_root, request_predicate, timestamp]
//! Private Witness: [token_chain, derivation_trace, issuer_key]
//! ```
//!
//! # Features
//!
//! - `plonky3` (default, always-on no-op): retained so the existing
//!   `#[cfg(feature = "plonky3")]` sites resolve true on the verify floor. Every p3
//!   dependency of this crate is non-optional — `dregg-circuit` IS the prover-free
//!   batch-STARK verify surface plus the recursion-free `prove_batch` provers. Turning
//!   this off does not remove Plonky3. See `Cargo.toml`'s split-policy note.
//!
//! There is no `mock` feature. The old `verifier` / `prover` features are gone: their
//! items are now unconditional or moved to `dregg-circuit-prove`, which owns the
//! recursion tower (`cargo tree -p dregg-circuit` is recursion-free, and that is
//! load-bearing).
//!
//! # Proof Backends
//!
//! - [`plonky3_prover`]: the deployed Plonky3 STARK prover/verifier (FRI + Poseidon2
//!   Merkle + Fiat-Shamir), including the production FRI knobs (`PROD_FRI_*`) the
//!   soundness ledger above is computed from.
//! - [`descriptor_ir2`]: the IR-v2 descriptor interpreter and its deployed FRI config
//!   (`IR2_FRI_*`) — the path a light client verifies against.
//! - [`lean_descriptor_air`]: parses a Lean-emitted `EffectVmDescriptor` and rebuilds
//!   the AIR from the descriptor alone (the prover authors no constraint).
//! - [`constraint_prover`]: constraint satisfaction checker that validates circuit
//!   logic by evaluating AIR constraints directly on the execution trace. It generates
//!   no cryptographic proof — it is a development/testing oracle, not a backend a
//!   verifier trusts.
//!
//! # Security Properties
//!
//! The circuit enforces:
//! 1. **Fact membership**: Every referenced fact exists in the committed Merkle tree.
//! 2. **Valid narrowing**: Each attenuation step only removes facts or adds checks.
//! 3. **Derivation correctness**: The authorization follows from the final state via valid rules.
//! 4. **Issuer accountability**: The token chain originates from a federated issuer.
//! 5. **Freshness**: The proof is bound to a specific timestamp.
//!
//! # Components
//!
//! - [`field`]: BabyBear field arithmetic (p = 2^31 - 1).
//! - [`poseidon2`]: SNARK-friendly hash function for in-circuit hashing.
//! - [`merkle_air`]: 4-ary Merkle membership proof circuit.
//! - [`constraint_prover`]: Constraint satisfaction evaluator (no cryptographic proof).
//! - [`plonky3_prover`]: the deployed STARK prover/verifier (FRI + Merkle + Fiat-Shamir).
//! - [`descriptor_ir2`] / [`lean_descriptor_air`]: the verified descriptor path.
//!
//! Hand-written dregg1 AIRs, retained and `#[deprecated]` — see the header warning above;
//! they are NOT the source of truth and retire one frontier at a time:
//! [`derivation_air`] (single Datalog derivation step), [`fold_air`] (attenuation step),
//! [`presentation`] (the composed presentation proof).

// ⚠ NOT YET DENIABLE — `#![deny(rustdoc::broken_intra_doc_links)]` belongs here and does not
// fit yet (measured 2026-07-15, `CRATE-EXCELLENCE-PLAN.md` §4 MOVE 4's last bullet). Turning it
// on today reds `cargo doc -p dregg-circuit` with **311** hits, of which ~187 are pure array
// notation rustdoc mis-parses as links (`[0]`, `[4..7]`) and most of the rest are prose in
// brackets (`[a]`, `[asset]`). Only a handful are genuine doc rot — the lint DID find one this
// sweep missed (`constraint_prover.rs`'s third live `[crate::stark]`, now dead). Landing the
// deny is a real lane (escape ~300 bracket spans), not a one-line add; shipping it red would
// just train readers to ignore `cargo doc`. Do it, but do it as its own lane.

pub mod air_descriptor;
pub mod babybear8;
pub mod binding;
pub mod body_membership;
pub mod constraint_prover;
pub mod dsl;
pub mod faithful8;
pub mod field;
pub mod ivc;
/// FFI symbols the Lean-compiled storage logic calls back for its Poseidon2 hashing (@[extern]).
pub mod storage_ffi;

// Shared accumulator types used by both DSL and non-membership modules.
pub mod accumulator_types;

// Backward-compatible shim modules (type definitions + re-exports from DSL).
// These contain deprecated StarkAir impls superseded by DSL descriptors.
pub mod bridge_action_witness;
#[allow(deprecated)]
pub mod derivation_air;
pub mod effect_action_air;
pub mod fold_types;
#[allow(deprecated)]
pub mod garbled_air;
pub mod merkle_air;
pub mod merkle_types;
#[allow(deprecated)]
pub mod multi_step_witness;
#[allow(deprecated)]
pub mod note_spending_witness;
#[allow(deprecated)]
pub mod poseidon2_air;
#[cfg(feature = "plonky3")]
pub mod temporal_predicate_air;

/// Backward-compatible re-export. Prefer [`constraint_prover`] for new code.
#[doc(hidden)]
pub mod mock_prover {
    pub use crate::constraint_prover::*;
}
pub mod poseidon2;
#[allow(deprecated)]
pub mod presentation;

/// The GENUINE-NON-AMP cap-graph descriptor loader (the ARGUS linchpin on the delegation family:
/// `delegate`/`delegateAtten`/`attenuate`/`introduce`/`revoke`/`refresh`): the Lean-verified
/// `EffectVmDescriptor` that, on a cap-graph row, RECOMPUTES `cap_root` (`hash[edge_leaf, old_root]`,
/// op-tagged — no opaque digest) AND enforces in-circuit non-amplification (`granted ⊑ held` submask,
/// per bit, over the SAME `rights` felt the recompute binds). Byte-pinned to
/// `Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.attenuateVmDescriptorGenuineNonAmp`; parsed by the
/// running `parse_vm_descriptor` (the prover authors no constraint). Standalone (not in the locked
/// `effect_vm_descriptors` registry); ONE JSON serves all six effects (selector→JSON fan-out).
#[cfg(feature = "plonky3")]
pub mod cap_delegation_nonamp_descriptor;
/// The OPENABLE `capability_root` descriptor loader (cap-reshape crown #103, the ARGUS linchpin):
/// the Lean-verified `EffectVmDescriptor` that checks non-amplification (`granted ⊑ held` submask, per
/// bit) + production-authority (the mint opens the issuer cap from the producer's held-set root)
/// IN-CIRCUIT. Byte-pinned to `Dregg2.Circuit.Emit.EffectVmEmitCapReshape.capReshapeJson`; parsed by
/// the running `parse_vm_descriptor` (the prover authors no constraint). Standalone (not in the locked
/// `effect_vm_descriptors` registry).
pub mod cap_reshape_descriptor;
/// The canonical, openable capability-set commitment: a sorted Poseidon2 binary
/// Merkle tree over a cell's c-list. The SINGLE source of truth for the
/// `cap_root` value — `dregg-cell`'s `compute_canonical_capability_root` calls
/// it, and the EffectVM circuit seeds its `cap_root` column from the same value
/// (cap Phase A). Pure Poseidon2 — no plonky3 dependency, so it builds on any consumer.
pub mod cap_root;
#[allow(deprecated)]
pub mod committed_threshold;
pub mod effect_vm;
/// The Lean-emitted EffectVM descriptor registry: every verified-by-construction
/// `EffectVmDescriptor` JSON, keyed by selector index, with an anti-drift
/// fingerprint guard. Foundation for the EffectVM circuit cutover.
pub mod effect_vm_descriptors;
#[allow(deprecated)]
pub mod garbled;
/// THE HEAP's canonical, openable commitment (REFINEMENT-DESIGN Decision 1):
/// the sorted Poseidon2 binary Merkle map over `(collection_id, key) → value`,
/// generalizing `cap_root` with the generic `hash[addr, value]` leaf. The
/// SINGLE source of truth for the `heap_root` register value; the descriptor
/// gadget (`EffectVmEmitHeapRoot.lean`) recomputes its address/leaf images
/// in-row. Pure Poseidon2 — no plonky3 dependency, so it builds on any consumer.
pub mod heap_root;
pub mod native_signature;
#[allow(deprecated)]
pub mod non_membership;
/// THE OPENABLE `fields_root` commitment + the in-circuit INSERTION gate (the
/// REFUSAL ledgerless-authority close, #103): a sorted Poseidon2 binary Merkle
/// map over a cell's overflow user-field entries `key → value`, whose
/// post-insertion root is DERIVED in-circuit from the pre-root + the public
/// `(key, value)`. Lets refusal's authority change be FORCED in-circuit (no
/// trusted post-cell / `Anchor::RecordDigest`). The path-folding AIR is
/// `dsl::openable_fields_insertion`.
pub mod openable_fields_root;
pub mod predicate_program;
#[allow(deprecated)]
pub mod quantified_absence;
pub mod schnorr_curve;
pub mod schnorr_sig;
pub mod stark_zk;

pub mod temporal_predicate_dsl;

#[cfg(feature = "plonky3")]
pub mod plonky3_prover;

/// Generic Plonky3 AIR that interprets a Lean-emitted circuit descriptor at
/// `eval`-time and drives the real `p3-uni-stark` prover — so Lean-emitted
/// circuits REPLACE hand-coded AIRs, including the retired Rust-authored Merkle
/// AIR. See module docs.
#[cfg(feature = "plonky3")]
pub mod lean_descriptor_air;

#[cfg(feature = "plonky3")]
pub mod plonky3_recursion;

// `plonky3_recursion_impl`, `lean_lookup_air`, `effect_vm_p3_air`, `shielded`,
// `custom_proof_bind`, `recursive_witness_bundle`, `ivc_turn_chain`,
// `joint_turn_aggregation`, and `joint_turn_recursive` moved to the
// `dregg-circuit-prove` crate (the heavy recursion/prove surface). This crate is
// the verify floor; a producer depends on `dregg-circuit-prove`.

/// Descriptor IR v2 — THE EPOCH multi-table batch-STARK interpreter
/// (`docs/EPOCH-DESIGN.md`). Parses the versioned `"ir":2` wire emitted by Lean
/// (`Dregg2.Circuit.DescriptorIR2.emitVmJson2`) and assembles the five-table
/// batch STARK (main + Poseidon2 chip + range/byte + memory + map-ops) over the
/// fork's `p3-batch-stark` + `p3-lookup` LogUp argument. Hashing becomes a
/// boundary phenomenon: hash sites ride the chip bus, state accesses ride the
/// offline-memory-checking multiset (Blum), and authenticated openings only
/// materialize at the map-ops boundary. The law is descriptor-driven — Rust
/// authors NO constraints; it realizes the declared tables/lookups/mem-ops/
/// map-ops. v1 descriptors keep proving through `lean_descriptor_air` until the
/// flag-day. See module docs.
///
/// THE EPOCH multi-table batch-STARK interpreter. Both the VERIFY surface
/// (`verify_vm_descriptor2{,_with_config}`, the AIRs, `ir2_config`) and the
/// recursion-free PROVE surface (`prove_vm_descriptor2*`, trace assembly,
/// `prove_batch`) live here — all on verify-floor p3 deps (`p3-batch-stark` /
/// `p3-uni-stark`), so the whole module is unconditional in the verify floor.
pub mod descriptor_ir2;

// `custom_proof_bind` and `recursive_witness_bundle` moved to `dregg-circuit-prove`.

/// Stage 7-γ.2 Phase 2 joint bilateral aggregation AIR. Consumes N per-cell
/// γ.2 PI vectors and the schedule-derived projection; emits a single outer
/// proof attesting bilateral consistency. See module docs and
/// `STAGE-7-GAMMA-2-PHASE-2-SKETCH.md`.
pub mod bilateral_aggregation_air;

/// Turn-wide CROSS-CELL value-conservation AIR (Σδ=0), emitted from Lean (law #1; closes foolable
/// gap #6). Sums the per-cell proofs' published signed NET_DELTA PIs into a prefix-sum-to-zero per
/// asset — the in-circuit `Σδ=0` the off-AIR debit↔credit pairing could not force. ADDITIVE: NOT
/// wired into the live `proof_verify.rs` (see module docs for the verifier handoff seam). Lean twin
/// `metatheory/Dregg2/Circuit/CrossCellConservation.lean`.
pub mod cross_cell_conservation_air;

/// The WHOLE-IMAGE FOLD CHIP: the in-circuit realization of the `hpin` obligation — an AIR that
/// COMPUTES the depth-`d` binary-Merkle fold of an ENTIRE declared whole-boundary view (via a
/// sorted-insert chain from the empty root) and PINS it to the published-root public input,
/// realizing the no-extra-cells direction of the cross-cell read in-circuit. Lean soundness:
/// `metatheory/Dregg2/Exec/UniversalBridge.lean` (`crossCellRead_whole_image` /
/// `cross_cell_read_no_extra_cell` / `_teeth`, the `MapMerkleRoot.mapRoot_injective` anti-ghost).
pub mod whole_image_fold;

/// BLOCK / BATCH-level cross-cell conservation COLLECTOR (the deeper half of gap #6): gathers every
/// per-cell proof's published signed NET_DELTA, groups by asset (AssetId := issuer-cell), and runs
/// the committed `cross_cell_conservation_air` per asset — ACCEPTS the block iff every asset's Σδ=0
/// (incl. declared mint/burn), else REJECTS. The cross-cell light-client bite the per-cell-isolated
/// path structurally cannot give. ADDITIVE: NOT wired into the live verifier (see module docs for
/// the `verify_proof_carrying_turn_bundle` handoff seam).
pub mod block_conservation;

// `effect_vm_p3_air` moved to `dregg-circuit-prove`.

/// Sorted-set neighbor-adjacency STARK: proves two leaves are *consecutive*
/// under a committed binary Merkle root, closing the Silver non-membership
/// wide-bracket forge. See module docs and `dregg_cell::predicate`'s
/// `SortedNeighborNonMembershipVerifier` / `CredentialSetMembershipVerifier`.
pub mod membership_adjacency_air;

/// Foundation 2 of the StarkProof→descriptor-prover migration: the depth-GENERAL binary
/// Poseidon2 Merkle-membership IR-v2 descriptor builder. One Merkle level per trace row, tied by
/// a `WindowGate` continuity gate (the `AdjacencyMembershipEmit` multi-level precedent), so a
/// depth-`d` witness genuinely hashes `d` levels — replacing the executor's depth-2 pad hack. See
/// module docs; the Rung-2 depth-general soundness lift is a named Lean follow-on.
pub mod membership_descriptor_general;

/// The depth-GENERAL **4-ary** Poseidon2 Merkle-membership IR-v2 descriptor builder — the arity-4
/// twin of `membership_descriptor_general`, byte-faithful to the DEPLOYED `hash_4_to_1`-chained set
/// root (production membership is 4-ary; the binary builder is an arity mismatch). One 4-ary Merkle
/// level per row, position carried as two bits so the child-selection gates keep integer
/// coefficients while reproducing production's Lagrange-on-position arrangement. See module docs.
pub mod membership_descriptor_4ary;

/// Rust witness builder for the emitted neighbor-adjacency descriptor
/// (`dregg-membership-adjacency::poseidon2-v1`) — the analog of `membership_witness`, so consumers of
/// `descriptor_by_name` can prove/verify a sorted-set non-membership (consecutive-leaf) witness. See
/// module docs.
pub mod adjacency_witness;

/// Rust witness builder for the emitted **Datalog derivation** descriptor
/// (`dregg-derivation-v1`, `DerivationEmit.lean`) — maps a `DerivationWitness` to the real deployed
/// 379-col trace (via `dsl::derivation::generate_derivation_trace_dsl`) plus the 13 public inputs the
/// emitted descriptor pins (`state_root`, `derived_hash`, and the 8 exported body-fact hashes), so
/// consumers of `descriptor_by_name` can prove/verify a derivation step through the real p3 prover
/// (the descriptor prover extends the trace to 386 cols and fills the C4 chip lanes). See module docs.
pub mod derivation_witness;

/// Rust witness builder for the emitted `presentation` descriptor
/// (`dregg-presentation-freshness::summary-v1`, `PresentationEmit.lean`) — the analog of
/// `membership_witness_4ary` for the blinded-presentation family, so consumers of
/// `descriptor_by_name` can prove/verify a fresh-token presentation summary. See module docs.
pub mod presentation_descriptor_witness;

/// Rust witness builder for the emitted **bound-presentation** descriptor
/// (`dregg-bound-presentation::v1`, `BoundPresentationEmit.lean`) — the Golden-Lift-stage-3a analog
/// of `presentation_descriptor_witness`, producing a trace whose `presentation_tag` PI is CONSTRAINED
/// in-circuit to its arity-4 Poseidon2 chip image, so consumers of `descriptor_by_name` can
/// prove/verify a bound presentation through the real p3 prover. See module docs.
pub mod bound_presentation_witness;

/// Rust witness builder for the emitted blinded ring-membership descriptor
/// (`dregg-blinded-membership::v1`, `BlindedMembershipEmit.lean`) — the blinded-membership twin of
/// `bound_presentation_witness`: `blinded_leaf` and the Merkle path are both constrained in-circuit,
/// so consumers of `descriptor_by_name` can prove/verify a blinded membership through the real p3
/// prover (and the fold adapter can wrap it as a recursion leaf). See module docs.
pub mod blinded_membership_witness;

/// Descriptor + Rust witness builder for the emitted note-spend recursion-leaf descriptor
/// (`note-spend-leaf::dregg-note-spending-dsl-v3`, `NoteSpendingLeafEmit.lean`) — the analog of
/// `membership_witness_4ary` / `adjacency_witness` for the note-spend (blinded-note) family, so
/// consumers of `descriptor_by_name` can prove/verify a real spend (spending-key knowledge +
/// full-width commitment + Merkle membership + the felt-domain mint identity) WITHOUT the recursion
/// crate. See module docs.
pub mod note_spend_witness;

/// Rust witness builder for the emitted sorted-tree non-revocation (freshness) descriptor
/// (`dregg-non-revocation-sorted-tree::poseidon2-v1`) — the analog of `adjacency_witness`, so
/// consumers of `descriptor_by_name` can prove/verify that a queried item is strictly bracketed by
/// two adjacent committed sorted leaves (hence NOT revoked). See module docs.
pub mod non_revocation_witness;

/// Depth-general production witness builder for the composed Lean-emitted non-revocation descriptor
/// (`dregg-non-revocation-adjacency::poseidon2-fact-v1`). Unlike the legacy depth-2 witness rail,
/// this emits one genuine authentication row per revocation-tree level and preserves the deployed
/// depth-4 / 16-leaf tree.
pub mod non_revocation_adjacency_witness;

/// Rust witness builder for the Lean-emitted whole-history turn-chain binding descriptor
/// (`dregg-turn-chain-binding-v2`). It builds the 14-column shared-Poseidon2-chip trace and the
/// four scalar public inputs, including the continuing-hash padding rows used by the deployed fold.
pub mod turn_chain_witness;

/// Rust witness builder for the emitted arithmetic-threshold descriptor
/// (`dregg-predicate-arith-ge::threshold-v1`) — the analog of `membership_witness_4ary` /
/// `adjacency_witness`, so consumers of `descriptor_by_name` can prove/verify a
/// `GreaterThanOrEqual(value, threshold)` predicate witness (value/threshold/diff + the appended
/// range-decomposition limbs). See module docs.
pub mod predicate_arith_witness;

/// Rust witness builders for the emitted arithmetic COMPARISON descriptors — the `≤` / `>` / `<` /
/// `≠` / `InRange` siblings of `predicate_arith_witness` (`≥`). Each rides the same range/diff tooth
/// (`≠` swaps in a nonzero-inverse gadget), dispatched via `descriptor_by_name`. See module docs.
pub mod predicate_comparison_witness;

/// The IR-v2 delegation scope-binding descriptor (`dregg-delegate::v2`) — the descriptor-world twin
/// of the executor's `StarkDelegation` scope check (`action.rs::verify_stark_delegation_binding`),
/// pinning the 24-limb `[root_issuer ‖ target ‖ scope_hash]` scope to public inputs. See module docs.
pub mod delegate_descriptor;

/// Foundation 1 of the StarkProof→descriptor-prover migration: `descriptor_by_name`, the
/// descriptor-world analog of `dsl::descriptors::circuit_for_air_name`. Maps a predicate-kind /
/// AIR-name to its emitted `EffectVmDescriptor2` (byte-pinned golden decode + the depth-general
/// membership builder); a miss returns `None` (never a silent accept). See module docs.
pub mod descriptor_by_name;

pub mod backends;
// `ivc_turn_chain`, `joint_turn_aggregation`, `joint_turn_recursive` moved to
// `dregg-circuit-prove`.
pub mod proof_forest;
pub mod proof_tier;

/// The shared REFUSAL DISCRIMINATOR for adversarial tests — `must_refuse` (require a fail-closed
/// `Err`), `must_refuse_or_unsat_panic` (accept the p3 debug prover's DOCUMENTED unsat panic, and
/// only that), and `must_accept` (the honest pole, so a paired negative is not vacuous).
///
/// Public rather than `#[cfg(test)]` because `dregg-circuit-prove` depends on this crate normally
/// and its `tests/` link it as an external rlib; see the module docs for why this is not a Cargo
/// feature. The module has no accept path, so it arms nothing in a production build.
pub mod refusal;

// `shielded` moved to `dregg-circuit-prove`.

#[cfg(test)]
#[allow(deprecated)]
mod tests;

// Proof tier types — prevents scaffold/test proofs from satisfying production verifiers.
pub use proof_tier::{CryptographicProof, ProofTier, VerifiedProof};

// The faithful-commitment TYPE WALL (docs/FAITHFUL-COMMITMENT-LAW.md).
pub use faithful8::Faithful8;

// Re-export primary types.
pub use binding::{
    ACTION_BINDING_WIDTH, ActionBinding, PRESENTATION_TAG_WIDTH, PresentationTag, WideHash,
    compute_action_binding, compute_action_binding_narrow, compute_presentation_tag,
    compute_presentation_tag_narrow,
};
pub use body_membership::{BodyFactMerkleProof, collect_body_fact_hashes};
#[allow(deprecated)]
pub use committed_threshold::{
    CommittedThresholdAir, CommittedThresholdWitness, compute_threshold_commitment,
    generate_blinding,
};
#[doc(hidden)]
pub use constraint_prover::MockProof;
#[doc(hidden)]
pub use constraint_prover::MockProofResult;
#[doc(hidden)]
pub use constraint_prover::MockProver;
pub use constraint_prover::{
    Air, ConstraintCheckResult, ConstraintProof, ConstraintProver, ConstraintViolation,
};
// `EffectVmAir` (the v1 hand-AIR) is RETIRED; the rotated IR-v2 descriptor path
// is the sole effect-VM circuit.
pub use effect_vm::{
    CellState, EFFECT_VM_WIDTH, Effect, NUM_EFFECTS, compute_effects_hash, encode_net_delta,
    extract_asset_class, extract_custom_proof_commitments, extract_net_delta,
    generate_effect_vm_trace, verify_balance_limb_pis,
};
pub use field::BabyBear;
pub use ivc::{
    FoldDelta, FoldStepWitness, IvcBackend, IvcBackendProof, IvcBuilder, IvcPresentationProof,
    IvcProof, IvcVerification, MAX_FOLD_DEPTH, StateTransitionAir, prove_ivc, verify_ivc,
};
pub use non_membership::{
    NonMembershipCheck, NonMembershipProver, SetIdentifier, compute_set_accumulator,
    derive_alpha_for_set,
};
pub use presentation::{
    AuthorizationProof, PresentationAir, PresentationProof, PresentationVerification,
    PresentationWitness, prove_authorization,
};
// Re-export predicate types at crate root for backward compatibility.
pub use dsl::predicates::{PredicateAir, PredicateType, PredicateWitness, compute_fact_commitment};

// Re-export arithmetic predicate types at crate root.
pub use dsl::predicates::{
    ArithExpr, ArithPredicate, ArithmeticPredicateWitness, CompareOp,
    compute_arithmetic_fact_commitment,
};

// Re-export relational predicate types at crate root.
pub use dsl::predicates::{
    RelationalOp as RelationType, RelationalPredicateWitness, RelationalWitness,
    compute_value_commitment,
};

// Re-export multi-step authorization constants.
pub use multi_step_witness::MAX_DELEGATION_DEPTH;

/// Backward-compatible module alias for predicate types.
pub mod predicate_types {
    pub use crate::dsl::predicates::compute_blinded_fact_commitment;
    pub use crate::dsl::predicates::*;
    pub use crate::dsl::predicates::*;
    pub use crate::dsl::predicates::*;
}

// Schnorr signature scheme over BabyBear^8 elliptic curve.
pub use babybear8::BabyBear8;
pub use schnorr_curve::{CurvePoint, GENERATOR as SCHNORR_GENERATOR};
pub use schnorr_sig::{
    SchnorrPublicKey, SchnorrSecretKey, SchnorrSignature, compress_public_key, schnorr_keygen,
    schnorr_sign, schnorr_verify,
};
