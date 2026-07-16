//! Re-prove a `custom` effect's `CellProgram` sub-proof as a RECURSION-FOLDABLE
//! IR-v2 leaf (Fork X).
//!
//! ## What this closes
//!
//! Today a custom effect's external program proof is a bespoke
//! [`dregg_circuit::dsl::circuit::CellProgram`] STARK
//! ([`dregg_circuit::stark`]). The deployed `proof_bind` engine
//! ([`crate::custom_proof_bind`]) verifies it OFF-AIR — a re-executing validator
//! runs `CellProgram::verify_transition`, but a PURE LIGHT CLIENT (one that only
//! folds the per-turn recursion tree) never witnesses it. The custom leg is the
//! one effect family whose soundness a light client cannot currently see.
//!
//! This module adapts the `CellProgram`'s [`CircuitDescriptor`] into an
//! [`EffectVmDescriptor2`] (the EPOCH multi-table grammar), proves it through the
//! GENERAL IR-v2 prover ([`prove_vm_descriptor2_for_config`]), and wraps the
//! result as a recursion leaf via the existing
//! [`prove_descriptor_leaf_rotated_with_config`] machinery. The output is the same
//! [`RecursionOutput<DreggRecursionConfig>`] every other descriptor leaf produces,
//! so a custom sub-proof now folds into the SAME `aggregate_tree` / chain a light
//! client verifies.
//!
//! ## The constraint mapping (`CellProgram` `ConstraintExpr` → `VmConstraint2`)
//!
//! The IR-v2 `main` table interprets the embedded v1 forms
//! ([`VmConstraint::Gate`]/[`VmConstraint::Transition`]/[`VmConstraint::PiBinding`])
//! over the same domains the v1 AIR used. Each pure-LOCAL algebraic `ConstraintExpr`
//! lowers to a single `Base(Gate(body))` whose `body` polynomial must vanish:
//!
//! | `ConstraintExpr`        | maps to                                             |
//! |-------------------------|-----------------------------------------------------|
//! | `Equality`              | `Base(Gate(a − b))`                                 |
//! | `Multiplication`        | `Base(Gate(a·b − out))`                             |
//! | `Binary`                | `Base(Gate(c·(c − 1)))`                             |
//! | `Polynomial`            | `Base(Gate(Σ coeffᵢ·∏ colⱼ))`                      |
//! | `Gated`                 | `Base(Gate(sel · inner_body))`                      |
//! | `InvertedGated`         | `Base(Gate((1 − sel) · inner_body))`               |
//! | `Squared`               | `Base(Gate(inner_body²))`                           |
//! | `ConditionalNonzero`    | `Base(Gate(sel·(val·inv − 1)))`                    |
//! | `AtLeastOne`            | `Base(Gate(∏ (1 − flagᵢ)))`                        |
//! | `Transition`            | `WindowGate(Nxt(next) − Loc(local))` on transition  |
//! | `PiBinding`             | `Base(PiBinding{First, col, pi})` (see note)        |
//!
//! `Transition` is realized as a [`WindowGate`] (the two-row primitive that reads
//! BOTH the current `Loc` and next `Nxt` row), NOT `Base(VmConstraint::Transition)`:
//! the latter hard-codes the EffectVM `state_before`/`state_after` window bases
//! (`EFFECTVM_STATE_BEFORE_BASE = 54`, `..._AFTER_BASE = 76`), so it cannot express
//! a generic `next[c] == local[c]` over arbitrary `CellProgram` columns. The
//! `WindowGate` is the faithful, column-general carrier and asserts on the same
//! transition domain (rows `0..n−2`) as a `CellProgram` cross-row constraint.
//!
//! **`PiBinding` note (a NAMED narrowing, not a hole):** a `CellProgram`
//! `ConstraintExpr::PiBinding` is a per-row gate `local[col] − pi[idx] == 0`, but a
//! per-row PI-reading gate is INEXPRESSIBLE in the IR-v2 `LeanExpr` (it reads only
//! columns, never public values). The faithful IR-v2 carrier is
//! `VmConstraint::PiBinding`, which is row-tag-guarded (first/last only); this
//! adapter emits a `First`-row binding, which NARROWS the semantics from every-row
//! to first-row. The follow-up is a per-row PI gate in the IR-v2 main AIR. The demo
//! program below does not use `PiBinding`, so this narrowing is not on the proven path.
//!
//! ## Poseidon2 hash sites — the LANE-WITNESSING extension (now mapped)
//!
//! `Hash2to1` / `Hash4to1` / `Hash3Cap` / `MerkleHash` lower to `Lookup`s into the
//! declared Poseidon2 CHIP table (`TID_P2`). One permutation = one 20-wide chip tuple
//! `[arity, in0..in10, out0, lane1..lane7]`; the chip-table AIR EQUALITY-binds all 8
//! output lanes to the genuine permutation (`out[i] == perm(ins)[i]`), so a forged
//! digest OR a forged intermediate lane is UNSAT. The 7 lane columns are ALLOCATED past
//! the base trace width per site and filled descriptor-side by `fill_chip_lanes`
//! (the `trace_with_chip_lanes` weld); the digest (lane 0/out0) is the site's own output
//! column, already filled by the `CellProgram`'s `generate_trace`. `MerkleHash`'s
//! position-ordered child reconstruction is emitted as degree-4 Lagrange-indicator chip
//! inputs (so the chip absorb's children match the evaluator at every grid position
//! `{0,1,2,3}`, pinned by the program's own position-validity gate). A Merkle PATH is a
//! chain of these sites (parent → next `current` via `Transition`) with the leaf/root
//! pinned to PIs by the boundary `PiBinding`s — see the tooth tests. This mirrors the
//! cap_root/heap_root in-circuit Merkle-open (a witnessed sibling path, constrained
//! recompute), and is the shared primitive every hash-heavy carrier's path verification
//! rides.
//!
//! ## The running-hash chain — the COPY-FORWARD extension (now mapped)
//!
//! `ChainedHash2to1 { out, seed, input }` is a CROSS-ROW running hash `next[out] ==
//! hash_2_to_1(local[seed], next[input])`; a single-row `TID_P2` lookup reads only the
//! `local` window, so it cannot reach the `next` input. The faithful carrier is a fresh
//! COPY-FORWARD accumulator column `acc`: a per-row chip `out == hash_2_to_1(acc, input)`,
//! a `WindowGate` copy-forward `next[acc] − local[seed] == 0` (so `acc[i+1]` = the prior
//! accumulator), and the chain's first-row seed `acc[0] == pi[seed_pi]` from its paired
//! `SeedHash2to1`. This reproduces BOTH the `ChainedHash2to1` rolling step AND the
//! `SeedHash2to1` table-commitment seed of `dregg-dfa-routing-v1` byte-for-byte; the `acc`
//! column is witnessed descriptor-side ([`fill_chain_columns`]) and the chip equality-binds
//! `out` to the genuine permutation, so a forged accumulator / broken chain is UNSAT.
//!
//! ## The transition table — `TableFunction` → its bivariate-Lagrange gate (now mapped)
//!
//! `TableFunction { a, b, out, .. }` (the GAP-A `next == step(state, symbol)`) lowers to the
//! pure-local gate `out − Σ_i Σ_j outputs[i·|b|+j]·Lᵢ(a)·Lⱼ(b)` (`Lᵢ` a Lagrange indicator
//! over the grid, exactly as `MerkleHash`'s position reconstruction). The paired grid-range
//! vanishing gates pin `(a, b)` onto the grid, so the interpolant is evaluated only at real
//! grid points. With these three, `dregg-dfa-routing-v1` FULLY lowers to a foldable leaf.
//!
//! ## Constraint kinds this extension does NOT map (precise blockers, not fakes)
//!
//! * `Hash` — the capacity-tagged fact-sponge `hash_fact(predicate, terms)` uses the
//!   arity-7 cap-leaf / `FACT_MARK` fact-bus seeding (state[5]=FACT_MARK, state[6]=1),
//!   NOT a narrow arity-2/3/4 absorb. Mapping it needs the chip's fact-bus path
//!   (`BUS_FACT`) — the named follow-up.
//! * `Lookup { table_id, .. }` — a `CellProgram` lookup names an arbitrary
//!   entry-set `LookupTable`. The IR-v2 `Lookup` targets DECLARED tables with FIXED
//!   semantics (range / chip / submask), not arbitrary entry sets, so there is no
//!   faithful target. Mapping it needs an IR-v2 "custom-contents" table family
//!   (the named small IR follow-up). `dregg-dfa-routing-v1` does NOT use it (it routes
//!   through `TableFunction`, which is now mapped).
//! * An UNSEEDED `ChainedHash2to1` (no paired first-row `SeedHash2to1`) and a standalone
//!   `SeedHash2to1` (no chain accumulating its output) — the per-row chip would
//!   over-constrain row 0 (resp. needs a first-row-ONLY chip gate). No deployed carrier
//!   hits these; the named residual.
//! * `BoundaryRow::Index` — an absolute-row boundary has no IR-v2 row-tag carrier
//!   (`when_first_row`/`when_last_row` only); the named residual.
//!
//! ## The remaining seam to the per-turn fold
//!
//! `prove_custom_leaf` carries the `CellProgram`'s public inputs as the leaf's
//! descriptor PIs (bound in-circuit — a tampered PI is UNSAT). The value the
//! deployed effect-VM `custom_proof_commitment` column must equal is
//! [`custom_proof_pi_commitment`] of those PIs. The OPEN seam is exposing that
//! Poseidon2 commitment as an in-circuit-computed CLAIM (an `expose` hook computing
//! `WideHash::from_poseidon2` over the bound PIs, the way
//! `prove_descriptor_leaf_rotated_with_segment` computes its segment digest
//! in-circuit) and connecting it to the EffectVM Custom row's `proof_bind` column.
//!
//! ## G2 status — the in-circuit commitment expose hook ([`prove_custom_leaf_with_commitment`])
//!
//! [`incircuit_custom_pi_commitment`] is the FAITHFUL in-circuit reconstruction of
//! [`custom_proof_pi_commitment`]: a width-16 BabyBear Poseidon2 (KAT-locked to
//! `default_babybear_poseidon2_16`, the SAME permutation [`WideHash::from_poseidon2`]'s
//! `Poseidon2State` runs) driven as the host's ADDITIVE rate-4 sponge — each four-PI chunk
//! packed into ext limb 0 (base lanes 0..4; chunks past the first are ADDED into the returned
//! rate and chained with `new_start = false`, capacity off-bus), the BLAKE3 domain seed + input
//! length in limb 1 (lanes 4,5) as the INITIAL rate state only, the
//! zero capacity tail in limbs 2,3. The host commitment is `to_felts()[0..4]` = the rate AFTER
//! the last absorb permutation, so only the absorb phase is reconstructed. The domain seed enters
//! as a compile-time `Const` (no in-circuit BLAKE3); `domain_seed_matches_widehash` pins it.
//!
//! The leaf PROVES, and its in-circuit-exposed 4-felt commitment is BYTE-IDENTICAL to the host
//! [`custom_proof_pi_commitment`] (the `incircuit_commitment_byte_matches_host` /
//! `incircuit_commitment_binds_pis` tests). The host commitment is `to_felts()[0..4]` = the 4
//! CONSECUTIVE base lanes 0,1,2,3 of one perm-output ext limb (verified in `binding.rs`). Exposing
//! those 4 base felts requires `decompose_ext_to_base_coeffs(out[0])` and exposing the
//! coefficients — and those per-coefficient base values must appear on the `WitnessChecks` bus, or
//! `expose_claim`'s per-coeff RECEIVE has no creator (the prior empirical failure:
//! `WitnessChecks tuple [...] net multiplicity p−1` = one unmatched RECEIVE, instance 5 row 0).
//! The fork's mechanism for exactly this is the `recompose/coeff` table, enabled on the expose path
//! by `set_recompose_coeff_ctl_for_decompose_links(true)`. The leaf-wrap backend registers that
//! table's prover / preprocessor / air-builder ONLY when
//! `cl = challenger.extension_degree() != D || force_coeff_lookups` (`recursion/src/backend/fri.rs`);
//! the first disjunct is FALSE for the D=4 width-16 challenger this config uses, so the leaf uses the
//! coeff-forced backend [`create_recursion_backend_with_coeff_lookups`] (fork rev `be52a51`'s
//! `with_coeff_lookups()` flag) to OR the gate true. The table is inert for non-custom leaves (which
//! never take the coeff-ctl decompose path), so existing leaves' VKs do not move. (The seg digest
//! sidesteps the bus entirely: its host digest is lanes 0,4,8,12 = coeff-0 of separate ext limbs,
//! exposable as-is with no decompose; the consecutive-lane custom commitment cannot.)
//!
//! ## The connect-into-the-fold step — DEPLOYED (the binding is REAL for a pure light client)
//!
//! The exposed claim is connected to the effect-vm leg's published `custom_proof_commitment` (IR2
//! PI slots 46..53 — the 8-felt flag-day exposure) IN THE DEPLOYED CHAIN PROVER. For a custom turn,
//! [`crate::ivc_turn_chain::prove_chain_core_rotated`] mints a DUAL-EXPOSE leg leaf
//! ([`crate::ivc_turn_chain::prove_descriptor_leaf_dual_expose`] — its single `expose_claim` carries
//! the chain SEGMENT in lanes `[0 .. SEG_WIDTH)` AND the claimed commitment in lanes
//! `[SEG_WIDTH ..)`) and folds it against THIS custom sub-proof leaf under
//! [`crate::joint_turn_recursive::prove_custom_binding_node_segmented`], which `connect`s the two
//! 4-felt commitments in-circuit AND re-exposes the segment so the node folds into `aggregate_tree`
//! like any segment leaf. A turn whose leg claims a commitment no verifying sub-proof backs is UNSAT
//! (the `connect` is a conflict — no satisfying partner), so no root exists and a PURE LIGHT CLIENT
//! verifying the deployed `WholeChainProof` never receives a verifying artifact. The premise of
//! Lean `CustomBindingFromFold.custom_binding_from_fold` is now TRUE on the deployed path.
//!
//! The two formerly-blocking threads are landed: (1) the custom sub-proof's re-provable witness
//! (`CellProgram` + trace witness + PIs) is retained PROVER-SIDE on
//! [`crate::joint_turn_aggregation::RotatedParticipantLeg::custom_witness`] (NEVER on the wire
//! `dregg_turn::CustomProgramProof`, which a light client sees), and (2) the dual-claim leaf +
//! segment-preserving binding node carry the segment AND the commitment. End-to-end honest-accept +
//! forged-reject through `prove_turn_chain_recursive` → `verify_turn_chain_recursive` is pinned by
//! `circuit-prove/tests/custom_binding_deployed_tooth.rs`. The single-claim
//! [`crate::joint_turn_recursive::prove_custom_binding_node`] + the
//! `forged_custom_commitment_is_rejected_by_the_fold` stand-in tooth remain as the minimal MECHANISM
//! teeth.

use dregg_circuit::descriptor_ir2::{
    Ir2Air, MemBoundaryWitness, UMemBoundaryWitness, ir2_airs_and_common_for_config,
    prove_vm_descriptor2_for_config,
};
use dregg_circuit::dsl::circuit::CellProgram;
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use std::collections::HashMap;

// The LOWERING half (`CellProgram` → IR-v2 descriptor + the copy-forward fill plan)
// moved to the verify floor — `dregg_circuit::custom_leaf_lowering` — so the turn
// executor's Custom-VK VERIFY path lowers without linking this recursion-prover
// crate. Re-exported here so existing
// `dregg_circuit_prove::custom_leaf_adapter::cellprogram_to_descriptor2` callers
// are unchanged.
pub use dregg_circuit::custom_leaf_lowering::cellprogram_to_descriptor2;

use dregg_circuit::custom_leaf_lowering::{Lowered, fill_chain_columns, lower_cellprogram};

use p3_baby_bear::BabyBear as P3BabyBear;
use p3_circuit::CircuitBuilder;
use p3_circuit::ops::Poseidon2Config;
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing, PrimeField32};
use p3_recursion::{
    ProveNextLayerParams, RecursionInput, RecursionOutput, Target,
    build_and_prove_next_layer_with_expose,
};
use p3_uni_stark::StarkGenericConfig;

use crate::custom_proof_bind::{CUSTOM_PROOF_PI_DOMAIN, ProofBindCommitment};
use crate::ivc_turn_chain::prove_descriptor_leaf_rotated_with_config;
use crate::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, create_recursion_backend_with_coeff_lookups,
};

/// The recursion config's challenge (extension) field — the field every leaf-wrap verifier
/// circuit (and this module's expose hook) builds over.
type RecursionChallenge = <DreggRecursionConfig as StarkGenericConfig>::Challenge;

/// Extension degree of the recursion config's PCS (D = 4 for the BabyBear-quartic stack).
const D: usize = 4;

/// Prove a `CellProgram` transition as a RECURSION-FOLDABLE IR-v2 leaf.
///
/// `witness_values` / `num_rows` are the `CellProgram` trace witness (retained prover-side
/// on [`crate::custom_proof_bind::BoundCustomProof`]); `public_inputs` are the sub-proof's
/// public inputs, carried as the leaf's descriptor PIs (bound in-circuit) and
/// committed by [`custom_proof_pi_commitment`]. `public_inputs.len()` MUST equal the
/// program's `descriptor.public_input_count`.
///
/// `config` must be the leaf-wrap recursion config
/// ([`crate::ivc_turn_chain::ir2_leaf_wrap_config`]): the inner IR-v2 batch is minted
/// under it so the in-circuit verifier consumes it with no cross-config mismatch.
///
/// On success the returned [`RecursionOutput`] is the same leaf the aggregation tree
/// folds. A witness that violates any mapped constraint has no satisfying assembly:
/// the inner prover's self-verify rejects it (or the debug constraint builder
/// panics) — the negative pole the test exercises.
pub fn prove_custom_leaf(
    program: &CellProgram,
    witness_values: &HashMap<String, Vec<BabyBear>>,
    num_rows: usize,
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    let lowered = lower_cellprogram(program)?;
    let desc2 = &lowered.desc;

    // The CellProgram main rows, augmented with the copy-forward accumulator columns the
    // running-hash chains witness (filled below); the chip-lane weld inside the prover then
    // derives each chip's lanes from them.
    let base_trace =
        augmented_base_trace(&lowered, program, witness_values, num_rows, public_inputs)?;

    // Mint the inner IR-v2 batch under the recursion config TYPE (the SIDESTEP), so
    // the leaf-wrap's in-circuit verifier consumes it directly.
    let inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
        desc2,
        &base_trace,
        public_inputs,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        config,
    )
    .map_err(|e| format!("custom-leaf inner IR-v2 prove failed: {e}"))?;

    // Wrap the inner batch as a recursion leaf, binding the descriptor PIs in-circuit.
    prove_descriptor_leaf_rotated_with_config(desc2, &inner, public_inputs, config)
        .map_err(|e| format!("custom-leaf recursion wrap failed: {e}"))
}

/// Generate the `CellProgram`'s base trace and augment it with the lowered descriptor's
/// copy-forward accumulator columns (witnessed per the running-hash chain plans). Each row
/// is widened to the lowered `trace_width` so the appended `acc`/lane columns exist; the
/// `acc` columns are filled BEFORE the chip-lane weld so each chip's lanes derive from the
/// genuine accumulator value. For a chain-free program this is exactly the raw base trace.
fn augmented_base_trace(
    lowered: &Lowered,
    program: &CellProgram,
    witness_values: &HashMap<String, Vec<BabyBear>>,
    num_rows: usize,
    public_inputs: &[BabyBear],
) -> Result<Vec<Vec<BabyBear>>, String> {
    let mut base_trace = program
        .generate_trace(witness_values, num_rows)
        .map_err(|e| format!("custom-leaf trace generation failed: {e}"))?;
    if !lowered.chains.is_empty() {
        for row in &mut base_trace {
            if row.len() < lowered.desc.trace_width {
                row.resize(lowered.desc.trace_width, BabyBear::ZERO);
            }
        }
        fill_chain_columns(&lowered.chains, &mut base_trace, public_inputs);
    }
    Ok(base_trace)
}

// ============================================================================
// G2: compute the custom sub-proof's PI-commitment IN-CIRCUIT and expose it as a
// bound claim, so a PURE LIGHT CLIENT (folding only the recursion tree) witnesses
// it — no off-AIR re-derivation of [`custom_proof_pi_commitment`].
// ============================================================================

/// The domain-separation seed [`custom_proof_pi_commitment`] writes into capacity lane 4.
///
/// Host-computed at circuit-build time (BLAKE3 over the FIXED domain string → first 4 bytes LE
/// → mod p), so it enters the circuit as a `Const` — there is NO in-circuit BLAKE3. This is the
/// EXACT value [`WideHash::from_poseidon2`] seeds: `BabyBear::new(u32::from_le_bytes(blake3(domain)[0..4]) % p)`.
fn custom_pi_domain_seed() -> u32 {
    let dsk_hash = *blake3::hash(CUSTOM_PROOF_PI_DOMAIN.as_bytes()).as_bytes();
    u32::from_le_bytes([dsk_hash[0], dsk_hash[1], dsk_hash[2], dsk_hash[3]]) % BABYBEAR_P
}

/// Embed a canonical base-field value as a `RecursionChallenge` (extension) constant target —
/// the base value rides in coefficient 0, the rest zero (the canonical base→ext lift).
fn embed_base_const(cb: &mut CircuitBuilder<RecursionChallenge>, v: u32) -> Target {
    cb.define_const(RecursionChallenge::from(P3BabyBear::from_u64(v as u64)))
}

/// Build the extension element whose base-field coefficients are `coeffs[0..4]` — i.e. the ext
/// limb that packs base lanes `[4i..4i+4]`. Used to mint the constant capacity-seed limbs
/// directly (NOT via in-circuit recompose), so the domain/len constants enter the perm as a
/// single bus-balanced `Const` rather than as unbacked recompose operands.
fn ext_from_base_coeffs(coeffs: [u32; 4]) -> RecursionChallenge {
    RecursionChallenge::from_basis_coefficients_fn(|i| P3BabyBear::from_u64(coeffs[i] as u64))
}

/// **The in-circuit custom-PI commitment** — a faithful in-AIR reconstruction of
/// [`crate::custom_proof_bind::custom_proof_pi_commitment`] (the deployed Custom-row
/// `custom_proof_commitment` column) over the leaf's BOUND public-input targets.
///
/// Byte-matches [`dregg_circuit::binding::WideHash::from_poseidon2`] under
/// [`CUSTOM_PROOF_PI_DOMAIN`]: a width-16 BabyBear Poseidon2 (the SAME permutation the FRI
/// challenger runs, KAT-locked to `default_babybear_poseidon2_16`), driven as an ADDITIVE
/// rate-4 sponge with the BLAKE3 domain seed in capacity lane 4 and the input length in lane 5.
///
/// The host commitment is the FULL `WideHash::to_felts()` (8 felts, flag-day rotation from 4):
/// felts 0..4 are the state rate (lanes 0..4) AFTER the last ABSORB permutation, and felts 4..8
/// are the GENUINE SECOND SQUEEZE BLOCK — the rate lanes after ONE MORE permutation of the same
/// full 16-lane state (`state.permute()` between the host's two squeeze reads). Both phases are
/// reconstructed here; the 8 returned targets are exactly the host's 8 felts — never duplication
/// or zero padding.
///
/// The width-16 base permutation is reached through the ENABLED ext-packed `BABY_BEAR_D4_W16`
/// challenger op (the recursion stack registers only the D=4 width-16/24 ops; the D=1 base op the
/// host sponge's `Poseidon2State` natively is is NOT registered). The 16 base lanes pack into 4
/// ext limbs (limb `i` = base lanes `4i..4i+4`): limb 0 = the rate (the absorbed 4-felt chunk),
/// limb 1 = `[domain, len, 0, 0]`, limbs 2,3 = the zero capacity tail. One challenger perm
/// (`new_start`) computes the same 16→16 permutation as the host; the commitment is base lanes
/// 0..4 of the output = the 4 coefficients of output limb 0.
///
/// For `inputs.len() <= 4` (the common custom case, incl. the demo's 2 PIs) this is exactly ONE
/// permutation (the original shape, byte-identical). Longer inputs chain further permutations
/// through the SAME bus-balanced sponge-step primitive with `new_start = false`, mirroring the
/// host's `for chunk in inputs.chunks(4) { state[i] += chunk[i]; permute() }` schedule exactly:
/// each later four-PI chunk is packed into one ext limb and ADDED into returned rate limb 0
/// (base lanes 0..4), returned rate limb 1 (base lanes 4..8 — the domain/len lanes, which the
/// host never re-touches during absorb) passes through unchanged, and the capacity (lanes
/// 8..16) stays chained OFF the bus (the AIR inherits the previous perm row's capacity output).
/// The host has NO padding block and NO length re-absorb, so neither exists here; the total
/// input length is bound once, in the initial lane-5 constant. The host DOES have exactly one
/// squeeze permute (between the two squeeze blocks), mirrored by the final chained sponge step
/// below: the rate limbs pass through UNCHANGED (nothing absorbed) and the capacity chains
/// off-bus — byte-identical to the host's `state.permute()` over the full post-absorb state.
fn incircuit_custom_pi_commitment(
    cb: &mut CircuitBuilder<RecursionChallenge>,
    pi_targets: &[Target],
) -> Result<[Target; 8], String> {
    let config = Poseidon2Config::BABY_BEAR_D4_W16;
    let zero = embed_base_const(cb, 0);

    // limb 1 = base lanes 4..8 = [domain, total_input_len, 0, 0] — a single compile-time ext
    // constant, the INITIAL rate state only (the host writes lanes 4,5 once, before any permute).
    let dom = custom_pi_domain_seed();
    let len = pi_targets.len() as u32;
    let limb1 = cb.define_const(ext_from_base_coeffs([dom, len, 0, 0]));
    // limbs 2,3 = base lanes 8..16 = the host's zero capacity tail (and the all-zero rate limb 0
    // for the empty-input squeeze).
    let zero_limb = cb.define_const(RecursionChallenge::ZERO);

    // Route every decompose's per-coefficient base values onto the `WitnessChecks` bus via the
    // `recompose/coeff` table (enabled by the coeff-forced backend), so `expose_claim`'s per-coeff
    // RECEIVE has a matching creator — without this the exposed consecutive base lanes have no
    // bus provenance and the global lookup is imbalanced (unmatched RECEIVEs). Builder flag: it
    // affects only decompose links, all of which are created below.
    cb.set_recompose_coeff_ctl_for_decompose_links(true);

    // ---- Squeeze block 1 (felts 0..4) + the squeeze permute (the host's `state.permute()`
    // between its two squeeze reads). Both branches end with `squeeze_rate` = the rate limbs
    // AFTER the squeeze permute, whose limb 0 is squeeze block 2.
    let (block1, squeeze_rate): ([Target; 4], Vec<Target>) = if pi_targets.is_empty() {
        // Host: zero chunks ⇒ NO absorb permute. Squeeze block 1 is the UNTOUCHED zero rate
        // (felts 0..4 == 0), and the squeeze permute is then the FIRST permutation — a
        // new-start step over the exact seeded initial state [0,0,0,0, dom, len=0, 0..0].
        let rate = cb
            .add_poseidon2_perm_sponge_step(
                config,
                true,
                &[zero_limb, limb1],
                &[zero_limb, zero_limb],
            )
            .map_err(|e| format!("width-16 sponge step failed: {e:?}"))?;
        ([zero, zero, zero, zero], rate)
    } else {
        // Pack one four-PI chunk into a single ext limb: coefficients = the chunk, zero-padded
        // (the host's partial final chunk adds nothing into the absent lanes — adding the zero
        // pad is the same value). The PI targets are bus-present (created by the verified inner
        // proof), so recomposing them is bus-balanced; the constant pads/domain/len must NOT go
        // through recompose (a const consumed as an ALU operand has no bus creator — the
        // WitnessChecks mismatch this avoids), so limb 1 and the capacity tail are DIRECT ext
        // constants (the same way the segment sponge feeds its tag).
        let pack = |cb: &mut CircuitBuilder<RecursionChallenge>,
                    chunk: &[Target]|
         -> Result<Target, String> {
            let lanes: Vec<Target> = (0..4)
                .map(|lane| chunk.get(lane).copied().unwrap_or(zero))
                .collect();
            cb.recompose_base_coeffs_to_ext_via_alu::<P3BabyBear>(&lanes)
                .map_err(|e| format!("recompose rate limb failed: {e:?}"))
        };

        let mut chunks = pi_targets.chunks(4);
        let first_chunk = chunks.next().expect("pi_targets is non-empty");

        // limb 0 = base lanes 0..4 = the first absorbed chunk (added into the host's untouched
        // zero rate).
        let limb0 = pack(cb, first_chunk)?;

        // The BUS-BALANCED sponge primitive (the same one the segment digest uses): rate_in = the
        // two rate ext-limbs (base lanes 0..8), capacity_seed = the two capacity ext-limbs (base
        // lanes 8..16). On `new_start` these are exactly the 16-lane pre-permutation state of the
        // host `WideHash::from_poseidon2`, and the perm is the SAME width-16 BabyBear permutation.
        let mut rate = cb
            .add_poseidon2_perm_sponge_step(config, true, &[limb0, limb1], &[zero_limb, zero_limb])
            .map_err(|e| format!("width-16 sponge step failed: {e:?}"))?;

        // Remaining chunks: the host adds each chunk into lanes 0..4 of the PERMUTED state and
        // permutes again, never re-touching lanes 4..8 (they carry the previous permutation
        // output forward). So: add the packed chunk into returned rate limb 0, pass returned rate
        // limb 1 through unchanged, and chain the capacity off-bus (`new_start = false` — the
        // capacity seed argument is ignored on chained steps).
        for chunk in chunks {
            let packed = pack(cb, chunk)?;
            let rate0 = cb.add(rate[0], packed);
            rate = cb
                .add_poseidon2_perm_sponge_step(
                    config,
                    false,
                    &[rate0, rate[1]],
                    &[zero_limb, zero_limb],
                )
                .map_err(|e| format!("width-16 sponge step failed: {e:?}"))?;
        }

        // Squeeze block 1 = base lanes 0..4 = the 4 coefficients of the first output rate limb
        // AFTER the last absorb permutation (strictly before the host's squeeze permute).
        let coeffs = cb
            .decompose_ext_to_base_coeffs::<P3BabyBear>(rate[0])
            .map_err(|e| format!("decompose output rate limb failed: {e:?}"))?;

        // THE SQUEEZE PERMUTE (host `WideHash::from_poseidon2`'s single `state.permute()` between
        // the two squeeze reads): one more chained sponge step with the rate limbs passed through
        // UNCHANGED — nothing is absorbed — and the capacity inherited off-bus. This is the
        // GENUINE second squeeze block's permutation, not duplication or padding.
        let rate2 = cb
            .add_poseidon2_perm_sponge_step(
                config,
                false,
                &[rate[0], rate[1]],
                &[zero_limb, zero_limb],
            )
            .map_err(|e| format!("width-16 squeeze-permute sponge step failed: {e:?}"))?;
        ([coeffs[0], coeffs[1], coeffs[2], coeffs[3]], rate2)
    };

    // ---- Squeeze block 2 (felts 4..8) = base lanes 0..4 AFTER the squeeze permute.
    let coeffs2 = cb
        .decompose_ext_to_base_coeffs::<P3BabyBear>(squeeze_rate[0])
        .map_err(|e| format!("decompose second squeeze rate limb failed: {e:?}"))?;
    Ok([
        block1[0], block1[1], block1[2], block1[3], coeffs2[0], coeffs2[1], coeffs2[2], coeffs2[3],
    ])
}

/// Prove a `CellProgram` transition as a recursion-foldable leaf (as [`prove_custom_leaf`]) AND
/// expose the custom sub-proof's PI-commitment as an IN-CIRCUIT-computed public CLAIM.
///
/// The returned [`RecursionOutput`] carries one `expose_claim` table whose 8 public values are
/// the in-circuit [`incircuit_custom_pi_commitment`] over the leaf's BOUND descriptor PIs — equal,
/// byte-for-byte, to the deployed [`custom_proof_pi_commitment`] the off-AIR engine writes into
/// the Custom row's `custom_proof_commitment` columns (flag-day rotation: 8 felts, both squeeze
/// blocks). Because the absorb reads the leaf's REAL
/// (in-circuit-bound) PI targets, a prover cannot expose a commitment that disagrees with the PIs
/// the leaf actually proves: the claim is welded to the execution, witnessable by a pure light
/// client folding the tree.
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`] (the same FRI engine the inner
/// batch is minted under), exactly as [`prove_custom_leaf`].
pub fn prove_custom_leaf_with_commitment(
    program: &CellProgram,
    witness_values: &HashMap<String, Vec<BabyBear>>,
    num_rows: usize,
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    let lowered = lower_cellprogram(program)?;
    let desc2 = &lowered.desc;

    let base_trace =
        augmented_base_trace(&lowered, program, witness_values, num_rows, public_inputs)?;

    let inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
        desc2,
        &base_trace,
        public_inputs,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        config,
    )
    .map_err(|e| format!("custom-leaf inner IR-v2 prove failed: {e}"))?;

    let (airs, table_public_inputs, common) =
        ir2_airs_and_common_for_config(desc2, &inner, public_inputs, config)
            .map_err(|e| format!("custom-leaf verify-triple build failed: {e}"))?;

    let input: RecursionInput<'_, DreggRecursionConfig, Ir2Air> =
        RecursionInput::NativeBatchStark {
            airs: &airs,
            proof: &inner,
            common_data: &common,
            table_public_inputs,
        };

    // The coeff-enabled backend: the in-circuit commitment expose decomposes one ext limb into
    // its 4 CONSECUTIVE base lanes, whose per-coefficient base values must ride the `WitnessChecks`
    // bus via the `recompose/coeff` table. That table is registered only when the backend's
    // `force_coeff_lookups` flag ORs the `cl` gate true (the D=4 W16 challenger has
    // `challenger_D == D`, so the default gate is false). See `create_recursion_backend_with_coeff_lookups`.
    let backend = create_recursion_backend_with_coeff_lookups();

    // The expose hook: instance 0 (main) carries the descriptor PIs (== `public_inputs`, in order).
    // Compute the in-circuit PI-commitment over them and expose the 8 felts as a public claim.
    let num_pi = public_inputs.len();
    let expose = move |cb: &mut CircuitBuilder<RecursionChallenge>, apt: &[Vec<Target>]| {
        let main = apt
            .first()
            .expect("custom leaf has a main instance carrying the descriptor PIs");
        debug_assert!(
            main.len() >= num_pi,
            "main instance must carry all {num_pi} descriptor PIs"
        );
        let pis: Vec<Target> = (0..num_pi).map(|k| main[k]).collect();
        let commit = incircuit_custom_pi_commitment(cb, &pis)
            .expect("in-circuit custom-PI commitment builds for the bound descriptor PIs");
        cb.expose_as_public_output(&commit);
    };

    build_and_prove_next_layer_with_expose::<DreggRecursionConfig, Ir2Air, _, D>(
        &input,
        config,
        &backend,
        &ProveNextLayerParams::default(),
        Some(&expose),
    )
    .map_err(|e| format!("custom-leaf commitment leaf-wrap failed: {e:?}"))
}

/// Read the full 8-felt [`ProofBindCommitment`] a
/// [`prove_custom_leaf_with_commitment`] leaf exposes through its
/// `expose_claim` table. Returns `None` if the proof carries no exposed claim
/// or exposes fewer than the full commitment width (a truncated/old 4-felt
/// artifact is refused here, matching `require_custom_commit_teeth_v2`'s
/// never-silently-widen rule).
pub fn read_exposed_pi_commitment(
    output: &RecursionOutput<DreggRecursionConfig>,
) -> Option<ProofBindCommitment> {
    use crate::custom_proof_bind::PROOF_BIND_COMMIT_WIDTH;
    let claims: Vec<BabyBear> = output
        .0
        .non_primitives
        .iter()
        .find(|e| e.op_type.as_str() == "expose_claim")?
        .public_values
        .iter()
        .map(|&v| BabyBear::new(v.as_canonical_u32()))
        .collect();
    if claims.len() < PROOF_BIND_COMMIT_WIDTH {
        return None;
    }
    Some(core::array::from_fn(|k| claims[k]))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::custom_proof_bind::custom_proof_pi_commitment;
    use crate::ivc_turn_chain::ir2_leaf_wrap_config;
    use dregg_circuit::descriptor_ir2::{CHIP_OUT_LANES, TID_P2, VmConstraint2};
    use dregg_circuit::dsl::circuit::{
        BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr,
        PolyTerm,
    };
    use dregg_circuit::lean_descriptor_air::VmConstraint;
    use dregg_circuit::refusal::must_refuse_or_unsat_panic;

    /// The same minimal-but-REAL custom program the off-AIR engine's tests use: one
    /// boolean column (`dir`) + one conservation polynomial
    /// (`new − old − amt + 2·dir·amt == 0`, the sovereign-transfer shape).
    fn demo_program() -> CellProgram {
        let p_minus_1 = BabyBear::new(dregg_circuit::field::BABYBEAR_P - 1);
        let descriptor = CircuitDescriptor {
            name: "dregg-custom-demo-v1".to_string(),
            trace_width: 4,
            max_degree: 2,
            columns: vec![
                ColumnDef {
                    name: "old".into(),
                    index: 0,
                    kind: ColumnKind::Value,
                },
                ColumnDef {
                    name: "amt".into(),
                    index: 1,
                    kind: ColumnKind::Value,
                },
                ColumnDef {
                    name: "new".into(),
                    index: 2,
                    kind: ColumnKind::Value,
                },
                ColumnDef {
                    name: "dir".into(),
                    index: 3,
                    kind: ColumnKind::Binary,
                },
            ],
            constraints: vec![
                ConstraintExpr::Binary { col: 3 },
                ConstraintExpr::Polynomial {
                    terms: vec![
                        PolyTerm {
                            coeff: BabyBear::ONE,
                            col_indices: vec![2],
                        },
                        PolyTerm {
                            coeff: p_minus_1,
                            col_indices: vec![0],
                        },
                        PolyTerm {
                            coeff: p_minus_1,
                            col_indices: vec![1],
                        },
                        PolyTerm {
                            coeff: BabyBear::new(2),
                            col_indices: vec![3, 1],
                        },
                    ],
                },
            ],
            boundaries: vec![],
            public_input_count: 2,
            lookup_tables: vec![],
        };
        CellProgram::new(descriptor, 1)
    }

    /// Honest witness for a credit (dir=0): new = old + amt, constant across rows.
    fn honest_witness() -> (HashMap<String, Vec<BabyBear>>, usize) {
        let rows = 4;
        let mut w = HashMap::new();
        w.insert("old".into(), vec![BabyBear::new(10); rows]);
        w.insert("amt".into(), vec![BabyBear::new(5); rows]);
        w.insert("new".into(), vec![BabyBear::new(15); rows]);
        w.insert("dir".into(), vec![BabyBear::ZERO; rows]);
        (w, rows)
    }

    /// The mapping is total over the demo's constraint kinds (Binary + Polynomial)
    /// and produces a table-free, two-constraint main-only descriptor.
    #[test]
    fn demo_maps_to_descriptor2() {
        let program = demo_program();
        let desc2 = cellprogram_to_descriptor2(&program).expect("demo maps");
        assert_eq!(desc2.trace_width, 4);
        assert_eq!(desc2.public_input_count, 2);
        assert!(desc2.tables.is_empty(), "demo uses no declared tables");
        assert_eq!(desc2.constraints.len(), 2);
        assert!(
            desc2
                .constraints
                .iter()
                .all(|c| matches!(c, VmConstraint2::Base(VmConstraint::Gate(_)))),
            "Binary + Polynomial both lower to Base(Gate(_))"
        );
    }

    /// THE POSITIVE POLE: the demo custom program proves as a foldable recursion
    /// leaf, AND the PI-commitment the fold would bind equals the off-AIR engine's
    /// `custom_proof_commitment` column value.
    #[test]
    fn demo_proves_as_foldable_leaf() {
        let program = demo_program();
        let (w, rows) = honest_witness();
        let pis: Vec<BabyBear> = vec![BabyBear::new(10), BabyBear::new(15)];
        let config = ir2_leaf_wrap_config();

        // Folds: the leaf wrap returns a RecursionOutput (its in-circuit FRI verify +
        // WitnessChecks bus balanced; a non-folding leaf would have errored here).
        // (The former off-AIR `prove_custom_program` cross-check died with the hand
        // STARK engine (stark-kill); the claim the per-turn fold binds —
        // `custom_proof_pi_commitment(pis)` — is pinned against the IN-CIRCUIT
        // derivation by `incircuit_commitment_byte_matches_host` and the multichunk
        // commitment tests below.)
        let _output = prove_custom_leaf(&program, &w, rows, &pis, &config)
            .expect("the honest custom program must prove as a foldable leaf");
    }

    /// THE NEGATIVE POLE: a FORGED witness (conservation violated: new = old + amt + 1)
    /// has no satisfying assembly — the leaf does NOT prove. The inner prover's
    /// self-verify rejects it, or the debug constraint builder panics; either way the
    /// forged custom program cannot mint a foldable leaf.
    #[test]
    fn forged_witness_does_not_fold() {
        let program = demo_program();
        let rows = 4;
        let mut w: HashMap<String, Vec<BabyBear>> = HashMap::new();
        w.insert("old".into(), vec![BabyBear::new(10); rows]);
        w.insert("amt".into(), vec![BabyBear::new(5); rows]);
        // FORGED: new should be 15; claim 16 (conservation poly is non-zero).
        w.insert("new".into(), vec![BabyBear::new(16); rows]);
        w.insert("dir".into(), vec![BabyBear::ZERO; rows]);
        let pis: Vec<BabyBear> = vec![BabyBear::new(10), BabyBear::new(16)];
        let config = ir2_leaf_wrap_config();

        must_refuse_or_unsat_panic("a FORGED custom witness", || {
            prove_custom_leaf(&program, &w, rows, &pis, &config)
        });
    }

    /// An honest witness for an arbitrary credit (dir=0): new = old + amt, constant across rows.
    fn credit_witness(
        old: u32,
        amt: u32,
    ) -> (HashMap<String, Vec<BabyBear>>, usize, Vec<BabyBear>) {
        let rows = 4;
        let mut w = HashMap::new();
        w.insert("old".into(), vec![BabyBear::new(old); rows]);
        w.insert("amt".into(), vec![BabyBear::new(amt); rows]);
        w.insert("new".into(), vec![BabyBear::new(old + amt); rows]);
        w.insert("dir".into(), vec![BabyBear::ZERO; rows]);
        (w, rows, vec![BabyBear::new(old), BabyBear::new(old + amt)])
    }

    /// Sanity (cheap, host-only): the domain seed this module precomputes is EXACTLY the value
    /// `WideHash::from_poseidon2` writes into capacity lane 4 — so the in-circuit `Const` matches
    /// the host sponge's domain separation byte-for-byte (no in-circuit BLAKE3).
    #[test]
    fn domain_seed_matches_widehash() {
        use dregg_circuit::field::BABYBEAR_P as P;
        let dsk = *blake3::hash(CUSTOM_PROOF_PI_DOMAIN.as_bytes()).as_bytes();
        let expected = u32::from_le_bytes([dsk[0], dsk[1], dsk[2], dsk[3]]) % P;
        assert_eq!(custom_pi_domain_seed(), expected);
    }

    /// THE POSITIVE POLE (G2): the custom leaf proves AND its IN-CIRCUIT-exposed PI-commitment
    /// is byte-identical to the host [`custom_proof_pi_commitment`] — proving the in-circuit
    /// width-16 Poseidon2 absorb reproduces the `WideHash::from_poseidon2` sponge exactly. A pure
    /// light client folding this leaf now witnesses the binding the off-AIR engine recomputed.
    ///
    /// The in-circuit sponge is the faithful width-16 additive rate-4 reconstruction of
    /// `WideHash::from_poseidon2` (the domain seed const is verified by `domain_seed_matches_widehash`;
    /// the lane layout mirrors the host). The host commitment is 4 CONSECUTIVE base lanes of one ext
    /// limb, so exposing them needs a `decompose` whose per-coefficient base values ride the bus via
    /// the `recompose/coeff` table. That table is opted in by the coeff-forced leaf-wrap backend
    /// ([`create_recursion_backend_with_coeff_lookups`]) plus
    /// `set_recompose_coeff_ctl_for_decompose_links(true)` on the expose path — closing the
    /// `WitnessChecks` global-lookup imbalance the prior spike hit.
    #[test]
    fn incircuit_commitment_byte_matches_host() {
        let program = demo_program();
        let (w, rows) = honest_witness();
        let pis: Vec<BabyBear> = vec![BabyBear::new(10), BabyBear::new(15)];
        let config = ir2_leaf_wrap_config();

        let output = prove_custom_leaf_with_commitment(&program, &w, rows, &pis, &config)
            .expect("the honest custom program must prove as a commitment-exposing leaf");

        // FLAG-DAY (proof-bind blocker #2): the exposed claim is the FULL 8-felt commitment —
        // the retired 4-felt expected values are gone; both sides re-derive the 8-felt
        // `WideHash` squeeze (first block byte-identical to the old KAT, second block new).
        let exposed = read_exposed_pi_commitment(&output)
            .expect("the leaf exposes the full 8-felt PI-commitment claim");
        let host = custom_proof_pi_commitment(&pis);
        assert_eq!(
            exposed, host,
            "the IN-CIRCUIT-exposed commitment must byte-match the host WideHash derivation"
        );
    }

    /// THE NEGATIVE POLE (G2): the exposed commitment is BOUND to the PIs, not free. Two honest
    /// leaves over DIFFERENT (still-valid) public inputs expose DIFFERENT commitments, each equal
    /// to its host derivation — so a prover cannot reuse one execution's commitment for another's
    /// PIs (tampering a PI changes the exposed claim).
    #[test]
    fn incircuit_commitment_binds_pis() {
        let program = demo_program();
        let config = ir2_leaf_wrap_config();

        let (w_a, rows_a, pis_a) = credit_witness(10, 5); // PIs [10, 15]
        let (w_b, rows_b, pis_b) = credit_witness(10, 7); // PIs [10, 17] — a tampered/other PI
        assert_ne!(pis_a, pis_b);

        let out_a = prove_custom_leaf_with_commitment(&program, &w_a, rows_a, &pis_a, &config)
            .expect("leaf A proves");
        let out_b = prove_custom_leaf_with_commitment(&program, &w_b, rows_b, &pis_b, &config)
            .expect("leaf B proves");

        let exposed_a = read_exposed_pi_commitment(&out_a).expect("A exposes a commitment");
        let exposed_b = read_exposed_pi_commitment(&out_b).expect("B exposes a commitment");

        assert_eq!(
            exposed_a,
            custom_proof_pi_commitment(&pis_a),
            "A binds its own PIs"
        );
        assert_eq!(
            exposed_b,
            custom_proof_pi_commitment(&pis_b),
            "B binds its own PIs"
        );
        assert_ne!(
            exposed_a, exposed_b,
            "distinct PIs MUST expose distinct commitments — the bind is real, not free"
        );
    }

    // ========================================================================
    // The Poseidon2 lane-witnessing / Merkle-path tooth.
    //
    // A real 4-ary Merkle membership `CellProgram` (`dsl::descriptors`'s carrier:
    // a `MerkleHash` parent hash per level, `Transition` chain continuity, and
    // first/last `PiBinding`s pinning leaf→root) lowers to a foldable IR-2 leaf via
    // the TID_P2 chip-lookup weld. An honest path PROVES; a forged sibling (the leaf
    // no longer climbs to the claimed root) is UNSAT.
    // ========================================================================

    use dregg_circuit::dsl::descriptors::{MERKLE_PUBLIC_INPUT_COUNT, merkle_poseidon2_descriptor};
    use dregg_circuit::poseidon2::hash_4_to_1;

    /// Reconstruct the 4 children EXACTLY as the DSL evaluator / the lowered chip
    /// inputs do: `current` at slot `position`, siblings filling the others in order.
    fn merkle_children(current: BabyBear, sibs: [BabyBear; 3], position: usize) -> [BabyBear; 4] {
        let mut children = [BabyBear::ZERO; 4];
        let mut sib_idx = 0;
        for (i, child) in children.iter_mut().enumerate() {
            if i == position {
                *child = current;
            } else {
                *child = sibs[sib_idx];
                sib_idx += 1;
            }
        }
        children
    }

    /// One honest 4-ary Merkle path of `depth` levels (rows). Returns the per-column
    /// witness + the public inputs `[leaf, root]`. Each level climbs `current →
    /// hash_4_to_1(children)`; the next level's `current` is this level's `parent`,
    /// and the final `parent` is the root.
    fn honest_merkle_path(
        leaf: BabyBear,
        levels: &[([BabyBear; 3], usize)],
    ) -> (HashMap<String, Vec<BabyBear>>, Vec<BabyBear>) {
        let depth = levels.len();
        let mut current_col = Vec::with_capacity(depth);
        let mut sib0 = Vec::with_capacity(depth);
        let mut sib1 = Vec::with_capacity(depth);
        let mut sib2 = Vec::with_capacity(depth);
        let mut position_col = Vec::with_capacity(depth);
        let mut parent_col = Vec::with_capacity(depth);

        let mut current = leaf;
        for (sibs, position) in levels {
            let children = merkle_children(current, *sibs, *position);
            let parent = hash_4_to_1(&children);
            current_col.push(current);
            sib0.push(sibs[0]);
            sib1.push(sibs[1]);
            sib2.push(sibs[2]);
            position_col.push(BabyBear::new(*position as u32));
            parent_col.push(parent);
            current = parent; // chain continuity: next current == this parent
        }
        let root = *parent_col.last().unwrap();

        let mut w = HashMap::new();
        w.insert("current".into(), current_col);
        w.insert("sib0".into(), sib0);
        w.insert("sib1".into(), sib1);
        w.insert("sib2".into(), sib2);
        w.insert("position".into(), position_col);
        w.insert("parent".into(), parent_col);
        (w, vec![leaf, root])
    }

    /// A 4-level path (`num_rows = 4`) over distinct sibling/position choices.
    fn demo_levels() -> Vec<([BabyBear; 3], usize)> {
        vec![
            ([BabyBear::new(7), BabyBear::new(8), BabyBear::new(9)], 0),
            ([BabyBear::new(11), BabyBear::new(12), BabyBear::new(13)], 2),
            ([BabyBear::new(21), BabyBear::new(22), BabyBear::new(23)], 1),
            ([BabyBear::new(31), BabyBear::new(32), BabyBear::new(33)], 3),
        ]
    }

    /// The MerkleHash carrier maps: the descriptor lowers, the trace widens by the
    /// per-site lane columns (one `MerkleHash` site ⇒ +7), and a TID_P2 chip lookup
    /// plus the first/last boundary pins appear.
    #[test]
    fn merkle_membership_maps_to_descriptor2() {
        let program = CellProgram::new(merkle_poseidon2_descriptor(), 1);
        let desc2 = cellprogram_to_descriptor2(&program).expect("merkle membership maps");
        // base width 6 + 7 lane columns for the single MerkleHash site.
        assert_eq!(desc2.trace_width, 6 + (CHIP_OUT_LANES - 1));
        assert_eq!(desc2.public_input_count, MERKLE_PUBLIC_INPUT_COUNT);
        let chip_lookups = desc2
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
            .count();
        assert_eq!(chip_lookups, 1, "the MerkleHash site is one chip lookup");
        let pi_bindings = desc2
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
            .count();
        assert_eq!(
            pi_bindings, 2,
            "the leaf (first) + root (last) pins survive"
        );
    }

    /// THE POSITIVE POLE: an honest Merkle membership path proves as a foldable IR-2
    /// leaf — the chip lookup binds every level's parent to the genuine Poseidon2
    /// permutation of its (position-ordered) children, and the chain climbs to the
    /// claimed root.
    #[test]
    fn honest_merkle_path_proves_as_foldable_leaf() {
        let program = CellProgram::new(merkle_poseidon2_descriptor(), 1);
        let (w, pis) = honest_merkle_path(BabyBear::new(1234), &demo_levels());
        let config = ir2_leaf_wrap_config();
        prove_custom_leaf(&program, &w, 4, &pis, &config)
            .expect("the honest Merkle membership path must prove as a foldable leaf");
    }

    /// THE NEGATIVE POLE: a FORGED path — one sibling corrupted while the claimed
    /// `[leaf, root]` PIs and the parent chain are left intact — has no satisfying
    /// assembly. The corrupted level's `parent` no longer equals the Poseidon2 hash of
    /// the forged children, so the chip lookup's `out0 == perm(children)[0]` equality
    /// (and the leaf→root chain) is violated: the leaf does NOT fold.
    #[test]
    fn forged_merkle_sibling_does_not_fold() {
        let program = CellProgram::new(merkle_poseidon2_descriptor(), 1);
        let (mut w, pis) = honest_merkle_path(BabyBear::new(1234), &demo_levels());
        // FORGE: corrupt a sibling at level 1 WITHOUT recomputing parents/chain. The
        // level-1 parent is now inconsistent with hash_4_to_1(forged children), and the
        // PIs still claim the honest leaf/root — no witness satisfies the lowered leaf.
        let sib0 = w.get_mut("sib0").unwrap();
        sib0[1] = sib0[1] + BabyBear::ONE;
        let config = ir2_leaf_wrap_config();

        must_refuse_or_unsat_panic("a FORGED Merkle path", || {
            prove_custom_leaf(&program, &w, 4, &pis, &config)
        });
    }

    /// A forged path that DOES recompute the chain (so every per-level `MerkleHash`
    /// holds) but climbs to a DIFFERENT root, while the PIs still claim the honest
    /// root, is also UNSAT — the last-row `parent == root` boundary pin bites.
    #[test]
    fn forged_merkle_root_pin_does_not_fold() {
        let program = CellProgram::new(merkle_poseidon2_descriptor(), 1);
        let honest_levels = demo_levels();
        let (_honest_w, honest_pis) = honest_merkle_path(BabyBear::new(1234), &honest_levels);

        // A self-consistent path over a DIFFERENT sibling set ⇒ a different (genuine)
        // root, but we keep the HONEST [leaf, root] PIs. C2 holds per level; the
        // last-row `parent == root_pi` boundary fails.
        let mut other_levels = honest_levels;
        other_levels[2].0[0] = other_levels[2].0[0] + BabyBear::new(99);
        let (w, other_pis) = honest_merkle_path(BabyBear::new(1234), &other_levels);
        assert_ne!(
            other_pis[1], honest_pis[1],
            "the forged path has a different root"
        );
        let config = ir2_leaf_wrap_config();

        must_refuse_or_unsat_panic("a root-pin mismatch", || {
            // honest_pis claims the honest root; `w` climbs to other root ⇒ pin fails.
            prove_custom_leaf(&program, &w, 4, &honest_pis, &config)
        });
    }

    // ========================================================================
    // The `dregg-dfa-routing-v1` FULL-lowering tooth.
    //
    // The production routing descriptor uses EVERY hash-heavy kind: `Hash4to1`
    // (entry-hash C1, lane-witnessed), `ChainedHash2to1` (running-hash C3) +
    // `SeedHash2to1` (the table-commitment seed) lowered together via a copy-forward
    // accumulator column, and `TableFunction` (the GAP-A transition table) lowered to
    // its bivariate-Lagrange gate. It now FULLY lowers to a foldable IR-2 leaf; an
    // honest route proves, and a forged transition (broken chain / wrong table entry /
    // wrong route-commitment) is UNSAT.
    // ========================================================================

    use dregg_circuit::dsl::dfa_routing::{build_routing_witness, dfa_routing_descriptor};

    /// The exact 4-state production router (`dfa_circuit.rs` / `dfa_routing.rs`):
    /// IDLE=0/LOCAL=1/REMOTE=2/REJECT=3; symbols internal/external/privileged/unknown.
    fn router_transitions() -> Vec<(u32, u32, u32)> {
        let table = [[1u32, 2, 1, 3], [1, 2, 1, 3], [1, 2, 3, 3], [3, 3, 3, 3]];
        let mut out = Vec::new();
        for (state, row) in table.iter().enumerate() {
            for (symbol, &next) in row.iter().enumerate() {
                out.push((state as u32, symbol as u32, next));
            }
        }
        out
    }

    /// `dregg-dfa-routing-v1` FULLY lowers — every kind (`Hash4to1` / `ChainedHash2to1` /
    /// `SeedHash2to1` / `TableFunction`) now maps. The chain adds one copy-forward `acc`
    /// column (+ its 7 chip lanes) for the running hash, on top of the entry-hash site's
    /// lanes; no kind is refused.
    #[test]
    fn dfa_routing_v1_fully_lowers() {
        let transitions = router_transitions();
        let program = CellProgram::new(
            dfa_routing_descriptor("dregg-dfa-routing-v1", &transitions),
            1,
        );
        let lowered =
            lower_cellprogram(&program).expect("dregg-dfa-routing-v1 fully lowers to IR-2");
        // Two chip sites (entry-hash C1 + the running-hash per-row chip) ⇒ 2·7 lane cols,
        // plus ONE copy-forward accumulator column for the chain.
        assert_eq!(
            lowered.desc.trace_width,
            program.descriptor.trace_width + 1 + 2 * (CHIP_OUT_LANES - 1)
        );
        assert_eq!(lowered.chains.len(), 1, "one running-hash chain");
        let chip_lookups = lowered
            .desc
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
            .count();
        assert_eq!(chip_lookups, 2, "entry-hash + running-hash chip sites");
    }

    /// THE POSITIVE POLE: an honest routing classification proves as a foldable IR-2 leaf —
    /// the entry-hash chip binds C1, the copy-forward chip binds the running hash to the
    /// genuine Poseidon2 chain seeded by the table commitment, and the TableFunction gate
    /// holds every (state, symbol, next) edge.
    #[test]
    fn honest_dfa_routing_folds() {
        let transitions = router_transitions();
        let program = CellProgram::new(
            dfa_routing_descriptor("dregg-dfa-routing-v1", &transitions),
            1,
        );
        // internal, external, internal: IDLE -> LOCAL -> REMOTE -> LOCAL.
        let (w, pis) = build_routing_witness(&transitions, 0, &[0, 1, 0]).expect("honest route");
        let rows = w.get("current_state").unwrap().len();
        let config = ir2_leaf_wrap_config();
        prove_custom_leaf(&program, &w, rows, &pis, &config)
            .expect("an honest dfa-routing transition proves as a foldable IR-2 leaf");
    }

    /// THE NEGATIVE POLE (broken chain): tampering one row's `running_hash` breaks the
    /// running-hash chip equality (`running == hash_2_to_1(acc, entry)`) — the forged
    /// accumulator no longer equals the genuine permutation, so the leaf is UNSAT.
    #[test]
    fn forged_route_commitment_chain_does_not_fold() {
        let transitions = router_transitions();
        let program = CellProgram::new(
            dfa_routing_descriptor("dregg-dfa-routing-v1", &transitions),
            1,
        );
        let (mut w, pis) =
            build_routing_witness(&transitions, 0, &[0, 1, 0]).expect("honest route");
        let rows = w.get("current_state").unwrap().len();
        // FORGE: corrupt the running hash at row 1. The per-row chip's `out0 ==
        // perm(acc, entry)[0]` no longer holds (and the copy-forward propagates the lie),
        // so no witness satisfies the lowered leaf.
        w.get_mut("running_hash").unwrap()[1] += BabyBear::ONE;
        let config = ir2_leaf_wrap_config();

        must_refuse_or_unsat_panic("a forged running-hash chain", || {
            prove_custom_leaf(&program, &w, rows, &pis, &config)
        });
    }

    /// THE NEGATIVE POLE (wrong table entry): tampering a `next_state` to an edge the
    /// transition TABLE forbids breaks the `TableFunction` gate (`next == step(state,
    /// symbol)`), the entry-hash C1, and the continuity C2 — the leaf is UNSAT.
    #[test]
    fn forged_table_entry_does_not_fold() {
        let transitions = router_transitions();
        let program = CellProgram::new(
            dfa_routing_descriptor("dregg-dfa-routing-v1", &transitions),
            1,
        );
        let (mut w, pis) =
            build_routing_witness(&transitions, 0, &[0, 1, 0]).expect("honest route");
        let rows = w.get("current_state").unwrap().len();
        // FORGE: claim row 1 routes to an edge the table forbids (LOCAL=1 where the real
        // step from LOCAL-external is REMOTE=2). TableFunction + entry hash both reject it.
        w.get_mut("next_state").unwrap()[1] = BabyBear::new(1);
        let config = ir2_leaf_wrap_config();

        must_refuse_or_unsat_panic("a forbidden table edge", || {
            prove_custom_leaf(&program, &w, rows, &pis, &config)
        });
    }

    // ========================================================================
    // The MULTI-CHUNK in-circuit PI commitment (upstream blocker #1: chain all
    // 32 custom-leaf public inputs) — ROTATED to the 8-felt commitment
    // (upstream blocker #2 flag day): every equality below is over BOTH squeeze
    // blocks, so the ladder pins the absorb schedule AND the genuine second
    // squeeze permutation. The old 4-felt expected values changed by
    // construction (they are re-derived from the NEW 8-felt host derivation,
    // never kept stale).
    //
    // Host/in-circuit equality is checked by EXECUTING the real gadget circuit
    // (CircuitRunner witness generation over the same enabled Poseidon2/recompose
    // ops the leaf wrap proves) — no FRI, so the whole length ladder is cheap.
    // The host side is the untouched `custom_proof_pi_commitment`
    // (`WideHash::from_poseidon2` over `Poseidon2State`, a fully independent
    // implementation), so the two paths share NO code: agreement pins the absorb
    // schedule (chunking, domain/len lanes, capacity chaining, no padding block,
    // no squeeze permute) byte-for-byte. The genuine end-to-end pole (the gadget
    // proving inside the leaf wrap and exposing through `expose_claim`) is the
    // 32-PI leaf test below.
    // ========================================================================

    use p3_baby_bear::default_babybear_poseidon2_16;
    use p3_circuit::ops::{generate_poseidon2_trace, generate_recompose_trace};
    use p3_poseidon2_circuit_air::BabyBearD4Width16;

    /// Execute (not prove) the in-circuit commitment gadget over `pis` and return
    /// the four base-field commitment lanes it computes.
    fn eval_incircuit_commitment(pis: &[BabyBear]) -> ProofBindCommitment {
        let mut cb: CircuitBuilder<RecursionChallenge> = CircuitBuilder::new();
        cb.enable_poseidon2_perm::<BabyBearD4Width16, _>(
            generate_poseidon2_trace::<RecursionChallenge, BabyBearD4Width16>,
            default_babybear_poseidon2_16(),
        );
        cb.enable_recompose::<P3BabyBear>(
            generate_recompose_trace::<P3BabyBear, RecursionChallenge>,
        );

        let ins: Vec<Target> = pis.iter().map(|_| cb.alloc_public_input("pi")).collect();
        let commit =
            incircuit_custom_pi_commitment(&mut cb, &ins).expect("commitment gadget builds");
        for (i, t) in commit.iter().enumerate() {
            cb.tag(*t, format!("commit{i}"))
                .expect("commitment lane tags");
        }
        let circuit = cb.build().expect("gadget circuit builds");
        let mut runner = circuit.runner();
        let pubs: Vec<RecursionChallenge> = pis
            .iter()
            .map(|&x| RecursionChallenge::from(P3BabyBear::from_u64(x.as_u32() as u64)))
            .collect();
        runner.set_public_inputs(&pubs).expect("public inputs set");
        let traces = runner.run().expect("gadget circuit executes");
        core::array::from_fn(|i| {
            let v = traces
                .probe(&format!("commit{i}"))
                .expect("commitment lane is tagged");
            let coeffs =
                <RecursionChallenge as BasedVectorSpace<P3BabyBear>>::as_basis_coefficients_slice(
                    v,
                );
            assert!(
                coeffs[1..].iter().all(|&c| c == P3BabyBear::ZERO),
                "a decomposed commitment lane is base-embedded (coeff 0 only)"
            );
            BabyBear::new(coeffs[0].as_canonical_u32())
        })
    }

    /// Host/in-circuit equality across the whole chunk-count ladder: empty (zero
    /// permutations), one partial chunk, one exact chunk, chunk+1, two exact chunks,
    /// eight chunks with and without a partial tail, and sixteen chunks.
    #[test]
    fn multichunk_incircuit_commitment_matches_host() {
        for &len in &[0usize, 1, 4, 5, 8, 31, 32, 64] {
            let pis: Vec<BabyBear> = (0..len as u32)
                .map(|i| BabyBear::new(1 + 977 * i))
                .collect();
            let got = eval_incircuit_commitment(&pis);
            let host = custom_proof_pi_commitment(&pis);
            assert_eq!(
                got, host,
                "host/in-circuit commitment mismatch at input length {len}"
            );
        }
    }

    /// Every PI position feeds the commitment (mutating PI 0 / 4 / 31 of a 32-PI
    /// input changes it, and the changed value still matches ITS host derivation),
    /// and the declared length is bound (31 inputs vs the same 31 zero-padded to 32
    /// do not collide — the lane-5 length tag differs).
    #[test]
    fn multichunk_commitment_binds_positions_and_length() {
        let base: Vec<BabyBear> = (0..32u32).map(|i| BabyBear::new(5 + 131 * i)).collect();
        let base_commit = eval_incircuit_commitment(&base);
        assert_eq!(base_commit, custom_proof_pi_commitment(&base));

        for &k in &[0usize, 4, 31] {
            let mut mutated = base.clone();
            mutated[k] += BabyBear::ONE;
            let got = eval_incircuit_commitment(&mutated);
            assert_eq!(
                got,
                custom_proof_pi_commitment(&mutated),
                "the mutated input still matches its own host derivation (PI {k})"
            );
            assert_ne!(
                got, base_commit,
                "mutating PI {k} must change the commitment"
            );
        }

        let short: Vec<BabyBear> = base[..31].to_vec();
        let mut padded = short.clone();
        padded.push(BabyBear::ZERO);
        let short_c = eval_incircuit_commitment(&short);
        let padded_c = eval_incircuit_commitment(&padded);
        assert_eq!(short_c, custom_proof_pi_commitment(&short));
        assert_eq!(padded_c, custom_proof_pi_commitment(&padded));
        assert_ne!(
            short_c, padded_c,
            "zero-padding must not collide: the declared length binds"
        );
    }

    /// A 32-column, 32-PI program: every column is pinned to its OWN public input on
    /// the first row (32 INDEPENDENTLY bound PIs — no PI is derived from another),
    /// plus a cross-row constraint keeping column 0 constant so the program has a
    /// real transition too.
    fn wide_pi_program(n: usize) -> CellProgram {
        let columns = (0..n)
            .map(|i| ColumnDef {
                name: format!("c{i}"),
                index: i,
                kind: ColumnKind::Value,
            })
            .collect();
        let boundaries = (0..n)
            .map(|i| BoundaryDef::PiBinding {
                row: BoundaryRow::First,
                col: i,
                pi_index: i,
            })
            .collect();
        let descriptor = CircuitDescriptor {
            name: format!("dregg-custom-widepi-{n}-v1"),
            trace_width: n,
            max_degree: 2,
            columns,
            constraints: vec![ConstraintExpr::Transition {
                next_col: 0,
                local_col: 0,
            }],
            boundaries,
            public_input_count: n,
            lookup_tables: vec![],
        };
        CellProgram::new(descriptor, 1)
    }

    /// Honest witness for [`wide_pi_program`]: column `i` constant at PI `i`.
    fn wide_pi_witness(n: usize) -> (HashMap<String, Vec<BabyBear>>, usize, Vec<BabyBear>) {
        let rows = 4;
        let pis: Vec<BabyBear> = (0..n as u32)
            .map(|i| BabyBear::new(101 + 313 * i))
            .collect();
        let mut w = HashMap::new();
        for (i, &v) in pis.iter().enumerate() {
            w.insert(format!("c{i}"), vec![v; rows]);
        }
        (w, rows, pis)
    }

    /// THE POSITIVE POLE (multi-chunk): a genuine 32-PI custom leaf proves through
    /// the full leaf wrap AND its in-circuit-exposed commitment equals the host
    /// [`custom_proof_pi_commitment`] over all 32 PIs — the 8-permutation chained
    /// absorb survives the WitnessChecks bus and the `expose_claim` weld. The
    /// first-chunk-only commitment differs, so the chain is real, not a truncation.
    #[test]
    fn thirtytwo_pi_leaf_proves_and_exposes_multichunk_commitment() {
        let program = wide_pi_program(32);
        let (w, rows, pis) = wide_pi_witness(32);
        let config = ir2_leaf_wrap_config();

        let output = prove_custom_leaf_with_commitment(&program, &w, rows, &pis, &config)
            .expect("the honest 32-PI custom program must prove as a commitment-exposing leaf");

        let exposed = read_exposed_pi_commitment(&output)
            .expect("the 32-PI leaf exposes the full 8-felt commitment claim");
        assert_eq!(
            exposed,
            custom_proof_pi_commitment(&pis),
            "the exposed commitment must byte-match the host over ALL 32 PIs"
        );
        assert_ne!(
            exposed,
            custom_proof_pi_commitment(&pis[..4]),
            "the multi-chunk absorb is real: the commitment is not the first chunk's alone"
        );
    }

    /// THE NEGATIVE POLE (stale witness): mutating PI 31 while leaving the witness
    /// stale violates that column's first-row `PiBinding` — the leaf REFUSES, so no
    /// commitment over the mutated PIs is ever exposed.
    #[test]
    fn thirtytwo_pi_leaf_refuses_stale_pi_mutation() {
        let program = wide_pi_program(32);
        let (w, rows, mut pis) = wide_pi_witness(32);
        pis[31] += BabyBear::ONE;
        let config = ir2_leaf_wrap_config();

        must_refuse_or_unsat_panic("a mutated PI with a stale witness minted a leaf", || {
            prove_custom_leaf_with_commitment(&program, &w, rows, &pis, &config)
        });
    }

    /// THE NEGATIVE POLE (declared length): passing 31 PIs against a 32-PI
    /// descriptor is REFUSED outright (`public_inputs.len()` must equal the
    /// descriptor's `public_input_count`), so a shortened input can never reach a
    /// shorter-length commitment.
    #[test]
    fn thirtytwo_pi_leaf_refuses_declared_length_mismatch() {
        let program = wide_pi_program(32);
        let (w, rows, pis) = wide_pi_witness(32);
        let short = pis[..31].to_vec();
        let config = ir2_leaf_wrap_config();

        must_refuse_or_unsat_panic(
            "a declared-length mismatch minted a leaf — the length is not bound",
            || prove_custom_leaf_with_commitment(&program, &w, rows, &short, &config),
        );
    }
}
