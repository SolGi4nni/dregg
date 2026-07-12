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
//! PI slots 46..49) IN THE DEPLOYED CHAIN PROVER. For a custom turn,
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

use dregg_circuit::cap_root::CAP_FACT_MARK;
use dregg_circuit::descriptor_ir2::{
    CHIP_OUT_LANES, CHIP_RATE, CHIP_TUPLE_LEN, EffectVmDescriptor2, Ir2Air, LookupSpec,
    MemBoundaryWitness, TID_P2, UMemBoundaryWitness, VmConstraint2, WindowExpr, WindowGateSpec,
    ir2_airs_and_common_for_config, prove_vm_descriptor2_for_config,
};
use dregg_circuit::dsl::circuit::{BoundaryDef, BoundaryRow, CellProgram, ConstraintExpr};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};
use std::collections::HashMap;

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

/// `x − y` as a `LeanExpr` (no subtraction node: `x + (−1)·y`).
fn sub(x: LeanExpr, y: LeanExpr) -> LeanExpr {
    LeanExpr::add(x, LeanExpr::mul(LeanExpr::Const(-1), y))
}

/// Lower a PURE-LOCAL `ConstraintExpr` to the `LeanExpr` polynomial body that must
/// vanish (`body == 0`). Returns `Err` for any kind that is cross-row, PI-reading,
/// or otherwise not expressible as a single local gate body (those are handled — or
/// refused — at the top level in [`cellprogram_to_descriptor2`]).
fn gate_body(expr: &ConstraintExpr) -> Result<LeanExpr, String> {
    Ok(match expr {
        ConstraintExpr::Equality { col_a, col_b } => {
            sub(LeanExpr::Var(*col_a), LeanExpr::Var(*col_b))
        }
        ConstraintExpr::Multiplication { a, b, output } => sub(
            LeanExpr::mul(LeanExpr::Var(*a), LeanExpr::Var(*b)),
            LeanExpr::Var(*output),
        ),
        ConstraintExpr::Binary { col } => LeanExpr::mul(
            LeanExpr::Var(*col),
            LeanExpr::add(LeanExpr::Var(*col), LeanExpr::Const(-1)),
        ),
        ConstraintExpr::Polynomial { terms } => {
            // Σ coeffᵢ · ∏ colⱼ. The BabyBear coeff is carried as its canonical u32
            // value (< p) reduced back into the field at eval-time, so e.g. `p − 1`
            // is the faithful `−1`.
            let mut acc: Option<LeanExpr> = None;
            for term in terms {
                let mut prod = LeanExpr::Const(term.coeff.0 as i64);
                for &ci in &term.col_indices {
                    prod = LeanExpr::mul(prod, LeanExpr::Var(ci));
                }
                acc = Some(match acc {
                    None => prod,
                    Some(a) => LeanExpr::add(a, prod),
                });
            }
            // An empty polynomial is the zero constraint.
            acc.unwrap_or(LeanExpr::Const(0))
        }
        ConstraintExpr::Gated {
            selector_col,
            inner,
        } => LeanExpr::mul(LeanExpr::Var(*selector_col), gate_body(inner)?),
        ConstraintExpr::InvertedGated {
            selector_col,
            inner,
        } => LeanExpr::mul(
            sub(LeanExpr::Const(1), LeanExpr::Var(*selector_col)),
            gate_body(inner)?,
        ),
        ConstraintExpr::Squared { inner } => {
            let b = gate_body(inner)?;
            LeanExpr::mul(b.clone(), b)
        }
        ConstraintExpr::ConditionalNonzero {
            selector_col,
            value_col,
            inverse_col,
        } => LeanExpr::mul(
            LeanExpr::Var(*selector_col),
            sub(
                LeanExpr::mul(LeanExpr::Var(*value_col), LeanExpr::Var(*inverse_col)),
                LeanExpr::Const(1),
            ),
        ),
        ConstraintExpr::AtLeastOne { flag_cols } => {
            // ∏ (1 − flagᵢ) == 0 iff at least one flag is 1.
            let mut acc: Option<LeanExpr> = None;
            for &c in flag_cols {
                let factor = sub(LeanExpr::Const(1), LeanExpr::Var(c));
                acc = Some(match acc {
                    None => factor,
                    Some(a) => LeanExpr::mul(a, factor),
                });
            }
            // An empty AtLeastOne is unsatisfiable in the DSL evaluator (product of
            // no factors is 1, never 0); mirror that as the constant-1 gate.
            acc.unwrap_or(LeanExpr::Const(1))
        }
        // Cross-row / PI-reading / hash / lookup kinds are not local gate bodies.
        other => {
            return Err(format!(
                "constraint kind {} is not expressible as a local IR-v2 gate body",
                kind_name(other)
            ));
        }
    })
}

/// A short kind name for error messages.
fn kind_name(expr: &ConstraintExpr) -> &'static str {
    match expr {
        ConstraintExpr::Equality { .. } => "Equality",
        ConstraintExpr::Multiplication { .. } => "Multiplication",
        ConstraintExpr::Binary { .. } => "Binary",
        ConstraintExpr::PiBinding { .. } => "PiBinding",
        ConstraintExpr::Transition { .. } => "Transition",
        ConstraintExpr::Polynomial { .. } => "Polynomial",
        ConstraintExpr::Gated { .. } => "Gated",
        ConstraintExpr::InvertedGated { .. } => "InvertedGated",
        ConstraintExpr::Squared { .. } => "Squared",
        ConstraintExpr::Hash { .. } => "Hash",
        ConstraintExpr::ConditionalNonzero { .. } => "ConditionalNonzero",
        ConstraintExpr::AtLeastOne { .. } => "AtLeastOne",
        ConstraintExpr::Hash2to1 { .. } => "Hash2to1",
        ConstraintExpr::Hash4to1 { .. } => "Hash4to1",
        ConstraintExpr::Hash3Cap { .. } => "Hash3Cap",
        ConstraintExpr::MerkleHash8 { .. } => "MerkleHash8",
        ConstraintExpr::MerkleHash { .. } => "MerkleHash",
        ConstraintExpr::Lookup { .. } => "Lookup",
        ConstraintExpr::ChainedHash2to1 { .. } => "ChainedHash2to1",
        ConstraintExpr::SeedHash2to1 { .. } => "SeedHash2to1",
        ConstraintExpr::TableFunction { .. } => "TableFunction",
    }
}

// ============================================================================
// Poseidon2 lane-witnessing (the shared MerkleHash / TID_P2 extension).
//
// A `CellProgram` Poseidon2 hash site (`Hash2to1` / `Hash4to1` / `Hash3Cap` /
// `MerkleHash`) is ONE Poseidon2 permutation. The faithful IR-v2 carrier is a
// `Lookup` into the declared chip table `TID_P2`, whose row is the 20-wide tuple
// `[arity, in0..in10 (CHIP_RATE), out0, lane1..lane7]`. The chip-table AIR enforces
// `out[i] == perm(ins)[i]` for ALL 8 output lanes, so a forged digest OR a forged
// intermediate lane is UNSAT (`ir2_forged_output_lane_refuses`). The lookup balances
// (LogUp) the main-side send against that genuine chip row, so the recompute is
// witnessed by a pure light client folding the leaf — exactly the cap_root/heap_root
// in-circuit Merkle-open pattern (a witnessed sibling path, constrained recompute).
//
// `out0` is the site's own DIGEST column (the `CellProgram` already fills it via
// `generate_trace`); the 7 lane columns (lanes 1..7) are ALLOCATED past the base
// trace width and filled descriptor-side by `fill_chip_lanes` (the
// `trace_with_chip_lanes` weld inside `prove_vm_descriptor2_for_config`). A Merkle
// PATH is many such sites chained: each level's parent (`out0`) feeds the next level's
// `current` via a `Transition`, and the leaf/root are pinned to PIs by the boundary
// `PiBinding`s — so a wrong sibling no longer reaches the root PI and the leaf is UNSAT.
// ============================================================================

/// Build one `TID_P2` chip lookup for a single Poseidon2 permutation site.
///
/// `arity` selects the chip's state seeding (2 = `hash_2_to_1`, 3 = `cap_node`
/// `[FACT_MARK,l,r]`, 4 = `hash_4_to_1`), `ins` are the absorb input expressions
/// (zero-padded to `CHIP_RATE`), `out0_col` is the digest column the program fills,
/// and `lane_base..lane_base+6` are the 7 freshly-allocated lane columns (lanes 1..7).
/// The resulting 20-wide tuple matches the chip-row shape `MainLayout::build` validates.
fn chip_lookup_site(
    arity: u32,
    ins: &[LeanExpr],
    out0_col: usize,
    lane_base: usize,
) -> VmConstraint2 {
    let mut tuple: Vec<LeanExpr> = Vec::with_capacity(CHIP_TUPLE_LEN);
    tuple.push(LeanExpr::Const(arity as i64));
    for i in 0..CHIP_RATE {
        tuple.push(ins.get(i).cloned().unwrap_or(LeanExpr::Const(0)));
    }
    // out0 = the digest (lane 0); the AIR binds it to `perm(ins)[0]`.
    tuple.push(LeanExpr::Var(out0_col));
    // lanes 1..7 — the genuine distinct permutation lanes, witnessed columns the AIR
    // EQUALITY-binds to `perm(ins)[i]` (a forged lane is UNSAT). `fill_chip_lanes` writes them.
    for j in 0..(CHIP_OUT_LANES - 1) {
        tuple.push(LeanExpr::Var(lane_base + j));
    }
    debug_assert_eq!(tuple.len(), CHIP_TUPLE_LEN);
    VmConstraint2::Lookup(LookupSpec {
        table: TID_P2,
        tuple,
    })
}

/// The Lagrange leading coefficient `1 / ∏_{j≠i}(i − j)` of the degree-3 indicator
/// `ind_i(p)` over the 4-point grid `{0,1,2,3}` (so `ind_i(i) = 1`, `ind_i(j≠i) = 0`),
/// as a canonical BabyBear value. Used to express the position-dependent child
/// reconstruction of `MerkleHash` as `LeanExpr` chip-input polynomials.
fn lagrange_coeff(i: usize) -> BabyBear {
    let mut denom = BabyBear::ONE;
    for j in 0..4usize {
        if j != i {
            // (i − j) in the field (i, j ∈ 0..4 so the difference is small; lift via i64).
            let d = i64_to_field(i as i64 - j as i64);
            denom *= d;
        }
    }
    denom
        .inverse()
        .expect("Lagrange denominator over a 4-point grid is a unit")
}

/// `n` (possibly negative, small) as a canonical BabyBear.
fn i64_to_field(n: i64) -> BabyBear {
    let p = BABYBEAR_P as i64;
    let r = ((n % p) + p) % p;
    BabyBear::new(r as u32)
}

/// The degree-3 position indicator `ind_i(position_col)` as a `LeanExpr`:
/// `coeff_i · ∏_{j≠i}(position − j)`, which is `1` when `position == i` and `0` for the
/// other grid points `{0,1,2,3}` (pinned by the program's position-validity gate).
fn position_indicator(position_col: usize, i: usize) -> LeanExpr {
    let mut acc = LeanExpr::Const(lagrange_coeff(i).as_u32() as i64);
    for j in 0..4usize {
        if j != i {
            // (position − j)
            let factor = LeanExpr::add(LeanExpr::Var(position_col), LeanExpr::Const(-(j as i64)));
            acc = LeanExpr::mul(acc, factor);
        }
    }
    acc
}

/// Sum a list of `LeanExpr`s (empty = `Const(0)`).
fn add_all(terms: Vec<LeanExpr>) -> LeanExpr {
    let mut it = terms.into_iter();
    match it.next() {
        None => LeanExpr::Const(0),
        Some(first) => it.fold(first, LeanExpr::add),
    }
}

/// The four `MerkleHash` children as `LeanExpr`s over `(current, sib0, sib1, sib2,
/// position)`, reproducing the evaluator's reconstruction (`current` at slot
/// `position`, siblings filling the other slots IN ORDER) for every grid position
/// `{0,1,2,3}`. Each child is `ind_p·current + Σ [slot-belongs-to-sib_k]·sib_k`, a
/// degree-4 polynomial; off-grid points are irrelevant (the LogUp balances over trace
/// rows, where the position-validity gate pins `position ∈ {0,1,2,3}`).
fn merkle_children_exprs(
    current_col: usize,
    sib_cols: &[usize; 3],
    position_col: usize,
) -> [LeanExpr; 4] {
    let ind = |i: usize| position_indicator(position_col, i);
    let cur = || LeanExpr::Var(current_col);
    let sib = |k: usize| LeanExpr::Var(sib_cols[k]);
    let mul = LeanExpr::mul;
    // slot 0: current at p=0, else sib0 (the first non-position slot for p>0).
    let child0 = add_all(vec![
        mul(ind(0), cur()),
        mul(add_all(vec![ind(1), ind(2), ind(3)]), sib(0)),
    ]);
    // slot 1: current at p=1; sib0 at p=0; sib1 at p∈{2,3}.
    let child1 = add_all(vec![
        mul(ind(1), cur()),
        mul(ind(0), sib(0)),
        mul(add_all(vec![ind(2), ind(3)]), sib(1)),
    ]);
    // slot 2: current at p=2; sib1 at p∈{0,1}; sib2 at p=3.
    let child2 = add_all(vec![
        mul(ind(2), cur()),
        mul(add_all(vec![ind(0), ind(1)]), sib(1)),
        mul(ind(3), sib(2)),
    ]);
    // slot 3: current at p=3, else sib2 (the last non-position slot for p<3).
    let child3 = add_all(vec![
        mul(ind(3), cur()),
        mul(add_all(vec![ind(0), ind(1), ind(2)]), sib(2)),
    ]);
    [child0, child1, child2, child3]
}

// ============================================================================
// Bivariate Lagrange (the `TableFunction` GAP-A transition table → a local gate).
//
// `TableFunction { a, b, out, a_values, b_values, outputs }` asserts `out == P(a, b)`
// where `P` is the unique bivariate interpolant agreeing with `outputs` on the grid
// `a_values × b_values`. It is PURE-LOCAL and gate-expressible: lower it to the
// degree-`(|a|-1)+(|b|-1)` polynomial body `out − Σ_i Σ_j outputs[i·|b|+j]·Lᵢ(a)·Lⱼ(b)`,
// each `Lᵢ` a Lagrange indicator over the grid (`Lᵢ(grid_k) = δ_{ik}`), exactly as
// `MerkleHash`'s position reconstruction lowers its 4-point indicator. The paired
// grid-range vanishing gates (`∏ (col − v) == 0`) pin `(a, b)` onto the grid, so the
// interpolant is evaluated only at real grid points (off-grid escapes are impossible).
// ============================================================================

/// The Lagrange leading coefficient `1 / ∏_{k≠i}(values[i] − values[k])` over an
/// arbitrary distinct grid `values`, as a canonical BabyBear. `Err` if the grid has a
/// repeated value (a zero denominator — the descriptor's grid is distinct by construction).
fn grid_lagrange_coeff(values: &[u32], i: usize) -> Result<BabyBear, String> {
    let xi = i64_to_field(values[i] as i64);
    let mut denom = BabyBear::ONE;
    for (k, &vk) in values.iter().enumerate() {
        if k != i {
            denom *= xi - i64_to_field(vk as i64);
        }
    }
    denom.inverse().ok_or_else(|| {
        "TableFunction grid has a repeated value (Lagrange denominator 0)".to_string()
    })
}

/// The Lagrange indicator `Lᵢ(col)` over `values`: `coeff_i · ∏_{k≠i}(col − values[k])`,
/// which is `1` when `col == values[i]` and `0` at the other grid points (pinned by the
/// paired grid-range vanishing gate). A degree-`(|values|−1)` `LeanExpr`.
fn grid_indicator(col: usize, values: &[u32], i: usize) -> Result<LeanExpr, String> {
    let coeff = grid_lagrange_coeff(values, i)?;
    let mut acc = LeanExpr::Const(coeff.as_u32() as i64);
    for (k, &vk) in values.iter().enumerate() {
        if k != i {
            acc = LeanExpr::mul(
                acc,
                LeanExpr::add(LeanExpr::Var(col), LeanExpr::Const(-(vk as i64))),
            );
        }
    }
    Ok(acc)
}

/// Lower a `TableFunction` to its bivariate-interpolation gate body
/// `out − Σ_i Σ_j outputs[i·|b|+j]·Lᵢ(a)·Lⱼ(b)` (which must vanish).
fn table_function_body(
    a_col: usize,
    b_col: usize,
    out_col: usize,
    a_values: &[u32],
    b_values: &[u32],
    outputs: &[u32],
) -> Result<LeanExpr, String> {
    let nb = b_values.len();
    if outputs.len() != a_values.len() * nb {
        return Err(format!(
            "TableFunction outputs len {} != |a|·|b| {}",
            outputs.len(),
            a_values.len() * nb
        ));
    }
    let mut terms: Vec<LeanExpr> = Vec::with_capacity(outputs.len());
    for (i, _) in a_values.iter().enumerate() {
        let la = grid_indicator(a_col, a_values, i)?;
        for (j, _) in b_values.iter().enumerate() {
            let out_ij = outputs[i * nb + j];
            let lb = grid_indicator(b_col, b_values, j)?;
            terms.push(LeanExpr::mul(
                LeanExpr::mul(LeanExpr::Const(out_ij as i64), la.clone()),
                lb,
            ));
        }
    }
    // `out − P(a, b)`.
    Ok(sub(LeanExpr::Var(out_col), add_all(terms)))
}

// ============================================================================
// Running-hash chains (the cross-row `ChainedHash2to1` + its `SeedHash2to1` seed)
// lowered via a COPY-FORWARD accumulator column.
//
// A `CellProgram` `ChainedHash2to1 { out, seed, input }` is a CROSS-ROW relation
// `next[out] == hash_2_to_1(local[seed], next[input])`: the absorb seeds from the
// PREVIOUS row's accumulator. A single-row `TID_P2` chip lookup reads only the `local`
// window, so it cannot reach the `next` input. The faithful carrier is a fresh
// COPY-FORWARD witness column `acc` that carries the prior accumulator onto the current
// row, so the per-row chip is single-row again:
//
//   * per-row chip (every row j):  `out[j] == hash_2_to_1(acc[j], input[j])`   (TID_P2)
//   * copy-forward (transition):   `next[acc] − local[seed] == 0`              (WindowGate)
//   * seed pin (first row):        `acc[0] == pi[seed_pi_index]`               (PiBinding)
//
// The copy-forward sets `acc[i+1] = seed[i]` (= the previous accumulator), so the chip
// reproduces `out[i+1] = hash(seed[i], input[i+1])` byte-for-byte; row 0 is pinned by the
// `SeedHash2to1` seed (`acc[0] = pi[tableCommitment]`), reproducing `out[0] =
// hash(tableCommitment, input[0])`. Together they reproduce BOTH the `ChainedHash2to1`
// rolling step (C3) AND the `SeedHash2to1` seed of `dregg-dfa-routing-v1` exactly. The
// `acc` column is witnessed descriptor-side ([`fill_chain_columns`]); the chip equality-
// binds `out` to the genuine permutation, so a forged accumulator / broken chain is UNSAT.
// ============================================================================

/// The trace-fill plan for one running-hash chain: which fresh column carries the
/// copy-forward accumulator, which column it copies (`acc[i] = source[i−1]`), and the
/// first-row seed (`acc[0] = pi[seed_pi]`).
#[derive(Clone, Debug)]
struct ChainFill {
    /// The freshly-allocated copy-forward accumulator column.
    acc_col: usize,
    /// The source accumulator column copied forward (`acc[i] = source[i−1]`); the
    /// `ChainedHash2to1`'s `seed_local_col`.
    source_col: usize,
    /// The first-row seed public input (`acc[0] = pi[seed_pi]`).
    seed_pi: usize,
}

/// The result of lowering a `CellProgram`: the IR-v2 descriptor plus the copy-forward
/// fill plans the trace producer must apply ([`fill_chain_columns`]).
struct Lowered {
    desc: EffectVmDescriptor2,
    chains: Vec<ChainFill>,
}

/// Unwrap a (possibly `Gated`-wrapped) `SeedHash2to1`, returning `(output_col,
/// seed_pi_index, input_col)`. The `dregg-dfa-routing-v1` seed is `Gated { is_first,
/// SeedHash2to1 { .. } }`; the first-row PI-binding tag replaces the `is_first` gate, so
/// the gate selector is irrelevant here.
fn as_seed_hash(expr: &ConstraintExpr) -> Option<(usize, usize, usize)> {
    match expr {
        ConstraintExpr::SeedHash2to1 {
            output_col,
            seed_pi_index,
            input_col,
        } => Some((*output_col, *seed_pi_index, *input_col)),
        ConstraintExpr::Gated { inner, .. } => match &**inner {
            ConstraintExpr::SeedHash2to1 {
                output_col,
                seed_pi_index,
                input_col,
            } => Some((*output_col, *seed_pi_index, *input_col)),
            _ => None,
        },
        _ => None,
    }
}

/// Fill the copy-forward accumulator columns of `trace` (in place) per the lowered
/// chain plan, BEFORE the chip-lane weld runs: row 0 = the seed public input, row `i` =
/// the previous row's accumulator source. The chip-lane fill then derives each row's
/// genuine permutation lanes from this `acc` value, so `out == hash_2_to_1(acc, input)`
/// holds at every row.
fn fill_chain_columns(
    chains: &[ChainFill],
    trace: &mut [Vec<BabyBear>],
    public_inputs: &[BabyBear],
) {
    let n = trace.len();
    for chain in chains {
        if n == 0 {
            continue;
        }
        trace[0][chain.acc_col] = public_inputs
            .get(chain.seed_pi)
            .copied()
            .unwrap_or(BabyBear::ZERO);
        for i in 1..n {
            trace[i][chain.acc_col] = trace[i - 1][chain.source_col];
        }
    }
}

/// Adapt a `CellProgram`'s [`CircuitDescriptor`] into the IR-v2
/// [`EffectVmDescriptor2`] so it can prove through the general prover.
///
/// Each `ConstraintExpr` maps per the module-level table. The Poseidon2 hash kinds
/// `Hash2to1` / `Hash4to1` / `Hash3Cap` / `MerkleHash` lower to `TID_P2` chip lookups
/// with per-site lane columns allocated past the base trace width (the lane-witnessing
/// extension). The cross-row running hash `ChainedHash2to1` + its `SeedHash2to1` first-row
/// seed lower TOGETHER via a copy-forward accumulator column (a per-row chip + a
/// `WindowGate` copy-forward + a first-row PI pin — see the running-hash section). The
/// `TableFunction` lowers to its bivariate-Lagrange gate body. The remaining kinds
/// (`Hash` fact-sponge, arbitrary-entry `Lookup`, an UNSEEDED `ChainedHash2to1`, a
/// `SeedHash2to1` with no paired chain) have no faithful carrier here and are REFUSED with
/// a precise blocker. `BoundaryDef::PiBinding`/`Fixed` (first/last row) graduate to the
/// row-tagged IR-v2 boundary carriers, so a chained Merkle path's leaf/root pins survive.
pub fn cellprogram_to_descriptor2(program: &CellProgram) -> Result<EffectVmDescriptor2, String> {
    lower_cellprogram(program).map(|l| l.desc)
}

/// [`cellprogram_to_descriptor2`] plus the copy-forward fill plan ([`fill_chain_columns`])
/// the trace producer must apply. The public adapter discards the plan; the leaf provers
/// ([`prove_custom_leaf`] / [`prove_custom_leaf_with_commitment`]) use it to witness the
/// running-hash accumulator columns.
fn lower_cellprogram(program: &CellProgram) -> Result<Lowered, String> {
    let desc = &program.descriptor;
    let mut constraints: Vec<VmConstraint2> = Vec::with_capacity(desc.constraints.len());

    // Chip-lane columns are appended PAST the base trace width: each Poseidon2 site
    // claims `CHIP_OUT_LANES - 1` (= 7) fresh witnessed columns (lanes 1..7), filled
    // descriptor-side by `fill_chip_lanes`. The digest (lane 0/out0) is the site's own
    // output column (in-bounds, filled by `generate_trace`).
    let mut width = desc.trace_width;
    let alloc_lanes = |w: &mut usize| -> usize {
        let base = *w;
        *w += CHIP_OUT_LANES - 1;
        base
    };

    // Pre-pass: index the running-hash chain SEEDS. Each `(possibly-Gated) SeedHash2to1`
    // seeding a chain output column is consumed BY that chain (lowered as the chain's
    // first-row `acc[0] == pi[seed]` pin), so the main loop must SKIP it rather than try to
    // lower it as a standalone gate. A `SeedHash2to1` whose output column NO chain
    // accumulates is left unconsumed and hits the standalone-seed blocker below.
    let chain_outputs: std::collections::HashSet<usize> = desc
        .constraints
        .iter()
        .filter_map(|c| match c {
            ConstraintExpr::ChainedHash2to1 {
                output_next_col, ..
            } => Some(*output_next_col),
            _ => None,
        })
        .collect();
    // output_col -> (seed_pi_index, input_col), only for seeds a chain accumulates.
    let mut seed_of: HashMap<usize, (usize, usize)> = HashMap::new();
    let mut consumed_seed: Vec<bool> = vec![false; desc.constraints.len()];
    for (idx, c) in desc.constraints.iter().enumerate() {
        if let Some((out, pi, input)) = as_seed_hash(c)
            && chain_outputs.contains(&out)
        {
            seed_of.insert(out, (pi, input));
            consumed_seed[idx] = true;
        }
    }

    // The copy-forward fill plans accumulated as chains are lowered.
    let mut chains: Vec<ChainFill> = Vec::new();

    for (idx, expr) in desc.constraints.iter().enumerate() {
        // A `SeedHash2to1` consumed by its chain is lowered as that chain's first-row pin.
        if consumed_seed[idx] {
            continue;
        }
        let c2 = match expr {
            ConstraintExpr::PiBinding { col, pi_index } => {
                // A per-row PI gate is inexpressible in `LeanExpr`; the faithful
                // IR-v2 carrier is the row-tag-guarded `PiBinding`. This NARROWS the
                // CellProgram's every-row semantics to first-row (see module docs).
                VmConstraint2::Base(VmConstraint::PiBinding {
                    row: VmRow::First,
                    col: *col,
                    pi_index: *pi_index,
                })
            }
            ConstraintExpr::Transition {
                next_col,
                local_col,
            } => {
                // The two-row carrier: `next[next_col] − local[local_col] == 0` on
                // the transition domain (rows 0..n−2), faithful and column-general.
                VmConstraint2::WindowGate(WindowGateSpec {
                    body: WindowExpr::Add(
                        Box::new(WindowExpr::Nxt(*next_col)),
                        Box::new(WindowExpr::Mul(
                            Box::new(WindowExpr::Const(-1)),
                            Box::new(WindowExpr::Loc(*local_col)),
                        )),
                    ),
                    on_transition: true,
                })
            }
            // ---- Poseidon2 hash sites → TID_P2 chip lookups (the lane-witnessing weld) ----
            ConstraintExpr::Hash2to1 {
                output_col,
                input_col_a,
                input_col_b,
            } => {
                let lane_base = alloc_lanes(&mut width);
                chip_lookup_site(
                    2,
                    &[LeanExpr::Var(*input_col_a), LeanExpr::Var(*input_col_b)],
                    *output_col,
                    lane_base,
                )
            }
            ConstraintExpr::Hash4to1 {
                output_col,
                input_cols,
            } => {
                let lane_base = alloc_lanes(&mut width);
                chip_lookup_site(
                    4,
                    &input_cols
                        .iter()
                        .map(|&c| LeanExpr::Var(c))
                        .collect::<Vec<_>>(),
                    *output_col,
                    lane_base,
                )
            }
            ConstraintExpr::Hash3Cap {
                output_col,
                left_col,
                right_col,
            } => {
                // The cap-tree node hash `cap_node(l, r) = absorb([FACT_MARK, l, r])`
                // (arity-3 chip seeding), matching `cap_root::cap_node`.
                let lane_base = alloc_lanes(&mut width);
                chip_lookup_site(
                    3,
                    &[
                        LeanExpr::Const(CAP_FACT_MARK as i64),
                        LeanExpr::Var(*left_col),
                        LeanExpr::Var(*right_col),
                    ],
                    *output_col,
                    lane_base,
                )
            }
            ConstraintExpr::MerkleHash {
                output_col,
                current_col,
                sib_cols,
                position_col,
            } => {
                // The 4-ary parent hash: reconstruct the position-ordered children as
                // chip-input polynomials, then an arity-4 absorb (== `hash_4_to_1`).
                let lane_base = alloc_lanes(&mut width);
                let children = merkle_children_exprs(*current_col, sib_cols, *position_col);
                chip_lookup_site(4, &children, *output_col, lane_base)
            }
            // The native 8-felt cap-tree node8 compression is a MULTI-output (8-lane)
            // Poseidon2 site arithmetized only by the DSL batch-stark AIR (`dsl_p3_air`,
            // via `poseidon2_permute_expr_lanes`). This IR-v2 chip adapter carries
            // single-output (out0) chip sites, so it has no faithful carrier for the
            // 8-output node8 — a precise blocker, never a lane-0 downgrade.
            ConstraintExpr::MerkleHash8 { .. } => {
                return Err(
                    "constraint kind MerkleHash8 (native 8-felt cap_node8, arity-16 compression) \
                     is an 8-OUTPUT Poseidon2 site; this IR-v2 chip adapter carries single-output \
                     (out0) chip sites only. It is arithmetized by the DSL batch-stark AIR \
                     (dsl_p3_air, 8-lane exposure), not folded here"
                        .to_string(),
                );
            }
            // ---- the remaining hash / lookup / table-function kinds: no faithful
            //      single-permutation chip carrier in this extension — precise blockers. ----
            ConstraintExpr::Hash { .. } => {
                return Err(
                    "constraint kind Hash (capacity-tagged fact-sponge `hash_fact`) uses the \
                     arity-7 cap-leaf / FACT_MARK fact-bus seeding, NOT a narrow arity \
                     2/3/4 absorb; map it via the fact-bus chip path (the named follow-up)"
                        .to_string(),
                );
            }
            // ---- the cross-row running hash + its first-row seed → a copy-forward
            //      accumulator column (the per-row chip + WindowGate copy-forward + PI pin). ----
            ConstraintExpr::ChainedHash2to1 {
                output_next_col,
                seed_local_col,
                input_next_col,
            } => {
                // The chain is faithful ONLY with a paired first-row `SeedHash2to1` pinning
                // `acc[0]`: without it the per-row chip would over-constrain row 0 (`out[0] ==
                // hash(acc[0], input[0])`) where the bare chain leaves it free. An unseeded
                // ChainedHash2to1 is the precise named residual.
                let &(seed_pi, seed_input) = seed_of.get(output_next_col).ok_or_else(|| {
                    "constraint kind ChainedHash2to1 has no paired first-row SeedHash2to1 seed \
                     for its output column; the copy-forward carrier needs the seed to pin \
                     acc[0] (an UNSEEDED running hash is the named residual)"
                        .to_string()
                })?;
                if seed_input != *input_next_col {
                    return Err(format!(
                        "ChainedHash2to1 absorbs column {input_next_col} but its paired \
                         SeedHash2to1 absorbs column {seed_input}; the seed must absorb the \
                         same first-entry column the chain rolls"
                    ));
                }
                // A fresh copy-forward accumulator column `acc`, then its 7 chip lanes.
                let acc_col = width;
                width += 1;
                let lane_base = alloc_lanes(&mut width);
                // Copy-forward: `next[acc] − local[seed_local_col] == 0` (acc[i+1] = the prior
                // accumulator), the cross-row carrier the single-row chip cannot reach.
                constraints.push(VmConstraint2::WindowGate(WindowGateSpec {
                    body: WindowExpr::Add(
                        Box::new(WindowExpr::Nxt(acc_col)),
                        Box::new(WindowExpr::Mul(
                            Box::new(WindowExpr::Const(-1)),
                            Box::new(WindowExpr::Loc(*seed_local_col)),
                        )),
                    ),
                    on_transition: true,
                }));
                // First-row seed pin: `acc[0] == pi[seed_pi]` (the table-commitment seed).
                constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
                    row: VmRow::First,
                    col: acc_col,
                    pi_index: seed_pi,
                }));
                chains.push(ChainFill {
                    acc_col,
                    source_col: *seed_local_col,
                    seed_pi,
                });
                // The per-row chip: `out == hash_2_to_1(acc, input)` (single-row, arity 2).
                chip_lookup_site(
                    2,
                    &[LeanExpr::Var(acc_col), LeanExpr::Var(*input_next_col)],
                    *output_next_col,
                    lane_base,
                )
            }
            // A `SeedHash2to1` that reaches here is NOT consumed by a chain (no chain
            // accumulates its output column) — a standalone first-row PI-seeded hash, which
            // would need a first-row-ONLY chip gate (the named residual).
            ConstraintExpr::SeedHash2to1 { output_col, .. } => {
                return Err(format!(
                    "constraint kind SeedHash2to1 (output col {output_col}) is a standalone \
                     PUBLIC-INPUT-seeded first-row hash with no paired ChainedHash2to1 chain; a \
                     first-row-only chip gate is the named residual"
                ));
            }
            ConstraintExpr::Lookup { table_id, .. } => {
                return Err(format!(
                    "constraint kind Lookup(table \"{table_id}\") names an arbitrary \
                     CellProgram entry-set; IR-v2 lookups target fixed-semantics \
                     declared tables only — no faithful target in this extension"
                ));
            }
            // ---- the deterministic transition table → its bivariate-Lagrange gate body. ----
            ConstraintExpr::TableFunction {
                a_col,
                b_col,
                out_col,
                a_values,
                b_values,
                outputs,
            } => VmConstraint2::Base(VmConstraint::Gate(table_function_body(
                *a_col, *b_col, *out_col, a_values, b_values, outputs,
            )?)),
            // Everything else is a pure-local algebraic gate.
            local => VmConstraint2::Base(VmConstraint::Gate(gate_body(local)?)),
        };
        constraints.push(c2);
    }

    // Boundary pins (leaf/root for a Merkle path; any first/last cell binding) graduate
    // to the row-tagged IR-v2 boundary carriers. `BoundaryRow::Index` has no row-tag
    // carrier (`when_first_row`/`when_last_row` only), so it is refused.
    for b in &desc.boundaries {
        let vmrow = |row: &BoundaryRow| -> Result<VmRow, String> {
            match row {
                BoundaryRow::First => Ok(VmRow::First),
                BoundaryRow::Last => Ok(VmRow::Last),
                BoundaryRow::Index(i) => Err(format!(
                    "boundary at absolute row {i} has no IR-v2 row-tag carrier (only \
                     first/last are expressible)"
                )),
            }
        };
        let c2 = match b {
            BoundaryDef::PiBinding { row, col, pi_index } => {
                VmConstraint2::Base(VmConstraint::PiBinding {
                    row: vmrow(row)?,
                    col: *col,
                    pi_index: *pi_index,
                })
            }
            BoundaryDef::Fixed { row, col, value } => {
                // `local[col] − value == 0`, guarded by the row tag.
                VmConstraint2::Base(VmConstraint::Boundary {
                    row: vmrow(row)?,
                    body: sub(LeanExpr::Var(*col), LeanExpr::Const(value.as_u32() as i64)),
                })
            }
        };
        constraints.push(c2);
    }

    Ok(Lowered {
        desc: EffectVmDescriptor2 {
            name: format!("custom-leaf::{}", desc.name),
            trace_width: width,
            public_input_count: desc.public_input_count,
            tables: vec![],
            constraints,
            hash_sites: vec![],
            ranges: vec![],
        },
        chains,
    })
}

/// Prove a `CellProgram` transition as a RECURSION-FOLDABLE IR-v2 leaf.
///
/// `witness_values` / `num_rows` are the `CellProgram` trace witness (the same the
/// off-AIR `prove_custom_program` consumes); `public_inputs` are the sub-proof's
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
/// The host commitment is `WideHash::to_felts()[0..4]`, which is the state rate (lanes 0..4)
/// AFTER the last ABSORB permutation — strictly BEFORE the squeeze permute. So only the absorb
/// phase is reconstructed here; the 4 returned targets are exactly the host's first 4 felts.
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
/// The host has NO padding block, NO length re-absorb, and NO squeeze permute, so neither
/// exists here; the total input length is bound once, in the initial lane-5 constant.
fn incircuit_custom_pi_commitment(
    cb: &mut CircuitBuilder<RecursionChallenge>,
    pi_targets: &[Target],
) -> Result<[Target; 4], String> {
    let config = Poseidon2Config::BABY_BEAR_D4_W16;
    let zero = embed_base_const(cb, 0);

    // Host: `for chunk in inputs.chunks(4) { state[i] += chunk[i]; permute() }`. Empty input ⇒ no
    // permute ⇒ commitment is the untouched zero rate.
    if pi_targets.is_empty() {
        return Ok([zero, zero, zero, zero]);
    }

    // Pack one four-PI chunk into a single ext limb: coefficients = the chunk, zero-padded (the
    // host's partial final chunk adds nothing into the absent lanes — adding the zero pad is the
    // same value). The PI targets are bus-present (created by the verified inner proof), so
    // recomposing them is bus-balanced; the constant pads/domain/len must NOT go through recompose
    // (a const consumed as an ALU operand has no bus creator — the WitnessChecks mismatch this
    // avoids), so limb 1 and the capacity tail are built as DIRECT ext constants (the same way the
    // segment sponge feeds its tag).
    let pack =
        |cb: &mut CircuitBuilder<RecursionChallenge>, chunk: &[Target]| -> Result<Target, String> {
            let lanes: Vec<Target> = (0..4)
                .map(|lane| chunk.get(lane).copied().unwrap_or(zero))
                .collect();
            cb.recompose_base_coeffs_to_ext_via_alu::<P3BabyBear>(&lanes)
                .map_err(|e| format!("recompose rate limb failed: {e:?}"))
        };

    let mut chunks = pi_targets.chunks(4);
    let first_chunk = chunks.next().expect("pi_targets is non-empty");

    // limb 0 = base lanes 0..4 = the first absorbed chunk (added into the host's untouched zero rate).
    let limb0 = pack(cb, first_chunk)?;
    // limb 1 = base lanes 4..8 = [domain, total_input_len, 0, 0] — a single compile-time ext
    // constant, the INITIAL rate state only (the host writes lanes 4,5 once, before any permute).
    let dom = custom_pi_domain_seed();
    let len = pi_targets.len() as u32;
    let limb1 = cb.define_const(ext_from_base_coeffs([dom, len, 0, 0]));
    // limbs 2,3 = base lanes 8..16 = the host's zero capacity tail.
    let zero_limb = cb.define_const(RecursionChallenge::ZERO);

    // The BUS-BALANCED sponge primitive (the same one the segment digest uses): rate_in = the two
    // rate ext-limbs (base lanes 0..8), capacity_seed = the two capacity ext-limbs (base lanes
    // 8..16). On `new_start` these are exactly the 16-lane pre-permutation state of the host
    // `WideHash::from_poseidon2`, and the perm is the SAME width-16 BabyBear permutation.
    let mut rate = cb
        .add_poseidon2_perm_sponge_step(config, true, &[limb0, limb1], &[zero_limb, zero_limb])
        .map_err(|e| format!("width-16 sponge step failed: {e:?}"))?;

    // Remaining chunks: the host adds each chunk into lanes 0..4 of the PERMUTED state and
    // permutes again, never re-touching lanes 4..8 (they carry the previous permutation output
    // forward). So: add the packed chunk into returned rate limb 0, pass returned rate limb 1
    // through unchanged, and chain the capacity off-bus (`new_start = false` — the capacity seed
    // argument is ignored on chained steps).
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

    // Commitment = base lanes 0..4 = the 4 coefficients of the first output rate limb AFTER the
    // last absorb permutation (strictly before the host's squeeze permute).
    // Route the decompose's per-coefficient base values onto the `WitnessChecks` bus via the
    // `recompose/coeff` table (enabled by the coeff-forced backend), so `expose_claim`'s per-coeff
    // RECEIVE has a matching creator — without this the four exposed consecutive base lanes have no
    // bus provenance and the global lookup is imbalanced (one unmatched RECEIVE).
    cb.set_recompose_coeff_ctl_for_decompose_links(true);
    let coeffs = cb
        .decompose_ext_to_base_coeffs::<P3BabyBear>(rate[0])
        .map_err(|e| format!("decompose output rate limb failed: {e:?}"))?;
    Ok([coeffs[0], coeffs[1], coeffs[2], coeffs[3]])
}

/// Prove a `CellProgram` transition as a recursion-foldable leaf (as [`prove_custom_leaf`]) AND
/// expose the custom sub-proof's PI-commitment as an IN-CIRCUIT-computed public CLAIM.
///
/// The returned [`RecursionOutput`] carries one `expose_claim` table whose 4 public values are
/// the in-circuit [`incircuit_custom_pi_commitment`] over the leaf's BOUND descriptor PIs — equal,
/// byte-for-byte, to the deployed [`custom_proof_pi_commitment`] the off-AIR engine writes into
/// the Custom row's `custom_proof_commitment` column. Because the absorb reads the leaf's REAL
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
    // Compute the in-circuit PI-commitment over them and expose the 4 felts as a public claim.
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

/// Read the 4-felt commitment a [`prove_custom_leaf_with_commitment`] leaf exposes through its
/// `expose_claim` table. Returns `None` if the proof carries no exposed claim.
pub fn read_exposed_pi_commitment(
    output: &RecursionOutput<DreggRecursionConfig>,
) -> Option<ProofBindCommitment> {
    let claims: Vec<BabyBear> = output
        .0
        .non_primitives
        .iter()
        .find(|e| e.op_type.as_str() == "expose_claim")?
        .public_values
        .iter()
        .map(|&v| BabyBear::new(v.as_canonical_u32()))
        .collect();
    if claims.len() < 4 {
        return None;
    }
    Some([claims[0], claims[1], claims[2], claims[3]])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::custom_proof_bind::custom_proof_pi_commitment;
    use crate::ivc_turn_chain::ir2_leaf_wrap_config;
    use dregg_circuit::dsl::circuit::{
        CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, PolyTerm,
    };

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

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_custom_leaf(&program, &w, rows, &pis, &config)
        }));
        match result {
            // The debug constraint builder panicked on the unsatisfied gate — rejected.
            Err(_) => {}
            // Or the inner self-verify returned an error — rejected.
            Ok(Err(_)) => {}
            Ok(Ok(_)) => panic!("a FORGED custom witness minted a foldable leaf — soundness OPEN"),
        }
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

        let exposed = read_exposed_pi_commitment(&output)
            .expect("the leaf exposes a 4-felt PI-commitment claim");
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

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_custom_leaf(&program, &w, 4, &pis, &config)
        }));
        match result {
            Err(_) => {}     // a debug constraint/chip builder panicked — rejected
            Ok(Err(_)) => {} // the inner self-verify returned an error — rejected
            Ok(Ok(_)) => panic!("a FORGED Merkle path minted a foldable leaf — soundness OPEN"),
        }
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

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            // honest_pis claims the honest root; `w` climbs to other root ⇒ pin fails.
            prove_custom_leaf(&program, &w, 4, &honest_pis, &config)
        }));
        match result {
            Err(_) => {}
            Ok(Err(_)) => {}
            Ok(Ok(_)) => panic!("a root-pin mismatch minted a foldable leaf — soundness OPEN"),
        }
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

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_custom_leaf(&program, &w, rows, &pis, &config)
        }));
        match result {
            Err(_) => {}
            Ok(Err(_)) => {}
            Ok(Ok(_)) => {
                panic!("a forged running-hash chain minted a foldable leaf — soundness OPEN")
            }
        }
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

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_custom_leaf(&program, &w, rows, &pis, &config)
        }));
        match result {
            Err(_) => {}
            Ok(Err(_)) => {}
            Ok(Ok(_)) => panic!("a forbidden table edge minted a foldable leaf — soundness OPEN"),
        }
    }

    // ========================================================================
    // The MULTI-CHUNK in-circuit PI commitment (upstream blocker #1: chain all
    // 32 custom-leaf public inputs).
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
            .expect("the 32-PI leaf exposes a 4-felt commitment claim");
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

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_custom_leaf_with_commitment(&program, &w, rows, &pis, &config)
        }));
        match result {
            Err(_) => {}     // debug constraint builder panicked — rejected
            Ok(Err(_)) => {} // inner self-verify errored — rejected
            Ok(Ok(_)) => {
                panic!("a mutated PI with a stale witness minted a leaf — soundness OPEN")
            }
        }
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

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_custom_leaf_with_commitment(&program, &w, rows, &short, &config)
        }));
        match result {
            Err(_) => {}
            Ok(Err(_)) => {}
            Ok(Ok(_)) => {
                panic!("a declared-length mismatch minted a leaf — the length is not bound")
            }
        }
    }
}
