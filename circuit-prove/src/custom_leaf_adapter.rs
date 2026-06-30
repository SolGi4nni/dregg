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
//! ## Constraint kinds this spike does NOT map (precise blockers, not fakes)
//!
//! * `Hash` / `Hash2to1` / `Hash4to1` / `Hash3Cap` / `MerkleHash` /
//!   `ChainedHash2to1` / `SeedHash2to1` — each is a Poseidon2 relation. In the
//!   existing `DslCircuit` STARK these are OPAQUE (degree-1, the `dsl_plonky3`
//!   lowering emits ZERO — they are not soundly enforced there either). The
//!   faithful IR-v2 realization routes the permutation through a `Lookup` into the
//!   declared Poseidon2 CHIP table (`TID_P2`), which requires witnessing all eight
//!   permutation lanes per site in the trace. That is real trace-assembly work and
//!   is the named follow-up; this adapter REFUSES these kinds rather than emit an
//!   unconstrained gate.
//! * `Lookup { table_id, .. }` — a `CellProgram` lookup names an arbitrary
//!   entry-set `LookupTable`. The IR-v2 `Lookup` targets DECLARED tables with FIXED
//!   semantics (range / chip / submask), not arbitrary entry sets, so there is no
//!   faithful target. Mapping it needs an IR-v2 "custom-contents" table family
//!   (the named small IR follow-up).
//! * `TableFunction` — a fixed bivariate Lagrange polynomial. It IS pure-local and
//!   gate-expressible IN PRINCIPLE (a large `Σ Lᵢ(a)Lⱼ(b)·outᵢⱼ` `LeanExpr`), but
//!   the symbolic lowering is non-trivial and unexercised by the custom corpus, so
//!   it is out of this spike's scope and refused.
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
//! `Poseidon2State` runs) driven as the host's ADDITIVE rate-4 sponge — the absorbed chunk in
//! ext limb 0 (base lanes 0..4), the BLAKE3 domain seed + input length in limb 1 (lanes 4,5), the
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
//! ## The connect-into-the-fold step — DONE
//!
//! The exposed claim is now wired to the effect-vm leg's published `custom_proof_commitment` (IR2
//! PI slots 46..49) by [`crate::joint_turn_recursive::prove_custom_binding_node`]: it folds this
//! leaf against the effect-vm leg leaf (re-exposed via
//! [`crate::ivc_turn_chain::prove_descriptor_leaf_with_pi_slice_expose`] — the inner descriptor PIs
//! land in the primitive `Public` table and never reach a combine hook, so the leg must re-expose
//! 46..49 through `expose_claim`) and `connect`s the two 4-felt claims in-circuit. A turn whose leg
//! claims a commitment no verifying sub-proof backs is UNSAT (the `connect` is a conflict — no
//! satisfying partner), so a PURE LIGHT CLIENT folding the tree now witnesses the binding
//! `StarkSoundCustom` falsely assumed (the `forged_custom_commitment_is_rejected_by_the_fold`
//! tooth).

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, Ir2Air, MemBoundaryWitness, UMemBoundaryWitness, VmConstraint2,
    WindowExpr, WindowGateSpec, ir2_airs_and_common_for_config, prove_vm_descriptor2_for_config,
};
use dregg_circuit::dsl::circuit::{CellProgram, ConstraintExpr};
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
        ConstraintExpr::MerkleHash { .. } => "MerkleHash",
        ConstraintExpr::Lookup { .. } => "Lookup",
        ConstraintExpr::ChainedHash2to1 { .. } => "ChainedHash2to1",
        ConstraintExpr::SeedHash2to1 { .. } => "SeedHash2to1",
        ConstraintExpr::TableFunction { .. } => "TableFunction",
    }
}

/// Adapt a `CellProgram`'s [`CircuitDescriptor`] into the IR-v2
/// [`EffectVmDescriptor2`] so it can prove through the general prover.
///
/// Each `ConstraintExpr` maps per the module-level table. Hash/lookup/table-function
/// kinds are REFUSED with a precise blocker (see the module docs) rather than
/// silently emitted as unconstrained gates. The descriptor declares NO tables: the
/// mapped corpus is pure main-table algebra (a hash/lookup kind that would need the
/// chip/range tables is exactly what is refused above).
pub fn cellprogram_to_descriptor2(program: &CellProgram) -> Result<EffectVmDescriptor2, String> {
    let desc = &program.descriptor;
    let mut constraints: Vec<VmConstraint2> = Vec::with_capacity(desc.constraints.len());

    for expr in &desc.constraints {
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
            // The hash / lookup / table-function kinds have no faithful IR-v2 carrier
            // in this spike — refuse with a precise blocker.
            ConstraintExpr::Hash { .. }
            | ConstraintExpr::Hash2to1 { .. }
            | ConstraintExpr::Hash4to1 { .. }
            | ConstraintExpr::Hash3Cap { .. }
            | ConstraintExpr::MerkleHash { .. }
            | ConstraintExpr::ChainedHash2to1 { .. }
            | ConstraintExpr::SeedHash2to1 { .. } => {
                return Err(format!(
                    "constraint kind {} is a Poseidon2 relation; the faithful IR-v2 \
                     route is a chip-table lookup (TID_P2) requiring per-site lane \
                     witnessing — the named follow-up, not mapped in this spike",
                    kind_name(expr)
                ));
            }
            ConstraintExpr::Lookup { table_id, .. } => {
                return Err(format!(
                    "constraint kind Lookup(table \"{table_id}\") names an arbitrary \
                     CellProgram entry-set; IR-v2 lookups target fixed-semantics \
                     declared tables only — no faithful target in this spike"
                ));
            }
            ConstraintExpr::TableFunction { .. } => {
                return Err(
                    "constraint kind TableFunction (bivariate Lagrange) is local-gate \
                     expressible in principle but its symbolic lowering is out of this \
                     spike's scope"
                        .to_string(),
                );
            }
            // Everything else is a pure-local algebraic gate.
            local => VmConstraint2::Base(VmConstraint::Gate(gate_body(local)?)),
        };
        constraints.push(c2);
    }

    Ok(EffectVmDescriptor2 {
        name: format!("custom-leaf::{}", desc.name),
        trace_width: desc.trace_width,
        public_input_count: desc.public_input_count,
        tables: vec![],
        constraints,
        hash_sites: vec![],
        ranges: vec![],
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
    let desc2 = cellprogram_to_descriptor2(program)?;

    // The CellProgram main rows (width == trace_width). The IR-v2 prover grows/fills
    // chip lanes itself; for a table-free descriptor that is a no-op.
    let base_trace = program
        .generate_trace(witness_values, num_rows)
        .map_err(|e| format!("custom-leaf trace generation failed: {e}"))?;

    // Mint the inner IR-v2 batch under the recursion config TYPE (the SIDESTEP), so
    // the leaf-wrap's in-circuit verifier consumes it directly.
    let inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
        &desc2,
        &base_trace,
        public_inputs,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        config,
    )
    .map_err(|e| format!("custom-leaf inner IR-v2 prove failed: {e}"))?;

    // Wrap the inner batch as a recursion leaf, binding the descriptor PIs in-circuit.
    prove_descriptor_leaf_rotated_with_config(&desc2, &inner, public_inputs, config)
        .map_err(|e| format!("custom-leaf recursion wrap failed: {e}"))
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
/// permutation. The `> 4`-PI multi-chunk additive sponge is the named residual (it would chain
/// permutations through the shared challenger op).
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
    if pi_targets.len() > 4 {
        return Err(format!(
            "in-circuit custom-PI commitment supports <=4 PIs in this spike (got {}); the \
             multi-chunk additive sponge over the shared challenger op is the named residual",
            pi_targets.len()
        ));
    }

    // limb 0 = base lanes 0..4 = the absorbed chunk (absent lanes 0, the host's untouched rate).
    // The PI targets are bus-present (created by the verified inner proof), so recomposing them is
    // bus-balanced; the constant pads/domain/len must NOT go through recompose (a const consumed as
    // an ALU operand has no bus creator — the WitnessChecks mismatch this avoids), so limb 1 and the
    // capacity tail are built as DIRECT ext constants (the same way the segment sponge feeds its tag).
    let rate0: Vec<Target> = (0..4)
        .map(|lane| pi_targets.get(lane).copied().unwrap_or(zero))
        .collect();
    let limb0 = cb
        .recompose_base_coeffs_to_ext_via_alu::<P3BabyBear>(&rate0)
        .map_err(|e| format!("recompose rate limb failed: {e:?}"))?;
    // limb 1 = base lanes 4..8 = [domain, len, 0, 0] — a single compile-time ext constant.
    let dom = custom_pi_domain_seed();
    let len = pi_targets.len() as u32;
    let limb1 = cb.define_const(ext_from_base_coeffs([dom, len, 0, 0]));
    // limbs 2,3 = base lanes 8..16 = the host's zero capacity tail.
    let zero_limb = cb.define_const(RecursionChallenge::ZERO);

    // The BUS-BALANCED sponge primitive (the same one the segment digest uses): rate_in = the two
    // rate ext-limbs (base lanes 0..8), capacity_seed = the two capacity ext-limbs (base lanes
    // 8..16). On `new_start` these are exactly the 16-lane pre-permutation state of the host
    // `WideHash::from_poseidon2`, and the perm is the SAME width-16 BabyBear permutation.
    let out = cb
        .add_poseidon2_perm_sponge_step(config, true, &[limb0, limb1], &[zero_limb, zero_limb])
        .map_err(|e| format!("width-16 sponge step failed: {e:?}"))?;

    // Commitment = base lanes 0..4 = the 4 coefficients of the first output rate limb.
    // Route the decompose's per-coefficient base values onto the `WitnessChecks` bus via the
    // `recompose/coeff` table (enabled by the coeff-forced backend), so `expose_claim`'s per-coeff
    // RECEIVE has a matching creator — without this the four exposed consecutive base lanes have no
    // bus provenance and the global lookup is imbalanced (one unmatched RECEIVE).
    cb.set_recompose_coeff_ctl_for_decompose_links(true);
    let coeffs = cb
        .decompose_ext_to_base_coeffs::<P3BabyBear>(out[0])
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
    let desc2 = cellprogram_to_descriptor2(program)?;

    let base_trace = program
        .generate_trace(witness_values, num_rows)
        .map_err(|e| format!("custom-leaf trace generation failed: {e}"))?;

    let inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
        &desc2,
        &base_trace,
        public_inputs,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        config,
    )
    .map_err(|e| format!("custom-leaf inner IR-v2 prove failed: {e}"))?;

    let (airs, table_public_inputs, common) =
        ir2_airs_and_common_for_config(&desc2, &inner, public_inputs, config)
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
    use crate::custom_proof_bind::{custom_proof_pi_commitment, prove_custom_program};
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
        let _output = prove_custom_leaf(&program, &w, rows, &pis, &config)
            .expect("the honest custom program must prove as a foldable leaf");

        // The claim the per-turn fold binds = custom_proof_pi_commitment(pis). It MUST
        // equal the off-AIR engine's column value for the SAME sub-proof: both engines
        // bind the identical PI-commitment, so the foldable leaf and the deployed
        // `proof_bind` column agree on what was proven.
        let bound = prove_custom_program(&program, &w, rows, &pis)
            .expect("off-AIR engine mints the same sub-proof");
        assert_eq!(
            bound.proof_commitment(),
            custom_proof_pi_commitment(&pis),
            "the off-AIR engine's commitment column == the leaf's bound PI-commitment"
        );
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
}
