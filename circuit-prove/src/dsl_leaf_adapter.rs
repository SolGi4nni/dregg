//! Re-prove a `Witnessed { Dfa }` predicate's `CellProgram` transition as a
//! RECURSION-FOLDABLE IR-v2 leaf — the DSL/Dfa twin of [`crate::custom_leaf_adapter`].
//!
//! ## What this closes (the RE-EXEC-ONLY gap)
//!
//! A `Dfa` caveat (the relay-routing predicate `dregg-dfa-routing-v1`, and any deployed
//! `CellProgram` predicate) is verified OFF-AIR by
//! `turn::executor::membership_verifier::DslCircuitDfaVerifier::verify`, which resolves the
//! program by its `vk_hash` and calls
//! [`dregg_circuit::dsl::circuit::CellProgram::verify_transition`] (the bespoke off-AIR
//! `CellProgram` transition gate). That gate runs in
//! the executor's witnessed-predicate registry, NOT inside the deployed effect-vm AIR. So a
//! re-executing validator witnesses the predicate, but a PURE LIGHT CLIENT (one that folds only the
//! per-turn recursion tree) never does: a validator with vs without `DslCircuitDfaVerifier`
//! registered produces the SAME `AttestedHistory` for a `Dfa`-gated turn. The Lean refutation is
//! `Dregg2.Circuit.DslBackingAttack` (`deployed_admits_unwitnessed`).
//!
//! The Dfa predicate is even MORE invisible to a light client than the custom carrier: a custom
//! effect at least has an in-AIR `proofBind` op (whose deployed denotation is the vacuous `True`),
//! whereas the Dfa predicate is a precondition CAVEAT with NO op on the deployed turn at all.
//!
//! ## The fix is REUSE — a DSL/Dfa transition IS a `CellProgram` STARK
//!
//! The carrier is, byte for byte, the SAME object the custom carrier re-proves: a `CellProgram`
//! transition proven and verified by the bespoke off-AIR `CellProgram` transition gate.
//! So the leaf machinery is DIRECT REUSE of [`crate::custom_leaf_adapter`]:
//!
//! * [`crate::custom_leaf_adapter::cellprogram_to_descriptor2`] adapts the program's
//!   [`dregg_circuit::dsl::circuit::CircuitDescriptor`] into the IR-v2 grammar, and
//! * [`crate::custom_leaf_adapter::prove_custom_leaf_with_commitment`] proves it as a foldable leaf
//!   that EXPOSES its PI-commitment in-circuit (the faithful in-AIR reconstruction of
//!   [`crate::custom_proof_bind::custom_proof_pi_commitment`] — the value a DSL `DfaProofWire`'s
//!   public inputs commit to). The exposed claim is the SAME 4-felt commitment shape a custom leaf
//!   exposes, so the binding node REUSES too (see [`prove_dsl_binding_node_segmented`]).
//!
//! [`prove_dsl_leaf_with_commitment`] is the thin DSL-named entrypoint; it simply routes the DSL/Dfa
//! `CellProgram` through that machinery. A light client folding the resulting leaf now witnesses the
//! DSL predicate transition the off-AIR `DslCircuitDfaVerifier` used to be the sole enforcer of.
//!
//! ## THE REAL GAP — which DSL programs reuse, and which hit the named carrier blockers
//!
//! [`cellprogram_to_descriptor2`] maps the PURE-ALGEBRAIC `ConstraintExpr` kinds
//! (`Equality`/`Multiplication`/`Binary`/`Polynomial`/`Gated`/`InvertedGated`/`Squared`/
//! `ConditionalNonzero`/`AtLeastOne`/`Transition`/`PiBinding`) faithfully, the Poseidon2-relation
//! kinds (`Hash2to1`/`Hash4to1`/`Hash3Cap`/`MerkleHash`) via the `TID_P2` lane-witnessing weld, the
//! cross-row running hash (`ChainedHash2to1` + its `SeedHash2to1` seed) via a copy-forward accumulator
//! column, and `TableFunction` via its bivariate-Lagrange gate. It still REFUSES the arity-7 fact-sponge
//! `Hash`, an arbitrary-entry `Lookup`, an UNSEEDED chain, and `BoundaryRow::Index` (the named residuals).
//!
//! Consequence, stated honestly:
//!
//! * An **algebraic DSL/Dfa transition** (a state-advance / continuity predicate over arithmetic
//!   columns, e.g. [`tests::dfa_advance_program`]) REUSES the custom leaf machinery DIRECTLY — it
//!   folds and exposes a bound PI-commitment with ZERO new mechanism.
//! * The **production `dregg-dfa-routing-v1`** descriptor now ALSO fully reuses: its `Hash4to1`
//!   (entry-hash C1), `ChainedHash2to1` (running-hash C3) + `SeedHash2to1` (the table-commitment
//!   seed), and `TableFunction` (the GAP-A transition table) all lower to the foldable IR-2 leaf
//!   (`TID_P2` chip lookups + the copy-forward accumulator + the Lagrange gate). A light client
//!   folding the leaf witnesses the routing predicate's hash chain + transition table in-AIR.
//!   [`dsl_leaf_unmapped_kinds`] reports a program's gap precisely (now empty for the router);
//!   [`tests::routing_descriptor_fully_maps`] pins the full lowering on the real descriptor, and the
//!   honest-folds / forged-UNSAT teeth live in `custom_leaf_adapter`'s `*_dfa_routing_*` tests.
//!
//! ## The rc-EMIT LANDED — the deployed-descriptor PI exposure for the Dfa leg (LIVE)
//!
//! The fold-bind needs a DEPLOYED leg leaf that RE-EXPOSES the Dfa predicate's published commitment at
//! a known PI slot range, so [`prove_dsl_binding_node_segmented`] can `connect` it to this sub-proof
//! leaf's genuine in-circuit commitment (exactly as the custom path connects the effect-vm leg's PI
//! slots 46..53 — the 8-felt `customPiExposure` / `customVmDescriptor2R24`). The Dfa predicate is a PRECONDITION
//! CAVEAT, not an effect — and the named big-bang emit LANDED: every deployed cohort member is wrapped
//! through Lean `withDfaRcPins`, publishing the caveat-region 4-felt DFA route-commitment carrier
//! (`trace_rotated::C_DFA_RC_OFF`, filled from `RotatedCaveatManifest::dfa_rc` =
//! `dfa_route_commitment(DfaProofWire.public_inputs)` on a Dfa-gated turn, the ZERO sentinel
//! otherwise) as member PIs — transfer at 46..49; post-exposure members vary, so the fold arm DERIVES
//! the slots from the committed descriptor (`crate::ivc_turn_chain::dsl_rc_claim_pi_lo`).
//!
//! THE DEPLOYED WIRE IS LIVE: `prove_chain_core_rotated`'s `CarrierWitness::Dsl` arm mints the
//! DUAL-EXPOSE Dfa leg leaf ([`crate::ivc_turn_chain::prove_descriptor_leaf_dual_expose_at`] at the
//! derived rc slots), re-proves the predicate through [`prove_dsl_leaf_with_commitment`], and folds
//! both under [`prove_dsl_binding_node_segmented`] — refusing pin-less descriptors AND the zero rc
//! sentinel (fail-closed both poles). The deployed-path tooth is
//! `tests/dsl_binding_deployed_tooth.rs`; the Lean flip is `Dregg2.Circuit.DslBindingFromFold`.

use std::collections::HashMap;

use dregg_circuit::dsl::circuit::CellProgram;
use dregg_circuit::field::BabyBear;
use p3_recursion::RecursionOutput;

use crate::custom_leaf_adapter::{cellprogram_to_descriptor2, prove_custom_leaf_with_commitment};
use crate::joint_turn_aggregation::JointAggError;
use crate::joint_turn_recursive::prove_claim_binding_node_segmented;
use crate::plonky3_recursion_impl::recursive::DreggRecursionConfig;

/// Prove a `Witnessed { Dfa }` predicate's `CellProgram` transition as a recursion-foldable IR-v2
/// leaf that EXPOSES its PI-commitment in-circuit — the DSL-named entrypoint into the reused
/// [`crate::custom_leaf_adapter::prove_custom_leaf_with_commitment`].
///
/// `program` is the deployed DSL program (resolved by its `vk_hash` in the production
/// `DslCircuitDfaVerifier`); `witness_values` / `num_rows` are its transition witness (the same the
/// off-AIR `CellProgram::prove_transition` consumes); `public_inputs` are the `DfaProofWire` public
/// inputs (e.g. `[initial_state, final_state, table_commitment, route_commitment]`), carried as the
/// leaf's descriptor PIs (bound in-circuit) and committed by
/// [`crate::custom_proof_bind::custom_proof_pi_commitment`].
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`]. The returned
/// [`RecursionOutput`]'s `expose_claim` is the 8-felt PI-commitment (the shared exposure widened
/// by the proof-bind flag day) — IDENTICAL in shape to a custom sub-proof leaf's — and
/// [`prove_dsl_binding_node_segmented`] binds its FIRST 4 lanes (the first squeeze block ==
/// the deployed 4-felt `dfa_rc` carrier) like any custom leaf.
///
/// Returns `Err` for a DSL program whose descriptor uses a constraint kind
/// [`cellprogram_to_descriptor2`] refuses (the Poseidon2 / `TableFunction` / `Lookup` carriers —
/// e.g. the production `dregg-dfa-routing-v1`; use [`dsl_leaf_unmapped_kinds`] to see which).
pub fn prove_dsl_leaf_with_commitment(
    program: &CellProgram,
    witness_values: &HashMap<String, Vec<BabyBear>>,
    num_rows: usize,
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    // A `Witnessed { Dfa }` predicate program is a `CellProgram`, structurally identical to a
    // custom-effect sub-proof (both are bespoke `CellProgram` STARKs over a `CircuitDescriptor`).
    // Route it through the SAME leaf machinery so the DSL predicate transition gains an in-circuit
    // PI-commitment a pure light client witnesses.
    prove_custom_leaf_with_commitment(program, witness_values, num_rows, public_inputs, config)
}

/// **The DSL/Dfa binding node — a REUSE of the segment-preserving binding node at the
/// DEPLOYED rc width ([`prove_claim_binding_node_segmented`] with `claim_len = DFA_RC_LEN = 4`).**
///
/// The DSL sub-proof leaf ([`prove_dsl_leaf_with_commitment`]) exposes the SAME 8-felt
/// PI-commitment a custom sub-proof leaf exposes (both call
/// [`crate::custom_leaf_adapter::prove_custom_leaf_with_commitment`]; the proof-bind flag day
/// widened that shared exposure to the full `WideHash` squeeze). The deployed Dfa leg surface is
/// UNCHANGED by that flag day: the caveat-region `dfa_rc` carrier is 4 felts (`DFA_RC_LEN`), and
/// `dfa_route_commitment` is byte-identical to the FIRST squeeze block — i.e. lanes `[0..4)` of
/// the sub-proof leaf's 8-felt exposed commitment. So this node `connect`s the leg's 4 CLAIMED
/// rc lanes (dual-expose lanes `[SEG_WIDTH .. SEG_WIDTH+4)`) to the sub-proof's commitment
/// lanes `[0..4)`, and RE-EXPOSES the segment so the node folds into `aggregate_tree` like any
/// per-turn segment leaf. A leg that claims a route-commitment no verifying DSL sub-proof backs
/// is UNSAT (the `connect` is a conflict ⇒ no root), so a pure light client never receives a
/// verifying artifact for a forged Dfa-gated turn.
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
pub fn prove_dsl_binding_node_segmented(
    dual_expose_leg_leaf: &RecursionOutput<DreggRecursionConfig>,
    dsl_subproof_leaf: &RecursionOutput<DreggRecursionConfig>,
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, JointAggError> {
    use dregg_circuit::effect_vm::trace_rotated::DFA_RC_LEN;
    prove_claim_binding_node_segmented(dual_expose_leg_leaf, dsl_subproof_leaf, config, DFA_RC_LEN)
}

/// Report the constraint kinds in `program` that [`cellprogram_to_descriptor2`] cannot map to the
/// IR-v2 grammar (the Poseidon2 / `Lookup` / `TableFunction` carriers). An EMPTY result means the
/// program is a pure-algebraic DSL transition that REUSES the custom leaf machinery directly; a
/// non-empty result is the precise (named, shared-with-custom) gap.
///
/// Returns the adapter's blocker message (which names the offending kind) on the first unmapped
/// constraint, or `Ok(())` if the whole program maps. This is the honest preflight a DSL/Dfa caller
/// runs before [`prove_dsl_leaf_with_commitment`].
pub fn dsl_leaf_unmapped_kinds(program: &CellProgram) -> Result<(), String> {
    cellprogram_to_descriptor2(program).map(|_| ())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::custom_leaf_adapter::read_exposed_pi_commitment;
    use crate::custom_proof_bind::custom_proof_pi_commitment;
    use crate::ivc_turn_chain::ir2_leaf_wrap_config;
    use dregg_circuit::dsl::circuit::{
        CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, PolyTerm,
    };

    /// A genuine ALGEBRAIC DFA transition predicate (no Poseidon2 / TableFunction), so it reuses the
    /// custom leaf machinery directly. A toy "advance" DFA: `next == state + symbol` per row (the
    /// state advances by the input symbol), with cross-row continuity `next_row.state == this.next`
    /// and a boolean symbol. This exercises the THREE mapped kinds a real DFA transition uses —
    /// `Polynomial` (the step relation), `Transition` (continuity, the WindowGate carrier), and
    /// `Binary` — proving the algebraic DSL fragment folds.
    ///
    /// Columns: 0 state, 1 symbol, 2 next. PIs: `[initial_state, final_state]` (carried + committed,
    /// the route-commitment-style binding).
    fn dfa_advance_program() -> CellProgram {
        let p_minus_1 = BabyBear::new(dregg_circuit::field::BABYBEAR_P - 1);
        let descriptor = CircuitDescriptor {
            name: "dregg-dfa-advance-algebraic-v1".to_string(),
            trace_width: 3,
            max_degree: 2,
            columns: vec![
                ColumnDef {
                    name: "state".into(),
                    index: 0,
                    kind: ColumnKind::Value,
                },
                ColumnDef {
                    name: "symbol".into(),
                    index: 1,
                    kind: ColumnKind::Binary,
                },
                ColumnDef {
                    name: "next".into(),
                    index: 2,
                    kind: ColumnKind::Value,
                },
            ],
            constraints: vec![
                // symbol is a bit.
                ConstraintExpr::Binary { col: 1 },
                // step relation: next - state - symbol == 0  (next == state + symbol).
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
                    ],
                },
                // continuity: next row's state == this row's next (the two-row WindowGate carrier).
                ConstraintExpr::Transition {
                    next_col: 0,
                    local_col: 2,
                },
            ],
            boundaries: vec![],
            public_input_count: 2,
            lookup_tables: vec![],
        };
        CellProgram::new(descriptor, 1)
    }

    /// Honest run over symbols [1,0,1,0] from state 0:
    /// state [0,1,1,2], next [1,1,2,2] — every step + continuity holds.
    fn honest_advance_witness() -> (HashMap<String, Vec<BabyBear>>, usize, Vec<BabyBear>) {
        let rows = 4;
        let mut w = HashMap::new();
        w.insert(
            "state".into(),
            vec![
                BabyBear::new(0),
                BabyBear::new(1),
                BabyBear::new(1),
                BabyBear::new(2),
            ],
        );
        w.insert(
            "symbol".into(),
            vec![
                BabyBear::new(1),
                BabyBear::new(0),
                BabyBear::new(1),
                BabyBear::new(0),
            ],
        );
        w.insert(
            "next".into(),
            vec![
                BabyBear::new(1),
                BabyBear::new(1),
                BabyBear::new(2),
                BabyBear::new(2),
            ],
        );
        // PIs: [initial_state=0, final_state=2].
        (w, rows, vec![BabyBear::new(0), BabyBear::new(2)])
    }

    /// The algebraic DFA transition maps to the IR-v2 grammar (no unmapped kinds) — the REUSE preflight.
    #[test]
    fn algebraic_dfa_transition_maps() {
        let program = dfa_advance_program();
        assert!(
            dsl_leaf_unmapped_kinds(&program).is_ok(),
            "an algebraic DFA transition (Polynomial+Transition+Binary) must map to IR-v2"
        );
    }

    /// THE TOOTH (positive pole): an honest DSL/Dfa-gated transition folds as a recursion leaf, AND
    /// the PI-commitment the per-turn fold would bind equals the off-AIR engine's
    /// `custom_proof_commitment` value for the SAME sub-proof — so the DSL leaf and the deployed
    /// `verify_transition` agree on what was proven. A pure light client folding this leaf witnesses
    /// the predicate.
    #[test]
    fn honest_dsl_transition_folds_and_binds() {
        let program = dfa_advance_program();
        let (w, rows, pis) = honest_advance_witness();
        let config = ir2_leaf_wrap_config();

        let output = prove_dsl_leaf_with_commitment(&program, &w, rows, &pis, &config)
            .expect("the honest algebraic DSL/Dfa transition must fold as a leaf");

        // The leaf's IN-CIRCUIT-exposed commitment is byte-identical to the host derivation over
        // the DSL public inputs. (The former off-AIR `prove_custom_program` cross-check died with
        // the hand STARK engine (stark-kill); `custom_proof_pi_commitment` IS the deployed
        // commitment derivation the effect-VM Custom row binds.)
        let exposed = read_exposed_pi_commitment(&output)
            .expect("the DSL leaf exposes the full 8-felt PI-commitment claim");
        let host = custom_proof_pi_commitment(&pis);
        assert_eq!(
            exposed, host,
            "the DSL leaf's in-circuit commitment byte-matches the host"
        );
    }

    /// THE TOOTH (negative pole): a FORGED transition that VIOLATES the DSL predicate (the step
    /// relation `next == state + symbol` broken) has no satisfying assembly — the leaf does NOT fold.
    /// The inner prover's self-verify rejects it (or the debug constraint builder panics); either way
    /// a turn failing the predicate cannot mint a foldable leaf, so the aggregate that would fold it is
    /// UNSAT and a light client never accepts it.
    #[test]
    fn forged_dsl_transition_does_not_fold() {
        let program = dfa_advance_program();
        let rows = 4;
        let mut w: HashMap<String, Vec<BabyBear>> = HashMap::new();
        w.insert(
            "state".into(),
            vec![
                BabyBear::new(0),
                BabyBear::new(1),
                BabyBear::new(1),
                BabyBear::new(2),
            ],
        );
        w.insert(
            "symbol".into(),
            vec![
                BabyBear::new(1),
                BabyBear::new(0),
                BabyBear::new(1),
                BabyBear::new(0),
            ],
        );
        // FORGED: next[2] should be 2 (= state 1 + symbol 1); claim 3. The step Polynomial is non-zero.
        w.insert(
            "next".into(),
            vec![
                BabyBear::new(1),
                BabyBear::new(1),
                BabyBear::new(3),
                BabyBear::new(2),
            ],
        );
        let pis: Vec<BabyBear> = vec![BabyBear::new(0), BabyBear::new(2)];
        let config = ir2_leaf_wrap_config();

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_dsl_leaf_with_commitment(&program, &w, rows, &pis, &config)
        }));
        match result {
            Err(_) => {}     // debug constraint builder panicked on the unsatisfied step gate
            Ok(Err(_)) => {} // or the inner self-verify returned an error
            Ok(Ok(_)) => panic!("a FORGED DSL transition minted a foldable leaf — soundness OPEN"),
        }
    }

    /// THE PRODUCTION DESCRIPTOR FULLY MAPS: `dregg-dfa-routing-v1` uses `Hash4to1` (entry-hash,
    /// lane-witnessed), `ChainedHash2to1` + `SeedHash2to1` (the running-hash chain, lowered via a
    /// copy-forward accumulator column), and `TableFunction` (the bivariate-Lagrange transition
    /// table) — ALL now mapped by `cellprogram_to_descriptor2`. So the production routing program
    /// REUSES the leaf machinery with no unmapped kinds: a pure light client folding the leaf
    /// witnesses the routing predicate's hash relations + transition table in-AIR.
    #[test]
    fn routing_descriptor_fully_maps() {
        // The exact 4-state router transition table (dfa_circuit.rs / dfa_routing.rs tests).
        let table = [[1u32, 2, 1, 3], [1, 2, 1, 3], [1, 2, 3, 3], [3, 3, 3, 3]];
        let mut transitions = Vec::new();
        for (state, row) in table.iter().enumerate() {
            for (symbol, &next) in row.iter().enumerate() {
                transitions.push((state as u32, symbol as u32, next));
            }
        }
        let descriptor = dregg_circuit::dsl::dfa_routing::dfa_routing_descriptor(
            "dregg-dfa-routing-v1",
            &transitions,
        );
        let program = CellProgram::new(descriptor, 1);

        assert!(
            dsl_leaf_unmapped_kinds(&program).is_ok(),
            "dregg-dfa-routing-v1 now fully lowers (Hash4to1 + running-hash chain + TableFunction)"
        );
    }
}
