//! Re-prove the bridge's full-fidelity action AIR as a RECURSION-FOLDABLE IR-v2
//! leaf (G1, sibling to the custom-leaf adapter's Fork X).
//!
//! ## What this closes
//!
//! Today a bridge mint's foreign note-spend binding is a bespoke
//! [`dregg_circuit::bridge_action_air::BridgeActionAir`] STARK, verified OFF-AIR
//! by [`turn::executor::apply::apply_bridge_mint`] (it calls
//! `verify_bridge_action` and compares the typed limbs). A re-executing validator
//! runs that off-AIR verify, but a PURE LIGHT CLIENT (one that only folds the
//! per-turn recursion tree) never witnesses the 26-slot full-fidelity binding —
//! it sees only the substrate `BridgeMint` row's compressed `value_lo`. The bridge
//! action binding is one of the legs whose soundness a light client cannot
//! currently see.
//!
//! This module adapts the `BridgeActionAir`'s boundary + transition constraints
//! into an [`EffectVmDescriptor2`] (the EPOCH multi-table grammar), proves it
//! through the GENERAL IR-v2 prover ([`prove_vm_descriptor2_for_config`]), and
//! wraps the result as a recursion leaf via the existing
//! [`prove_descriptor_leaf_rotated_with_config`] machinery. The output is the same
//! [`RecursionOutput<DreggRecursionConfig>`] every other descriptor leaf produces,
//! so the bridge-action sub-proof now folds into the SAME `aggregate_tree` / chain
//! a light client verifies, carrying the bound
//! `(nullifier, recipient, dest_federation, amount)` tuple as its descriptor PIs.
//!
//! ## The constraint mapping (`BridgeActionAir` → `VmConstraint2`)
//!
//! The standalone AIR (`circuit/src/bridge_action_air.rs`) has exactly two
//! constraint families, both of which have an EXACT, faithful IR-v2 carrier — no
//! narrowing, no refusal:
//!
//! | `BridgeActionAir` constraint                              | maps to                                                  |
//! |----------------------------------------------------------|----------------------------------------------------------|
//! | boundary: `row0[col c] == pi[c]` (all 26 slots)          | `Base(PiBinding{ row: First, col: c, pi_index: c })`    |
//! | transition: `next[c] − local[c] == 0` (every column)    | `WindowGate{ body: Nxt(c) − Loc(c), on_transition }`    |
//!
//! * **Boundary → `PiBinding{First}` is EXACT here.** Unlike the custom adapter
//!   (where a `CellProgram` `PiBinding` is an every-row gate that narrows to
//!   first-row), the `BridgeActionAir`'s boundary constraints pin row 0 ONLY (they
//!   are emitted by `boundary_constraints` at `row: 0`). `VmConstraint::PiBinding`
//!   with `row: VmRow::First` is the term-for-term carrier — `local[col] ==
//!   public_values[pi_index]` guarded by `when_first_row`. The 26-slot PI layout
//!   (8-limb nullifier / 8-limb recipient / 8-limb dest_federation / 2-limb amount)
//!   is preserved identically: `pi_index == col` for every slot, matching the AIR's
//!   `col`/`pi` modules which agree by construction.
//! * **Transition → `WindowGate` is EXACT.** The AIR's `eval_constraints` asserts
//!   every column is constant across rows (`next[c] − local[c] == 0`, RLC-folded
//!   over `alpha`). Each per-column difference lowers to one `WindowGate` whose
//!   body `Nxt(c) + (−1)·Loc(c)` must vanish on the transition domain (rows
//!   `0..n−2`) — the same domain the AIR's `eval_constraints` fires on. This is the
//!   "1 typed row replicated for FRI power-of-2 padding" continuity glue, so a
//!   prover cannot put bound values in row 0 and different values in a padding row.
//!
//! Both carriers are `main`-table algebra; the descriptor declares NO tables
//! (no hash sites, no ranges, no lookups). The mapping is therefore TOTAL over the
//! bridge AIR — there is no kind to refuse, and `bridge_action_to_descriptor2`
//! always returns `Ok`. (The `Result` is kept for signature parity with the custom
//! adapter and to make any FUTURE non-mappable bridge constraint a precise blocker
//! rather than a panic.)
//!
//! ## The remaining seams to the per-turn fold
//!
//! This leaf binds the 26-slot full-fidelity tuple in-circuit, so a light client
//! folding it WITNESSES the bridge action's typed binding. Two seams remain to a
//! complete light-client-unfoolable bridge mint:
//!
//! 1. **Backing-existence (the foreign note-spend).** The `BridgeActionAir` is a
//!    BINDING-ONLY AIR — it does NOT re-prove the underlying spend (Merkle
//!    membership + spending-key knowledge); that is `note_spending`'s job, today
//!    verified by the bespoke `circuit/src/stark.rs`. This adapter closes only the
//!    ACTION-binding half — the tuple its leaf binds is still PROVER-CHOSEN, so a
//!    fold of this leaf ALONE is not a sound backing (WELD-STATE §3 bridge row).
//!    The SPEND half is now BUILT: [`crate::note_spend_leaf_adapter`] re-proves the
//!    REAL note-spend STARK (`dregg-note-spending-dsl-v3`, the circuit
//!    `apply_bridge_mint` verifies) as a foldable leaf exposing
//!    `(…PIs…, mint_hash)` with the mint identity recomputed in-circuit.
//! 2. **Effect-VM member wiring.** This leaf carries the bound tuple as descriptor
//!    PIs (bound in-circuit — a tampered PI is UNSAT). Connecting it into the
//!    bridge-mint effect-vm member means equating these PIs to the substrate
//!    `BridgeMint` row's value/recipient columns inside the EffectVM AIR (the way
//!    the custom leg's `proof_bind` column would equate the custom commitment), so
//!    the SAME aggregate fold ties the full-fidelity binding to the deployed mint.
//!    Until that lands, [`turn::executor::apply::apply_bridge_mint`]'s off-AIR
//!    `verify_bridge_action` remains the deployed enforcer; this leaf is its
//!    light-client-witnessable shadow.

use dregg_circuit::bridge_action_air::{
    BRIDGE_ACTION_PI_COUNT, BRIDGE_ACTION_WIDTH, BridgeActionAir, BridgeActionWitness,
};
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, UMemBoundaryWitness, VmConstraint2, WindowExpr,
    WindowGateSpec, prove_vm_descriptor2_for_config,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{VmConstraint, VmRow};

use p3_recursion::RecursionOutput;

use crate::ivc_turn_chain::prove_descriptor_leaf_rotated_with_config;
use crate::plonky3_recursion_impl::recursive::DreggRecursionConfig;

/// Adapt the `BridgeActionAir`'s boundary + transition constraints into the IR-v2
/// [`EffectVmDescriptor2`] so it can prove through the general prover.
///
/// The 26 boundary constraints map to `Base(PiBinding{First, col=c, pi=c})` (EXACT
/// — the AIR pins row 0 only) and the 26 transition constraints map to
/// `WindowGate{Nxt(c) − Loc(c), on_transition}` (EXACT — the AIR asserts every
/// column constant on the transition domain). See the module docs for the full
/// mapping discipline. The mapping is total: there is no bridge constraint kind to
/// refuse, so this always returns `Ok`.
pub fn bridge_action_to_descriptor2() -> Result<EffectVmDescriptor2, String> {
    let mut constraints: Vec<VmConstraint2> = Vec::with_capacity(2 * BRIDGE_ACTION_WIDTH);

    // Family 1 — the 26 boundary pins: `row0[col c] == pi[c]`. `PiBinding{First}` is
    // the term-for-term carrier of the AIR's `boundary_constraints` (all at row 0),
    // and the PI layout is identity (`pi_index == col`), preserving the
    // 8/8/8/2-limb nullifier/recipient/dest_federation/amount slots exactly.
    for c in 0..BRIDGE_ACTION_PI_COUNT {
        constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
            row: VmRow::First,
            col: c,
            pi_index: c,
        }));
    }

    // Family 2 — the 26 transition pins: `next[c] − local[c] == 0` on rows 0..n−2.
    // Each per-column difference is one two-row `WindowGate` (no subtraction node:
    // `Nxt(c) + (−1)·Loc(c)`), the faithful column-general carrier of the AIR's
    // "every column constant across rows" continuity glue.
    for c in 0..BRIDGE_ACTION_WIDTH {
        constraints.push(VmConstraint2::WindowGate(WindowGateSpec {
            body: WindowExpr::Add(
                Box::new(WindowExpr::Nxt(c)),
                Box::new(WindowExpr::Mul(
                    Box::new(WindowExpr::Const(-1)),
                    Box::new(WindowExpr::Loc(c)),
                )),
            ),
            on_transition: true,
        }));
    }

    Ok(EffectVmDescriptor2 {
        name: "bridge-action-leaf::bridge_action_air_v1".to_string(),
        trace_width: BRIDGE_ACTION_WIDTH,
        public_input_count: BRIDGE_ACTION_PI_COUNT,
        tables: vec![],
        constraints,
        hash_sites: vec![],
        ranges: vec![],
    })
}

/// Prove a bridge action binding as a RECURSION-FOLDABLE IR-v2 leaf.
///
/// `backing` is the bridge-action witness whose trace carries the typed limbs (the
/// SAME witness `prove_bridge_action` consumes off-AIR). `public_inputs` are the
/// 26-slot bound tuple `(nullifier, recipient, dest_federation, amount)` carried as
/// the leaf's descriptor PIs (bound in-circuit) — for an HONEST proof these equal
/// `backing.public_inputs()`. Passing a DIFFERENT 26-slot vector here is exactly a
/// forged backing (the trace claims one tuple, the bound PIs another): the
/// `PiBinding{First}` requires `row0[col c] == pi[c]`, so the mismatch is UNSAT and
/// no foldable leaf is minted.
///
/// `config` must be the leaf-wrap recursion config
/// ([`crate::ivc_turn_chain::ir2_leaf_wrap_config`]): the inner IR-v2 batch is
/// minted under it so the in-circuit verifier consumes it with no cross-config
/// mismatch.
///
/// On success the returned [`RecursionOutput`] is the same leaf the aggregation
/// tree folds, exposing the bound 26-slot tuple as its in-circuit-bound descriptor
/// PIs.
pub fn prove_bridge_leaf(
    backing: &BridgeActionWitness,
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    if public_inputs.len() != BRIDGE_ACTION_PI_COUNT {
        return Err(format!(
            "bridge-action leaf expects {BRIDGE_ACTION_PI_COUNT} PI slots, got {}",
            public_inputs.len()
        ));
    }
    let desc2 = bridge_action_to_descriptor2()?;

    // The bridge-action trace (width == BRIDGE_ACTION_WIDTH, 4 rows: one typed row
    // replicated for FRI power-of-2 padding). The IR-v2 prover grows/fills chip
    // lanes itself; for a table-free descriptor that is a no-op.
    let (base_trace, _trace_pis) = BridgeActionAir::generate_trace(backing);

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
    .map_err(|e| format!("bridge-action leaf inner IR-v2 prove failed: {e}"))?;

    // Wrap the inner batch as a recursion leaf, binding the descriptor PIs (the
    // 26-slot bound tuple) in-circuit.
    prove_descriptor_leaf_rotated_with_config(&desc2, &inner, public_inputs, config)
        .map_err(|e| format!("bridge-action leaf recursion wrap failed: {e}"))
}

/// Prove a bridge action binding as a recursion-foldable leaf (as [`prove_bridge_leaf`]) AND
/// RE-EXPOSE its 26-slot bound tuple `(nullifier, recipient, dest_federation, amount)` as an
/// IN-CIRCUIT `expose_claim` (lanes `[0 .. BRIDGE_ACTION_PI_COUNT)`), read from the leaf's own
/// FRI-bound descriptor PIs (not free scalars).
///
/// This is the BRIDGE analog of
/// [`crate::custom_leaf_adapter::prove_custom_leaf_with_commitment`]: it is the SUB-PROOF half of
/// the bridge-binding fold — the leaf whose exposed tuple
/// [`crate::joint_turn_recursive::prove_bridge_binding_node`] /
/// [`prove_bridge_binding_node_segmented`](crate::joint_turn_recursive::prove_bridge_binding_node_segmented)
/// `connect`s to the bridge-mint leg's CLAIMED tuple. Because the claim reads the leaf's REAL bound
/// PIs (the `PiBinding{First}` makes a tampered PI UNSAT), a prover cannot expose a tuple that
/// disagrees with the action this leaf actually proves: the claim is welded to the execution,
/// witnessable by a pure light client folding the tree.
///
/// Unlike custom (whose claim is a 4-felt in-circuit HASH of the PIs), the bridge tuple IS the claim
/// — the 26 bound PI lanes are re-exposed directly through
/// [`crate::ivc_turn_chain::prove_descriptor_leaf_with_pi_slice_expose`], no in-circuit hash needed.
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
pub fn prove_bridge_leaf_tuple_claim(
    backing: &BridgeActionWitness,
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    if public_inputs.len() != BRIDGE_ACTION_PI_COUNT {
        return Err(format!(
            "bridge-action tuple-claim leaf expects {BRIDGE_ACTION_PI_COUNT} PI slots, got {}",
            public_inputs.len()
        ));
    }
    let desc2 = bridge_action_to_descriptor2()?;
    let (base_trace, _trace_pis) = BridgeActionAir::generate_trace(backing);

    let inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
        &desc2,
        &base_trace,
        public_inputs,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        config,
    )
    .map_err(|e| format!("bridge-action tuple-claim leaf inner IR-v2 prove failed: {e}"))?;

    // RE-EXPOSE the 26 bound PI lanes (the whole tuple) as the leaf's `expose_claim`, so the binding
    // node can `connect` it to the bridge-mint leg's claimed tuple.
    crate::ivc_turn_chain::prove_descriptor_leaf_with_pi_slice_expose(
        &desc2,
        &inner,
        public_inputs,
        config,
        0,
        BRIDGE_ACTION_PI_COUNT,
    )
    .map_err(|e| format!("bridge-action tuple-claim leaf expose-wrap failed: {e}"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ivc_turn_chain::ir2_leaf_wrap_config;

    /// A typed bridge-action backing (the same shape `bridge_action_air`'s tests
    /// use): distinct 32-byte nullifier/recipient/dest_federation and a full
    /// 64-bit amount above 2^32 (exercising the high limb).
    fn make_witness() -> BridgeActionWitness {
        BridgeActionWitness {
            nullifier: [0x10; 32],
            recipient: [0x20; 32],
            destination_federation: [0x30; 32],
            amount: 0xDEAD_BEEF_CAFE_F00D,
        }
    }

    /// The mapping is total over the bridge AIR's two constraint families and
    /// produces a table-free descriptor: 26 `PiBinding{First}` + 26 `WindowGate`.
    #[test]
    fn bridge_action_maps_to_descriptor2() {
        let desc2 = bridge_action_to_descriptor2().expect("bridge maps");
        assert_eq!(desc2.trace_width, BRIDGE_ACTION_WIDTH);
        assert_eq!(desc2.public_input_count, BRIDGE_ACTION_PI_COUNT);
        assert!(desc2.tables.is_empty(), "bridge uses no declared tables");
        assert!(desc2.hash_sites.is_empty());
        assert!(desc2.ranges.is_empty());
        assert_eq!(desc2.constraints.len(), 2 * BRIDGE_ACTION_WIDTH);

        let pi_bindings = desc2
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
            .count();
        let window_gates = desc2
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::WindowGate(_)))
            .count();
        assert_eq!(
            pi_bindings, BRIDGE_ACTION_PI_COUNT,
            "one PiBinding per PI slot"
        );
        assert_eq!(
            window_gates, BRIDGE_ACTION_WIDTH,
            "one WindowGate per column"
        );

        // The PI layout is identity (`pi_index == col`), preserving the
        // 8/8/8/2-limb slot order exactly.
        for (i, c) in desc2
            .constraints
            .iter()
            .filter_map(|c| match c {
                VmConstraint2::Base(VmConstraint::PiBinding { col, pi_index, .. }) => {
                    Some((*col, *pi_index))
                }
                _ => None,
            })
            .enumerate()
        {
            assert_eq!(c, (i, i), "PiBinding {i} pins col == pi_index == {i}");
        }
    }

    /// THE POSITIVE POLE: an honest bridge action proves as a foldable recursion
    /// leaf, AND the bound descriptor PIs are exactly the witness's 26-slot
    /// `(nullifier, recipient, dest_federation, amount)` tuple — the claim the
    /// per-turn fold exposes.
    #[test]
    fn honest_bridge_action_proves_as_foldable_leaf() {
        let w = make_witness();
        let pis = w.public_inputs();
        assert_eq!(pis.len(), BRIDGE_ACTION_PI_COUNT);
        let config = ir2_leaf_wrap_config();

        // Folds: the leaf wrap returns a RecursionOutput (its in-circuit FRI verify
        // + WitnessChecks bus balanced; a non-folding leaf would have errored here).
        let _output = prove_bridge_leaf(&w, &pis, &config)
            .expect("the honest bridge action must prove as a foldable leaf");
    }

    /// THE NEGATIVE POLE: a FORGED backing (the trace carries one tuple, the bound
    /// PIs claim a TAMPERED nullifier + amount) has no satisfying assembly — the
    /// `PiBinding{First}` requires `row0[col] == pi[col]`, so the mismatch is UNSAT.
    /// The inner prover's self-verify rejects it (or the debug constraint builder
    /// panics); either way the forged binding cannot mint a foldable leaf.
    #[test]
    fn forged_backing_does_not_fold() {
        let w = make_witness();
        // The bound PIs claim a DIFFERENT nullifier (first limb flipped) and a
        // DIFFERENT amount than the trace `w` carries.
        let mut tampered = w.clone();
        tampered.nullifier[0] ^= 0xFF;
        tampered.amount = w.amount.wrapping_add(1);
        let forged_pis = tampered.public_inputs();
        // Sanity: the forged PI vector genuinely differs from the trace's.
        assert_ne!(forged_pis, w.public_inputs());
        let config = ir2_leaf_wrap_config();

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_bridge_leaf(&w, &forged_pis, &config)
        }));
        match result {
            // The debug constraint builder panicked on the unsatisfied PiBinding.
            Err(_) => {}
            // Or the inner self-verify returned an error — rejected.
            Ok(Err(_)) => {}
            Ok(Ok(_)) => {
                panic!("a FORGED bridge backing minted a foldable leaf — soundness OPEN")
            }
        }
    }
}
