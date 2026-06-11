//! Proof-carrying forest: verify a forest of standalone per-step EffectVm
//! STARK proofs **and** that they chain.
//!
//! This is the Rust realization of the design in
//! `docs/rebuild/PHASE-PROOF-CARRYING.md` — Proof-Carrying Data **minus** the
//! accumulation/recursion step. We ship the *whole forest* of per-step proofs,
//! each independently verifiable, plus the linking witness (the public-input
//! commitments). [`verify_forest`] accepts only if:
//!
//!   1. **Per-proof soundness** — every proof verifies against its own public
//!      inputs under the real [`EffectVmAir`] (`stark::verify`).
//!   2. **The link** — along every sequential edge, the predecessor's
//!      `NEW_COMMIT` public input equals the successor's `OLD_COMMIT` public
//!      input (state continuity).
//!
//! The load-bearing property this module demonstrates: **composition soundness
//! comes from the linking, not from the per-proof validity alone.** If you
//! break the link (`prev.new != next.old`) while leaving both proofs
//! individually valid, [`verify_forest`] rejects at the *link* check with a
//! distinct [`ForestError::LinkBroken`].
//!
//! Scope (smallest first increment, §9 of the design): sequential intra-cell
//! links only — no cross-cell `Σδ = 0` family binding, **no recursion /
//! aggregation feature**. Cross-cell families slot in as a later increment;
//! aggregation slots in as a node-local artifact swap that does not touch this
//! verifier (§8 of the design).

use crate::effect_vm::EffectVmAir;
use crate::effect_vm::pi;
use crate::field::BabyBear;
use crate::stark::{self, StarkProof};

/// One node in the proof forest: a standalone EffectVm STARK proof plus the
/// public-input vector it attests. The public inputs carry the linking surface
/// (`OLD_COMMIT` at [`pi::OLD_COMMIT_BASE`], `NEW_COMMIT` at
/// [`pi::NEW_COMMIT_BASE`], each 4 felts).
#[derive(Clone, Debug)]
pub struct ForestNode {
    /// The standalone EffectVm STARK proof.
    pub proof: StarkProof,
    /// The public inputs this proof was generated against. Indexed by the
    /// `pi::*` offsets.
    pub public_inputs: Vec<BabyBear>,
}

impl ForestNode {
    /// The 4-felt `OLD_COMMIT` public input (input state commitment).
    pub fn old_commit(&self) -> &[BabyBear] {
        &self.public_inputs[pi::OLD_COMMIT_BASE..pi::OLD_COMMIT_BASE + pi::OLD_COMMIT_LEN]
    }

    /// The 4-felt `NEW_COMMIT` public input (output state commitment).
    pub fn new_commit(&self) -> &[BabyBear] {
        &self.public_inputs[pi::NEW_COMMIT_BASE..pi::NEW_COMMIT_BASE + pi::NEW_COMMIT_LEN]
    }
}

/// A happened-before edge linking two nodes. For the smallest increment we
/// model only sequential intra-cell continuity edges (`from.NEW_COMMIT ==
/// to.OLD_COMMIT`). Cross-cell family edges are a later increment.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LinkEdge {
    /// Source node index (the predecessor step).
    pub from: usize,
    /// Destination node index (the successor step).
    pub to: usize,
}

/// The proof-forest artifact: the per-step proofs + the linking edges.
#[derive(Clone, Debug)]
pub struct ProofForest {
    /// One node per step (pre-order, the call-forest order).
    pub nodes: Vec<ForestNode>,
    /// The happened-before sequential edges. `prev.NEW_COMMIT == next.OLD_COMMIT`
    /// must hold along each.
    pub edges: Vec<LinkEdge>,
}

/// Why a forest failed to verify. The variants are deliberately distinct so a
/// caller (and the negative test) can tell **whether the failure was a
/// per-proof crypto failure or a link-discipline failure** — the whole point of
/// the proof-forest soundness story.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ForestError {
    /// Node `index`'s STARK proof failed to verify against its public inputs
    /// under the EffectVm AIR. This is the cryptographic leaf obligation.
    ProofInvalid {
        /// The node whose proof failed.
        index: usize,
        /// The underlying `stark::verify` error message.
        reason: String,
    },
    /// A node's public-input vector is too short to even carry the linking
    /// commitments (structural malformation).
    MalformedPublicInputs {
        /// The malformed node.
        index: usize,
        /// The actual PI length found.
        len: usize,
    },
    /// An edge references a node index that does not exist.
    EdgeOutOfBounds {
        /// The offending edge.
        edge: LinkEdge,
        /// How many nodes the forest has.
        node_count: usize,
    },
    /// **The load-bearing rejection.** Along edge `from -> to`, the
    /// predecessor's `NEW_COMMIT` does not equal the successor's `OLD_COMMIT`.
    /// Both proofs may individually be perfectly valid — the *composite* is
    /// unsound because the steps do not chain.
    LinkBroken {
        /// The edge whose link is broken.
        edge: LinkEdge,
        /// The predecessor's `NEW_COMMIT` (4 felts as u32).
        expected_old_commit: Vec<u32>,
        /// The successor's `OLD_COMMIT` (4 felts as u32).
        actual_old_commit: Vec<u32>,
    },
}

impl core::fmt::Display for ForestError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ForestError::ProofInvalid { index, reason } => {
                write!(f, "node {index} proof invalid: {reason}")
            }
            ForestError::MalformedPublicInputs { index, len } => {
                write!(
                    f,
                    "node {index} public inputs malformed: len {len} < required {}",
                    pi::NEW_COMMIT_BASE + pi::NEW_COMMIT_LEN
                )
            }
            ForestError::EdgeOutOfBounds { edge, node_count } => write!(
                f,
                "edge {}->{} out of bounds (forest has {node_count} nodes)",
                edge.from, edge.to
            ),
            ForestError::LinkBroken {
                edge,
                expected_old_commit,
                actual_old_commit,
            } => write!(
                f,
                "link broken at edge {}->{}: predecessor NEW_COMMIT {:?} != successor OLD_COMMIT {:?}",
                edge.from, edge.to, expected_old_commit, actual_old_commit
            ),
        }
    }
}

impl std::error::Error for ForestError {}

/// Verify a proof forest: (1) every proof verifies under the real EffectVm AIR
/// against its own public inputs, and (2) every sequential edge links
/// (`prev.NEW_COMMIT == next.OLD_COMMIT`).
///
/// Returns `Ok(())` only if both obligations hold. The order is deliberate:
/// per-proof verification first (the §8 cryptographic seam), then the
/// combinatorial link check. A forest whose proofs are all individually valid
/// but whose links are broken is rejected with [`ForestError::LinkBroken`] —
/// demonstrating that the composite's soundness is supplied by the linking, not
/// by the per-proof validity.
///
/// This uses **only** the production-path EffectVm STARK (`stark::verify`); no
/// recursion or aggregation feature is involved.
pub fn verify_forest(forest: &ProofForest) -> Result<(), ForestError> {
    let min_pi_len = pi::NEW_COMMIT_BASE + pi::NEW_COMMIT_LEN;

    // (1) Per-proof soundness — the cryptographic leaf obligation. Every proof
    //     must verify against its own public inputs under the EffectVm AIR.
    for (index, node) in forest.nodes.iter().enumerate() {
        if node.public_inputs.len() < min_pi_len {
            return Err(ForestError::MalformedPublicInputs {
                index,
                len: node.public_inputs.len(),
            });
        }
        // The AIR's trace height is the proof's trace length; `EffectVmAir::new`
        // requires a power-of-two >= 64, which every real proof satisfies. We
        // reconstruct the verifying AIR from the proof's own declared height so
        // verification binds the proof to the *same* AIR shape it was proven
        // under (the proof also carries `air_name`, which `stark::verify`
        // cross-checks).
        let air = EffectVmAir::new(node.proof.trace_len);
        if let Err(reason) = stark::verify(&air, &node.proof, &node.public_inputs) {
            return Err(ForestError::ProofInvalid { index, reason });
        }
    }

    // (2) Intra-cell chain-link — purely combinatorial, no crypto. For every
    //     sequential edge, the predecessor's NEW_COMMIT must equal the
    //     successor's OLD_COMMIT (state continuity). THIS is what makes the
    //     composite sound; breaking it rejects here even though step (1) passed.
    for &edge in &forest.edges {
        if edge.from >= forest.nodes.len() || edge.to >= forest.nodes.len() {
            return Err(ForestError::EdgeOutOfBounds {
                edge,
                node_count: forest.nodes.len(),
            });
        }
        let prev = &forest.nodes[edge.from];
        let next = &forest.nodes[edge.to];
        let prev_new = prev.new_commit();
        let next_old = next.old_commit();
        if prev_new != next_old {
            return Err(ForestError::LinkBroken {
                edge,
                expected_old_commit: prev_new.iter().map(|b| b.0).collect(),
                actual_old_commit: next_old.iter().map(|b| b.0).collect(),
            });
        }
    }

    Ok(())
}

// ============================================================================
// DESCRIPTOR-BACKED FOREST — the ONE-circuit cutover of the forest consumer.
// ============================================================================
//
// `verify_forest` above is the LEGACY path: it verifies per-step proofs through
// the bespoke-`stark` hand AIR (`EffectVmAir` + `stark::verify`). The ONE-circuit
// migration re-points this consumer onto the verified-by-construction Lean
// DESCRIPTOR INTERPRETER (`EffectVmDescriptorAir`, driven by the byte-exact
// Lean-emitted descriptor JSON in `effect_vm_descriptors`), which the differential
// harness (`circuit/tests/effect_vm_descriptor_cutover_harness.rs`) proves decides
// IDENTICALLY to the hand-AIR on the real witness (honest accept + anti-ghost
// reject) for the 17 GRADUATED single-effect selectors.
//
// A descriptor forest node carries an `EffectVmP3Proof` (the SAME wire type the SDK
// production prove-path emits via `prove_effect_vm_with_cutover`), so this is the
// real cutover surface — NOT a parallel toy. Each node is verified SELECTOR-BOUND
// through the descriptor verifier: a node proof verifies under EXACTLY ONE cutover
// descriptor (its own effect selector, enforced by the Lean `selectorGate s` tooth
// proven in `descriptor_proof_binds_to_its_selector`), so a cross-selector replay
// is rejected. The legacy bespoke-`stark` path is RETAINED as the transitional
// differential guard until every consumer + the non-graduated selectors are cut
// over (then the hand-AIR retires).

use crate::effect_vm_descriptors::descriptor_for_selector;
use crate::effect_vm_p3_full_air::EffectVmP3Proof;
use crate::lean_descriptor_air::{parse_vm_descriptor, verify_vm_descriptor};

/// The cutover-ready selectors whose descriptors the differential harness has
/// GRADUATED (descriptor ⟺ hand-AIR proven IDENTICAL on the real witness +
/// anti-ghost, AND each carries the Lean `selectorGate s` binding tooth). Mirror
/// of `sdk::full_turn_proof::CUTOVER_READY_SELECTORS` and the harness's
/// `descriptor_proof_binds_to_its_selector` cutover set.
pub const CUTOVER_READY_SELECTORS: &[usize] = &[
    crate::effect_vm::columns::sel::TRANSFER,
    crate::effect_vm::columns::sel::NOTE_SPEND,
    crate::effect_vm::columns::sel::NOTE_CREATE,
    crate::effect_vm::columns::sel::EMIT_EVENT,
    crate::effect_vm::columns::sel::BRIDGE_MINT,
    crate::effect_vm::columns::sel::BURN,
    crate::effect_vm::columns::sel::CELL_SEAL,
    crate::effect_vm::columns::sel::CELL_DESTROY,
    crate::effect_vm::columns::sel::REFUSAL,
    crate::effect_vm::columns::sel::SET_VERIFICATION_KEY,
    crate::effect_vm::columns::sel::SET_PERMISSIONS,
    crate::effect_vm::columns::sel::EXERCISE_VIA_CAPABILITY,
    crate::effect_vm::columns::sel::PIPELINED_SEND,
    crate::effect_vm::columns::sel::INCREMENT_NONCE,
    crate::effect_vm::columns::sel::REFRESH_DELEGATION,
    crate::effect_vm::columns::sel::REVOKE_DELEGATION,
    crate::effect_vm::columns::sel::INTRODUCE,
];

/// One node in a DESCRIPTOR-backed proof forest: a descriptor-interpreter proof
/// (`EffectVmP3Proof`, the production wire type) plus the public-input vector it
/// attests. The linking surface (`OLD_COMMIT`/`NEW_COMMIT`) is in the descriptor
/// PI prefix, so the same chain discipline as `ForestNode` applies.
///
/// (`EffectVmP3Proof` = `BatchProof<DreggStarkConfig>` is neither `Clone` nor
/// `Debug`, so this node is move-only — matching the production proof artifact.)
pub struct DescriptorForestNode {
    /// The descriptor-interpreter STARK proof (audited p3 batch-stark).
    pub proof: EffectVmP3Proof,
    /// The full EffectVM public-input vector this proof attests.
    pub public_inputs: Vec<BabyBear>,
}

impl DescriptorForestNode {
    /// The 4-felt `OLD_COMMIT` public input (input state commitment).
    pub fn old_commit(&self) -> &[BabyBear] {
        &self.public_inputs[pi::OLD_COMMIT_BASE..pi::OLD_COMMIT_BASE + pi::OLD_COMMIT_LEN]
    }

    /// The 4-felt `NEW_COMMIT` public input (output state commitment).
    pub fn new_commit(&self) -> &[BabyBear] {
        &self.public_inputs[pi::NEW_COMMIT_BASE..pi::NEW_COMMIT_BASE + pi::NEW_COMMIT_LEN]
    }
}

/// A descriptor-backed proof forest (the cutover analogue of [`ProofForest`]).
pub struct DescriptorProofForest {
    /// One node per step (call-forest order).
    pub nodes: Vec<DescriptorForestNode>,
    /// The happened-before sequential edges (`prev.NEW_COMMIT == next.OLD_COMMIT`).
    pub edges: Vec<LinkEdge>,
}

/// Verify a node's descriptor-interpreter proof SELECTOR-BOUND: try each cutover
/// descriptor's audited verifier over the descriptor's PI prefix and record which
/// selectors accept. A SOUND descriptor proof verifies under EXACTLY ONE — its own
/// effect selector (the Lean `selectorGate s` tooth). Returns the bound selector on
/// success; rejects zero (not a cutover descriptor proof) or multiple (ambiguous
/// binding — must not happen with the gate in place). This is the exact discipline
/// `sdk::full_turn_proof::verify_effect_vm_proof_with_cutover` runs, reused here so
/// the forest consumer's per-proof seam is the verified descriptor interpreter.
fn verify_descriptor_node_selector_bound(node: &DescriptorForestNode) -> Result<usize, String> {
    let mut bound: Vec<usize> = Vec::new();
    for &s in CUTOVER_READY_SELECTORS {
        if let Some(json) = descriptor_for_selector(s) {
            if let Ok(desc) = parse_vm_descriptor(json) {
                if node.public_inputs.len() >= desc.public_input_count {
                    let dpis = &node.public_inputs[..desc.public_input_count];
                    if verify_vm_descriptor(&desc, &node.proof, dpis).is_ok() {
                        bound.push(s);
                    }
                }
            }
        }
    }
    match bound.as_slice() {
        [only] => Ok(*only),
        [] => Err("descriptor forest node verified under NO cutover selector \
             (not a graduated descriptor proof)"
            .into()),
        multi => Err(format!(
            "descriptor forest node verified under MULTIPLE cutover selectors {multi:?} \
             — selector binding ambiguous, rejecting"
        )),
    }
}

/// Verify a DESCRIPTOR-backed proof forest: (1) every node's descriptor-interpreter
/// proof verifies SELECTOR-BOUND through the verified-by-construction descriptor
/// interpreter (the cutover replacement for the hand-AIR per-proof seam), and (2)
/// every sequential edge links (`prev.NEW_COMMIT == next.OLD_COMMIT`).
///
/// Same load-bearing story as [`verify_forest`]: composition soundness comes from
/// the linking, not per-proof validity. A forest of individually-valid descriptor
/// proofs whose links are broken is rejected at the link check with
/// [`ForestError::LinkBroken`]. The difference is the per-proof seam: the descriptor
/// interpreter, not `stark::verify(EffectVmAir)`.
pub fn verify_descriptor_forest(forest: &DescriptorProofForest) -> Result<(), ForestError> {
    let min_pi_len = pi::NEW_COMMIT_BASE + pi::NEW_COMMIT_LEN;

    // (1) Per-proof soundness — selector-bound through the descriptor interpreter.
    for (index, node) in forest.nodes.iter().enumerate() {
        if node.public_inputs.len() < min_pi_len {
            return Err(ForestError::MalformedPublicInputs {
                index,
                len: node.public_inputs.len(),
            });
        }
        if let Err(reason) = verify_descriptor_node_selector_bound(node) {
            return Err(ForestError::ProofInvalid { index, reason });
        }
    }

    // (2) Intra-cell chain-link — identical to the legacy path.
    for &edge in &forest.edges {
        if edge.from >= forest.nodes.len() || edge.to >= forest.nodes.len() {
            return Err(ForestError::EdgeOutOfBounds {
                edge,
                node_count: forest.nodes.len(),
            });
        }
        let prev = &forest.nodes[edge.from];
        let next = &forest.nodes[edge.to];
        let prev_new = prev.new_commit();
        let next_old = next.old_commit();
        if prev_new != next_old {
            return Err(ForestError::LinkBroken {
                edge,
                expected_old_commit: prev_new.iter().map(|b| b.0).collect(),
                actual_old_commit: next_old.iter().map(|b| b.0).collect(),
            });
        }
    }

    Ok(())
}

#[cfg(test)]
mod descriptor_tests {
    use super::*;
    use crate::effect_vm::columns::sel;
    use crate::effect_vm::{CellState, Effect, generate_effect_vm_trace};
    use crate::lean_descriptor_air::prove_vm_descriptor;

    /// Prove one step through the DESCRIPTOR INTERPRETER (the cutover prover), for a
    /// graduated single-effect turn. Returns the descriptor node (proof + full PI) so
    /// the caller can chain. This is the production cutover path:
    /// `generate_effect_vm_trace` -> descriptor JSON -> `prove_vm_descriptor`.
    fn prove_descriptor_step(
        initial_state: &CellState,
        effects: &[Effect],
        selector: usize,
    ) -> DescriptorForestNode {
        let (trace, public_inputs) = generate_effect_vm_trace(initial_state, effects);
        let json = descriptor_for_selector(selector).expect("graduated selector has a descriptor");
        let desc = parse_vm_descriptor(json).expect("descriptor parses");
        let dpis = &public_inputs[..desc.public_input_count];
        let proof = prove_vm_descriptor(&desc, &trace, dpis)
            .expect("descriptor interpreter proves the honest graduated witness");
        DescriptorForestNode {
            proof,
            public_inputs,
        }
    }

    fn apply_transfer(state: &CellState, amount: u64, direction: u32) -> CellState {
        let new_balance = if direction == 0 {
            state.balance + amount
        } else {
            state.balance - amount
        };
        CellState::new(new_balance, state.nonce + 1)
    }

    /// (1) POSITIVE: a 2-step linked forest of REAL DESCRIPTOR-INTERPRETER proofs
    /// verifies — the forest consumer is cut over onto the verified circuit.
    #[test]
    fn two_step_descriptor_forest_verifies() {
        let s0 = CellState::new(100, 0);
        let node0 = prove_descriptor_step(
            &s0,
            &[Effect::Transfer {
                amount: 30,
                direction: 0,
            }],
            sel::TRANSFER,
        );
        let s1 = apply_transfer(&s0, 30, 0);
        let node1 = prove_descriptor_step(
            &s1,
            &[Effect::Transfer {
                amount: 10,
                direction: 1,
            }],
            sel::TRANSFER,
        );

        assert_eq!(
            node0.new_commit(),
            node1.old_commit(),
            "construction precondition: NEW_COMMIT(step0) == OLD_COMMIT(step1)"
        );

        let forest = DescriptorProofForest {
            nodes: vec![node0, node1],
            edges: vec![LinkEdge { from: 0, to: 1 }],
        };
        verify_descriptor_forest(&forest)
            .expect("linked descriptor forest must verify through the descriptor interpreter");
    }

    /// (2) THE TEETH — broken link with both descriptor proofs individually valid is
    /// rejected AT THE LINK (`LinkBroken`), proving composition soundness is supplied
    /// by the link, not per-proof validity — on the descriptor path.
    #[test]
    fn tampered_link_rejected_on_descriptor_path() {
        let s0 = CellState::new(100, 0);
        let node0 = prove_descriptor_step(
            &s0,
            &[Effect::Transfer {
                amount: 30,
                direction: 0,
            }],
            sel::TRANSFER,
        );
        // Step 1 starts from an UNRELATED state, so its OLD_COMMIT != step0 NEW_COMMIT.
        let s1_wrong = CellState::new(999, 1);
        let node1 = prove_descriptor_step(
            &s1_wrong,
            &[Effect::Transfer {
                amount: 10,
                direction: 1,
            }],
            sel::TRANSFER,
        );
        assert_ne!(
            node0.new_commit(),
            node1.old_commit(),
            "link must be broken"
        );

        // Both individually valid through the descriptor interpreter.
        verify_descriptor_node_selector_bound(&node0).expect("node0 valid");
        verify_descriptor_node_selector_bound(&node1).expect("node1 valid");

        let forest = DescriptorProofForest {
            nodes: vec![node0, node1],
            edges: vec![LinkEdge { from: 0, to: 1 }],
        };
        match verify_descriptor_forest(&forest).expect_err("broken link must reject") {
            ForestError::LinkBroken { edge, .. } => assert_eq!(edge, LinkEdge { from: 0, to: 1 }),
            other => panic!("expected LinkBroken, got {other:?}"),
        }
    }

    /// (3) ANTI-GHOST / SELECTOR-BINDING: a graduated BURN proof must verify
    /// selector-bound to BURN and NOT under any other cutover selector — the
    /// cross-selector replay is closed (the Lean `selectorGate s` tooth). This is the
    /// per-node soundness the forest now rests on.
    #[test]
    fn descriptor_node_binds_to_its_own_selector() {
        let s = CellState::new(100_000, 0);
        let node = prove_descriptor_step(
            &s,
            &[Effect::Burn {
                target_hash: BabyBear::new(0xB0B),
                amount_lo: BabyBear::new(75),
                amount_full: 75,
            }],
            sel::BURN,
        );
        let bound = verify_descriptor_node_selector_bound(&node)
            .expect("burn descriptor node must verify selector-bound");
        assert_eq!(
            bound,
            sel::BURN,
            "must bind to BURN and no other cutover selector"
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::effect_vm::{CellState, Effect, generate_effect_vm_trace};
    use crate::stark::prove;

    /// Produce a real EffectVm STARK proof for one step: `initial_state`
    /// transitions under `effects`. Returns the node (proof + PI) and the
    /// resulting CellState so the caller can chain the next step from it.
    ///
    /// This is the production EffectVm path: `generate_effect_vm_trace` →
    /// `EffectVmAir` → `stark::prove`. No recursion feature.
    fn prove_step(initial_state: &CellState, effects: &[Effect]) -> ForestNode {
        let (trace, public_inputs) = generate_effect_vm_trace(initial_state, effects);
        let air = EffectVmAir::new(trace.len());
        let proof = prove(&air, &trace, &public_inputs);
        ForestNode {
            proof,
            public_inputs,
        }
    }

    /// Apply the same effects the trace applied, to derive the successor cell
    /// state, so step 1 can start exactly where step 0 ended. Mirrors the
    /// (limited) effect semantics the trace generator uses for `Transfer`.
    fn apply_transfer(state: &CellState, amount: u64, direction: u32) -> CellState {
        let new_balance = if direction == 0 {
            state.balance + amount // incoming credit
        } else {
            state.balance - amount // outgoing debit
        };
        // The trace generator bumps the nonce by 1 per non-NoOp effect.
        CellState::new(new_balance, state.nonce + 1)
    }

    /// Build a genuinely-linked 2-step forest of real EffectVm proofs.
    ///
    /// Step 0: balance 100, credit +30 -> balance 130.
    /// Step 1: starts from balance 130, debit -10 -> balance 120.
    /// By construction `NEW_COMMIT(step0) == OLD_COMMIT(step1)`.
    fn build_linked_two_step() -> (ForestNode, ForestNode) {
        let s0 = CellState::new(100, 0);
        let e0 = vec![Effect::Transfer {
            amount: 30,
            direction: 0,
        }];
        let node0 = prove_step(&s0, &e0);

        // Successor state = exactly where step 0 ended.
        let s1 = apply_transfer(&s0, 30, 0);
        let e1 = vec![Effect::Transfer {
            amount: 10,
            direction: 1,
        }];
        let node1 = prove_step(&s1, &e1);

        (node0, node1)
    }

    /// (1) POSITIVE: a 2-step linked forest of REAL EffectVmAir proofs verifies.
    /// Confirms the link actually holds (NEW_COMMIT(π0) == OLD_COMMIT(π1)) and
    /// that `verify_forest` accepts.
    #[test]
    fn two_step_linked_forest_verifies() {
        let (node0, node1) = build_linked_two_step();

        // Sanity: the link the construction promises actually holds on the PIs.
        assert_eq!(
            node0.new_commit(),
            node1.old_commit(),
            "construction precondition: NEW_COMMIT(step0) must equal OLD_COMMIT(step1)"
        );

        let forest = ProofForest {
            nodes: vec![node0, node1],
            edges: vec![LinkEdge { from: 0, to: 1 }],
        };

        let result = verify_forest(&forest);
        assert!(
            result.is_ok(),
            "linked 2-step forest of real EffectVm proofs must verify: {:?}",
            result.err()
        );
    }

    /// (2) NEGATIVE (the teeth): tamper the link so `NEW_COMMIT(π0) !=
    /// OLD_COMMIT(π1)`, while BOTH proofs remain individually valid.
    /// `verify_forest` must reject AT THE LINK CHECK with `LinkBroken`.
    ///
    /// We construct two independently-valid proofs that *do not* chain: step 1
    /// starts from a DIFFERENT state (balance 999, not the 130 step 0 produced).
    /// Each proof verifies on its own; the composite is unsound because the
    /// steps do not continue each other. This proves composition soundness is
    /// supplied by the link, not by per-proof validity.
    #[test]
    fn tampered_link_rejected_at_link_with_both_proofs_valid() {
        // Step 0 as before: 100 -> 130.
        let s0 = CellState::new(100, 0);
        let node0 = prove_step(
            &s0,
            &[Effect::Transfer {
                amount: 30,
                direction: 0,
            }],
        );

        // Step 1 starts from an UNRELATED state (balance 999), so its OLD_COMMIT
        // does NOT equal step 0's NEW_COMMIT. It is still a perfectly valid
        // EffectVm proof in its own right.
        let s1_wrong = CellState::new(999, 1);
        let node1 = prove_step(
            &s1_wrong,
            &[Effect::Transfer {
                amount: 10,
                direction: 1,
            }],
        );

        // Precondition for the test to be meaningful: the link is genuinely
        // broken (the two commitments differ).
        assert_ne!(
            node0.new_commit(),
            node1.old_commit(),
            "test setup: the link must be broken for this negative test"
        );

        // BOTH proofs must verify INDIVIDUALLY — this is the load-bearing fact.
        let air0 = EffectVmAir::new(node0.proof.trace_len);
        stark::verify(&air0, &node0.proof, &node0.public_inputs)
            .expect("step 0 proof must be individually valid");
        let air1 = EffectVmAir::new(node1.proof.trace_len);
        stark::verify(&air1, &node1.proof, &node1.public_inputs)
            .expect("step 1 proof must be individually valid");

        // Yet the FOREST must be rejected — and specifically AT THE LINK CHECK.
        let forest = ProofForest {
            nodes: vec![node0, node1],
            edges: vec![LinkEdge { from: 0, to: 1 }],
        };
        let err = verify_forest(&forest).expect_err(
            "forest with a broken link must be rejected even though both proofs are valid",
        );

        match err {
            ForestError::LinkBroken { edge, .. } => {
                assert_eq!(edge, LinkEdge { from: 0, to: 1 });
            }
            other => panic!(
                "expected rejection AT THE LINK (ForestError::LinkBroken), got {other:?} — \
                 a non-link rejection would mean the test is not exercising composition soundness"
            ),
        }
    }

    /// Defense-in-depth negative: a corrupted proof byte is rejected at the
    /// per-proof (step 1) check, NOT the link check — distinguishing the two
    /// failure modes.
    #[test]
    fn corrupted_proof_rejected_at_proof_check() {
        let (mut node0, node1) = build_linked_two_step();

        // Corrupt step 0's proof: flip its trace commitment. The link PIs are
        // untouched, so a LinkBroken would be wrong here — it must fail at the
        // proof check.
        node0.proof.trace_commitment[0] ^= 0xFF;

        let forest = ProofForest {
            nodes: vec![node0, node1],
            edges: vec![LinkEdge { from: 0, to: 1 }],
        };
        let err = verify_forest(&forest).expect_err("corrupted proof must be rejected");
        match err {
            ForestError::ProofInvalid { index, .. } => assert_eq!(index, 0),
            other => panic!("expected ProofInvalid at node 0, got {other:?}"),
        }
    }
}
