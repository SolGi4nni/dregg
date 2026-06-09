//! Full-turn STARK proving on the node's finalized-turn commit path.
//!
//! This module makes the public claim — *every committed state transition is
//! proven* — TRUE for the running node. When the devnet enables full-turn
//! proving, [`crate::blocklace_sync::execute_finalized_turn`] calls
//! [`prove_and_verify_finalized_turn`] for each finalized turn:
//!
//! 1. **Prove.** The turn's effects (projected onto the actor cell) are
//!    marshalled into the Effect VM encoding via the cipherclerk's existing
//!    [`AgentCipherclerk::convert_effects_to_vm`] marshaller, and a real
//!    `FullTurnProof` (a composed STARK over the Effect-VM AIR) is generated
//!    with [`dregg_sdk::prove_turn_self_sovereign`].
//!
//! 2. **Verify → accept.** The freshly generated proof is *re-verified*
//!    against the actor cell's pre-state commitment (`old_commit`) and the
//!    proven post-state commitment (`new_commit`) using
//!    [`dregg_sdk::verify_full_turn`] — the same verifier remote peers use.
//!    Acceptance is **gated** on this check: if the proof does not verify
//!    against the expected commitments, the turn is *not* accepted as proven
//!    (the caller surfaces a rejection).
//!
//! The anti-ghost property is exercised in this module's tests: a turn whose
//! post-state commitment is forged (any felt off by one) is **REJECTED** by
//! `verify_full_turn`, because the Effect-VM AIR binds the new commitment at
//! its boundary row and the verifier checks it against the caller's expected
//! value (`CommitmentMismatch`).
//!
//! ## Soundness scope (honest)
//!
//! The Effect VM proves the actor cell's `(balance, nonce, fields, cap_root)`
//! transition. `old_commit` is the actor cell's pre-execution
//! `CellState::compute_commitment` and `new_commit` is read from the AIR's
//! boundary public input (the prover cannot forge it without producing an
//! invalid trace). This is the per-cell whole-turn binding the SDK FullTurn
//! phase established; it is the load-bearing commit-path leg the public claim
//! rests on. Cross-cell / multi-root aggregation is the Silver→Gold vision and
//! is tracked separately — it does not weaken what is proven here.
//!
//! ## FRESHNESS / no-double-spend (the LIVE binding this module wires)
//!
//! A finalized turn that SPENDS a note (carries an [`dregg_turn::Effect::NoteSpend`])
//! is routed through [`prove_and_verify_finalized_turn_freshness`] instead of the
//! plain self-sovereign path. That function attaches a **non-revocation** sub-proof
//! whose sorted-Merkle tree is built from the node's CANONICAL spent-nullifier set
//! (the persisted [`dregg_persist::Store`] nullifier set, folded into the field the
//! Effect-VM uses), and then verifies the composed proof through
//! [`dregg_sdk::verify_full_turn_bound`] with `expected_revocation_root` pinned to
//! that canonical root. This makes the SDK's two no-double-spend teeth FIRE on the
//! live commit path:
//!
//! - **binding (a)** [`FullTurnVerifyError::RevocationRootMismatch`]: the freshness
//!   proof must be against THE canonical nullifier set the node maintains — a
//!   prover-chosen (empty/stale) accumulator is rejected;
//! - **binding (b)** [`FullTurnVerifyError::NullifierMismatch`]: the item proved
//!   fresh must be THIS turn's spent nullifier, not some other item.
//!
//! ### Accumulator reconciliation (PolynomialAccumulator vs sorted-Merkle)
//!
//! The node has two distinct "absence" structures for two distinct sets:
//! `NodeState::revocation_accumulator` (a `PolynomialAccumulator` over revoked
//! capability-token hashes) and the persisted note-nullifier set (double-spend
//! prevention for `NoteSpend`). They are NOT the same set. The circuit's
//! non-revocation AIR ([`dregg_circuit::dsl::revocation`]) is a fixed-capacity
//! sorted-Merkle tree, so for note-spend freshness we make the **sorted-Merkle
//! tree derived from the persisted nullifier set** the canonical structure the
//! verifier pins. The derived root is a deterministic function of the node's
//! authoritative set (built here via [`canonical_revocation_root_for_set`]), so a
//! peer/light-client re-deriving it from the same set obtains the same root: the
//! verifier's `revocation_root` check is against the node's REAL set, never a
//! prover-chosen tree.
//!
//! ### Capacity bound (honest)
//!
//! The audited non-revocation circuit is hardwired to
//! [`dregg_circuit::dsl::revocation::TREE_DEPTH`] (`= 4`, a 16-leaf tree, so at
//! most `16 - 2 = 14` revoked entries after the two sentinels). When the canonical
//! nullifier set exceeds that capacity, a single fixed-depth proof cannot cover it
//! WITHOUT a deeper circuit (a circuit change, out of scope here). Rather than
//! silently truncate the canonical set (which would be UNSOUND — it could omit the
//! very nullifier being re-spent), [`canonical_revocation_root_for_set`] returns
//! `Err(RevocationCapacityExceeded)` and the spend turn is committed but carries NO
//! freshness-bound proof, logged loudly as a real limitation. Closing this needs a
//! depth-parameterized non-revocation AIR (tracked, not faked).
//!
//! ## AUTHORITY leg — NOT wired here (named blocker, see module-level note in the
//! commit message): binding a hosted/capability-gated turn's authorization leg
//! non-vacuously requires the Effect-VM cross-binding to bind to `capability_root`
//! (not the whole-state commitment) AND the executor to thread the *consumed*
//! capability's slot/fact/Merkle-path into the [`dregg_turn::TurnReceipt`]. Neither
//! exists today (`derivation_records` records GRANTS the turn *creates*, not the
//! capability it *consumes*; the cell c-list is not a Merkle tree rooted at the
//! Effect-VM state commitment). Wiring an authorization leg now would carry a FREE
//! (unconstrained) body-fact witness — a vacuous "the actor holds this capability"
//! claim. We do not do that; the AUTHORITY tooth stays correctly absent until the
//! circuit + executor support a real witness.

use dregg_circuit::dsl::revocation::{DslRevocationTree, TREE_DEPTH};
use dregg_circuit::effect_vm::fold_bytes32_to_bb;
use dregg_circuit::field::BabyBear;
use dregg_circuit::{CellState, generate_effect_vm_trace};
use dregg_sdk::{
    AgentCipherclerk, FullTurnProof, FullTurnVerifyError, FullTurnWitness, NonRevocationWitness,
    prove_full_turn, prove_turn_self_sovereign, verify_full_turn_bound,
};
use dregg_types::CellId;

/// Maximum number of revoked entries the audited non-revocation circuit can
/// authenticate in a single proof: the sorted-Merkle tree is hardwired to
/// [`TREE_DEPTH`] (`= 4`, a `2^4 = 16`-leaf tree) and reserves two leaves for the
/// `SENTINEL_MIN`/`SENTINEL_MAX` ordering sentinels, leaving `16 - 2 = 14`.
///
/// This is a CIRCUIT capacity, not a node policy: building the canonical tree at
/// any other depth would not match the verifier's AIR. See the module-level
/// "Capacity bound" note.
pub const MAX_REVOCATION_TREE_ENTRIES: usize = (1usize << TREE_DEPTH) - 2;

/// A finalized turn that carries a real, re-verified full-turn STARK proof.
#[derive(Clone, Debug)]
pub struct ProvenFinalizedTurn {
    /// The composed full-turn proof (Effect-VM STARK), ready for wire transmission.
    pub proof: FullTurnProof,
    /// Position-0 felt of the actor cell's pre-execution state commitment.
    pub old_commit: BabyBear,
    /// Position-0 felt of the proven post-execution state commitment.
    pub new_commit: BabyBear,
}

impl ProvenFinalizedTurn {
    /// Serialized proof bytes (the wire form attached to the committed turn).
    pub fn proof_bytes(&self) -> &[u8] {
        &self.proof.proof_bytes
    }
}

/// Errors from the full-turn proving + verify→accept leg.
#[derive(Debug)]
pub enum FullTurnProvingError {
    /// Proof generation failed (invalid witness).
    Prove(dregg_sdk::SdkError),
    /// The freshly generated proof did NOT verify against the expected
    /// pre/post commitments. Acceptance is gated on this: a turn whose proof
    /// does not verify is not accepted as proven.
    Verify(FullTurnVerifyError),
    /// The canonical spent-nullifier set is larger than the audited
    /// non-revocation circuit's fixed capacity ([`MAX_REVOCATION_TREE_ENTRIES`]).
    /// A single fixed-depth freshness proof cannot soundly cover it (omitting any
    /// entry could hide a double-spend), so the freshness-bound proof is NOT
    /// produced for this turn. Closing this needs a depth-parameterized
    /// non-revocation AIR.
    RevocationCapacityExceeded { have: usize, max: usize },
    /// The turn was routed to the freshness path but the prover could not build a
    /// non-membership witness — the spent nullifier is ALREADY in the canonical
    /// set (a genuine double-spend the executor should also have rejected) or the
    /// witness was otherwise unconstructible. The turn carries no freshness proof.
    NullifierAlreadyRevoked,
}

impl std::fmt::Display for FullTurnProvingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Prove(e) => write!(f, "full-turn proof generation failed: {e}"),
            Self::Verify(e) => write!(f, "full-turn proof verification failed: {e}"),
            Self::RevocationCapacityExceeded { have, max } => write!(
                f,
                "canonical nullifier set ({have}) exceeds the non-revocation circuit capacity \
                 ({max}); freshness-bound proof not produced (needs a deeper non-revocation AIR)"
            ),
            Self::NullifierAlreadyRevoked => write!(
                f,
                "spent nullifier is already in the canonical revocation set (double-spend) — \
                 no non-membership witness exists"
            ),
        }
    }
}

impl std::error::Error for FullTurnProvingError {}

/// Prove a finalized NON-SPEND turn and gate acceptance on the proof verifying.
///
/// This is the self-sovereign path: it carries ONLY the Effect-VM state-transition
/// leg (no authorization / membership / non-revocation sub-proofs), which is the
/// correct trust model for an owner-authorized turn that spends no note. A turn
/// that spends a note (`NoteSpend`) must instead go through
/// [`prove_and_verify_finalized_turn_freshness`] so the no-double-spend bindings
/// fire; the caller branches on [`spent_nullifiers`].
///
/// `pre_balance` / `pre_nonce` are the actor cell's state captured **before**
/// the executor mutated the ledger (the pre-state the proof's `old_commit`
/// binds to). `effects` are the turn's effects (the caller passes
/// `turn.call_forest.total_effects()` cloned).
///
/// Returns the proven turn on success, or [`FullTurnProvingError`] if proving
/// fails or — critically — if the freshly generated proof does not verify
/// against the expected commitments (the verify→accept leg).
pub fn prove_and_verify_finalized_turn(
    agent: &CellId,
    pre_balance: u64,
    pre_nonce: u64,
    effects: &[dregg_turn::Effect],
    turn_hash: [u8; 32],
) -> Result<ProvenFinalizedTurn, FullTurnProvingError> {
    // 1. Marshal the turn's effects onto the actor cell in the Effect-VM
    //    encoding (reuses the cipherclerk's canonical marshaller so the node
    //    proves exactly what the cipherclerk would sign).
    let vm_effects = AgentCipherclerk::convert_effects_to_vm(agent, effects);

    // 2. Build the actor cell's pre-execution Effect-VM state. The old
    //    commitment the proof binds to is this state's commitment.
    let initial_vm_state = CellState::new(pre_balance, pre_nonce as u32);
    let old_commit = initial_vm_state.state_commitment;

    // 3. Derive the proven post-state commitment from the AIR boundary public
    //    input. The prover cannot forge this without an invalid trace.
    let (_trace, pi) = generate_effect_vm_trace(&initial_vm_state, &vm_effects);
    let new_commit = pi[dregg_circuit::effect_vm::pi::NEW_COMMIT];

    // 4. Generate the real composed full-turn STARK proof.
    let proof = prove_turn_self_sovereign(&initial_vm_state, &vm_effects, turn_hash)
        .map_err(FullTurnProvingError::Prove)?;

    // 5. VERIFY → ACCEPT leg. Re-verify the proof against the expected
    //    pre/post commitments using the same verifier a remote peer runs.
    //    Acceptance is gated on this returning Ok.
    dregg_sdk::verify_full_turn(&proof, old_commit, new_commit)
        .map_err(FullTurnProvingError::Verify)?;

    Ok(ProvenFinalizedTurn {
        proof,
        old_commit,
        new_commit,
    })
}

/// Extract the raw 32-byte nullifiers of every `NoteSpend` in a turn's effects
/// (including those nested inside `ExerciseViaCapability`), in order.
///
/// A turn with at least one entry here is a SPEND turn and is routed through the
/// freshness path. The current freshness circuit attests ONE nullifier per proof;
/// the caller proves the first and (when several are present) the rest ride the
/// per-cell Effect-VM binding (multi-nullifier batching is a circuit extension).
pub fn spent_nullifiers(effects: &[dregg_turn::Effect]) -> Vec<[u8; 32]> {
    fn collect(effect: &dregg_turn::Effect, out: &mut Vec<[u8; 32]>) {
        match effect {
            dregg_turn::Effect::NoteSpend { nullifier, .. } => out.push(nullifier.0),
            dregg_turn::Effect::ExerciseViaCapability { inner_effects, .. } => {
                for inner in inner_effects {
                    collect(inner, out);
                }
            }
            _ => {}
        }
    }
    let mut out = Vec::new();
    for e in effects {
        collect(e, &mut out);
    }
    out
}

/// Fold a raw 32-byte note nullifier into the BabyBear field element the
/// Effect-VM uses for `PI[NOTESPEND_NULLIFIER]`.
///
/// This is the SAME fold the cipherclerk's `convert_effects_to_vm` applies to a
/// `NoteSpend` nullifier (`dregg_circuit::effect_vm::fold_bytes32_to_bb`), so the
/// canonical revocation tree's leaves and the queried `item_hash` live in the
/// same field as the Effect-VM nullifier the verifier's binding-(b) tooth checks.
pub fn nullifier_to_field(nullifier: &[u8; 32]) -> BabyBear {
    fold_bytes32_to_bb(nullifier)
}

/// Build the canonical [`DslRevocationTree`] from the node's authoritative
/// spent-nullifier set (the raw 32-byte nullifiers), folding each into the
/// Effect-VM field. Returns the tree (whose `root()` is the canonical revocation
/// root) or [`FullTurnProvingError::RevocationCapacityExceeded`] when the set is
/// too large for the fixed-depth circuit.
///
/// The set passed in is the previously-spent nullifiers — i.e. it must EXCLUDE
/// the nullifier of the turn currently being proven (freshness = "not yet in the
/// set"). The caller is responsible for capturing the set before recording this
/// turn's spend.
pub fn canonical_revocation_tree_for_set(
    previously_spent: &[[u8; 32]],
) -> Result<DslRevocationTree, FullTurnProvingError> {
    if previously_spent.len() > MAX_REVOCATION_TREE_ENTRIES {
        return Err(FullTurnProvingError::RevocationCapacityExceeded {
            have: previously_spent.len(),
            max: MAX_REVOCATION_TREE_ENTRIES,
        });
    }
    let leaves: Vec<BabyBear> = previously_spent.iter().map(nullifier_to_field).collect();
    Ok(DslRevocationTree::new(leaves, TREE_DEPTH))
}

/// Canonical revocation root for a spent-nullifier set: the root of the
/// sorted-Merkle tree the audited non-revocation circuit authenticates against,
/// derived deterministically from the node's authoritative set. A peer/light
/// client re-deriving from the same set obtains the same root.
pub fn canonical_revocation_root_for_set(
    previously_spent: &[[u8; 32]],
) -> Result<BabyBear, FullTurnProvingError> {
    Ok(canonical_revocation_tree_for_set(previously_spent)?.root())
}

/// Prove a finalized SPEND turn and gate acceptance on the freshness-bound
/// verifier (`verify_full_turn_bound` with the canonical revocation root pinned).
///
/// This is the no-double-spend path. In addition to the Effect-VM post-state
/// binding [`prove_and_verify_finalized_turn`] establishes, it:
///
/// 1. builds the canonical [`DslRevocationTree`] from `previously_spent` (the
///    node's authoritative set of nullifiers spent BEFORE this turn);
/// 2. attaches a non-revocation sub-proof of freshness for `spent_nullifier`
///    (this turn's nullifier, folded into the Effect-VM field);
/// 3. verifies through [`verify_full_turn_bound`] with `expected_revocation_root`
///    pinned to the canonical root — so the SDK's binding-(a)
///    ([`FullTurnVerifyError::RevocationRootMismatch`]) and binding-(b)
///    ([`FullTurnVerifyError::NullifierMismatch`]) teeth FIRE on the live path.
///
/// `spent_nullifier` is the raw 32-byte nullifier of THIS turn's `NoteSpend`
/// (the executor already rejected a genuine double-spend; this proof attests
/// freshness against the canonical set so a light client can re-check it).
///
/// Returns the proven turn, or:
/// - [`FullTurnProvingError::RevocationCapacityExceeded`] if the canonical set is
///   too large for the fixed-depth circuit (turn carries no freshness proof);
/// - [`FullTurnProvingError::NullifierAlreadyRevoked`] if the nullifier is already
///   in the canonical set (double-spend; no non-membership witness);
/// - [`FullTurnProvingError::Prove`] / [`FullTurnProvingError::Verify`] on the
///   usual proving / verify-gate failures.
#[allow(clippy::too_many_arguments)]
pub fn prove_and_verify_finalized_turn_freshness(
    agent: &CellId,
    pre_balance: u64,
    pre_nonce: u64,
    effects: &[dregg_turn::Effect],
    turn_hash: [u8; 32],
    spent_nullifier: &[u8; 32],
    previously_spent: &[[u8; 32]],
) -> Result<ProvenFinalizedTurn, FullTurnProvingError> {
    // Canonical revocation tree from the node's authoritative set (built from the
    // set BEFORE this turn's nullifier is recorded — freshness is non-membership).
    let tree = canonical_revocation_tree_for_set(previously_spent)?;
    let canonical_root = tree.root();
    let item_hash = nullifier_to_field(spent_nullifier);

    // A genuine double-spend has no non-membership witness; refuse rather than
    // attach an unsound/absent proof. (The executor's NullifierSet should already
    // have rejected this turn; this is defence in depth.)
    if tree.contains(&item_hash) {
        return Err(FullTurnProvingError::NullifierAlreadyRevoked);
    }

    // Same Effect-VM marshalling + pre-state as the self-sovereign path.
    let vm_effects = AgentCipherclerk::convert_effects_to_vm(agent, effects);
    let initial_vm_state = CellState::new(pre_balance, pre_nonce as u32);
    let old_commit = initial_vm_state.state_commitment;
    let (_trace, pi) = generate_effect_vm_trace(&initial_vm_state, &vm_effects);
    let new_commit = pi[dregg_circuit::effect_vm::pi::NEW_COMMIT];

    // Compose the full-turn proof WITH the non-revocation leg.
    let witness = FullTurnWitness {
        initial_cell_state: initial_vm_state,
        effects: vm_effects,
        authorization: None,
        membership: None,
        conservation: None,
        non_revocation: Some(NonRevocationWitness { tree, item_hash }),
        turn_hash,
    };
    let proof = prove_full_turn(&witness).map_err(FullTurnProvingError::Prove)?;

    // VERIFY → ACCEPT leg, BOUND to the canonical revocation root. Acceptance is
    // gated on this Ok: a freshness proof against any other (prover-chosen) root,
    // or for any item other than this turn's nullifier, is rejected here.
    verify_full_turn_bound(&proof, old_commit, new_commit, Some(canonical_root))
        .map_err(FullTurnProvingError::Verify)?;

    Ok(ProvenFinalizedTurn {
        proof,
        old_commit,
        new_commit,
    })
}

/// Config-store key under which a finalized turn's proof bytes are persisted,
/// keyed by the turn hash (hex). Lets an operator / API surface the attached
/// proof for any committed turn.
pub fn turn_proof_config_key(turn_hash_hex: &str) -> String {
    format!("full_turn_proof:{turn_hash_hex}")
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A committed transfer turn carries a proof that VERIFIES against the
    /// expected pre/post commitments (the verify→accept leg succeeds).
    #[test]
    fn committed_turn_carries_verifying_proof() {
        let alice = CellId::from_bytes([0xA1; 32]);
        let bob = CellId::from_bytes([0xB2; 32]);

        // Alice sends 100 to Bob. From Alice's actor-cell perspective this is
        // an outgoing transfer (balance debits by 100).
        let effects = vec![dregg_turn::Effect::Transfer {
            from: alice,
            to: bob,
            amount: 100,
        }];
        let turn_hash = [0x11u8; 32];

        let proven = prove_and_verify_finalized_turn(&alice, 1000, 0, &effects, turn_hash)
            .expect("finalized turn should prove and self-verify");

        // The proof is real (non-empty wire bytes) and re-verifies.
        assert!(!proven.proof_bytes().is_empty());
        assert!(proven.proof.components.has_state_transition);
        assert_eq!(proven.proof.turn_hash, turn_hash);

        // Independent re-verification against the carried commitments.
        dregg_sdk::verify_full_turn(&proven.proof, proven.old_commit, proven.new_commit)
            .expect("carried proof must re-verify against carried commitments");
    }

    /// ANTI-GHOST: a turn whose post-state commitment is FORGED (off by one
    /// felt) is REJECTED. The Effect-VM AIR binds the new commitment at its
    /// boundary; `verify_full_turn` checks it against the expected value and
    /// returns `CommitmentMismatch`.
    #[test]
    fn forged_post_state_is_rejected() {
        let alice = CellId::from_bytes([0xA1; 32]);
        let bob = CellId::from_bytes([0xB2; 32]);

        let effects = vec![dregg_turn::Effect::Transfer {
            from: alice,
            to: bob,
            amount: 100,
        }];
        let turn_hash = [0x22u8; 32];

        let proven = prove_and_verify_finalized_turn(&alice, 1000, 0, &effects, turn_hash)
            .expect("honest turn should prove");

        // Forge the post-state commitment: claim a DIFFERENT new state than
        // the one the proof actually attests.
        let forged_new_commit = proven.new_commit + BabyBear::new(1);
        assert_ne!(forged_new_commit, proven.new_commit);

        let result =
            dregg_sdk::verify_full_turn(&proven.proof, proven.old_commit, forged_new_commit);
        assert!(
            result.is_err(),
            "ANTI-GHOST: forged post-state commitment MUST be rejected"
        );
        match result.unwrap_err() {
            FullTurnVerifyError::CommitmentMismatch { which, .. } => {
                assert_eq!(which, "new_commitment");
            }
            other => panic!("expected new_commitment mismatch, got {other:?}"),
        }
    }

    /// ANTI-GHOST (pre-state): forging the OLD commitment (claiming the turn
    /// started from a different cell state than it did) is also REJECTED.
    #[test]
    fn forged_pre_state_is_rejected() {
        let alice = CellId::from_bytes([0xA1; 32]);
        let bob = CellId::from_bytes([0xB2; 32]);

        let effects = vec![dregg_turn::Effect::Transfer {
            from: alice,
            to: bob,
            amount: 50,
        }];
        let turn_hash = [0x33u8; 32];

        let proven = prove_and_verify_finalized_turn(&alice, 777, 3, &effects, turn_hash)
            .expect("honest turn should prove");

        let forged_old_commit = proven.old_commit + BabyBear::new(1);
        let result =
            dregg_sdk::verify_full_turn(&proven.proof, forged_old_commit, proven.new_commit);
        assert!(
            result.is_err(),
            "ANTI-GHOST: forged pre-state commitment MUST be rejected"
        );
        match result.unwrap_err() {
            FullTurnVerifyError::CommitmentMismatch { which, .. } => {
                assert_eq!(which, "old_commitment");
            }
            other => panic!("expected old_commitment mismatch, got {other:?}"),
        }
    }

    // ──────────────────────────────────────────────────────────────────────
    // FRESHNESS / no-double-spend routing (the LIVE bindings this module wires)
    // ──────────────────────────────────────────────────────────────────────

    /// Build a turn-level `NoteSpend` effect with the given raw nullifier.
    fn note_spend_effect(nullifier: [u8; 32], value: u64) -> dregg_turn::Effect {
        dregg_turn::Effect::NoteSpend {
            nullifier: dregg_cell::note::Nullifier(nullifier),
            note_tree_root: [0u8; 32],
            value,
            asset_type: 0,
            spending_proof: Vec::new(),
            value_commitment: None,
        }
    }

    /// ROUTING: `spent_nullifiers` classifies a spend turn (so the commit path
    /// routes it to the freshness fn) and a non-spend turn (which stays on the
    /// self-sovereign path).
    #[test]
    fn routing_identifies_spend_vs_non_spend() {
        let alice = CellId::from_bytes([0xA1; 32]);
        let bob = CellId::from_bytes([0xB2; 32]);

        let transfer = vec![dregg_turn::Effect::Transfer {
            from: alice,
            to: bob,
            amount: 100,
        }];
        assert!(
            spent_nullifiers(&transfer).is_empty(),
            "a pure transfer is NOT a spend turn — stays on the self-sovereign path",
        );

        let nf = [0x5Eu8; 32];
        let spend = vec![note_spend_effect(nf, 500)];
        assert_eq!(
            spent_nullifiers(&spend),
            vec![nf],
            "a NoteSpend turn surfaces its nullifier so the commit path routes it to freshness",
        );

        // Nested inside ExerciseViaCapability is still detected.
        let nested = vec![dregg_turn::Effect::ExerciseViaCapability {
            cap_slot: 0,
            inner_effects: vec![note_spend_effect(nf, 500)],
        }];
        assert_eq!(
            spent_nullifiers(&nested),
            vec![nf],
            "a NoteSpend nested under ExerciseViaCapability is still routed to freshness",
        );
    }

    /// CONTROL (honest spend): a NoteSpend turn whose freshness is proven against
    /// the node's canonical spent-nullifier set VERIFIES through the bound
    /// verify→accept leg.
    #[test]
    fn honest_spend_freshness_verifies() {
        let alice = CellId::from_bytes([0xA1; 32]);
        let nf = [0x11u8; 32];
        // Some previously-spent nullifiers (NOT including this turn's nf).
        let previously: Vec<[u8; 32]> = (1..=6u8).map(|i| [i; 32]).collect();
        assert!(!previously.contains(&nf));

        let effects = vec![note_spend_effect(nf, 500)];
        let proven = prove_and_verify_finalized_turn_freshness(
            &alice,
            1000,
            0,
            &effects,
            [0xA0u8; 32],
            &nf,
            &previously,
        )
        .expect("honest spend (fresh against the canonical set) must prove + bound-verify");

        assert!(proven.proof.components.has_non_revocation);
        assert!(!proven.proof_bytes().is_empty());

        // Independent re-verification against the SAME canonical root the node
        // would derive (a light client's path).
        let canonical_root = canonical_revocation_root_for_set(&previously).unwrap();
        verify_full_turn_bound(
            &proven.proof,
            proven.old_commit,
            proven.new_commit,
            Some(canonical_root),
        )
        .expect("light-client re-verify against the canonical root must accept");
    }

    /// ANTI-FORGERY binding (a) — RevocationRootMismatch: an honest spend proof
    /// is REJECTED when re-verified against a DIFFERENT (stale / wrong) revocation
    /// root than the one its freshness was proven against. This is exactly the
    /// counterfeiting hole the bound verify closes on the live path: a proof of
    /// freshness against one nullifier set must not be accepted as freshness
    /// against another.
    #[test]
    fn spend_against_wrong_revocation_root_is_rejected() {
        let alice = CellId::from_bytes([0xA1; 32]);
        let nf = [0x22u8; 32];
        let previously: Vec<[u8; 32]> = (1..=6u8).map(|i| [i; 32]).collect();

        let effects = vec![note_spend_effect(nf, 500)];
        let proven = prove_and_verify_finalized_turn_freshness(
            &alice, 1000, 0, &effects, [0xB0u8; 32], &nf, &previously,
        )
        .expect("honest spend proves");

        // A DIFFERENT canonical set (e.g. a staler view that already includes nf,
        // or simply a different set) yields a different canonical root.
        let other_set: Vec<[u8; 32]> = (1..=8u8).map(|i| [i; 32]).collect();
        let wrong_root = canonical_revocation_root_for_set(&other_set).unwrap();
        let honest_root = canonical_revocation_root_for_set(&previously).unwrap();
        assert_ne!(wrong_root, honest_root);

        let result = verify_full_turn_bound(
            &proven.proof,
            proven.old_commit,
            proven.new_commit,
            Some(wrong_root),
        );
        match result {
            Err(FullTurnVerifyError::RevocationRootMismatch { expected, got }) => {
                assert_eq!(expected, wrong_root);
                assert_eq!(got, honest_root);
            }
            Ok(()) => panic!(
                "SOUNDNESS (no-double-spend binding a): a freshness proof against one nullifier \
                 set was ACCEPTED against a DIFFERENT root — the counterfeiting hole is OPEN!"
            ),
            Err(other) => panic!("expected RevocationRootMismatch, got {other:?}"),
        }
    }

    /// ANTI-FORGERY binding (b) — NullifierMismatch: a spend turn whose Effect-VM
    /// nullifier is N, but whose attached freshness proof attests a DIFFERENT item
    /// M, is REJECTED by the bound verify→accept leg. We drive this through the
    /// live freshness fn by passing a `spent_nullifier` (the freshness item) that
    /// differs from the turn's actual NoteSpend nullifier (the Effect-VM PI).
    #[test]
    fn spend_freshness_for_wrong_item_is_rejected() {
        let alice = CellId::from_bytes([0xA1; 32]);
        // The turn genuinely spends N.
        let n = [0x33u8; 32];
        // The prover attaches freshness for a DIFFERENT item M.
        let m = [0x44u8; 32];
        assert_ne!(n, m);
        let previously: Vec<[u8; 32]> = (1..=6u8).map(|i| [i + 100; 32]).collect();

        let effects = vec![note_spend_effect(n, 500)];
        let result = prove_and_verify_finalized_turn_freshness(
            &alice, 1000, 0, &effects, [0xC0u8; 32], &m, &previously,
        );
        match result {
            Err(FullTurnProvingError::Verify(FullTurnVerifyError::NullifierMismatch {
                proven_item,
                effect_nullifier,
            })) => {
                assert_eq!(proven_item, nullifier_to_field(&m));
                assert_eq!(effect_nullifier, nullifier_to_field(&n));
            }
            Ok(_) => panic!(
                "SOUNDNESS (no-double-spend binding b): a spend of N whose freshness attests a \
                 DIFFERENT item M was ACCEPTED — the verify→accept gate did not fire!"
            ),
            Err(other) => panic!("expected Verify(NullifierMismatch), got {other:?}"),
        }
    }

    /// A spend whose nullifier is ALREADY in the canonical set (a double-spend)
    /// has no non-membership witness; the freshness fn refuses rather than fake a
    /// proof.
    #[test]
    fn double_spend_has_no_freshness_witness() {
        let alice = CellId::from_bytes([0xA1; 32]);
        let nf = [0x55u8; 32];
        // nf is ALREADY spent.
        let previously: Vec<[u8; 32]> = vec![[1u8; 32], nf, [3u8; 32]];

        let effects = vec![note_spend_effect(nf, 500)];
        let result = prove_and_verify_finalized_turn_freshness(
            &alice, 1000, 0, &effects, [0xD0u8; 32], &nf, &previously,
        );
        assert!(
            matches!(result, Err(FullTurnProvingError::NullifierAlreadyRevoked)),
            "a double-spend must NOT be able to produce a freshness proof, got {result:?}",
        );
    }

    /// The canonical revocation tree honours the fixed-depth circuit capacity:
    /// a set within capacity builds; a set over capacity is refused (we never
    /// silently truncate, which could hide a double-spend).
    #[test]
    fn revocation_tree_respects_circuit_capacity() {
        let within: Vec<[u8; 32]> = (0..MAX_REVOCATION_TREE_ENTRIES as u8)
            .map(|i| [i; 32])
            .collect();
        assert!(
            canonical_revocation_tree_for_set(&within).is_ok(),
            "a set at the capacity bound must build",
        );

        let over: Vec<[u8; 32]> = (0..=MAX_REVOCATION_TREE_ENTRIES as u8)
            .map(|i| [i; 32])
            .collect();
        match canonical_revocation_tree_for_set(&over) {
            Err(FullTurnProvingError::RevocationCapacityExceeded { have, max }) => {
                assert_eq!(have, over.len());
                assert_eq!(max, MAX_REVOCATION_TREE_ENTRIES);
            }
            other => panic!("expected RevocationCapacityExceeded, got {other:?}"),
        }
    }
}
