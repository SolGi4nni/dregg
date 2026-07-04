//! End-to-end keystone: `SenderAuthorized { PublicRoot }` ENFORCES FOR REAL
//! through the embedded executor, on the honest fire path — not fail-closed.
//!
//! This is the proof that the real STARK-backed `MerkleMembership` verifier is
//! wired into `EmbeddedExecutor`'s underlying `dregg_sdk::AgentRuntime` BY
//! DEFAULT, so an honest issuer turn is genuinely ACCEPTED and a non-member's
//! turn is genuinely REFUSED — at the Poseidon2 / STARK level, not by an
//! executor-side field compare and not by a fail-closed reject-everything stub.
//!
//! The chain under test:
//!
//!   1. A cell carries `StateConstraint::SenderAuthorized { PublicRoot { slot } }`.
//!   2. `slot` is seeded with `single_member_authorized_root(member_pk)` — the
//!      32-byte LE root of the trivial one-leaf Poseidon2 tree whose sole member
//!      is `member_pk` (the honest single-issuer authorized set).
//!   3. A state-changing turn (`Effect::SetField` on a free slot) attaches a
//!      `WitnessKind::MerklePath` blob carrying
//!      `single_member_membership_proof(member_pk)`.
//!   4. The executor builds a `WitnessBundle` from `action.witness_blobs` + its
//!      `witnessed_registry` (the REAL one, by default) and feeds the proof to
//!      `MerkleMembershipStarkVerifier`. The candidate the verifier checks is the
//!      TARGET CELL's public key (`EvalContext.sender`).
//!
//! Because the verifier compresses the candidate pk to the membership leaf and
//! checks a genuine Poseidon2 Merkle path to the slot's root, only a cell whose
//! pk is actually the set member passes — a different signer (non-member) is
//! rejected even if it presents the member's own valid proof (the proof binds
//! the member's leaf, not the candidate's).
//!
//! Encoding convention (shared prover/verifier, see
//! `dregg_turn::executor::membership_verifier`):
//!   * leaf  = `compress(pk)` = `dregg_commit::typed::compress_member(pk)` — THE
//!            canonical chip-native compress (lane 0 of the arity-16 `node8`
//!            absorb over `canonical_32_to_felts_8(pk) ‖ 0⁸`)
//!   * root  = `root_felt_from_slot(slot)` = the felt in the slot's low 4 LE bytes
//!   * tree  = single member at position 0 of a depth-2 zero-sibling-padded tree;
//!            `single_member_authorized_root` and `single_member_membership_proof`
//!            are both derived from that one tree so they are mutually consistent.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthorizedSet, CellProgram, EmbeddedExecutor,
    StateConstraint, field_from_u64,
};
use dregg_turn::action::{WitnessBlob, WitnessKind};
use dregg_turn::executor::{single_member_authorized_root, single_member_membership_proof};

/// Slot holding the authorized-set root (the `PublicRoot { set_root_index }`).
const AUTH_ROOT_SLOT: u8 = 4;
/// A free slot the firing turn mutates (so a SetField actually runs and triggers
/// the per-cell `SenderAuthorized` evaluation). Distinct from the root slot so we
/// never disturb the published root.
const FREE_SLOT: u8 = 7;

fn make_cclerk(fed: u8) -> AppCipherclerk {
    AppCipherclerk::new(AgentCipherclerk::new(), [fed; 32])
}

/// Install `SenderAuthorized { PublicRoot { AUTH_ROOT_SLOT } }` on `cell_id`'s
/// program and seed `AUTH_ROOT_SLOT` with the single-member root for `member_pk`.
fn arm_sender_gate(
    exec: &EmbeddedExecutor,
    cell_id: dregg_app_framework::CellId,
    member_pk: [u8; 32],
) {
    let root = single_member_authorized_root(&member_pk);
    exec.with_ledger_mut(|ledger| {
        if let Some(cell) = ledger.get_mut(&cell_id) {
            cell.state.fields[AUTH_ROOT_SLOT as usize] = root;
            cell.program = CellProgram::Predicate(vec![StateConstraint::SenderAuthorized {
                set: AuthorizedSet::PublicRoot {
                    set_root_index: AUTH_ROOT_SLOT,
                },
            }]);
        }
    });
}

/// A self-action that writes `FREE_SLOT := value` and carries `proof` as a
/// `MerklePath` witness blob. The witness blob is attached BEFORE the final sign
/// (re-signing via `sign_action`) so the action is signed in its complete shape —
/// matching the established `coverage_state_constraints` witness idiom. (The
/// canonical signing message itself does not hash `witness_blobs` — the witness-
/// circularity carve-out, since a proof can't commit to a message containing
/// itself — so the re-sign is belt-and-suspenders, not load-bearing.)
fn witnessed_setfield(
    cclerk: &AppCipherclerk,
    value: u64,
    proof: Vec<u8>,
) -> dregg_app_framework::Action {
    use dregg_app_framework::Effect;
    let mut action = cclerk.make_self_action(
        "set_field",
        vec![Effect::SetField {
            cell: cclerk.cell_id(),
            index: FREE_SLOT as usize,
            value: field_from_u64(value),
        }],
    );
    action.witness_blobs = vec![WitnessBlob::new(WitnessKind::MerklePath, proof)];
    cclerk.sign_action(action)
}

/// ACCEPT: the agent IS the sole member of its own cell's authorized set. Its
/// genuine single-member membership proof verifies against the seeded root, so a
/// state-changing turn is COMMITTED through the embedded real-registry executor.
#[test]
fn embedded_authorized_member_accepts() {
    let cclerk = make_cclerk(0x11);
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let member_pk = cclerk.public_key().0;

    arm_sender_gate(&exec, cclerk.cell_id(), member_pk);

    let proof = single_member_membership_proof(&member_pk);
    let action = witnessed_setfield(&cclerk, 1, proof);

    let receipt = exec
        .submit_action(&cclerk, action)
        .expect("authorized member's genuine membership STARK must be ACCEPTED end-to-end");
    assert_ne!(
        receipt.turn_hash, [0u8; 32],
        "committed turn has a real hash"
    );

    // The state change landed: FREE_SLOT now holds 1.
    let after = exec
        .with_ledger_mut(|l| l.get(&cclerk.cell_id()).unwrap().state.fields[FREE_SLOT as usize]);
    assert_eq!(
        after,
        field_from_u64(1),
        "the accepted turn mutated the slot"
    );
}

/// REJECT: a DIFFERENT agent (not the set member) acts on its own cell, whose
/// `SenderAuthorized` root is seeded to the MEMBER's root. Even though the agent
/// presents the member's own valid proof, the verifier's candidate is THIS cell's
/// pk (a non-member), whose compressed leaf has no Poseidon2 path to the member's
/// root — so the STARK rejects and the turn is REFUSED. This is the soundness
/// tooth: a stolen proof cannot authorize a non-member.
#[test]
fn embedded_non_member_rejected_at_stark_level() {
    // The honest member (whose root we publish) and a separate non-member agent.
    let member = make_cclerk(0x22);
    let member_pk = member.public_key().0;

    let intruder = make_cclerk(0x23);
    let intruder_exec = EmbeddedExecutor::new(&intruder, "default");
    assert_ne!(member_pk, intruder.public_key().0, "distinct agents");

    // Arm the INTRUDER's own cell with the MEMBER's authorized-set root.
    arm_sender_gate(&intruder_exec, intruder.cell_id(), member_pk);

    // The intruder presents the member's genuine proof (the strongest forge).
    let stolen_proof = single_member_membership_proof(&member_pk);
    let action = witnessed_setfield(&intruder, 1, stolen_proof);

    let err = intruder_exec
        .submit_action(&intruder, action)
        .expect_err("a non-member must be REFUSED even presenting the member's valid proof");
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("member")
            || msg.contains("sender")
            || msg.contains("program")
            || msg.contains("witness"),
        "refusal must cite the sender-membership gate, got: {msg}"
    );

    // The intruder's free slot never moved.
    let after = intruder_exec
        .with_ledger_mut(|l| l.get(&intruder.cell_id()).unwrap().state.fields[FREE_SLOT as usize]);
    assert_eq!(after, [0u8; 32], "the refused turn did not mutate state");
}

/// The default IS the real registry — proven by opting OUT: with the registry
/// swapped to `empty()`, even the genuine member is REFUSED (the `MerkleMembership`
/// slot is absent → `AuthModeNotRegistered`-class fail-closed). This is the
/// control that the ACCEPT above is load-bearing on the real-registry default,
/// not on some unrelated permissive path.
#[test]
fn empty_registry_fails_closed_even_for_member() {
    let cclerk = make_cclerk(0x33);
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let member_pk = cclerk.public_key().0;

    arm_sender_gate(&exec, cclerk.cell_id(), member_pk);

    // Opt out of the real registry.
    exec.set_witnessed_registry(dregg_cell::WitnessedPredicateRegistry::empty());

    let proof = single_member_membership_proof(&member_pk);
    let action = witnessed_setfield(&cclerk, 1, proof);

    let err = exec.submit_action(&cclerk, action).expect_err(
        "with an empty registry, SenderAuthorized must fail closed even for the member",
    );
    let _ = err; // any rejection suffices; the point is it does NOT commit.

    let after = exec
        .with_ledger_mut(|l| l.get(&cclerk.cell_id()).unwrap().state.fields[FREE_SLOT as usize]);
    assert_eq!(after, [0u8; 32], "fail-closed: no state change");
}
