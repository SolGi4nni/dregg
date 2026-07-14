use super::*;
use crate::preconditions::EvalContext;

fn ctx_at(height: u64) -> EvalContext {
    EvalContext {
        block_height: height,
        ..Default::default()
    }
}

fn ctx_sender(sender: [u8; 32], epoch_count: u32) -> EvalContext {
    EvalContext {
        sender: Some(sender),
        sender_epoch_count: epoch_count,
        ..Default::default()
    }
}

/// Mock adjacency verifier for cell-side NonMembership program tests. The
/// REAL Merkle-adjacency STARK lives in `dregg-circuit`/`dregg-turn`
/// (`CircuitNeighborAdjacencyVerifier`, exercised end-to-end by
/// `dregg_turn::executor::membership_verifier`'s
/// `e2e_consecutive_non_membership_accepts`). Here we only need to drive the
/// cell program's renunciation plumbing through a registry that HAS an
/// adjacency verifier installed (the post-hardening positive path), so the
/// mock accepts the canonical `b"ADJ-OK"` blob for any `lower < upper`.
struct ProgramMockAdjacency;
impl crate::predicate::NeighborAdjacencyVerifier for ProgramMockAdjacency {
    fn verify_adjacency(
        &self,
        _root: &[u8; 32],
        lower: &[u8; 32],
        upper: &[u8; 32],
        adjacency_proof: &[u8],
    ) -> Result<(), String> {
        if adjacency_proof != b"ADJ-OK" {
            return Err("mock: missing/invalid adjacency proof".into());
        }
        if lower >= upper {
            return Err("mock: lower !< upper".into());
        }
        Ok(())
    }
}

/// A stub registry with the mock adjacency verifier installed on
/// NonMembership/BlindedSet — mirrors the production turn-layer wiring
/// (`registry_with_real_verifiers`) so genuine renunciations verify.
fn registry_with_mock_adjacency() -> crate::predicate::WitnessedPredicateRegistry {
    use crate::predicate::{
        CredentialSetMembershipVerifier, NeighborAdjacencyVerifier,
        SortedNeighborNonMembershipVerifier, WitnessedPredicateRegistry,
    };
    use std::sync::Arc;
    let mut r = WitnessedPredicateRegistry::with_stubs();
    let adj: Arc<dyn NeighborAdjacencyVerifier> = Arc::new(ProgramMockAdjacency);
    r.register_builtin(Arc::new(
        SortedNeighborNonMembershipVerifier::with_adjacency(adj.clone()),
    ));
    r.register_builtin(Arc::new(CredentialSetMembershipVerifier::with_adjacency(
        adj,
    )));
    r
}

/// Build a v2 non-membership proof carrying the mock-accepted adjacency
/// blob, bound to `commitment`.
fn honest_renunciation_v2(commitment: &[u8; 32], lower: [u8; 32], upper: [u8; 32]) -> Vec<u8> {
    crate::predicate::NonMembershipProofV2 {
        neighbor: crate::predicate::NonMembershipNeighborProof::new(commitment, lower, upper),
        adjacency_proof: b"ADJ-OK".to_vec(),
    }
    .to_bytes()
}

fn ctx_preimage(p: [u8; 32]) -> EvalContext {
    EvalContext {
        revealed_preimage: Some(p),
        ..Default::default()
    }
}

// ── Existing variants (regression) ───────────────────────────────────

#[test]
fn no_program_backward_compat() {
    let p = CellProgram::None;
    let s = CellState::new(100);
    assert!(p.evaluate(&s, None, None).is_ok());
}

#[test]
fn field_equals_pass_and_fail() {
    let p = CellProgram::Predicate(vec![StateConstraint::FieldEquals {
        index: 0,
        value: field_from_u64(42),
    }]);
    let mut s = CellState::new(0);
    s.fields[0] = field_from_u64(42);
    assert!(p.evaluate(&s, None, None).is_ok());
    s.fields[0] = field_from_u64(99);
    assert!(p.evaluate(&s, None, None).is_err());
}

#[test]
fn immutable_round_trip() {
    let p = CellProgram::Predicate(vec![StateConstraint::Immutable { index: 3 }]);
    let mut old = CellState::new(0);
    old.fields[3] = field_from_u64(77);
    let mut new_s = old.clone();
    assert!(p.evaluate(&new_s, Some(&old), None).is_ok());
    new_s.fields[3] = field_from_u64(88);
    assert!(p.evaluate(&new_s, Some(&old), None).is_err());
}

#[test]
fn immutable_no_old_state_init_path() {
    let p = CellProgram::Predicate(vec![StateConstraint::Immutable { index: 3 }]);
    let mut s = CellState::new(0);
    s.fields[3] = field_from_u64(77);
    assert!(p.evaluate(&s, None, None).is_ok());
}

#[test]
fn immutable_no_old_state_with_history_fails_closed() {
    let p = CellProgram::Predicate(vec![StateConstraint::Immutable { index: 3 }]);
    let mut s = CellState::new(0);
    s.fields[3] = field_from_u64(77);
    s.set_nonce(5);
    let err = p.evaluate(&s, None, None).unwrap_err();
    assert!(matches!(
        err,
        ProgramError::TransitionCheckRequiresOldState { .. }
    ));
}

// ── Heap-keyed atoms (HeapField — THE ROTATION's app-state lane) ─────
//
// Per lifted atom: ADMIT + REFUSE + ABSENCE, mirroring the Lean
// theorems in metatheory/Dregg2/Exec/Program.lean (evalHeap_*_iff,
// evalHeap_*_absent_*, _pinned, _frozen). The heap key sits well above
// STATE_SLOTS so every read goes through fields_map.

const HK: u64 = 99;

fn heap_prog(atom: HeapAtom) -> CellProgram {
    CellProgram::Predicate(vec![StateConstraint::HeapField { key: HK, atom }])
}

fn heap_state(v: Option<u64>) -> CellState {
    let mut s = CellState::new(0);
    if let Some(v) = v {
        assert!(s.set_field_ext(HK, field_from_u64(v)));
    }
    s
}

fn heap_eval(
    p: &CellProgram,
    new: &CellState,
    old: Option<&CellState>,
) -> Result<(), ProgramError> {
    p.evaluate_full(
        new,
        old,
        None,
        &TransitionMeta::wildcard(),
        &WitnessBundle::empty(),
    )
}

#[test]
fn heap_equals_admit_refuse_absent() {
    let p = heap_prog(HeapAtom::Equals {
        value: field_from_u64(5),
    });
    assert!(heap_eval(&p, &heap_state(Some(5)), Some(&heap_state(None))).is_ok());
    assert!(heap_eval(&p, &heap_state(Some(6)), Some(&heap_state(None))).is_err());
    // Absent post-state refuses (evalHeap_equals_absent_refuses).
    assert!(heap_eval(&p, &heap_state(None), Some(&heap_state(None))).is_err());
    // Absent ≠ present-zero on the heap: Equals{0} still refuses absence.
    let p0 = heap_prog(HeapAtom::Equals { value: FIELD_ZERO });
    assert!(heap_eval(&p0, &heap_state(None), Some(&heap_state(None))).is_err());
    assert!(heap_eval(&p0, &heap_state(Some(0)), Some(&heap_state(None))).is_ok());
}

#[test]
fn heap_gte_lte_admit_refuse_absent() {
    let ge = heap_prog(HeapAtom::Gte {
        value: field_from_u64(10),
    });
    assert!(heap_eval(&ge, &heap_state(Some(10)), None).is_ok());
    assert!(heap_eval(&ge, &heap_state(Some(9)), None).is_err());
    assert!(heap_eval(&ge, &heap_state(None), None).is_err());
    let le = heap_prog(HeapAtom::Lte {
        value: field_from_u64(10),
    });
    assert!(heap_eval(&le, &heap_state(Some(10)), None).is_ok());
    assert!(heap_eval(&le, &heap_state(Some(11)), None).is_err());
    assert!(heap_eval(&le, &heap_state(None), None).is_err());
}

#[test]
fn heap_immutable_first_write_pin_erase() {
    let p = heap_prog(HeapAtom::Immutable);
    // Absent-old: the FIRST write is free (evalHeap_immutable_absent_old_admits)
    // — including via a missing old_state (the Lean empty record).
    assert!(heap_eval(&p, &heap_state(Some(7)), Some(&heap_state(None))).is_ok());
    assert!(heap_eval(&p, &heap_state(Some(7)), None).is_ok());
    // Present-old PINS (evalHeap_immutable_pinned): unchanged admits…
    assert!(heap_eval(&p, &heap_state(Some(7)), Some(&heap_state(Some(7)))).is_ok());
    // …a flip refuses…
    assert!(heap_eval(&p, &heap_state(Some(8)), Some(&heap_state(Some(7)))).is_err());
    // …and ERASURE refuses (evalHeap_immutable_erase_refused).
    assert!(heap_eval(&p, &heap_state(None), Some(&heap_state(Some(7)))).is_err());
}

#[test]
fn heap_write_once_then_frozen() {
    let p = heap_prog(HeapAtom::WriteOnce);
    // Absent-old and zero-old admit (evalHeap_writeOnce_absent/zero_admits).
    assert!(heap_eval(&p, &heap_state(Some(9)), Some(&heap_state(None))).is_ok());
    assert!(heap_eval(&p, &heap_state(Some(9)), Some(&heap_state(Some(0)))).is_ok());
    // A written (nonzero) key freezes (evalHeap_writeOnce_frozen):
    assert!(heap_eval(&p, &heap_state(Some(9)), Some(&heap_state(Some(9)))).is_ok());
    assert!(heap_eval(&p, &heap_state(Some(1)), Some(&heap_state(Some(9)))).is_err());
    assert!(heap_eval(&p, &heap_state(None), Some(&heap_state(Some(9)))).is_err());
}

#[test]
fn heap_monotonic_no_init_escape() {
    let p = heap_prog(HeapAtom::Monotonic);
    assert!(heap_eval(&p, &heap_state(Some(2)), Some(&heap_state(Some(1)))).is_ok());
    assert!(heap_eval(&p, &heap_state(Some(2)), Some(&heap_state(Some(2)))).is_ok());
    assert!(heap_eval(&p, &heap_state(Some(1)), Some(&heap_state(Some(2)))).is_err());
    // ABSENT-old refuses — deliberately NO init escape on the heap
    // (evalHeap_monotonic_absent_old_refuses), including a missing
    // old_state entirely (≠ the slot Monotonic nonce-0 carve-out).
    assert!(heap_eval(&p, &heap_state(Some(2)), Some(&heap_state(None))).is_err());
    assert!(heap_eval(&p, &heap_state(Some(2)), None).is_err());
    // Absent-new refuses (a monotone key cannot be erased).
    assert!(heap_eval(&p, &heap_state(None), Some(&heap_state(Some(1)))).is_err());
}

#[test]
fn heap_strict_monotonic_admit_refuse_absent() {
    let p = heap_prog(HeapAtom::StrictMonotonic);
    assert!(heap_eval(&p, &heap_state(Some(2)), Some(&heap_state(Some(1)))).is_ok());
    // The equality edge Monotonic admits and StrictMonotonic refuses.
    assert!(heap_eval(&p, &heap_state(Some(2)), Some(&heap_state(Some(2)))).is_err());
    assert!(heap_eval(&p, &heap_state(Some(2)), Some(&heap_state(None))).is_err());
    assert!(heap_eval(&p, &heap_state(None), Some(&heap_state(Some(1)))).is_err());
}

#[test]
fn heap_member_of_and_range_admit_refuse_absent() {
    let m = heap_prog(HeapAtom::MemberOf { set: vec![1, 2, 3] });
    assert!(heap_eval(&m, &heap_state(Some(2)), None).is_ok());
    assert!(heap_eval(&m, &heap_state(Some(9)), None).is_err());
    assert!(heap_eval(&m, &heap_state(None), None).is_err());
    let r = heap_prog(HeapAtom::InRangeTwoSided { lo: 100, hi: 200 });
    assert!(heap_eval(&r, &heap_state(Some(150)), None).is_ok());
    assert!(heap_eval(&r, &heap_state(Some(99)), None).is_err());
    assert!(heap_eval(&r, &heap_state(None), None).is_err());
}

#[test]
fn heap_delta_bounded_admit_refuse_absent() {
    let p = heap_prog(HeapAtom::DeltaBounded { d: 5 });
    assert!(heap_eval(&p, &heap_state(Some(104)), Some(&heap_state(Some(100)))).is_ok());
    assert!(heap_eval(&p, &heap_state(Some(96)), Some(&heap_state(Some(100)))).is_ok());
    assert!(heap_eval(&p, &heap_state(Some(110)), Some(&heap_state(Some(100)))).is_err());
    assert!(heap_eval(&p, &heap_state(Some(90)), Some(&heap_state(Some(100)))).is_err());
    assert!(heap_eval(&p, &heap_state(Some(3)), Some(&heap_state(None))).is_err());
    assert!(heap_eval(&p, &heap_state(None), Some(&heap_state(Some(3)))).is_err());
}

#[test]
fn heap_delta_equals_exact_offby_one_absent() {
    // EXACT signed delta: new - old == d. Twin of the Lean
    // `HeapAtom.deltaEquals` (lifts to `fieldDelta`, both-present-refuse).
    let up = heap_prog(HeapAtom::DeltaEquals { d: 4 });
    // exact +4 ACCEPTS.
    assert!(heap_eval(&up, &heap_state(Some(104)), Some(&heap_state(Some(100)))).is_ok());
    // off-by-one (either direction) REJECTS — DeltaBounded would have admitted
    // both; DeltaEquals pins the precise delta.
    assert!(heap_eval(&up, &heap_state(Some(105)), Some(&heap_state(Some(100)))).is_err());
    assert!(heap_eval(&up, &heap_state(Some(103)), Some(&heap_state(Some(100)))).is_err());
    // a NEGATIVE exact delta.
    let down = heap_prog(HeapAtom::DeltaEquals { d: -3 });
    assert!(heap_eval(&down, &heap_state(Some(97)), Some(&heap_state(Some(100)))).is_ok());
    assert!(heap_eval(&down, &heap_state(Some(98)), Some(&heap_state(Some(100)))).is_err());
    // BOTH-present fail-closed (no init/nonce escape): absent-old AND absent-new
    // both REFUSE, including a missing old_state entirely.
    assert!(heap_eval(&up, &heap_state(Some(4)), Some(&heap_state(None))).is_err());
    assert!(heap_eval(&up, &heap_state(Some(4)), None).is_err());
    assert!(heap_eval(&up, &heap_state(None), Some(&heap_state(Some(0)))).is_err());
}

// ── Cross-KEY heap relation (HeapFieldLteOther) ─────────────────────────
//
// Two heap keys compared in the post-state: new[key] <= new[other_key] +
// delta. The heap twin of the slot FieldLteOther, fail-closed on an absent
// key. Mirrors the Lean `heapFieldLteOther` / `evalHeapRel_fieldLteOther_iff`.

const HK_A: u64 = 130; // both well above STATE_SLOTS ⇒ fields_map reads.
const HK_B: u64 = 131;

fn cross_key_state(a: Option<u64>, b: Option<u64>) -> CellState {
    let mut s = CellState::new(0);
    if let Some(a) = a {
        assert!(s.set_field_ext(HK_A, field_from_u64(a)));
    }
    if let Some(b) = b {
        assert!(s.set_field_ext(HK_B, field_from_u64(b)));
    }
    s
}

#[test]
fn heap_field_lte_other_capacity_and_underflow() {
    // CAPACITY-style bound: new[A] <= new[B] + delta.
    let cap = CellProgram::Predicate(vec![StateConstraint::HeapFieldLteOther {
        key: HK_A,
        other_key: HK_B,
        delta: 2,
    }]);
    let ev = |s: &CellState| {
        cap.evaluate_full(
            s,
            None,
            None,
            &TransitionMeta::wildcard(),
            &WitnessBundle::empty(),
        )
    };
    // 5 <= 3 + 2 = 5 : boundary ACCEPTS.
    assert!(ev(&cross_key_state(Some(5), Some(3))).is_ok());
    // 6 <= 3 + 2 = 5 : VIOLATION rejects.
    assert!(ev(&cross_key_state(Some(6), Some(3))).is_err());
    // absent EITHER operand fails closed.
    assert!(ev(&cross_key_state(None, Some(3))).is_err());
    assert!(ev(&cross_key_state(Some(5), None)).is_err());
    assert!(ev(&cross_key_state(None, None)).is_err());

    // NO-UNDERFLOW bound with delta 0: new[A] <= new[B].
    let uf = CellProgram::Predicate(vec![StateConstraint::HeapFieldLteOther {
        key: HK_A,
        other_key: HK_B,
        delta: 0,
    }]);
    let ev0 = |s: &CellState| {
        uf.evaluate_full(
            s,
            None,
            None,
            &TransitionMeta::wildcard(),
            &WitnessBundle::empty(),
        )
    };
    assert!(ev0(&cross_key_state(Some(4), Some(4))).is_ok());
    assert!(ev0(&cross_key_state(Some(3), Some(4))).is_ok());
    assert!(ev0(&cross_key_state(Some(5), Some(4))).is_err());
}

#[test]
fn heap_atom_composes_under_heyting_fragment() {
    // Not(HeapField) is the clean complement (heap atoms only ever emit
    // ConstraintViolated, never a structural error, so the Heyting Not
    // short-circuit applies): refuse-the-pin becomes admit.
    let not_eq = CellProgram::Predicate(vec![StateConstraint::AnyOf {
        variants: vec![SimpleStateConstraint::Not(Box::new(
            SimpleStateConstraint::HeapField {
                key: HK,
                atom: HeapAtom::Equals {
                    value: field_from_u64(5),
                },
            },
        ))],
    }]);
    assert!(heap_eval(&not_eq, &heap_state(Some(6)), None).is_ok());
    assert!(heap_eval(&not_eq, &heap_state(Some(5)), None).is_err());
    // Absent inner ⇒ inner refuses ⇒ Not admits (the Lean !false).
    assert!(heap_eval(&not_eq, &heap_state(None), None).is_ok());

    // The per-HEAP-field actor binding: AnyOf[HeapField{Immutable},
    // SenderIs{pk}] — the heap twin of the polis approval-slot tooth
    // (Lean heapActorBound_flip_requires_sender).
    let bound_pk = [0xAB; 32];
    let bound = CellProgram::Predicate(vec![StateConstraint::AnyOf {
        variants: vec![
            SimpleStateConstraint::HeapField {
                key: HK,
                atom: HeapAtom::Immutable,
            },
            SimpleStateConstraint::SenderIs { pk: bound_pk },
        ],
    }]);
    let old = heap_state(Some(1));
    let flipped = heap_state(Some(2));
    // The bound sender flips the heap key: admitted.
    assert!(
        bound
            .evaluate_full(
                &flipped,
                Some(&old),
                Some(&ctx_sender(bound_pk, 0)),
                &TransitionMeta::wildcard(),
                &WitnessBundle::empty(),
            )
            .is_ok()
    );
    // A stranger flipping the heap key: refused.
    assert!(
        bound
            .evaluate_full(
                &flipped,
                Some(&old),
                Some(&ctx_sender([0x57; 32], 0)),
                &TransitionMeta::wildcard(),
                &WitnessBundle::empty(),
            )
            .is_err()
    );
    // A stranger leaving the key alone: admitted (the ceremony stays open).
    assert!(
        bound
            .evaluate_full(
                &old,
                Some(&old),
                Some(&ctx_sender([0x57; 32], 0)),
                &TransitionMeta::wildcard(),
                &WitnessBundle::empty(),
            )
            .is_ok()
    );
}

#[test]
fn heap_and_slot_constraints_coexist_in_one_program() {
    // One predicate carrying a SLOT tooth and a HEAP tooth — each bites
    // independently (the Lean mixedHeapProgram twin).
    let p = CellProgram::Predicate(vec![
        StateConstraint::Monotonic { index: 0 },
        StateConstraint::HeapField {
            key: HK,
            atom: HeapAtom::Monotonic,
        },
    ]);
    let mut old = heap_state(Some(5));
    old.fields[0] = field_from_u64(1);
    // Both advance: admitted.
    let mut good = heap_state(Some(9));
    good.fields[0] = field_from_u64(2);
    assert!(heap_eval(&p, &good, Some(&old)).is_ok());
    // Heap tooth bites (slot fine, heap decreases).
    let mut bad_heap = heap_state(Some(3));
    bad_heap.fields[0] = field_from_u64(2);
    assert!(heap_eval(&p, &bad_heap, Some(&old)).is_err());
    // Slot tooth still bites (heap fine, slot decreases). Slot 0 of
    // `old` is 1; new slot 0 = 0 < 1.
    let bad_slot = heap_state(Some(9));
    assert!(heap_eval(&p, &bad_slot, Some(&old)).is_err());
}

// ── Aggregate-over-a-collection (CollectionAggregate — the heap/layout
//    rung; LAW #1 mirror of metatheory/Dregg2/Exec/Collections.lean) ─────
//
// The Lean §6/§6.1/§7 biting teeth, transported to the felt heap layout:
// a collection lives under `(collection_id, key)` with element `i` at the
// stride `[i*stride .. i*stride+stride)`. The council elements are
// `{voter: offset 0, vote: offset 1}` (the Lean `approver id v =
// {voter := sym id, vote := int v}`); `approved` = `vote == 1` (votedYes);
// `key_offset = 0` (the voter identity). The 3-of-5 ACCEPTS three distinct
// approvers, REFUSES sub-quorum, REFUSES the duplicate-padded forge (where
// a naive CountSatGe IS fooled — proven below), REFUSES the unbound forge,
// and FAILS CLOSED on an absent collection.

const COLL_ID: u32 = 7;
/// Element width: offset 0 = voter id (key), offset 1 = vote.
const COLL_STRIDE: u32 = 2;
/// Element-relative offsets, mirroring the Lean named fields.
const VOTER_OFF: u32 = 0;
const VOTE_OFF: u32 = 1;

/// Lay an approver collection (`(voter_id, vote)` pairs) into a fresh
/// cell's heap under `COLL_ID`, element `i` at stride `i*COLL_STRIDE`. The
/// Rust mirror of building the Lean `council3of5`/`councilSub`/… lists. A
/// voter id of 0 is written as a PRESENT zero-valued key (the element
/// exists; its identity key is 0) — presence is by map-membership, exactly
/// as `approver 0 _` is a real list element in Lean.
fn council_state(approvers: &[(u64, u64)]) -> CellState {
    let mut s = CellState::new(0);
    for (i, (voter, vote)) in approvers.iter().enumerate() {
        let base = (i as u32) * COLL_STRIDE;
        assert!(s.set_heap(COLL_ID, base + VOTER_OFF, field_from_u64(*voter)));
        assert!(s.set_heap(COLL_ID, base + VOTE_OFF, field_from_u64(*vote)));
    }
    s
}

/// `votedYes` per element: the `vote` field (offset 1) equals 1.
fn voted_yes() -> ElemPredAtom {
    ElemPredAtom::FieldEquals {
        offset: VOTE_OFF,
        value: field_from_u64(1),
    }
}

/// A `CollectionAggregate` program over `COLL_ID` carrying `pred`, with
/// `fuel` large enough to read the whole council.
fn coll_prog(pred: CollPred) -> CellProgram {
    CellProgram::Predicate(vec![StateConstraint::CollectionAggregate {
        collection_id: COLL_ID,
        stride: COLL_STRIDE,
        fuel: 16,
        pred,
    }])
}

fn coll_eval(p: &CellProgram, new: &CellState) -> Result<(), ProgramError> {
    p.evaluate_full(
        new,
        None,
        None,
        &TransitionMeta::wildcard(),
        &WitnessBundle::empty(),
    )
}

#[test]
fn council_3of5_accepts_refuses_subquorum_dupforge_unbound() {
    // The council gate at threshold 3 (Lean `mOfNDistinct 3 "voter"
    // votedYes`).
    let council = coll_prog(CollPred::MOfNDistinct {
        m: 3,
        key_offset: VOTER_OFF,
        approved: voted_yes(),
    });

    // ACCEPT — voters 0,1,2 vote YES (distinct); 3,4 vote NO. 3 distinct
    // approvers reach the quorum (Lean `council_accepts`, N=5 past the
    // documented N≤3 fixed-slot cap).
    let ok = council_state(&[(0, 1), (1, 1), (2, 1), (3, 0), (4, 0)]);
    assert!(coll_eval(&council, &ok).is_ok());

    // REFUSE (sub-quorum) — only voters 0,1 vote YES ⇒ 2 distinct < 3
    // (Lean `council_subquorum_refuses`).
    let sub = council_state(&[(0, 1), (1, 1), (2, 0), (3, 0), (4, 0)]);
    assert!(coll_eval(&council, &sub).is_err());

    // REFUSE (DUPLICATE-PADDED forge) — voter 0 listed 3×, all YES. The
    // raw satisfying-count is 3, but there is ONE distinct identity ⇒ the
    // distinct quorum is 1 ⇒ refuses (Lean `council_dup_forge_refuses`,
    // the anti-fake keystone).
    let dup = council_state(&[(0, 1), (0, 1), (0, 1), (3, 0), (4, 0)]);
    assert!(coll_eval(&council, &dup).is_err());

    // REFUSE (UNBOUND forge) — voters 0,1 genuinely vote YES; a THIRD
    // padding element (voter 7) votes NO. It fails `approved`, is filtered
    // before the count ⇒ 2 distinct < 3 ⇒ refuses (Lean
    // `council_unbound_forge_refuses`).
    let unbound = council_state(&[(0, 1), (1, 1), (7, 0)]);
    assert!(coll_eval(&council, &unbound).is_err());
}

#[test]
fn council_dup_forge_raw_vs_distinct_naive_countsatge_fooled() {
    // The forge's anatomy as a discriminator (Lean
    // `council_dup_forge_raw_vs_distinct`): the SAME duplicate-padded
    // collection that a naive `CountSatGe 3` ADMITS, the distinctness-
    // enforced `MOfNDistinct 3` REFUSES. Distinctness — not the raw count
    // — is the load-bearing gate, and the naive aggregate is genuinely
    // fooled where the council is not.
    let dup = council_state(&[(0, 1), (0, 1), (0, 1), (3, 0), (4, 0)]);

    // Naive raw-count aggregate IS fooled: raw satisfying-count is 3.
    let naive = coll_prog(CollPred::CountSatGe {
        m: 3,
        p: voted_yes(),
    });
    assert!(
        coll_eval(&naive, &dup).is_ok(),
        "naive CountSatGe must be fooled by the duplicate-padded forge \
             (raw count 3), so the council's distinctness is load-bearing"
    );

    // The distinct council is NOT fooled: 1 distinct identity < 3.
    let council = coll_prog(CollPred::MOfNDistinct {
        m: 3,
        key_offset: VOTER_OFF,
        approved: voted_yes(),
    });
    assert!(coll_eval(&council, &dup).is_err());

    // And on the HONEST council the two agree (3 distinct == raw 3).
    let ok = council_state(&[(0, 1), (1, 1), (2, 1), (3, 0), (4, 0)]);
    assert!(coll_eval(&naive, &ok).is_ok());
    assert!(coll_eval(&council, &ok).is_ok());
}

#[test]
fn collection_absent_fails_closed() {
    // Fail-closed entry (Lean `collectionAggregate_absent_refuses` /
    // `collectionCouncil_absent_refuses`): a cell with NO collection under
    // COLL_ID has no element-0 anchor ⇒ `read_collection` is `None` ⇒ the
    // aggregate REFUSES — an aggregate over an absent collection is
    // unevaluable.
    let council = coll_prog(CollPred::MOfNDistinct {
        m: 3,
        key_offset: VOTER_OFF,
        approved: voted_yes(),
    });
    let empty = CellState::new(0);
    assert!(coll_eval(&council, &empty).is_err());
    // Every aggregate shape fails closed on the absent collection.
    assert!(
        coll_eval(
            &coll_prog(CollPred::CountSatGe {
                m: 1,
                p: voted_yes()
            }),
            &empty
        )
        .is_err()
    );
    assert!(
        coll_eval(
            &coll_prog(CollPred::SumOfLe {
                offset: VOTE_OFF,
                bound: 0
            }),
            &empty
        )
        .is_err()
    );
    assert!(coll_eval(&coll_prog(CollPred::AllMembers { p: voted_yes() }), &empty).is_err());
    assert!(
        coll_eval(
            &coll_prog(CollPred::ExistsMember { p: voted_yes() }),
            &empty
        )
        .is_err()
    );
}

#[test]
fn collection_truncates_at_first_gap() {
    // The `readIndexed` fail-closed truncation: the collection is exactly
    // the contiguous present prefix; a hole truncates it (no phantom tail
    // beyond a gap). We place 3 approvers, then SKIP element 3's anchor and
    // place an approver at element 4 — element 4 must NOT be seen, so the
    // gap caps the council at the 3-distinct prefix.
    let council = coll_prog(CollPred::MOfNDistinct {
        m: 4,
        key_offset: VOTER_OFF,
        approved: voted_yes(),
    });
    let mut s = council_state(&[(0, 1), (1, 1), (2, 1)]);
    // Element 4 (base 8) is a fourth distinct approver — but element 3
    // (base 6) is absent, so the read stops at index 3 and never reaches
    // it. A threshold-4 council therefore REFUSES (only 3 visible).
    assert!(s.set_heap(COLL_ID, 4 * COLL_STRIDE + VOTER_OFF, field_from_u64(9)));
    assert!(s.set_heap(COLL_ID, 4 * COLL_STRIDE + VOTE_OFF, field_from_u64(1)));
    assert!(coll_eval(&council, &s).is_err());
    // Threshold 3 over the visible prefix still ACCEPTS — the prefix is
    // intact, only the post-gap tail is dropped.
    let council3 = coll_prog(CollPred::MOfNDistinct {
        m: 3,
        key_offset: VOTER_OFF,
        approved: voted_yes(),
    });
    assert!(coll_eval(&council3, &s).is_ok());
}

#[test]
fn collection_sum_cap_discriminates() {
    // The treasury sum-cap (Lean `sumCap_discriminates`, §6.1): three
    // line-items with `amount` at offset 0 summing to 90. `SumOfLe 100`
    // admits (within budget); `SumOfLe 80` refuses (over budget). A
    // genuine discriminator over arbitrary-N data.
    let ledger = {
        let mut s = CellState::new(0);
        for (i, amt) in [40u64, 30, 20].iter().enumerate() {
            let base = (i as u32) * 1; // stride 1: one `amount` field.
            assert!(s.set_heap(COLL_ID, base, field_from_u64(*amt)));
        }
        s
    };
    let prog = |bound: i64| {
        CellProgram::Predicate(vec![StateConstraint::CollectionAggregate {
            collection_id: COLL_ID,
            stride: 1,
            fuel: 16,
            pred: CollPred::SumOfLe { offset: 0, bound },
        }])
    };
    assert!(coll_eval(&prog(100), &ledger).is_ok());
    assert!(coll_eval(&prog(80), &ledger).is_err());
    // The sum FLOOR discriminates the other way: ≥ 90 holds, ≥ 91 fails.
    let floor = |bound: i64| {
        CellProgram::Predicate(vec![StateConstraint::CollectionAggregate {
            collection_id: COLL_ID,
            stride: 1,
            fuel: 16,
            pred: CollPred::SumOfGe { offset: 0, bound },
        }])
    };
    assert!(coll_eval(&floor(90), &ledger).is_ok());
    assert!(coll_eval(&floor(91), &ledger).is_err());
}

#[test]
fn collection_forall_exists_discriminate() {
    // ∀ / ∃ over the collection (Lean §6.1 `allMembers`/`existsMember`).
    // Ledger items with `amount` at offset 0: {40, 30, 20}.
    let ledger = {
        let mut s = CellState::new(0);
        for (i, amt) in [40u64, 30, 20].iter().enumerate() {
            assert!(s.set_heap(COLL_ID, i as u32, field_from_u64(*amt)));
        }
        s
    };
    let all_ge_1 = coll_prog_strided(
        1,
        CollPred::AllMembers {
            p: ElemPredAtom::FieldGte {
                offset: 0,
                value: field_from_u64(1),
            },
        },
    );
    // Every item ≥ 1 ⇒ ∀ holds.
    assert!(coll_eval(&all_ge_1, &ledger).is_ok());
    // Zero out one item ⇒ ∀ fails (the Lean `:: ledger` zeroed-head twin).
    let mut zeroed = ledger.clone();
    // Prepend a zero by shifting: simplest is to overwrite item 2's amount.
    assert!(zeroed.set_heap(COLL_ID, 2, field_from_u64(0)));
    assert!(coll_eval(&all_ge_1, &zeroed).is_err());

    // ∃ an item > 35 (the 40) ⇒ holds; none > 100 ⇒ fails.
    let any_gt_35 = coll_prog_strided(
        1,
        CollPred::ExistsMember {
            p: ElemPredAtom::FieldGte {
                offset: 0,
                value: field_from_u64(36),
            },
        },
    );
    assert!(coll_eval(&any_gt_35, &ledger).is_ok());
    let any_gt_100 = coll_prog_strided(
        1,
        CollPred::ExistsMember {
            p: ElemPredAtom::FieldGte {
                offset: 0,
                value: field_from_u64(101),
            },
        },
    );
    assert!(coll_eval(&any_gt_100, &ledger).is_err());
}

/// A `CollectionAggregate` program with an explicit stride.
fn coll_prog_strided(stride: u32, pred: CollPred) -> CellProgram {
    CellProgram::Predicate(vec![StateConstraint::CollectionAggregate {
        collection_id: COLL_ID,
        stride,
        fuel: 16,
        pred,
    }])
}

#[test]
fn collection_aggregate_view_round_trips() {
    // The view-projection arm (StateConstraintView::CollectionAggregate):
    // a council projects its threshold + key/approval shape for serving.
    let council = StateConstraint::CollectionAggregate {
        collection_id: COLL_ID,
        stride: COLL_STRIDE,
        fuel: 16,
        pred: CollPred::MOfNDistinct {
            m: 3,
            key_offset: VOTER_OFF,
            approved: voted_yes(),
        },
    };
    match council.to_view() {
        StateConstraintView::CollectionAggregate {
            collection_id,
            pred,
            ..
        } => {
            assert_eq!(collection_id, COLL_ID);
            match pred {
                CollPredView::MOfNDistinct { m, key_offset, .. } => {
                    assert_eq!(m, 3);
                    assert_eq!(key_offset, VOTER_OFF);
                }
                other => panic!("expected MOfNDistinct view, got {other:?}"),
            }
        }
        other => panic!("expected CollectionAggregate view, got {other:?}"),
    }
}

// ── FieldsCollectionAggregate: THE COUNCIL LIFT over the EXECUTOR-REACHABLE
//    user-field map (`_RECORD-LAYER-UPGRADE.md`'s `fields_map`). The
//    `CollectionAggregate` twin whose read source is the map the executor's
//    `SetField { index >= STATE_SLOTS }` effect actually writes — so a
//    large council is reachable end-to-end through a real turn. Same
//    distinctness teeth, only the store differs. ─────────────────────────

/// Base user-map key (>= STATE_SLOTS) the council collection starts at.
const FMAP_BASE: u64 = dregg_cell::state::STATE_SLOTS as u64;

/// Lay an approver collection (`(voter_id, vote)` pairs) into a fresh cell's
/// EXECUTOR-REACHABLE `fields_map` starting at `FMAP_BASE`, element `i` at
/// `FMAP_BASE + i*COLL_STRIDE`. The `fields_map` twin of `council_state`:
/// each write goes through [`CellState::set_field_ext`] (the same accessor
/// the executor's `SetField` path calls for keys `>= STATE_SLOTS`), so the
/// laid-out collection is committed by `fields_root`.
fn fmap_council_state(approvers: &[(u64, u64)]) -> CellState {
    let mut s = CellState::new(0);
    for (i, (voter, vote)) in approvers.iter().enumerate() {
        let base = FMAP_BASE + (i as u64) * (COLL_STRIDE as u64);
        assert!(s.set_field_ext(base + VOTER_OFF as u64, field_from_u64(*voter)));
        assert!(s.set_field_ext(base + VOTE_OFF as u64, field_from_u64(*vote)));
    }
    s
}

/// A `FieldsCollectionAggregate` program over `FMAP_BASE` carrying `pred`.
fn fmap_coll_prog(pred: CollPred) -> CellProgram {
    CellProgram::Predicate(vec![StateConstraint::FieldsCollectionAggregate {
        base: FMAP_BASE,
        stride: COLL_STRIDE,
        fuel: 16,
        pred,
    }])
}

#[test]
fn fmap_council_3of5_accepts_refuses_subquorum_dupforge_unbound() {
    // The council gate at threshold 3, now over the user-field MAP. The
    // SAME distinctness keystone (`MOfNDistinct`) the heap council proves —
    // the `CollPred` evaluator is reused verbatim; only the read source is
    // `fields_map` (executor-reachable) instead of the heap.
    let council = fmap_coll_prog(CollPred::MOfNDistinct {
        m: 3,
        key_offset: VOTER_OFF,
        approved: voted_yes(),
    });

    // ACCEPT — voters 0,1,2 vote YES (distinct); 3,4 NO. 3 distinct ⇒ quorum.
    let ok = fmap_council_state(&[(0, 1), (1, 1), (2, 1), (3, 0), (4, 0)]);
    assert!(coll_eval(&council, &ok).is_ok());

    // REFUSE (sub-quorum) — only 0,1 YES ⇒ 2 distinct < 3.
    let sub = fmap_council_state(&[(0, 1), (1, 1), (2, 0), (3, 0), (4, 0)]);
    assert!(coll_eval(&council, &sub).is_err());

    // REFUSE (DUPLICATE-PADDED forge) — voter 0 listed 3×, all YES ⇒ ONE
    // distinct identity ⇒ refuses (the anti-fake keystone over the map).
    let dup = fmap_council_state(&[(0, 1), (0, 1), (0, 1), (3, 0), (4, 0)]);
    assert!(coll_eval(&council, &dup).is_err());

    // REFUSE (UNBOUND forge) — 0,1 YES; a padding voter 7 votes NO, filtered
    // before the count ⇒ 2 distinct < 3.
    let unbound = fmap_council_state(&[(0, 1), (1, 1), (7, 0)]);
    assert!(coll_eval(&council, &unbound).is_err());
}

#[test]
fn fmap_council_absent_fails_closed() {
    // Fail-closed: a cell with NO collection in its map has no element-0
    // anchor ⇒ `read_collection_fields` is `None` ⇒ the aggregate REFUSES.
    let council = fmap_coll_prog(CollPred::MOfNDistinct {
        m: 1,
        key_offset: VOTER_OFF,
        approved: voted_yes(),
    });
    let empty = CellState::new(0);
    assert!(coll_eval(&council, &empty).is_err());
}

#[test]
fn fmap_council_truncates_at_first_gap() {
    // The `readIndexed` truncation over the map: a hole caps the council at
    // the contiguous present prefix (no phantom tail beyond a gap).
    let mut s = fmap_council_state(&[(0, 1), (1, 1), (2, 1)]);
    // Element 4 (base FMAP_BASE + 4*stride) is a fourth distinct approver,
    // but element 3 is absent, so the read stops at index 3.
    let e4 = FMAP_BASE + 4 * (COLL_STRIDE as u64);
    assert!(s.set_field_ext(e4 + VOTER_OFF as u64, field_from_u64(9)));
    assert!(s.set_field_ext(e4 + VOTE_OFF as u64, field_from_u64(1)));
    let council4 = fmap_coll_prog(CollPred::MOfNDistinct {
        m: 4,
        key_offset: VOTER_OFF,
        approved: voted_yes(),
    });
    assert!(coll_eval(&council4, &s).is_err());
    // Threshold 3 over the visible prefix still ACCEPTS.
    let council3 = fmap_coll_prog(CollPred::MOfNDistinct {
        m: 3,
        key_offset: VOTER_OFF,
        approved: voted_yes(),
    });
    assert!(coll_eval(&council3, &s).is_ok());
}

#[test]
fn fmap_council_view_round_trips() {
    let council = StateConstraint::FieldsCollectionAggregate {
        base: FMAP_BASE,
        stride: COLL_STRIDE,
        fuel: 16,
        pred: CollPred::MOfNDistinct {
            m: 3,
            key_offset: VOTER_OFF,
            approved: voted_yes(),
        },
    };
    let json = serde_json::to_value(council.to_view()).expect("view serializes");
    assert_eq!(
        json.get("kind").and_then(|k| k.as_str()),
        Some("FieldsCollectionAggregate"),
    );
    assert_eq!(json["base"], FMAP_BASE);
    assert_eq!(json["pred"]["m"], 3);
}

// ── New variants ──────────────────────────────────────────────────────

#[test]
fn write_once_first_write_then_frozen() {
    let p = CellProgram::Predicate(vec![StateConstraint::WriteOnce { index: 0 }]);
    // First write: old slot is zero, new is non-zero — allowed.
    let mut old = CellState::new(0);
    let mut new_s = CellState::new(0);
    new_s.fields[0] = field_from_u64(42);
    assert!(p.evaluate(&new_s, Some(&old), None).is_ok());
    // Subsequent write attempt: old is non-zero, new differs — rejected.
    old.fields[0] = field_from_u64(42);
    let mut tampered = old.clone();
    tampered.fields[0] = field_from_u64(99);
    assert!(p.evaluate(&tampered, Some(&old), None).is_err());
    // Unchanged: allowed.
    assert!(p.evaluate(&old, Some(&old), None).is_ok());
}

#[test]
fn monotonic_only_increases() {
    let p = CellProgram::Predicate(vec![StateConstraint::Monotonic { index: 1 }]);
    let mut old = CellState::new(0);
    old.fields[1] = field_from_u64(10);
    let mut new_s = old.clone();
    new_s.fields[1] = field_from_u64(20);
    assert!(p.evaluate(&new_s, Some(&old), None).is_ok());
    new_s.fields[1] = field_from_u64(10);
    assert!(p.evaluate(&new_s, Some(&old), None).is_ok()); // equal allowed
    new_s.fields[1] = field_from_u64(5);
    assert!(p.evaluate(&new_s, Some(&old), None).is_err()); // decrease rejected
}

#[test]
fn strict_monotonic_must_strictly_increase() {
    let p = CellProgram::Predicate(vec![StateConstraint::StrictMonotonic { index: 0 }]);
    let mut old = CellState::new(0);
    old.fields[0] = field_from_u64(10);
    let mut new_s = old.clone();
    new_s.fields[0] = field_from_u64(11);
    assert!(p.evaluate(&new_s, Some(&old), None).is_ok());
    new_s.fields[0] = field_from_u64(10);
    assert!(p.evaluate(&new_s, Some(&old), None).is_err()); // equal rejected
    new_s.fields[0] = field_from_u64(9);
    assert!(p.evaluate(&new_s, Some(&old), None).is_err()); // decrease rejected
}

#[test]
fn bounded_by_requires_witness_armed() {
    let p = CellProgram::Predicate(vec![StateConstraint::BoundedBy {
        index: 0,
        witness_index: 1,
    }]);
    let old = CellState::new(0);
    // Change slot 0 with witness zero → rejected.
    let mut new_s = CellState::new(0);
    new_s.fields[0] = field_from_u64(99);
    assert!(p.evaluate(&new_s, Some(&old), None).is_err());
    // Change slot 0 with witness non-zero → allowed.
    new_s.fields[1] = field_from_u64(1);
    assert!(p.evaluate(&new_s, Some(&old), None).is_ok());
}

#[test]
fn field_delta_exact_step() {
    let p = CellProgram::Predicate(vec![StateConstraint::FieldDelta {
        index: 0,
        delta: field_from_u64(100),
    }]);
    let mut old = CellState::new(0);
    old.fields[0] = field_from_u64(500);
    let mut new_s = old.clone();
    new_s.fields[0] = field_from_u64(600);
    assert!(p.evaluate(&new_s, Some(&old), None).is_ok());
    new_s.fields[0] = field_from_u64(700);
    assert!(p.evaluate(&new_s, Some(&old), None).is_err());
}

#[test]
fn field_delta_in_range() {
    let p = CellProgram::Predicate(vec![StateConstraint::FieldDeltaInRange {
        index: 0,
        min_delta: field_from_u64(0),
        max_delta: field_from_u64(10),
    }]);
    let mut old = CellState::new(0);
    old.fields[0] = field_from_u64(50);
    let mut new_s = old.clone();
    new_s.fields[0] = field_from_u64(55);
    assert!(p.evaluate(&new_s, Some(&old), None).is_ok());
    new_s.fields[0] = field_from_u64(70);
    assert!(p.evaluate(&new_s, Some(&old), None).is_err());
}

#[test]
fn clearance_dominates_root_bound_dominance() {
    // The kernel tooth for the SGM/CWM clearance mandate: an actor whose
    // clearance label DOMINATES the required compartment in the (root-bound)
    // graph admits; an actor that does not is REFUSED; and the stored
    // `root` slot is LOAD-BEARING — a tampered root / substituted graph
    // FAILS CLOSED. The graph mirrors the Lean `charterGraph3`:
    //   officer ⊐ {review, redact, sign},  clerk ⊐ {review}.
    const OFFICER: FieldElement = [0xA0; 32];
    const CLERK: FieldElement = [0xB0; 32];
    const REVIEW: FieldElement = [0x01; 32];
    const REDACT: FieldElement = [0x02; 32];
    const SIGN: FieldElement = [0x03; 32];
    let edges = vec![
        (OFFICER, REVIEW),
        (OFFICER, REDACT),
        (OFFICER, SIGN),
        (CLERK, REVIEW),
    ];
    let root = clearance_graph_root(&edges);

    // slot 0 = actor label, slot 1 = box (required compartment), slot 2 = root.
    let p = CellProgram::Predicate(vec![StateConstraint::ClearanceDominates {
        actor_label_index: 0,
        box_index: 1,
        root_index: 2,
        edges: edges.clone(),
    }]);

    let mk = |actor: FieldElement, box_label: FieldElement, root: FieldElement| {
        let mut s = CellState::new(1);
        s.fields[0] = actor;
        s.fields[1] = box_label;
        s.fields[2] = root;
        s
    };

    // ADMIT: officer dominates redact (officer → redact edge).
    assert!(p.evaluate(&mk(OFFICER, REDACT, root), None, None).is_ok());
    // ADMIT: officer dominates sign.
    assert!(p.evaluate(&mk(OFFICER, SIGN, root), None, None).is_ok());
    // ADMIT (reflexive): clerk holding exactly review dominates review.
    assert!(p.evaluate(&mk(CLERK, REVIEW, root), None, None).is_ok());

    // REJECT: clerk does NOT dominate redact (incomparable — no clerk→redact path).
    assert!(p.evaluate(&mk(CLERK, REDACT, root), None, None).is_err());
    // REJECT: clerk does NOT dominate sign.
    assert!(p.evaluate(&mk(CLERK, SIGN, root), None, None).is_err());

    // ROOT TOOTH: a TAMPERED root slot fails closed even for a dominating
    // actor (the carried graph no longer commits to the stored root).
    let wrong_root = [0xFF; 32];
    assert!(
        p.evaluate(&mk(OFFICER, REDACT, wrong_root), None, None)
            .is_err(),
        "a tampered clearance-graph root must fail closed"
    );

    // GRAPH-SUBSTITUTION TOOTH: a turn that walks an OVER-PERMISSIVE graph
    // (adds clerk → sign) against the cell's ORIGINAL committed root is
    // refused — the substituted graph does not match the stored root.
    let over_permissive = {
        let mut e = edges.clone();
        e.push((CLERK, SIGN));
        e
    };
    let p_sub = CellProgram::Predicate(vec![StateConstraint::ClearanceDominates {
        actor_label_index: 0,
        box_index: 1,
        root_index: 2,
        edges: over_permissive,
    }]);
    assert!(
        p_sub.evaluate(&mk(CLERK, SIGN, root), None, None).is_err(),
        "an over-permissive substituted graph must not match the committed root"
    );
}

#[test]
fn clearance_graph_root_is_order_and_dup_independent() {
    // The commitment is a SET commitment: reordering edges or adding a
    // duplicate edge does NOT change the root (so two encodings of the same
    // graph commit identically), but a genuinely different edge DOES.
    const A: FieldElement = [1u8; 32];
    const B: FieldElement = [2u8; 32];
    const C: FieldElement = [3u8; 32];
    let g1 = vec![(A, B), (B, C)];
    let g2 = vec![(B, C), (A, B)]; // reordered
    let g3 = vec![(A, B), (B, C), (A, B)]; // duplicate edge
    let g4 = vec![(A, B), (A, C)]; // different graph
    assert_eq!(clearance_graph_root(&g1), clearance_graph_root(&g2));
    assert_eq!(clearance_graph_root(&g1), clearance_graph_root(&g3));
    assert_ne!(clearance_graph_root(&g1), clearance_graph_root(&g4));
}

#[test]
fn field_gte_height_uses_ctx() {
    let p = CellProgram::Predicate(vec![StateConstraint::FieldGteHeight {
        index: 0,
        offset: 100,
    }]);
    let mut s = CellState::new(0);
    s.fields[0] = field_from_u64(250);
    // current_height=100, expiry=250, bound=100+100=200, 250>=200 → ok
    assert!(p.evaluate(&s, None, Some(&ctx_at(100))).is_ok());
    // bound=300 (height=200, offset=100): 250<300 → fail
    assert!(p.evaluate(&s, None, Some(&ctx_at(200))).is_err());
}

#[test]
fn field_lte_height_uses_ctx() {
    let p = CellProgram::Predicate(vec![StateConstraint::FieldLteHeight {
        index: 0,
        offset: 100,
    }]);
    let mut s = CellState::new(0);
    s.fields[0] = field_from_u64(150);
    // bound = 100+100=200, 150<=200 → ok
    assert!(p.evaluate(&s, None, Some(&ctx_at(100))).is_ok());
    // bound = 50+100=150 with value 150 → still ok (equal)
    assert!(p.evaluate(&s, None, Some(&ctx_at(50))).is_ok());
    // bound = 49+100=149, 150>149 → fail
    assert!(p.evaluate(&s, None, Some(&ctx_at(49))).is_err());
}

#[test]
fn sum_equals_across_intra_cell_conservation() {
    // sum(new[0,1]) == sum(old[0,1]) + sum(new[2,3])
    let p = CellProgram::Predicate(vec![StateConstraint::SumEqualsAcross {
        input_fields: vec![0, 1],
        output_fields: vec![2, 3],
    }]);
    let mut old = CellState::new(0);
    old.fields[0] = field_from_u64(100);
    old.fields[1] = field_from_u64(50);
    let mut new_s = old.clone();
    new_s.fields[0] = field_from_u64(160);
    new_s.fields[1] = field_from_u64(80);
    new_s.fields[2] = field_from_u64(60);
    new_s.fields[3] = field_from_u64(30);
    // sum(new in) = 240, sum(old in)=150, sum(new out)=90, 150+90=240 ✓
    assert!(p.evaluate(&new_s, Some(&old), None).is_ok());
    new_s.fields[2] = field_from_u64(0);
    assert!(p.evaluate(&new_s, Some(&old), None).is_err());
}

#[test]
fn sender_authorized_needs_sender_in_ctx() {
    let p = CellProgram::Predicate(vec![StateConstraint::SenderAuthorized {
        set: AuthorizedSet::PublicRoot { set_root_index: 7 },
    }]);
    let s = CellState::new(0);
    // No ctx → MissingContextField
    let err = p.evaluate(&s, None, None).unwrap_err();
    assert!(matches!(err, ProgramError::MissingContextField { .. }));
    // ctx with no sender → also missing
    let bare = EvalContext::default();
    let err = p.evaluate(&s, None, Some(&bare)).unwrap_err();
    assert!(matches!(err, ProgramError::MissingContextField { .. }));
    // ctx with sender but no registry → SenderMembershipWitnessMissing
    // (the registry + witness blob are also required for full verification)
    let err = p
        .evaluate(&s, None, Some(&ctx_sender([1u8; 32], 0)))
        .unwrap_err();
    assert!(matches!(err, ProgramError::SenderMembershipWitnessMissing));
}

#[test]
fn rate_limit_enforces_per_epoch_cap() {
    let p = CellProgram::Predicate(vec![StateConstraint::RateLimit {
        max_per_epoch: 3,
        epoch_duration: 100,
    }]);
    let s = CellState::new(0);
    let sender = [9u8; 32];
    // 0 < 3 → ok
    assert!(p.evaluate(&s, None, Some(&ctx_sender(sender, 0))).is_ok());
    // 2 < 3 → ok
    assert!(p.evaluate(&s, None, Some(&ctx_sender(sender, 2))).is_ok());
    // 3 >= 3 → fail
    assert!(p.evaluate(&s, None, Some(&ctx_sender(sender, 3))).is_err());
}

#[test]
fn rate_limit_by_sum_caps_delta() {
    let p = CellProgram::Predicate(vec![StateConstraint::RateLimitBySum {
        slot_index: 0,
        max_sum_per_epoch: 100,
        epoch_duration: 1000,
    }]);
    let mut old = CellState::new(0);
    old.fields[0] = field_from_u64(50);
    let mut new_s = old.clone();
    new_s.fields[0] = field_from_u64(140); // +90 < 100 → ok
    assert!(p.evaluate(&new_s, Some(&old), None).is_ok());
    new_s.fields[0] = field_from_u64(200); // +150 > 100 → fail
    assert!(p.evaluate(&new_s, Some(&old), None).is_err());
}

#[test]
fn temporal_gate_enforces_window() {
    let p = CellProgram::Predicate(vec![StateConstraint::TemporalGate {
        not_before: Some(100),
        not_after: Some(200),
    }]);
    let s = CellState::new(0);
    assert!(p.evaluate(&s, None, Some(&ctx_at(50))).is_err());
    assert!(p.evaluate(&s, None, Some(&ctx_at(150))).is_ok());
    assert!(p.evaluate(&s, None, Some(&ctx_at(250))).is_err());
}

#[test]
fn preimage_gate_verifies_hash() {
    let preimage = [7u8; 32];
    let commitment = *blake3::hash(&preimage).as_bytes();
    let p = CellProgram::Predicate(vec![StateConstraint::PreimageGate {
        commitment_index: 0,
        hash_kind: HashKind::Blake3,
    }]);
    let mut s = CellState::new(0);
    s.fields[0] = commitment;
    // Correct preimage → ok
    assert!(p.evaluate(&s, None, Some(&ctx_preimage(preimage))).is_ok());
    // Wrong preimage → fail
    assert!(
        p.evaluate(&s, None, Some(&ctx_preimage([8u8; 32])))
            .is_err()
    );
    // No preimage in ctx → missing
    assert!(p.evaluate(&s, None, Some(&EvalContext::default())).is_err());
}

/// `PreimageGate` on a **Poseidon2**-tagged slot: the gate now computes the
/// real STARK-native digest. The committed slot word must be the
/// `felt_to_bytes32` encoding of `dregg_circuit::poseidon2::hash_bytes`, and
/// the gate accepts exactly the real preimage and rejects a wrong one. This
/// is the load-bearing closure of the former `poseidon2-stub:` BLAKE3
/// stand-in: the same digest the circuit verifies.
#[test]
fn preimage_gate_poseidon2_verifies_real_hash() {
    let preimage = [7u8; 32];
    // The canonical Poseidon2 commitment — IDENTICAL to the circuit's.
    let commitment = crate::felt_to_bytes32(dregg_circuit::poseidon2::hash_bytes(&preimage));
    let p = CellProgram::Predicate(vec![StateConstraint::PreimageGate {
        commitment_index: 0,
        hash_kind: HashKind::Poseidon2,
    }]);
    let mut s = CellState::new(0);
    s.fields[0] = commitment;

    // Correct preimage → accepts.
    assert!(
        p.evaluate(&s, None, Some(&ctx_preimage(preimage))).is_ok(),
        "Poseidon2 PreimageGate must accept the real preimage"
    );
    // Wrong preimage → rejects.
    assert!(
        p.evaluate(&s, None, Some(&ctx_preimage([8u8; 32])))
            .is_err(),
        "Poseidon2 PreimageGate must reject a wrong preimage"
    );
    // A Poseidon2 slot must NOT be openable by the old BLAKE3 stand-in
    // digest — proves the function genuinely changed (non-vacuous cutover).
    let mut s_blake = CellState::new(0);
    s_blake.fields[0] = *blake3::hash(&preimage).as_bytes();
    assert!(
        p.evaluate(&s_blake, None, Some(&ctx_preimage(preimage)))
            .is_err(),
        "a BLAKE3-digest slot must NOT satisfy a Poseidon2 gate"
    );
}

/// `KeyRotationGate` on a **Poseidon2**-tagged digest register: the preimage
/// exhibit against the OLD digest uses the real Poseidon2 hash, so an honest
/// rotation that pre-committed `hash_bytes(next_keys)` exhibits and installs.
#[test]
fn key_rotation_gate_poseidon2_real_hash() {
    let gate = StateConstraint::KeyRotationGate {
        digest_slot: 1,
        current_slot: 2,
        last_rotated_slot: 3,
        cooling_period: 50,
        hash_kind: HashKind::Poseidon2,
    };
    let p = CellProgram::Predicate(vec![gate]);
    let next: [u8; 32] = [0xAB; 32]; // the pre-committed next key-set.
    // Pre-committed digest = the REAL Poseidon2 of `next`.
    let digest = crate::felt_to_bytes32(dregg_circuit::poseidon2::hash_bytes(&next));

    let ctx = |height: u64, preimage: Option<[u8; 32]>| EvalContext {
        block_height: height,
        revealed_preimage: preimage,
        ..EvalContext::default()
    };

    let mut old = CellState::new(0);
    old.nonce = 1;
    old.fields[1] = digest;
    old.fields[2] = [0x01; 32];
    old.fields[3] = field_from_u64(100);

    // Honest rotation at height 200: exhibit `next`, install, re-commit.
    let mut rotated = old.clone();
    rotated.fields[1] = crate::felt_to_bytes32(dregg_circuit::poseidon2::hash_bytes(&[0xCD; 32]));
    rotated.fields[2] = next;
    rotated.fields[3] = field_from_u64(200);
    assert!(
        p.evaluate(&rotated, Some(&old), Some(&ctx(200, Some(next))))
            .is_ok(),
        "Poseidon2 rotation must accept the real preimage exhibit"
    );

    // A WRONG preimage (does not Poseidon2-hash to the committed digest) → reject.
    let mut rotated_bad = rotated.clone();
    rotated_bad.fields[2] = [0x99; 32];
    assert!(
        p.evaluate(&rotated_bad, Some(&old), Some(&ctx(200, Some([0x99; 32]))))
            .is_err(),
        "Poseidon2 rotation must reject a preimage that does not exhibit the digest"
    );
}

/// `KeyRotationGate`: the rotate verb as a guarded write — preimage
/// exhibit against the OLD digest register, install, fresh re-commit,
/// cooling. The full triangle lives in `starbridge_polis::identity`
/// tests; this pins the constraint's own semantics.
#[test]
fn key_rotation_gate_semantics() {
    let gate = StateConstraint::KeyRotationGate {
        digest_slot: 1,
        current_slot: 2,
        last_rotated_slot: 3,
        cooling_period: 50,
        hash_kind: HashKind::Blake3,
    };
    let p = CellProgram::Predicate(vec![gate]);
    let next: [u8; 32] = [0xAB; 32]; // the pre-committed key-set commitment
    let digest = *blake3::hash(&next).as_bytes();

    let ctx = |height: u64, preimage: Option<[u8; 32]>| EvalContext {
        block_height: height,
        revealed_preimage: preimage,
        ..EvalContext::default()
    };

    // Committed state: digest register live, last rotation at 100.
    let mut old = CellState::new(0);
    old.nonce = 1;
    old.fields[1] = digest;
    old.fields[2] = [0x01; 32]; // current keys (must be irrelevant)
    old.fields[3] = field_from_u64(100);

    // No-op turn (registers untouched): admitted without a preimage.
    assert!(p.evaluate(&old, Some(&old), Some(&ctx(0, None))).is_ok());

    // Honest rotation at height 200 (cooled past 100 + 50): exhibit
    // `next`, install it, commit fresh, stamp 200.
    let mut rotated = old.clone();
    rotated.fields[1] = *blake3::hash(&[0xCD; 32]).as_bytes();
    rotated.fields[2] = next;
    rotated.fields[3] = field_from_u64(200);
    assert!(
        p.evaluate(&rotated, Some(&old), Some(&ctx(200, Some(next))))
            .is_ok()
    );
    // CURRENT KEYS ARE IRRELEVANT: the same rotation from a state with
    // ANY other current key set is decided identically (the structural
    // mirror of `rotate_current_keys_irrelevant`).
    let mut stolen = old.clone();
    stolen.fields[2] = [0xEE; 32];
    let mut rotated2 = rotated.clone();
    rotated2.fields[2] = next;
    assert!(
        p.evaluate(&rotated2, Some(&stolen), Some(&ctx(200, Some(next))))
            .is_ok()
    );

    // Wrong preimage (forged key set): refused.
    assert!(
        p.evaluate(&rotated, Some(&old), Some(&ctx(200, Some([0xEE; 32]))))
            .is_err()
    );
    // No preimage at all: refused even though the turn is well-formed.
    assert!(
        matches!(
            p.evaluate(&rotated, Some(&old), Some(&ctx(200, None))),
            Err(ProgramError::PreimageWitnessMissing)
        ),
        "rotation without the exhibit must surface PreimageWitnessMissing"
    );
    // Install mismatch: exhibiting the right preimage but installing a
    // different current commitment is refused.
    let mut misinstalled = rotated.clone();
    misinstalled.fields[2] = [0x99; 32];
    assert!(
        p.evaluate(&misinstalled, Some(&old), Some(&ctx(200, Some(next))))
            .is_err()
    );
    // Chain break: zeroing the register is refused.
    let mut chainless = rotated.clone();
    chainless.fields[1] = FIELD_ZERO;
    assert!(
        p.evaluate(&chainless, Some(&old), Some(&ctx(200, Some(next))))
            .is_err()
    );
    // Cooling: inside the window (100 + 50 > 149) even the honest
    // rotation is refused; the stamp must equal the height.
    let mut early = rotated.clone();
    early.fields[3] = field_from_u64(149);
    assert!(
        p.evaluate(&early, Some(&old), Some(&ctx(149, Some(next))))
            .is_err()
    );
    let mut misstamped = rotated.clone();
    misstamped.fields[3] = field_from_u64(150);
    assert!(
        p.evaluate(&misstamped, Some(&old), Some(&ctx(200, Some(next))))
            .is_err()
    );

    // Inception: from the unborn register (old digest == 0) the first
    // commitment installs without a preimage; a zero digest is refused.
    let born = CellState::new(0);
    let mut inducted = CellState::new(0);
    inducted.fields[1] = digest;
    inducted.fields[2] = [0x01; 32];
    assert!(
        p.evaluate(&inducted, Some(&born), Some(&ctx(0, None)))
            .is_ok()
    );
    let mut zeroed = inducted.clone();
    zeroed.fields[1] = FIELD_ZERO;
    assert!(
        p.evaluate(&zeroed, Some(&born), Some(&ctx(0, None)))
            .is_err()
    );
}

#[test]
fn monotonic_sequence_increments_by_one() {
    let p = CellProgram::Predicate(vec![StateConstraint::MonotonicSequence { seq_index: 0 }]);
    let mut old = CellState::new(0);
    old.fields[0] = field_from_u64(5);
    let mut new_s = old.clone();
    new_s.fields[0] = field_from_u64(6);
    assert!(p.evaluate(&new_s, Some(&old), None).is_ok());
    new_s.fields[0] = field_from_u64(7);
    assert!(p.evaluate(&new_s, Some(&old), None).is_err()); // skipped one
    new_s.fields[0] = field_from_u64(5);
    assert!(p.evaluate(&new_s, Some(&old), None).is_err()); // no increment
}

#[test]
fn allowed_transitions_state_machine() {
    let open = field_from_u64(1);
    let claimed = field_from_u64(2);
    let paid = field_from_u64(3);
    let p = CellProgram::Predicate(vec![StateConstraint::AllowedTransitions {
        slot_index: 0,
        allowed: vec![(open, claimed), (claimed, paid)],
    }]);
    let mut old = CellState::new(0);
    old.fields[0] = open;
    let mut new_s = old.clone();
    new_s.fields[0] = claimed;
    assert!(p.evaluate(&new_s, Some(&old), None).is_ok());
    new_s.fields[0] = paid;
    assert!(p.evaluate(&new_s, Some(&old), None).is_err()); // Open→Paid not allowed
}

#[test]
fn temporal_predicate_requires_witness() {
    let p = CellProgram::Predicate(vec![StateConstraint::TemporalPredicate {
        witness_index: 0,
        dsl_hash: [0xAB; 32],
    }]);
    let s = CellState::new(0);
    let err = p.evaluate(&s, None, None).unwrap_err();
    assert!(matches!(
        err,
        ProgramError::TemporalPredicateWitnessMissing { .. }
    ));
}

#[test]
fn bound_delta_surfaces_cross_cell_sentinel() {
    let peer = crate::id::CellId::from_bytes([7u8; 32]);
    let p = CellProgram::Predicate(vec![StateConstraint::BoundDelta {
        local_slot: 0,
        peer_cell: peer,
        peer_slot: 0,
        delta_relation: DeltaRelation::EqualAndOpposite,
    }]);
    let s = CellState::new(0);
    let err = p.evaluate(&s, None, None).unwrap_err();
    assert!(matches!(err, ProgramError::BoundDeltaNotWired { .. }));
}

#[test]
fn any_of_one_branch_must_hold() {
    let p = CellProgram::Predicate(vec![StateConstraint::AnyOf {
        variants: vec![
            SimpleStateConstraint::FieldEquals {
                index: 0,
                value: field_from_u64(7),
            },
            SimpleStateConstraint::FieldEquals {
                index: 0,
                value: field_from_u64(9),
            },
        ],
    }]);
    let mut s = CellState::new(0);
    s.fields[0] = field_from_u64(7);
    assert!(p.evaluate(&s, None, None).is_ok());
    s.fields[0] = field_from_u64(9);
    assert!(p.evaluate(&s, None, None).is_ok());
    s.fields[0] = field_from_u64(11);
    assert!(p.evaluate(&s, None, None).is_err());
}

#[test]
fn capability_uniqueness_index_bounds_checked() {
    let p = CellProgram::Predicate(vec![StateConstraint::CapabilityUniqueness {
        cap_set_root_slot: 200,
    }]);
    let s = CellState::new(0);
    assert!(matches!(
        p.evaluate(&s, None, None).unwrap_err(),
        ProgramError::InvalidFieldIndex { .. }
    ));
}

#[test]
fn custom_remains_fail_closed_without_runtime() {
    let p = CellProgram::Predicate(vec![StateConstraint::Custom {
        ir_hash: [0u8; 32],
        descriptor: CustomDescriptor::default(),
        reads: ReadSet::default(),
    }]);
    let s = CellState::new(0);
    assert!(matches!(
        p.evaluate(&s, None, None).unwrap_err(),
        ProgramError::CustomConstraintUnevaluable { .. }
    ));
}

// ── Adversarial / multi-constraint ────────────────────────────────────

#[test]
fn multiple_constraints_all_must_pass() {
    let p = CellProgram::Predicate(vec![
        StateConstraint::FieldGte {
            index: 0,
            value: field_from_u64(10),
        },
        StateConstraint::FieldLte {
            index: 0,
            value: field_from_u64(100),
        },
    ]);
    let mut s = CellState::new(0);
    s.fields[0] = field_from_u64(50);
    assert!(p.evaluate(&s, None, None).is_ok());
    s.fields[0] = field_from_u64(5);
    assert!(p.evaluate(&s, None, None).is_err());
    s.fields[0] = field_from_u64(200);
    assert!(p.evaluate(&s, None, None).is_err());
}

#[test]
fn invalid_field_index() {
    let p = CellProgram::Predicate(vec![StateConstraint::FieldEquals {
        index: 99,
        value: field_from_u64(1),
    }]);
    let s = CellState::new(0);
    assert!(matches!(
        p.evaluate(&s, None, None).unwrap_err(),
        ProgramError::InvalidFieldIndex { index: 99 }
    ));
}

// ── Heyting fragment — Not / Implies ─────────────────────────────────
// CROSS-CELL-CATEGORICAL-ANALYSIS.md §3.1 + §9.1.1.

#[test]
fn not_field_equals_accepts_when_field_differs() {
    // Not(FieldEquals(0, 7)) accepts when field[0] != 7.
    let p = CellProgram::Predicate(vec![StateConstraint::AnyOf {
        variants: vec![SimpleStateConstraint::Not(Box::new(
            SimpleStateConstraint::FieldEquals {
                index: 0,
                value: field_from_u64(7),
            },
        ))],
    }]);
    let mut s = CellState::new(0);
    s.fields[0] = field_from_u64(99);
    assert!(p.evaluate(&s, None, None).is_ok());
    // and rejects when it matches.
    s.fields[0] = field_from_u64(7);
    assert!(p.evaluate(&s, None, None).is_err());
}

#[test]
fn not_write_once_permits_overwriting() {
    // The app-driver case: Not(WriteOnce(0)) flips WriteOnce's
    // semantics — overwriting is now permitted; *not* writing
    // (or writing for the first time) is rejected.
    let p = CellProgram::Predicate(vec![StateConstraint::AnyOf {
        variants: vec![SimpleStateConstraint::Not(Box::new(
            SimpleStateConstraint::WriteOnce { index: 0 },
        ))],
    }]);
    // Old slot non-zero, new differs ⇒ WriteOnce rejects ⇒ Not accepts.
    let mut old = CellState::new(0);
    old.fields[0] = field_from_u64(42);
    let mut new_s = old.clone();
    new_s.fields[0] = field_from_u64(99);
    assert!(p.evaluate(&new_s, Some(&old), None).is_ok());
    // Old slot zero, new non-zero ⇒ WriteOnce accepts ⇒ Not rejects.
    let old_zero = CellState::new(0);
    let mut fresh = old_zero.clone();
    fresh.fields[0] = field_from_u64(42);
    assert!(p.evaluate(&fresh, Some(&old_zero), None).is_err());
}

#[test]
fn not_monotonic_permits_decrement() {
    // The app-driver case: Not(Monotonic(0)) accepts decrements;
    // rejects monotone non-decreases.
    let p = CellProgram::Predicate(vec![StateConstraint::AnyOf {
        variants: vec![SimpleStateConstraint::Not(Box::new(
            SimpleStateConstraint::Monotonic { index: 0 },
        ))],
    }]);
    let mut old = CellState::new(0);
    old.fields[0] = field_from_u64(50);
    let mut new_s = old.clone();
    // Decrement — Monotonic rejects, Not accepts.
    new_s.fields[0] = field_from_u64(40);
    assert!(p.evaluate(&new_s, Some(&old), None).is_ok());
    // Increase — Monotonic accepts, Not rejects.
    new_s.fields[0] = field_from_u64(60);
    assert!(p.evaluate(&new_s, Some(&old), None).is_err());
    // Equal — Monotonic accepts (>=), Not rejects.
    new_s.fields[0] = field_from_u64(50);
    assert!(p.evaluate(&new_s, Some(&old), None).is_err());
}

#[test]
fn not_propagates_unevaluable_error() {
    // Not(Immutable(0)) with no old_state and nonce > 0:
    // inner Immutable surfaces TransitionCheckRequiresOldState; Not
    // propagates the same — fail-closed on unevaluable inputs.
    let p = CellProgram::Predicate(vec![StateConstraint::AnyOf {
        variants: vec![SimpleStateConstraint::Not(Box::new(
            SimpleStateConstraint::Immutable { index: 0 },
        ))],
    }]);
    let mut s = CellState::new(0);
    s.set_nonce(5);
    let err = p.evaluate(&s, None, None).unwrap_err();
    // The error surfaces *through* the AnyOf as the last-branch
    // error — and must NOT be a vacuous Ok. We assert non-Ok and
    // that the surfaced error is the transition-check shape.
    assert!(matches!(
        err,
        ProgramError::TransitionCheckRequiresOldState { .. }
            | ProgramError::ConstraintViolated { .. }
    ));
}

#[test]
fn implies_accepts_when_antecedent_false() {
    // Implies(FieldEquals(0, 7), FieldEquals(1, 9)) — antecedent
    // false means the implication is vacuously satisfied; the
    // consequent need not hold.
    let p = CellProgram::Predicate(vec![StateConstraint::implies(
        SimpleStateConstraint::FieldEquals {
            index: 0,
            value: field_from_u64(7),
        },
        SimpleStateConstraint::FieldEquals {
            index: 1,
            value: field_from_u64(9),
        },
    )]);
    let mut s = CellState::new(0);
    // field[0] != 7 ⇒ antecedent false ⇒ Implies accepts regardless of slot 1.
    s.fields[0] = field_from_u64(123);
    s.fields[1] = field_from_u64(0);
    assert!(p.evaluate(&s, None, None).is_ok());
}

#[test]
fn implies_accepts_when_consequent_true() {
    let p = CellProgram::Predicate(vec![StateConstraint::implies(
        SimpleStateConstraint::FieldEquals {
            index: 0,
            value: field_from_u64(7),
        },
        SimpleStateConstraint::FieldEquals {
            index: 1,
            value: field_from_u64(9),
        },
    )]);
    let mut s = CellState::new(0);
    // antecedent true AND consequent true — Implies accepts.
    s.fields[0] = field_from_u64(7);
    s.fields[1] = field_from_u64(9);
    assert!(p.evaluate(&s, None, None).is_ok());
}

#[test]
fn implies_rejects_when_antecedent_true_consequent_false() {
    let p = CellProgram::Predicate(vec![StateConstraint::implies(
        SimpleStateConstraint::FieldEquals {
            index: 0,
            value: field_from_u64(7),
        },
        SimpleStateConstraint::FieldEquals {
            index: 1,
            value: field_from_u64(9),
        },
    )]);
    let mut s = CellState::new(0);
    // antecedent true, consequent false ⇒ Implies rejects.
    s.fields[0] = field_from_u64(7);
    s.fields[1] = field_from_u64(0);
    assert!(p.evaluate(&s, None, None).is_err());
}

#[test]
fn implies_via_builder_method_equals_static_constructor() {
    let antec = SimpleStateConstraint::FieldEquals {
        index: 0,
        value: field_from_u64(1),
    };
    let conseq = SimpleStateConstraint::FieldGte {
        index: 1,
        value: field_from_u64(2),
    };
    let via_method = antec.clone().implies(conseq.clone());
    let via_static = StateConstraint::implies(antec, conseq);
    assert_eq!(via_method, via_static);
}

#[test]
fn not_round_trips_serde() {
    let s = SimpleStateConstraint::Not(Box::new(SimpleStateConstraint::FieldEquals {
        index: 3,
        value: field_from_u64(42),
    }));
    let bytes = postcard::to_allocvec(&s).expect("serialize");
    let back: SimpleStateConstraint = postcard::from_bytes(&bytes).expect("deserialize");
    assert_eq!(back, s);
}

#[test]
fn circuit_program_requires_proof() {
    let p = CellProgram::Circuit {
        circuit_hash: [0xAB; 32],
    };
    let s = CellState::new(0);
    assert!(matches!(
        p.evaluate(&s, None, None).unwrap_err(),
        ProgramError::CircuitProofRequired { .. }
    ));
}

// ── Renunciation — Tier 2 §3.2 / §9.2.1 ──────────────────────────────

#[test]
fn renounced_accepts_legal_non_membership() {
    // Sender 0x05 is between lower=0x04 and upper=0x06 → not in
    // the set → renunciation accepts. Post-hardening, the bare 96-byte
    // neighbor proof is rejected (wide-bracket forge closed); the positive
    // path now ships a `NonMembershipProofV2` with a real Merkle-adjacency
    // proof, verified against a registry that has an adjacency verifier
    // installed (mocked here; the production adjacency STARK is exercised
    // end-to-end in dregg-turn).
    let candidate = [0x05u8; 32];
    let proof_bytes = honest_renunciation_v2(&[0xAB; 32], [0x04u8; 32], [0x06u8; 32]);
    let registry = registry_with_mock_adjacency();
    let blobs: [WitnessBlobView<'_>; 1] = [WitnessBlobView {
        kind: WitnessKindTag::ProofBytes,
        bytes: &proof_bytes,
    }];
    let bundle = WitnessBundle {
        blobs: &blobs,
        registry: Some(&registry),
        finalized_roots: None,
    };

    let p = CellProgram::Predicate(vec![StateConstraint::Renounced {
        set: RenouncedSet::BlindedSet {
            commitment: [0xAB; 32],
        },
    }]);
    let s = CellState::new(0);
    let ctx = ctx_sender(candidate, 0);
    p.evaluate_full(&s, None, Some(&ctx), &TransitionMeta::wildcard(), &bundle)
        .expect("legal renunciation accepts");
}

#[test]
fn renounced_rejects_when_prover_is_in_set() {
    // Adversarial: candidate == lower neighbor → the prover IS in
    // the set but is forging a renunciation. Must reject.
    let candidate = [0x05u8; 32];
    let proof = crate::predicate::NonMembershipNeighborProof::new(
        &[0xAB; 32],
        [0x05u8; 32], // candidate matches lower → in set
        [0x06u8; 32],
    );
    let proof_bytes = proof.to_bytes();
    let registry = crate::predicate::WitnessedPredicateRegistry::with_stubs();
    let blobs: [WitnessBlobView<'_>; 1] = [WitnessBlobView {
        kind: WitnessKindTag::ProofBytes,
        bytes: &proof_bytes,
    }];
    let bundle = WitnessBundle {
        blobs: &blobs,
        registry: Some(&registry),
        finalized_roots: None,
    };

    let p = CellProgram::Predicate(vec![StateConstraint::Renounced {
        set: RenouncedSet::BlindedSet {
            commitment: [0xAB; 32],
        },
    }]);
    let s = CellState::new(0);
    let ctx = ctx_sender(candidate, 0);
    let err = p
        .evaluate_full(&s, None, Some(&ctx), &TransitionMeta::wildcard(), &bundle)
        .unwrap_err();
    assert!(matches!(
        err,
        ProgramError::WitnessedPredicateRejected {
            kind_name: "NonMembership",
            ..
        }
    ));
}

#[test]
fn renounced_rejects_forged_adjacency_tag() {
    let candidate = [0x05u8; 32];
    let proof = crate::predicate::NonMembershipNeighborProof {
        lower: [0x04u8; 32],
        upper: [0x06u8; 32],
        adjacency_tag: [0u8; 32], // forged (zero != commitment-keyed tag)
    };
    let proof_bytes = proof.to_bytes();
    let registry = crate::predicate::WitnessedPredicateRegistry::with_stubs();
    let blobs: [WitnessBlobView<'_>; 1] = [WitnessBlobView {
        kind: WitnessKindTag::ProofBytes,
        bytes: &proof_bytes,
    }];
    let bundle = WitnessBundle {
        blobs: &blobs,
        registry: Some(&registry),
        finalized_roots: None,
    };

    let p = CellProgram::Predicate(vec![StateConstraint::Renounced {
        set: RenouncedSet::BlindedSet {
            commitment: [0xAB; 32],
        },
    }]);
    let s = CellState::new(0);
    let ctx = ctx_sender(candidate, 0);
    let err = p
        .evaluate_full(&s, None, Some(&ctx), &TransitionMeta::wildcard(), &bundle)
        .unwrap_err();
    assert!(matches!(
        err,
        ProgramError::WitnessedPredicateRejected {
            kind_name: "NonMembership",
            ..
        }
    ));
}

#[test]
fn renounced_requires_sender_in_ctx() {
    let registry = crate::predicate::WitnessedPredicateRegistry::with_stubs();
    let bundle = WitnessBundle {
        blobs: &[],
        registry: Some(&registry),
        finalized_roots: None,
    };
    let p = CellProgram::Predicate(vec![StateConstraint::Renounced {
        set: RenouncedSet::BlindedSet {
            commitment: [0xAB; 32],
        },
    }]);
    let s = CellState::new(0);
    // No ctx at all.
    let err = p
        .evaluate_full(&s, None, None, &TransitionMeta::wildcard(), &bundle)
        .unwrap_err();
    assert!(matches!(err, ProgramError::MissingContextField { .. }));
    // Ctx without sender.
    let bare = EvalContext::default();
    let err = p
        .evaluate_full(&s, None, Some(&bare), &TransitionMeta::wildcard(), &bundle)
        .unwrap_err();
    assert!(matches!(err, ProgramError::MissingContextField { .. }));
}

#[test]
fn renounced_public_root_reads_slot_commitment() {
    // PublicRoot variant pulls commitment from a state slot.
    let candidate = [0x05u8; 32];
    // Slot 3 carries the set root [0xCC; 32] (see below). Post-hardening
    // positive path: a NonMembershipProofV2 bound to that root, with a real
    // Merkle-adjacency proof (mocked here), verified against a registry that
    // has the adjacency verifier installed.
    let proof_bytes = honest_renunciation_v2(&[0xCC; 32], [0x04u8; 32], [0x06u8; 32]);
    let registry = registry_with_mock_adjacency();
    let blobs: [WitnessBlobView<'_>; 1] = [WitnessBlobView {
        kind: WitnessKindTag::ProofBytes,
        bytes: &proof_bytes,
    }];
    let bundle = WitnessBundle {
        blobs: &blobs,
        registry: Some(&registry),
        finalized_roots: None,
    };

    let p = CellProgram::Predicate(vec![StateConstraint::Renounced {
        set: RenouncedSet::PublicRoot { set_root_index: 3 },
    }]);
    let mut s = CellState::new(0);
    s.fields[3] = [0xCC; 32]; // set root from slot
    let ctx = ctx_sender(candidate, 0);
    p.evaluate_full(&s, None, Some(&ctx), &TransitionMeta::wildcard(), &bundle)
        .expect("legal renunciation via PublicRoot accepts");
}

// ─────────────────────────────────────────────────────────────────────
// AUDIT adversarial tests (FAIL-before / PASS-after)
// ─────────────────────────────────────────────────────────────────────

// Item 2: RateLimit no longer trusts a self-attested `RateLimitCount`
// witness blob. A submitter who attests count=0 while over the limit
// must be rejected — the count comes ONLY from ctx.sender_epoch_count.
#[test]
fn rate_limit_ignores_self_attested_count_witness() {
    let p = CellProgram::Predicate(vec![StateConstraint::RateLimit {
        max_per_epoch: 3,
        epoch_duration: 100,
    }]);
    let s = CellState::new(0);
    let sender = [9u8; 32];

    // Adversary attests count=0 in the witness blob while the
    // authoritative ctx count is 5 (over the cap). Pre-fix this
    // accepted (ctx==0 fallthrough never happened, but a submitter
    // setting ctx-bypassing self-attest=0 on the FIRST action of an
    // epoch — when the real counter is 0 — would always pass).
    let zero = 0u32.to_le_bytes();
    let blobs: [WitnessBlobView<'_>; 1] = [WitnessBlobView {
        kind: WitnessKindTag::RateLimitCount,
        bytes: &zero,
    }];
    let bundle = WitnessBundle {
        blobs: &blobs,
        registry: None,
        finalized_roots: None,
    };
    // Authoritative ctx count is over the cap → MUST reject, the
    // self-attested 0 must be ignored.
    let over = ctx_sender(sender, 5);
    let err = p
        .evaluate_full(&s, None, Some(&over), &TransitionMeta::wildcard(), &bundle)
        .expect_err("over-cap ctx count must reject despite self-attested 0");
    assert!(matches!(err, ProgramError::ConstraintViolated { .. }));

    // And when ctx count is 0 (first action of the epoch), a witness
    // blob claiming a huge count must NOT be able to "use up" the
    // budget either — the witness is simply ignored, so it accepts.
    let huge = 999u32.to_le_bytes();
    let blobs2: [WitnessBlobView<'_>; 1] = [WitnessBlobView {
        kind: WitnessKindTag::RateLimitCount,
        bytes: &huge,
    }];
    let bundle2 = WitnessBundle {
        blobs: &blobs2,
        registry: None,
        finalized_roots: None,
    };
    let zero_ctx = ctx_sender(sender, 0);
    p.evaluate_full(
        &s,
        None,
        Some(&zero_ctx),
        &TransitionMeta::wildcard(),
        &bundle2,
    )
    .expect("ctx count 0 accepts regardless of witness blob");
}

// Item 1: CapabilityUniqueness fails CLOSED in the scalar evaluator —
// it can never silently pass. The real enforcement lives in the
// executor (turn/tests covers the structural cap-set path).
#[test]
fn capability_uniqueness_scalar_fails_closed() {
    let p = CellProgram::Predicate(vec![StateConstraint::CapabilityUniqueness {
        cap_set_root_slot: 0,
    }]);
    let mut s = CellState::new(0);
    s.fields[0] = [0xAB; 32]; // non-zero root; still must fail closed
    let err = p.evaluate(&s, None, None).unwrap_err();
    assert!(
        matches!(
            err,
            ProgramError::CapabilityUniquenessRequiresExecutor { .. }
        ),
        "scalar CapabilityUniqueness must fail closed, got {err:?}"
    );
}

// Item 4: a mismatched / ambiguous witness must be rejected rather
// than cross-matched. Two ProofBytes blobs make the binding ambiguous
// for Renounced → fail closed (pre-fix the first-of-kind scan would
// silently pick blob 0).
#[test]
fn renounced_ambiguous_witness_rejected() {
    let candidate = [0x05u8; 32];
    let proof =
        crate::predicate::NonMembershipNeighborProof::new(&[0xCC; 32], [0x04u8; 32], [0x06u8; 32]);
    let pb = proof.to_bytes();
    let registry = crate::predicate::WitnessedPredicateRegistry::with_stubs();
    // TWO ProofBytes blobs — ambiguous.
    let blobs: [WitnessBlobView<'_>; 2] = [
        WitnessBlobView {
            kind: WitnessKindTag::ProofBytes,
            bytes: &pb,
        },
        WitnessBlobView {
            kind: WitnessKindTag::ProofBytes,
            bytes: &pb,
        },
    ];
    let bundle = WitnessBundle {
        blobs: &blobs,
        registry: Some(&registry),
        finalized_roots: None,
    };
    let p = CellProgram::Predicate(vec![StateConstraint::Renounced {
        set: RenouncedSet::PublicRoot { set_root_index: 3 },
    }]);
    let mut s = CellState::new(0);
    s.fields[3] = [0xCC; 32];
    let ctx = ctx_sender(candidate, 0);
    let err = p
        .evaluate_full(&s, None, Some(&ctx), &TransitionMeta::wildcard(), &bundle)
        .expect_err("ambiguous double-ProofBytes witness must reject");
    assert!(
        matches!(
            err,
            ProgramError::WitnessedPredicateRejected {
                kind_name: "NonMembership",
                ..
            }
        ),
        "expected ambiguity rejection, got {err:?}"
    );
}

// Item 4: TemporalPredicate binds its proof explicitly at
// `witness_index + 1`. A proof placed elsewhere (or of the wrong
// kind at that slot) must be rejected, not first-of-kind matched.
#[test]
fn temporal_predicate_proof_must_be_at_explicit_index() {
    let registry = crate::predicate::WitnessedPredicateRegistry::with_stubs();
    let input = [1u8; 8];
    let proof = [2u8; 64];
    // input at index 0, but proof placed at index 2 (not 1) — the
    // explicit slot (index 1) is the wrong kind.
    let wrong_kind = [9u8; 4];
    let blobs: [WitnessBlobView<'_>; 3] = [
        WitnessBlobView {
            kind: WitnessKindTag::Cleartext,
            bytes: &input,
        },
        WitnessBlobView {
            kind: WitnessKindTag::RateLimitCount,
            bytes: &wrong_kind,
        },
        WitnessBlobView {
            kind: WitnessKindTag::ProofBytes,
            bytes: &proof,
        },
    ];
    let bundle = WitnessBundle {
        blobs: &blobs,
        registry: Some(&registry),
        finalized_roots: None,
    };
    let p = CellProgram::Predicate(vec![StateConstraint::TemporalPredicate {
        witness_index: 0,
        dsl_hash: [0xAB; 32],
    }]);
    let s = CellState::new(0);
    let err = p
        .evaluate_full(&s, None, None, &TransitionMeta::wildcard(), &bundle)
        .expect_err("proof not at witness_index+1 must reject");
    assert!(
        matches!(
            err,
            ProgramError::WitnessedPredicateRejected {
                kind_name: "Temporal",
                ..
            }
        ),
        "expected explicit-index rejection, got {err:?}"
    );

    // Now place the proof at the correct explicit slot (index 1) →
    // the Temporal stub verifier accepts.
    let blobs_ok: [WitnessBlobView<'_>; 2] = [
        WitnessBlobView {
            kind: WitnessKindTag::Cleartext,
            bytes: &input,
        },
        WitnessBlobView {
            kind: WitnessKindTag::ProofBytes,
            bytes: &proof,
        },
    ];
    let bundle_ok = WitnessBundle {
        blobs: &blobs_ok,
        registry: Some(&registry),
        finalized_roots: None,
    };
    p.evaluate_full(&s, None, None, &TransitionMeta::wildcard(), &bundle_ok)
        .expect("proof at witness_index+1 accepts via stub verifier");
}

// ─── Turn-context atoms (CELL-PROGRAM-LANGUAGE.md §3) ───

/// The polis council shape: "approval slot 3 may change only if the
/// turn's sender is member A" — `AnyOf[Immutable{3}, SenderIs{a}]`.
/// This is THE per-slot actor binding (polis gap 5) at the program
/// level.
#[test]
fn sender_is_binds_slot_to_actor() {
    let member_a = [0xAAu8; 32];
    let member_b = [0xBBu8; 32];
    let program = CellProgram::Predicate(vec![StateConstraint::AnyOf {
        variants: vec![
            SimpleStateConstraint::Immutable { index: 3 },
            SimpleStateConstraint::SenderIs { pk: member_a },
        ],
    }]);
    let old = CellState::new(0);
    let mut flipped = old.clone();
    flipped.fields[3] = field_from_u64(1);

    // Member A flips their own slot: admitted.
    assert!(
        program
            .evaluate(&flipped, Some(&old), Some(&ctx_sender(member_a, 0)))
            .is_ok(),
        "the bound actor may flip the slot"
    );
    // Member B (a real key, a real capability — just NOT the bound
    // identity) flips A's slot: rejected.
    assert!(
        program
            .evaluate(&flipped, Some(&old), Some(&ctx_sender(member_b, 0)))
            .is_err(),
        "another actor cannot flip the bound slot"
    );
    // A turn by member B that does NOT touch the slot: admitted via
    // the Immutable disjunct (propose/certify/execute stay open).
    assert!(
        program
            .evaluate(&old, Some(&old), Some(&ctx_sender(member_b, 0)))
            .is_ok(),
        "untouched slot admits any sender"
    );
    // No sender in context while flipping: fail-closed.
    assert!(
        program
            .evaluate(&flipped, Some(&old), Some(&ctx_at(5)))
            .is_err(),
        "missing sender fails closed"
    );
}

#[test]
fn sender_in_slot_binds_to_slot_held_identity() {
    let owner = [0x11u8; 32];
    let thief = [0x22u8; 32];
    let program = CellProgram::Predicate(vec![StateConstraint::SenderInSlot { index: 2 }]);
    let mut state = CellState::new(0);
    state.fields[2] = owner;
    assert!(
        program
            .evaluate(&state, None, Some(&ctx_sender(owner, 0)))
            .is_ok()
    );
    assert!(
        program
            .evaluate(&state, None, Some(&ctx_sender(thief, 0)))
            .is_err()
    );
    // Out-of-range slot: structural error, not a pass.
    let bad = CellProgram::Predicate(vec![StateConstraint::SenderInSlot { index: 99 }]);
    assert!(matches!(
        bad.evaluate(&state, None, Some(&ctx_sender(owner, 0))),
        Err(ProgramError::InvalidFieldIndex { index: 99 })
    ));
}

/// Balance atoms read the cell's own sealed balance — the
/// "resolve drains the full balance" tooth becomes program-enforced:
/// `state == RESOLVED ⇒ balance == 0` as
/// `AnyOf[Not(state==RESOLVED), BalanceLte{0}]`.
#[test]
fn balance_atoms_see_own_balance() {
    let resolved = field_from_u64(2);
    let drain_tooth = CellProgram::Predicate(vec![StateConstraint::AnyOf {
        variants: vec![
            SimpleStateConstraint::Not(Box::new(SimpleStateConstraint::FieldEquals {
                index: 0,
                value: resolved,
            })),
            SimpleStateConstraint::BalanceLte { max: 0 },
        ],
    }]);
    // Resolved with a drained balance: admitted.
    let mut drained = CellState::new(0);
    drained.fields[0] = resolved;
    drained.set_balance(0);
    assert!(drain_tooth.evaluate(&drained, None, None).is_ok());
    // Resolved while still holding value: rejected (stranded /
    // partially-drained settlement cannot commit).
    let mut holding = drained.clone();
    holding.set_balance(40);
    assert!(drain_tooth.evaluate(&holding, None, None).is_err());
    // Not resolved: balance unconstrained.
    let mut open = CellState::new(0);
    open.fields[0] = field_from_u64(1);
    open.set_balance(40);
    assert!(drain_tooth.evaluate(&open, None, None).is_ok());

    // Solvency floor: BalanceGte.
    let floor = CellProgram::Predicate(vec![StateConstraint::BalanceGte { min: 10 }]);
    let mut funded = CellState::new(0);
    funded.set_balance(10);
    assert!(floor.evaluate(&funded, None, None).is_ok());
    funded.set_balance(9);
    assert!(floor.evaluate(&funded, None, None).is_err());
}

/// Apps gap 3 — the multi-admin actor binding. `SenderMemberOf` is the
/// clean form of `AnyOf[SenderIs{a}, SenderIs{b}, …]`. Mirrors the Lean
/// keystone `evalSimpleCtx_senderMemberOf_iff`: admits IFF a sender is in
/// context AND on the board; off-board or no-context fail closed.
#[test]
fn sender_member_of_binds_multi_admin() {
    let alice = [0x11u8; 32];
    let bob = [0x22u8; 32];
    let mallory = [0x99u8; 32];
    let board = CellProgram::Predicate(vec![StateConstraint::SenderMemberOf {
        members: vec![alice, bob],
    }]);
    let st = CellState::new(0);
    // A board member is admitted.
    assert!(
        board
            .evaluate(&st, None, Some(&ctx_sender(alice, 0)))
            .is_ok()
    );
    assert!(board.evaluate(&st, None, Some(&ctx_sender(bob, 0))).is_ok());
    // A non-member is rejected (ConstraintViolated, not a pass).
    assert!(matches!(
        board.evaluate(&st, None, Some(&ctx_sender(mallory, 0))),
        Err(ProgramError::ConstraintViolated { .. })
    ));
    // No sender in context ⇒ MissingContextField (fail-closed).
    assert!(matches!(
        board.evaluate(&st, None, Some(&ctx_at(7))),
        Err(ProgramError::MissingContextField { field: "sender" })
    ));
    // No context at all ⇒ MissingContextField.
    assert!(matches!(
        board.evaluate(&st, None, None),
        Err(ProgramError::MissingContextField { field: "sender" })
    ));

    // The multi-admin per-slot binding: slot 0 flips only for a board
    // member, but ANY sender may leave it alone (the council ceremony
    // stays open). `AnyOf[Immutable{0}, SenderMemberOf{board}]`.
    let bound = CellProgram::Predicate(vec![StateConstraint::AnyOf {
        variants: vec![
            SimpleStateConstraint::Immutable { index: 0 },
            SimpleStateConstraint::SenderMemberOf {
                members: vec![alice, bob],
            },
        ],
    }]);
    let mut old = CellState::new(0);
    old.fields[0] = field_from_u64(5);
    let mut flipped = old.clone();
    flipped.fields[0] = field_from_u64(6);
    // Mallory leaving the slot ALONE is admitted (Immutable branch).
    assert!(
        bound
            .evaluate(&old, Some(&old), Some(&ctx_sender(mallory, 0)))
            .is_ok()
    );
    // Mallory FLIPPING the slot is rejected (neither branch passes).
    assert!(
        bound
            .evaluate(&flipped, Some(&old), Some(&ctx_sender(mallory, 0)))
            .is_err()
    );
    // Alice (a member) flipping the slot is admitted (member branch).
    assert!(
        bound
            .evaluate(&flipped, Some(&old), Some(&ctx_sender(alice, 0)))
            .is_ok()
    );
}

/// Apps gap 4 — the per-turn balance RATE gates. `BalanceDeltaLte` /
/// `BalanceDeltaGte` bound `new.balance − old.balance` (the pre-balance is
/// the executor's `old_state`). Mirrors the Lean keystones
/// `evalSimpleCtx_balanceDeltaLe_iff` / `_balanceDeltaGe_iff`. SIGNED
/// bounds (a negative `max` forces a loss). Fail-closed without a pre-state.
#[test]
fn balance_delta_atoms_bound_the_rate() {
    // Ceiling: may gain at most 10 per turn.
    let ceil = CellProgram::Predicate(vec![StateConstraint::BalanceDeltaLte { max: 10 }]);
    let mut old = CellState::new(0);
    old.set_balance(100);
    let mut up5 = old.clone();
    up5.set_balance(105); // +5 ≤ 10 → admit
    assert!(ceil.evaluate(&up5, Some(&old), None).is_ok());
    let mut up20 = old.clone();
    up20.set_balance(120); // +20 > 10 → reject
    assert!(matches!(
        ceil.evaluate(&up20, Some(&old), None),
        Err(ProgramError::ConstraintViolated { .. })
    ));
    // A drain (negative delta) trivially satisfies a positive ceiling.
    let mut down = old.clone();
    down.set_balance(50); // −50 ≤ 10 → admit
    assert!(ceil.evaluate(&down, Some(&old), None).is_ok());

    // Floor: may LOSE at most 30 per turn (delta ≥ −30).
    let floor = CellProgram::Predicate(vec![StateConstraint::BalanceDeltaGte { min: -30 }]);
    let mut lose20 = old.clone();
    lose20.set_balance(80); // −20 ≥ −30 → admit
    assert!(floor.evaluate(&lose20, Some(&old), None).is_ok());
    let mut lose40 = old.clone();
    lose40.set_balance(60); // −40 < −30 → reject
    assert!(matches!(
        floor.evaluate(&lose40, Some(&old), None),
        Err(ProgramError::ConstraintViolated { .. })
    ));

    // Fail-closed: a rate gate without a pre-state (no old_state) cannot be
    // satisfied — TransitionCheckRequiresOldState (both endpoints needed).
    assert!(matches!(
        ceil.evaluate(&up5, None, None),
        Err(ProgramError::TransitionCheckRequiresOldState { .. })
    ));
}

/// Apps gap 2 — the multi-field delta gate. `AffineDeltaLe` bounds
/// `Σ kᵢ·(new[fᵢ] − old[fᵢ]) ≤ c` (a treasury's COMBINED per-turn
/// outflow across two spend slots). Mirrors the Lean keystone
/// `evalConstraint_affineDeltaLe_iff`. Fail-closed without a pre-state.
#[test]
fn affine_delta_le_bounds_combined_outflow() {
    // out_a (slot 1) + out_b (slot 2) may grow by at most 50 per turn.
    let budget = CellProgram::Predicate(vec![StateConstraint::AffineDeltaLe {
        terms: vec![(1, 1), (1, 2)],
        c: 50,
    }]);
    let mut old = CellState::new(0);
    old.fields[1] = field_from_u64(10);
    old.fields[2] = field_from_u64(20);
    // Δout_a=15, Δout_b=20 ⇒ sum 35 ≤ 50 → admit.
    let mut within = old.clone();
    within.fields[1] = field_from_u64(25);
    within.fields[2] = field_from_u64(40);
    assert!(budget.evaluate(&within, Some(&old), None).is_ok());
    // Δout_a=30, Δout_b=30 ⇒ sum 60 > 50 → reject (combined cap, even
    // though neither single slot is obviously out of bounds).
    let mut over = old.clone();
    over.fields[1] = field_from_u64(40);
    over.fields[2] = field_from_u64(50);
    assert!(matches!(
        budget.evaluate(&over, Some(&old), None),
        Err(ProgramError::ConstraintViolated { .. })
    ));
    // Fail-closed without a pre-state.
    assert!(matches!(
        budget.evaluate(&within, None, None),
        Err(ProgramError::TransitionCheckRequiresOldState { .. })
    ));
}

/// §11.2 — the cross-cell verified-observation atom. A market cell's
/// `mark` (slot 0) must equal an oracle cell's FINALIZED `price`
/// (`source_field` 1) at a finalized root. The host
/// [`FinalizedRootAuthority`] is the cross-cell analogue of
/// [`crate::predicate::IssuerRootAuthority`]: it confirms `at_root` is the
/// peer's genuine finalized commitment and opens the field. Mirrors the
/// proven Lean keystone `evalConstraintCtx_observedFieldEquals_iff` +
/// `observedFieldEquals_mismatch_refuses` +
/// `evalConstraintCtx_observedFieldEquals_absent_proof_refuses`.
#[test]
fn observed_field_equals_reads_a_finalized_peer_value() {
    use crate::predicate::{FinalizedRootAuthority, StaticFinalizedRootAuthority};

    let oracle = [0x11u8; 32]; // the peer (oracle) cell
    let at_root = [0xABu8; 32]; // a finalized state-commitment of the oracle
    let price = field_from_u64(42); // the oracle's finalized `price` (field 1)

    // The host knows the oracle's finalized root opens field 1 to 42.
    let authority: std::sync::Arc<dyn FinalizedRootAuthority> = std::sync::Arc::new(
        StaticFinalizedRootAuthority::new().authorize(oracle, at_root, 1, price),
    );
    // The Merkle-open proof rides in the witness at the bound index.
    let proof_bytes = [0u8; 1];
    let blobs = [WitnessBlobView {
        kind: WitnessKindTag::MerklePath,
        bytes: &proof_bytes,
    }];
    let bundle = WitnessBundle {
        blobs: &blobs,
        registry: None,
        finalized_roots: Some(authority.as_ref()),
    };

    // The market cell: `mark` (slot 0) MUST equal the oracle's finalized price.
    let market = CellProgram::Predicate(vec![StateConstraint::ObservedFieldEquals {
        local_field: 0,
        source_cell: oracle,
        source_field: 1,
        at_root,
        proof_witness_index: 0,
    }]);
    let meta = TransitionMeta::wildcard();

    // ADMIT: the market set mark = 42, exactly the oracle's finalized price.
    let mut matched = CellState::new(0);
    matched.fields[0] = price;
    assert!(
        market
            .evaluate_full(&matched, None, None, &meta, &bundle)
            .is_ok(),
        "mark == the oracle's finalized price must ADMIT (the natural cross-cell read)"
    );

    // REJECT (the mismatch tooth): the market tried to set mark = 99 while
    // the oracle's finalized price is 42 — the binding is real, the turn
    // cannot diverge its local field from the peer's finalized value.
    let mut mismatched = CellState::new(0);
    mismatched.fields[0] = field_from_u64(99);
    assert!(matches!(
        market.evaluate_full(&mismatched, None, None, &meta, &bundle),
        Err(ProgramError::ConstraintViolated { .. })
    ));

    // REJECT (the anti-forge tooth): a FORGED `at_root` the host never
    // finalized for the oracle — the authority has no binding, fail-closed.
    let forged = CellProgram::Predicate(vec![StateConstraint::ObservedFieldEquals {
        local_field: 0,
        source_cell: oracle,
        source_field: 1,
        at_root: [0xCDu8; 32], // not the oracle's finalized root
        proof_witness_index: 0,
    }]);
    assert!(matches!(
        forged.evaluate_full(&matched, None, None, &meta, &bundle),
        Err(ProgramError::WitnessedPredicateRejected { .. })
    ));

    // REJECT (no host authority installed): no channel to the peer's real
    // finalized roots ⇒ a self-fabricated read is indistinguishable, so the
    // evaluator refuses (the empty-`observedFields` Lean carrier).
    let no_authority = WitnessBundle {
        blobs: &blobs,
        registry: None,
        finalized_roots: None,
    };
    assert!(matches!(
        market.evaluate_full(&matched, None, None, &meta, &no_authority),
        Err(ProgramError::WitnessedPredicateRequiresExecutor {
            kind_name: "ObservedFieldEquals"
        })
    ));

    // REJECT (missing Merkle-open proof): the witness carries no blob at
    // the bound index ⇒ the portal could not have opened it, fail-closed.
    let empty_blobs: [WitnessBlobView<'_>; 0] = [];
    let no_proof = WitnessBundle {
        blobs: &empty_blobs,
        registry: None,
        finalized_roots: Some(authority.as_ref()),
    };
    assert!(matches!(
        market.evaluate_full(&matched, None, None, &meta, &no_proof),
        Err(ProgramError::WitnessedPredicateRejected { .. })
    ));
}

/// §11.3 — `AnyOfBound`: witnessed branches under ⊔. An escrow releases when
/// EITHER the cheap `Simple` timeout branch (`state >= 2`) holds OR the
/// `Witnessed` cross-cell finalized-read branch opens (`mark` (slot 0) ==
/// oracle 0x11's finalized `price`). Mirrors the proven Lean keystones
/// `evalConstraint_anyOfBound_iff` (admit iff some branch admits),
/// `anyOfBound_stripped_proof_branch_fails` (THE anti-strip tooth — a
/// witnessed branch with an absent proof FAILS, cannot masquerade as a
/// no-proof branch), and `BoundBranch.witnessed_iff` (the witnessed branch
/// has real teeth). LAW #1: each branch CALLS the evaluator the executor
/// already owns (`evaluate_simple_constraint` / the `ObservedFieldEquals`
/// verification) — no new semantics.
#[test]
fn any_of_bound_disjoins_witnessed_and_cheap_branches() {
    use crate::predicate::{FinalizedRootAuthority, StaticFinalizedRootAuthority};

    let oracle = [0x11u8; 32];
    let at_root = [0xABu8; 32];
    let price = field_from_u64(7); // the oracle's finalized `price` (field 1)

    let authority: std::sync::Arc<dyn FinalizedRootAuthority> = std::sync::Arc::new(
        StaticFinalizedRootAuthority::new().authorize(oracle, at_root, 1, price),
    );
    let proof_bytes = [0u8; 1];
    let blobs = [WitnessBlobView {
        kind: WitnessKindTag::MerklePath,
        bytes: &proof_bytes,
    }];
    // Bundle WITH the host authority + Merkle-open proof (the witnessed
    // branch can open).
    let opened = WitnessBundle {
        blobs: &blobs,
        registry: None,
        finalized_roots: Some(authority.as_ref()),
    };
    // Bundle with NO host authority (the witnessed branch's proof is
    // effectively STRIPPED — no channel to the peer's real finalized roots).
    let stripped = WitnessBundle::empty();
    let meta = TransitionMeta::wildcard();

    // The escrow: release if `state >= 2` (cheap timeout) OR mark == oracle's
    // finalized price (witnessed cross-cell read).
    let escrow = CellProgram::Predicate(vec![StateConstraint::AnyOfBound {
        branches: vec![
            BoundBranch::Simple(SimpleStateConstraint::FieldGte {
                index: 1, // `state` slot
                value: field_from_u64(2),
            }),
            BoundBranch::Witnessed {
                local_field: 0, // `mark` slot
                source_cell: oracle,
                source_field: 1,
                at_root,
                proof_witness_index: 0,
            },
        ],
    }]);

    // ADMIT via the CHEAP branch (state = 2 >= 2) — no proof needed; even the
    // stripped bundle admits because the cheap leg carries the turn.
    let mut timed_out = CellState::new(0);
    timed_out.fields[1] = field_from_u64(2);
    timed_out.fields[0] = field_from_u64(999); // mark mismatches — irrelevant, cheap leg wins
    assert!(
        escrow
            .evaluate_full(&timed_out, None, None, &meta, &stripped)
            .is_ok(),
        "the cheap timeout branch must admit with no proof (AnyOfBound is a disjunction)"
    );

    // ADMIT via the WITNESSED branch (mark = 7 == oracle's finalized price),
    // even though the cheap branch FAILS (state = 1 < 2). The witnessed
    // branch has real teeth (`BoundBranch.witnessed_iff`).
    let mut credentialed = CellState::new(0);
    credentialed.fields[1] = field_from_u64(1); // cheap branch fails
    credentialed.fields[0] = price; // mark == finalized price
    assert!(
        escrow
            .evaluate_full(&credentialed, None, None, &meta, &opened)
            .is_ok(),
        "the witnessed finalized-read branch must admit when its proof opens"
    );

    // REFUSE-ALL (THE anti-strip tooth, `anyOfBound_stripped_proof_branch_fails`):
    // the cheap branch fails (state = 1 < 2) AND the witnessed branch's proof
    // is STRIPPED (no host authority) — the witnessed branch CANNOT masquerade
    // as a no-proof branch, so the whole gate REFUSES. A submitter stripping
    // the proof does NOT slide down a cheaper path (§4).
    assert!(
        matches!(
            escrow.evaluate_full(&credentialed, None, None, &meta, &stripped),
            Err(_)
        ),
        "a stripped witnessed branch must FAIL, not masquerade as a no-proof branch"
    );

    // REFUSE: the witnessed proof opens but MISMATCHES (mark = 9 != finalized
    // 7) and the cheap branch fails — the binding has teeth in both
    // directions (`observedFieldEquals_mismatch_refuses`).
    let mut diverged = CellState::new(0);
    diverged.fields[1] = field_from_u64(1); // cheap branch fails
    diverged.fields[0] = field_from_u64(9); // mark != finalized price
    assert!(matches!(
        escrow.evaluate_full(&diverged, None, None, &meta, &opened),
        Err(_)
    ));

    // A PURELY-witnessed AnyOfBound with the proof stripped refuses entirely
    // (no cheap fallback) — the strongest form of the anti-strip tooth.
    let witnessed_only = CellProgram::Predicate(vec![StateConstraint::AnyOfBound {
        branches: vec![BoundBranch::Witnessed {
            local_field: 0,
            source_cell: oracle,
            source_field: 1,
            at_root,
            proof_witness_index: 0,
        }],
    }]);
    assert!(
        matches!(
            witnessed_only.evaluate_full(&credentialed, None, None, &meta, &stripped),
            Err(_)
        ),
        "a purely-witnessed AnyOfBound with no proof must refuse (no cheap path exists)"
    );
    // …but admits once the finalized read opens (real teeth).
    assert!(
        witnessed_only
            .evaluate_full(&credentialed, None, None, &meta, &opened)
            .is_ok()
    );

    // An empty AnyOfBound is fail-closed (no branch can admit).
    let empty = CellProgram::Predicate(vec![StateConstraint::AnyOfBound { branches: vec![] }]);
    assert!(matches!(
        empty.evaluate_full(&timed_out, None, None, &meta, &opened),
        Err(ProgramError::ConstraintViolated { .. })
    ));

    // The view projection round-trips (the StateConstraintView arm is total).
    let view = StateConstraint::AnyOfBound {
        branches: vec![
            BoundBranch::Simple(SimpleStateConstraint::FieldGte {
                index: 1,
                value: field_from_u64(2),
            }),
            BoundBranch::Witnessed {
                local_field: 0,
                source_cell: oracle,
                source_field: 1,
                at_root,
                proof_witness_index: 0,
            },
        ],
    }
    .to_view();
    assert!(matches!(
        view,
        StateConstraintView::AnyOfBound { branches } if branches.len() == 2
    ));
}

/// Blueprint gap 1: the committed-value knowledge gate under a state
/// guard — `state == RELEASED ⇒ PreimageGate` — now expressible
/// because `PreimageGate` is a `SimpleStateConstraint`.
#[test]
fn preimage_gate_composes_under_state_guard() {
    let released = field_from_u64(2);
    let preimage = [0x5Au8; 32];
    let commitment = *blake3::hash(&preimage).as_bytes();
    let gate = CellProgram::Predicate(vec![StateConstraint::AnyOf {
        variants: vec![
            SimpleStateConstraint::Not(Box::new(SimpleStateConstraint::FieldEquals {
                index: 0,
                value: released,
            })),
            SimpleStateConstraint::PreimageGate {
                commitment_index: 4,
                hash_kind: HashKind::Blake3,
            },
        ],
    }]);
    let mut state = CellState::new(0);
    state.fields[0] = released;
    state.fields[4] = commitment;

    let blobs = [WitnessBlobView {
        kind: WitnessKindTag::Preimage32,
        bytes: &preimage,
    }];
    let with_reveal = WitnessBundle {
        blobs: &blobs,
        registry: None,
        finalized_roots: None,
    };
    // Release with the correct reveal: admitted.
    assert!(
        gate.evaluate_full(
            &state,
            None,
            None,
            &TransitionMeta::wildcard(),
            &with_reveal
        )
        .is_ok()
    );
    // Release without a reveal: rejected (fail-closed inside AnyOf).
    assert!(
        gate.evaluate_full(
            &state,
            None,
            None,
            &TransitionMeta::wildcard(),
            &WitnessBundle::empty()
        )
        .is_err()
    );
    // Wrong preimage: rejected.
    let wrong = [0x66u8; 32];
    let blobs_wrong = [WitnessBlobView {
        kind: WitnessKindTag::Preimage32,
        bytes: &wrong,
    }];
    let with_wrong = WitnessBundle {
        blobs: &blobs_wrong,
        registry: None,
        finalized_roots: None,
    };
    assert!(
        gate.evaluate_full(&state, None, None, &TransitionMeta::wildcard(), &with_wrong)
            .is_err()
    );
    // Not released: the gate is dormant, no reveal needed.
    let mut open = state.clone();
    open.fields[0] = field_from_u64(1);
    assert!(
        gate.evaluate_full(
            &open,
            None,
            None,
            &TransitionMeta::wildcard(),
            &WitnessBundle::empty()
        )
        .is_ok()
    );
}

/// VIEW-PROJECTION TOTALITY PIN — the live-view seam must never reopen.
///
/// Constructs one instance of EVERY `StateConstraint` variant (and every
/// `SimpleStateConstraint` variant), projects each through `to_view`,
/// and pins the serialized `kind` tag. Two teeth:
///
/// 1. The `to_view` match itself has no wildcard arm, so adding a
///    variant without a projection is a COMPILE error.
/// 2. This test exhaustively matches over the same constructor list, so
///    a projection that maps a variant to the WRONG kind tag (or drops
///    its payload tag) fails here.
#[test]
fn view_projection_is_total_and_kind_tagged() {
    use crate::predicate::{InputRef, WitnessedPredicate, WitnessedPredicateKind};

    let fe = field_from_u64(7);
    let all: Vec<(StateConstraint, &str)> = vec![
        (
            StateConstraint::FieldEquals {
                index: 0,
                value: fe,
            },
            "FieldEquals",
        ),
        (
            StateConstraint::FieldGte {
                index: 0,
                value: fe,
            },
            "FieldGte",
        ),
        (
            StateConstraint::FieldLte {
                index: 0,
                value: fe,
            },
            "FieldLte",
        ),
        (
            StateConstraint::FieldLteField {
                left_index: 0,
                right_index: 1,
            },
            "FieldLteField",
        ),
        (
            StateConstraint::FieldLteOther {
                index: 0,
                other: 1,
                delta: -3,
            },
            "FieldLteOther",
        ),
        (
            StateConstraint::SumEquals {
                indices: vec![0, 1],
                value: fe,
            },
            "SumEquals",
        ),
        (StateConstraint::WriteOnce { index: 1 }, "WriteOnce"),
        (StateConstraint::Immutable { index: 1 }, "Immutable"),
        (StateConstraint::Monotonic { index: 1 }, "Monotonic"),
        (
            StateConstraint::StrictMonotonic { index: 1 },
            "StrictMonotonic",
        ),
        (
            StateConstraint::BoundedBy {
                index: 1,
                witness_index: 2,
            },
            "BoundedBy",
        ),
        (
            StateConstraint::FieldDelta {
                index: 1,
                delta: fe,
            },
            "FieldDelta",
        ),
        (
            StateConstraint::FieldDeltaInRange {
                index: 1,
                min_delta: fe,
                max_delta: fe,
            },
            "FieldDeltaInRange",
        ),
        (
            StateConstraint::FieldGteHeight {
                index: 1,
                offset: 0,
            },
            "FieldGteHeight",
        ),
        (
            StateConstraint::FieldLteHeight {
                index: 1,
                offset: 0,
            },
            "FieldLteHeight",
        ),
        (
            StateConstraint::SumEqualsAcross {
                input_fields: vec![0],
                output_fields: vec![1],
            },
            "SumEqualsAcross",
        ),
        (
            StateConstraint::SenderAuthorized {
                set: AuthorizedSet::BlindedSet {
                    commitment: [9u8; 32],
                },
            },
            "SenderAuthorized",
        ),
        (
            StateConstraint::CapabilityUniqueness {
                cap_set_root_slot: 3,
            },
            "CapabilityUniqueness",
        ),
        (
            StateConstraint::RateLimit {
                max_per_epoch: 4,
                epoch_duration: 100,
            },
            "RateLimit",
        ),
        (
            StateConstraint::RateLimitBySum {
                slot_index: 1,
                max_sum_per_epoch: 10,
                epoch_duration: 100,
            },
            "RateLimitBySum",
        ),
        (
            StateConstraint::TemporalGate {
                not_before: Some(5),
                not_after: None,
            },
            "TemporalGate",
        ),
        (
            StateConstraint::PreimageGate {
                commitment_index: 2,
                hash_kind: HashKind::Poseidon2,
            },
            "PreimageGate",
        ),
        (
            StateConstraint::MonotonicSequence { seq_index: 0 },
            "MonotonicSequence",
        ),
        (
            StateConstraint::AllowedTransitions {
                slot_index: 0,
                allowed: vec![(field_from_u64(0), field_from_u64(1))],
            },
            "AllowedTransitions",
        ),
        (
            StateConstraint::TemporalPredicate {
                witness_index: 0,
                dsl_hash: [1u8; 32],
            },
            "TemporalPredicate",
        ),
        (
            StateConstraint::BoundDelta {
                local_slot: 0,
                peer_cell: crate::id::CellId([2u8; 32]),
                peer_slot: 1,
                delta_relation: DeltaRelation::EqualAndOpposite,
            },
            "BoundDelta",
        ),
        (
            StateConstraint::AnyOf {
                variants: vec![
                    SimpleStateConstraint::Monotonic { index: 0 },
                    SimpleStateConstraint::Not(Box::new(SimpleStateConstraint::FieldEquals {
                        index: 0,
                        value: fe,
                    })),
                ],
            },
            "AnyOf",
        ),
        (
            StateConstraint::Witnessed {
                wp: WitnessedPredicate {
                    kind: WitnessedPredicateKind::Dfa,
                    commitment: [3u8; 32],
                    input_ref: InputRef::Sender,
                    proof_witness_index: 0,
                },
            },
            "Witnessed",
        ),
        (
            StateConstraint::Renounced {
                set: RenouncedSet::BlindedSet {
                    commitment: [4u8; 32],
                },
            },
            "Renounced",
        ),
        (
            StateConstraint::MemberOf {
                index: 0,
                set: vec![1, 2, 3],
            },
            "MemberOf",
        ),
        (
            StateConstraint::PrefixOf {
                seg_indices: vec![0, 1],
                prefix: vec![42],
            },
            "PrefixOf",
        ),
        (
            StateConstraint::InRangeTwoSided {
                index: 0,
                lo: 1,
                hi: 9,
            },
            "InRangeTwoSided",
        ),
        (
            StateConstraint::DeltaBounded { index: 0, d: 5 },
            "DeltaBounded",
        ),
        (
            StateConstraint::AffineLe {
                terms: vec![(2, 2), (-1, 3)],
                c: 0,
            },
            "AffineLe",
        ),
        (
            StateConstraint::AffineEq {
                terms: vec![(1, 0), (1, 1)],
                c: 10,
            },
            "AffineEq",
        ),
        (
            StateConstraint::Reachable {
                from_index: 0,
                to_label: 9,
                edges: vec![(1, 9)],
            },
            "Reachable",
        ),
        (
            StateConstraint::AllOf {
                variants: vec![SimpleStateConstraint::WriteOnce { index: 0 }],
            },
            "AllOf",
        ),
        (
            StateConstraint::Custom {
                ir_hash: [5u8; 32],
                descriptor: CustomDescriptor::default(),
                reads: ReadSet::default(),
            },
            "Custom",
        ),
        (StateConstraint::SenderIs { pk: [7u8; 32] }, "SenderIs"),
        (StateConstraint::SenderInSlot { index: 2 }, "SenderInSlot"),
        (StateConstraint::BalanceGte { min: 10 }, "BalanceGte"),
        (StateConstraint::BalanceLte { max: 0 }, "BalanceLte"),
        (
            StateConstraint::KeyRotationGate {
                digest_slot: 1,
                current_slot: 2,
                last_rotated_slot: 3,
                cooling_period: 50,
                hash_kind: HashKind::Blake3,
            },
            "KeyRotationGate",
        ),
        (
            StateConstraint::HeapField {
                key: 99,
                atom: HeapAtom::Monotonic,
            },
            "HeapField",
        ),
        (
            StateConstraint::DelegationEpochEquals { index: 2 },
            "DelegationEpochEquals",
        ),
        (
            StateConstraint::CountGe {
                threshold: 2,
                set_commitment_slot: 5,
            },
            "CountGe",
        ),
        (
            StateConstraint::SenderMemberOf {
                members: vec![[1u8; 32], [2u8; 32]],
            },
            "SenderMemberOf",
        ),
        (
            StateConstraint::BalanceDeltaLte { max: 10 },
            "BalanceDeltaLte",
        ),
        (
            StateConstraint::BalanceDeltaGte { min: -5 },
            "BalanceDeltaGte",
        ),
        (
            StateConstraint::AffineDeltaLe {
                terms: vec![(1, 1), (1, 2)],
                c: 50,
            },
            "AffineDeltaLe",
        ),
        (
            StateConstraint::ObservedFieldEquals {
                local_field: 0,
                source_cell: [9u8; 32],
                source_field: 1,
                at_root: [7u8; 32],
                proof_witness_index: 0,
            },
            "ObservedFieldEquals",
        ),
        (
            StateConstraint::CollectionAggregate {
                collection_id: 1,
                stride: 2,
                fuel: 8,
                pred: CollPred::MOfNDistinct {
                    m: 3,
                    key_offset: 0,
                    approved: ElemPredAtom::FieldEquals {
                        offset: 1,
                        value: field_from_u64(1),
                    },
                },
            },
            "CollectionAggregate",
        ),
        (
            StateConstraint::FieldsCollectionAggregate {
                base: 16,
                stride: 2,
                fuel: 8,
                pred: CollPred::MOfNDistinct {
                    m: 3,
                    key_offset: 0,
                    approved: ElemPredAtom::FieldEquals {
                        offset: 1,
                        value: field_from_u64(1),
                    },
                },
            },
            "FieldsCollectionAggregate",
        ),
        (
            StateConstraint::AnyOfBound {
                branches: vec![
                    BoundBranch::Simple(SimpleStateConstraint::FieldGte {
                        index: 1,
                        value: field_from_u64(2),
                    }),
                    BoundBranch::Witnessed {
                        local_field: 0,
                        source_cell: [9u8; 32],
                        source_field: 1,
                        at_root: [7u8; 32],
                        proof_witness_index: 0,
                    },
                ],
            },
            "AnyOfBound",
        ),
        (StateConstraint::SymEq { index: 0, sym: 7 }, "SymEq"),
        (
            StateConstraint::SymMemberOf {
                index: 0,
                set: vec![0, 1, 2],
            },
            "SymMemberOf",
        ),
        (
            StateConstraint::DigEq {
                index: 0,
                digest: [9u8; 32],
            },
            "DigEq",
        ),
        (
            StateConstraint::DigFieldEq {
                left_index: 0,
                right_index: 1,
            },
            "DigFieldEq",
        ),
        (
            StateConstraint::ClearanceDominates {
                actor_label_index: 0,
                box_index: 6,
                root_index: 3,
                edges: vec![([1u8; 32], [2u8; 32])],
            },
            "ClearanceDominates",
        ),
        (
            StateConstraint::RateBound {
                counter_index: 1,
                k: 5,
            },
            "RateBound",
        ),
        (
            StateConstraint::CooledSince {
                staged_at: 100,
                period: 50,
            },
            "CooledSince",
        ),
        (StateConstraint::UntilEvent { flag_index: 2 }, "UntilEvent"),
        (StateConstraint::SinceEvent { flag_index: 2 }, "SinceEvent"),
        (
            StateConstraint::ChallengeWindow {
                challenge_index: 2,
                staged_at: 100,
                period: 50,
            },
            "ChallengeWindow",
        ),
        (
            StateConstraint::SettleEscrow {
                leg_a_index: 3,
                leg_b_index: 4,
            },
            "SettleEscrow",
        ),
        (
            StateConstraint::DischargeObligation {
                cursor_slot: 1,
                due_slot: 2,
                amount_slot: 3,
                period: 100,
                amount: 50,
            },
            "DischargeObligation",
        ),
        (
            StateConstraint::VaultDeposit {
                assets_slot: 0,
                shares_slot: 1,
            },
            "VaultDeposit",
        ),
        (
            StateConstraint::HeapFieldLteOther {
                key: 130,
                other_key: 131,
                delta: 0,
            },
            "HeapFieldLteOther",
        ),
    ];

    // COVERAGE TOOTH: this match must name every variant exactly once.
    // Adding a `StateConstraint` variant forces an arm here AND a
    // projection arm in `to_view` (both are non-wildcard matches).
    for (sc, _) in &all {
        match sc {
            StateConstraint::FieldEquals { .. }
            | StateConstraint::FieldGte { .. }
            | StateConstraint::FieldLte { .. }
            | StateConstraint::FieldLteField { .. }
            | StateConstraint::FieldLteOther { .. }
            | StateConstraint::SumEquals { .. }
            | StateConstraint::WriteOnce { .. }
            | StateConstraint::Immutable { .. }
            | StateConstraint::Monotonic { .. }
            | StateConstraint::StrictMonotonic { .. }
            | StateConstraint::BoundedBy { .. }
            | StateConstraint::FieldDelta { .. }
            | StateConstraint::FieldDeltaInRange { .. }
            | StateConstraint::FieldGteHeight { .. }
            | StateConstraint::FieldLteHeight { .. }
            | StateConstraint::SumEqualsAcross { .. }
            | StateConstraint::SenderAuthorized { .. }
            | StateConstraint::CapabilityUniqueness { .. }
            | StateConstraint::RateLimit { .. }
            | StateConstraint::RateLimitBySum { .. }
            | StateConstraint::TemporalGate { .. }
            | StateConstraint::PreimageGate { .. }
            | StateConstraint::MonotonicSequence { .. }
            | StateConstraint::AllowedTransitions { .. }
            | StateConstraint::TemporalPredicate { .. }
            | StateConstraint::BoundDelta { .. }
            | StateConstraint::AnyOf { .. }
            | StateConstraint::Witnessed { .. }
            | StateConstraint::Renounced { .. }
            | StateConstraint::MemberOf { .. }
            | StateConstraint::PrefixOf { .. }
            | StateConstraint::InRangeTwoSided { .. }
            | StateConstraint::DeltaBounded { .. }
            | StateConstraint::AffineLe { .. }
            | StateConstraint::AffineEq { .. }
            | StateConstraint::Reachable { .. }
            | StateConstraint::AllOf { .. }
            | StateConstraint::Custom { .. }
            | StateConstraint::SenderIs { .. }
            | StateConstraint::SenderInSlot { .. }
            | StateConstraint::BalanceGte { .. }
            | StateConstraint::BalanceLte { .. }
            | StateConstraint::KeyRotationGate { .. }
            | StateConstraint::HeapField { .. }
            | StateConstraint::DelegationEpochEquals { .. }
            | StateConstraint::CountGe { .. }
            | StateConstraint::SenderMemberOf { .. }
            | StateConstraint::BalanceDeltaLte { .. }
            | StateConstraint::BalanceDeltaGte { .. }
            | StateConstraint::AffineDeltaLe { .. }
            | StateConstraint::ObservedFieldEquals { .. }
            | StateConstraint::CollectionAggregate { .. }
            | StateConstraint::FieldsCollectionAggregate { .. }
            | StateConstraint::AnyOfBound { .. }
            | StateConstraint::SymEq { .. }
            | StateConstraint::SymMemberOf { .. }
            | StateConstraint::DigEq { .. }
            | StateConstraint::DigFieldEq { .. }
            | StateConstraint::ClearanceDominates { .. }
            | StateConstraint::RateBound { .. }
            | StateConstraint::CooledSince { .. }
            | StateConstraint::UntilEvent { .. }
            | StateConstraint::SinceEvent { .. }
            | StateConstraint::ChallengeWindow { .. }
            | StateConstraint::SettleEscrow { .. }
            | StateConstraint::DischargeObligation { .. }
            | StateConstraint::VaultDeposit { .. }
            | StateConstraint::HeapFieldLteOther { .. } => {}
        }
    }

    for (sc, expected_kind) in &all {
        let view = sc.to_view();
        let json = serde_json::to_value(&view).expect("view serializes");
        assert_eq!(
            json.get("kind").and_then(|k| k.as_str()),
            Some(*expected_kind),
            "view kind tag for {sc:?}"
        );
    }

    // Semantic-payload spot checks for the newly projected variants —
    // a live council cell must self-describe its threshold M.
    let affine = StateConstraint::AffineLe {
        terms: vec![(2, 2), (-1, 3), (-1, 4)],
        c: 0,
    };
    let j = serde_json::to_value(affine.to_view()).unwrap();
    assert_eq!(j["terms"][0][0], 2, "AffineLe view carries coefficients");
    assert_eq!(j["terms"][0][1], 2, "AffineLe view carries slot indices");
    assert_eq!(j["c"], 0, "AffineLe view carries the bound");

    let member = StateConstraint::MemberOf {
        index: 6,
        set: vec![10, 20],
    };
    let j = serde_json::to_value(member.to_view()).unwrap();
    assert_eq!(
        j["set"],
        serde_json::json!([10, 20]),
        "MemberOf view carries the allowed set"
    );

    // SimpleStateConstraint totality (incl. the structural Not view).
    let simples: Vec<(SimpleStateConstraint, &str)> = vec![
        (
            SimpleStateConstraint::FieldEquals {
                index: 0,
                value: fe,
            },
            "FieldEquals",
        ),
        (
            SimpleStateConstraint::FieldGte {
                index: 0,
                value: fe,
            },
            "FieldGte",
        ),
        (
            SimpleStateConstraint::FieldLte {
                index: 0,
                value: fe,
            },
            "FieldLte",
        ),
        (SimpleStateConstraint::WriteOnce { index: 0 }, "WriteOnce"),
        (SimpleStateConstraint::Immutable { index: 0 }, "Immutable"),
        (SimpleStateConstraint::Monotonic { index: 0 }, "Monotonic"),
        (
            SimpleStateConstraint::StrictMonotonic { index: 0 },
            "StrictMonotonic",
        ),
        (
            SimpleStateConstraint::BoundedBy {
                index: 0,
                witness_index: 1,
            },
            "BoundedBy",
        ),
        (
            SimpleStateConstraint::FieldGteHeight {
                index: 0,
                offset: 1,
            },
            "FieldGteHeight",
        ),
        (
            SimpleStateConstraint::FieldLteHeight {
                index: 0,
                offset: 1,
            },
            "FieldLteHeight",
        ),
        (
            SimpleStateConstraint::TemporalGate {
                not_before: None,
                not_after: Some(9),
            },
            "TemporalGate",
        ),
        (
            SimpleStateConstraint::Not(Box::new(SimpleStateConstraint::WriteOnce { index: 0 })),
            "Not",
        ),
        (
            SimpleStateConstraint::SenderIs { pk: [7u8; 32] },
            "SenderIs",
        ),
        (
            SimpleStateConstraint::SenderInSlot { index: 2 },
            "SenderInSlot",
        ),
        (SimpleStateConstraint::BalanceGte { min: 10 }, "BalanceGte"),
        (SimpleStateConstraint::BalanceLte { max: 0 }, "BalanceLte"),
        (
            SimpleStateConstraint::PreimageGate {
                commitment_index: 4,
                hash_kind: HashKind::Blake3,
            },
            "PreimageGate",
        ),
        (
            SimpleStateConstraint::HeapField {
                key: 99,
                atom: HeapAtom::Immutable,
            },
            "HeapField",
        ),
        (
            SimpleStateConstraint::DelegationEpochEquals { index: 2 },
            "DelegationEpochEquals",
        ),
        (
            SimpleStateConstraint::CountGe {
                threshold: 2,
                set_commitment_slot: 5,
            },
            "CountGe",
        ),
    ];
    for (sc, expected_kind) in &simples {
        match sc {
            SimpleStateConstraint::FieldEquals { .. }
            | SimpleStateConstraint::FieldGte { .. }
            | SimpleStateConstraint::FieldLte { .. }
            | SimpleStateConstraint::WriteOnce { .. }
            | SimpleStateConstraint::Immutable { .. }
            | SimpleStateConstraint::Monotonic { .. }
            | SimpleStateConstraint::StrictMonotonic { .. }
            | SimpleStateConstraint::BoundedBy { .. }
            | SimpleStateConstraint::FieldGteHeight { .. }
            | SimpleStateConstraint::FieldLteHeight { .. }
            | SimpleStateConstraint::TemporalGate { .. }
            | SimpleStateConstraint::Not(_)
            | SimpleStateConstraint::SenderIs { .. }
            | SimpleStateConstraint::SenderInSlot { .. }
            | SimpleStateConstraint::BalanceGte { .. }
            | SimpleStateConstraint::BalanceLte { .. }
            | SimpleStateConstraint::PreimageGate { .. }
            | SimpleStateConstraint::HeapField { .. }
            | SimpleStateConstraint::DelegationEpochEquals { .. }
            | SimpleStateConstraint::CountGe { .. }
            | SimpleStateConstraint::SenderMemberOf { .. }
            | SimpleStateConstraint::BalanceDeltaLte { .. }
            | SimpleStateConstraint::BalanceDeltaGte { .. } => {}
        }
        let json = serde_json::to_value(sc.to_view()).expect("simple view serializes");
        assert_eq!(
            json.get("kind").and_then(|k| k.as_str()),
            Some(*expected_kind),
            "simple view kind tag for {sc:?}"
        );
    }
    // Not carries its inner constraint structurally (not a debug hack).
    let not = SimpleStateConstraint::Not(Box::new(SimpleStateConstraint::FieldEquals {
        index: 0,
        value: fe,
    }));
    let j = serde_json::to_value(not.to_view()).unwrap();
    assert_eq!(
        j["inner"]["kind"], "FieldEquals",
        "Not view nests its inner view"
    );
}

// ── Register-reading temporal atoms (the proven `TemporalAlgebra` family) ──
//
// PLUMBING-ON-PROOF: these mirror, value-for-value, the `#assert_axioms`-clean
// Lean `#guard` non-vacuity examples in
// `metatheory/Dregg2/Authority/TemporalAlgebra{,2}.lean` (§6 / §1). Each atom
// reads the COMMITTED PRE-state register (`old_state`) the way the Lean atoms
// read the target cell's pre-state record; both polarities must bite.

/// Pre-state record carrying the two registers the register atoms read:
/// an admission counter `bids_count` at slot 1 = 3, an empty `challenge`
/// register at slot 2 = 0 (the Lean `tRec`).
fn t_rec(counter: u64, challenge: u64) -> CellState {
    let mut s = CellState::new(0);
    s.fields[1] = field_from_u64(counter);
    s.fields[2] = field_from_u64(challenge);
    s
}

#[test]
fn rate_bound_under_and_at_limit() {
    // Lean: rateBound "bids_count" 5 .eval _ tRec == true (3 < 5);
    //       rateBound "bids_count" 3 .eval _ tRec == false (3 ≮ 3).
    let old = t_rec(3, 0);
    let new_s = t_rec(3, 0);
    let under = CellProgram::Predicate(vec![StateConstraint::RateBound {
        counter_index: 1,
        k: 5,
    }]);
    assert!(
        under.evaluate(&new_s, Some(&old), None).is_ok(),
        "3 < 5 admits"
    );
    let at = CellProgram::Predicate(vec![StateConstraint::RateBound {
        counter_index: 1,
        k: 3,
    }]);
    assert!(
        at.evaluate(&new_s, Some(&old), None).is_err(),
        "3 ≮ 3 rejects"
    );
}

#[test]
fn until_since_event_flip() {
    // Lean: untilEvent admits while flag = 0, rejects once set; sinceEvent the
    // exact complement (until_since_complement).
    let until = CellProgram::Predicate(vec![StateConstraint::UntilEvent { flag_index: 2 }]);
    let since = CellProgram::Predicate(vec![StateConstraint::SinceEvent { flag_index: 2 }]);

    let open = t_rec(3, 0); // challenge register 0 = event not yet fired
    assert!(
        until.evaluate(&open, Some(&open), None).is_ok(),
        "U admits before event"
    );
    assert!(
        since.evaluate(&open, Some(&open), None).is_err(),
        "S fails closed before event"
    );

    let fired = t_rec(3, 1); // the event register flipped non-zero
    assert!(
        until.evaluate(&fired, Some(&fired), None).is_err(),
        "U closed after event"
    );
    assert!(
        since.evaluate(&fired, Some(&fired), None).is_ok(),
        "S admits since event"
    );
}

#[test]
fn cooled_since_boundary() {
    // Lean: cooledSince 100 50 refuses at 149 (still cooling), admits at 150.
    let p = CellProgram::Predicate(vec![StateConstraint::CooledSince {
        staged_at: 100,
        period: 50,
    }]);
    assert!(
        p.evaluate(&t_rec(3, 0), None, Some(&ctx_at(149))).is_err(),
        "still cooling at 149"
    );
    assert!(
        p.evaluate(&t_rec(3, 0), None, Some(&ctx_at(150))).is_ok(),
        "cooled at 150"
    );
}

#[test]
fn challenge_window_three_polarities() {
    // Lean: challengeWindow "challenge" 100 50 — true after a challenge-free
    // window (height 150, register 0); false while the window is open (120);
    // false once challenged (height 150, register != 0).
    let p = CellProgram::Predicate(vec![StateConstraint::ChallengeWindow {
        challenge_index: 2,
        staged_at: 100,
        period: 50,
    }]);
    let clean = t_rec(3, 0);
    let challenged = t_rec(3, 1);
    assert!(
        p.evaluate(&clean, Some(&clean), Some(&ctx_at(150))).is_ok(),
        "elapsed + unchallenged"
    );
    assert!(
        p.evaluate(&clean, Some(&clean), Some(&ctx_at(120)))
            .is_err(),
        "window still open"
    );
    assert!(
        p.evaluate(&challenged, Some(&challenged), Some(&ctx_at(150)))
            .is_err(),
        "challenge filed"
    );
}

#[test]
fn temporal_register_atoms_round_trip_views() {
    // The new caveats are first-class in the self-describing live view.
    for (sc, kind) in [
        (
            StateConstraint::RateBound {
                counter_index: 1,
                k: 5,
            },
            "RateBound",
        ),
        (
            StateConstraint::CooledSince {
                staged_at: 100,
                period: 50,
            },
            "CooledSince",
        ),
        (StateConstraint::UntilEvent { flag_index: 2 }, "UntilEvent"),
        (StateConstraint::SinceEvent { flag_index: 2 }, "SinceEvent"),
        (
            StateConstraint::ChallengeWindow {
                challenge_index: 2,
                staged_at: 100,
                period: 50,
            },
            "ChallengeWindow",
        ),
    ] {
        let json = serde_json::to_value(sc.to_view()).expect("view serializes");
        assert_eq!(json.get("kind").and_then(|k| k.as_str()), Some(kind));
    }
}

// ─── NUMERICS AUDIT: DischargeObligation no-wrap (field-vs-integer close) ────────
//
// The DischargeObligation gate verifies a schedule transition
// `cursor_after == cursor_before + period` and `total_after == total_before + amount`.
// Both were computed with `wrapping_add`, so a `total_before` near `u64::MAX` let the
// expected total WRAP to a small value — a prover could then satisfy the equality with
// a `total_after` that does NOT reflect the true accumulated discharge (a
// value-conservation forgery by wraparound, the exact class the shielded-ring /
// cross-cell conservation AIRs close). The gate now uses `checked_add` and fails CLOSED
// on overflow. Both polarities:

/// The HONEST discharge (advance by exactly one period / the schedule amount) still
/// passes — no liveness lost by the no-wrap hardening.
#[test]
fn discharge_obligation_honest_advance_passes() {
    let p = CellProgram::Predicate(vec![StateConstraint::DischargeObligation {
        cursor_slot: 1,
        due_slot: 2,
        amount_slot: 3,
        period: 1,
        amount: 50,
    }]);
    let mut old = CellState::new(0);
    old.fields[1] = field_from_u64(0); // cursor_before
    old.fields[2] = field_from_u64(0); // due_block
    old.fields[3] = field_from_u64(100); // total_before
    let mut new_s = CellState::new(0);
    new_s.fields[1] = field_from_u64(1); // cursor advances one period
    new_s.fields[2] = field_from_u64(0);
    new_s.fields[3] = field_from_u64(150); // total advances by the schedule amount
    assert!(
        p.evaluate(&new_s, Some(&old), Some(&ctx_at(10))).is_ok(),
        "the honest per-period discharge must still pass"
    );
}

/// THE WRAPAROUND FORGERY, now UNSAT: `total_before = u64::MAX - 10`, `amount = 50`,
/// so the true total overflows `u64`. Pre-fix, `wrapping_add` yielded 39 and a prover
/// setting `total_after = 39` PASSED — minting a wrong committed total. The `checked_add`
/// gate now REFUSES the overflowing schedule (no wraparound-satisfiable equality).
#[test]
fn discharge_obligation_total_wraparound_is_refused() {
    let p = CellProgram::Predicate(vec![StateConstraint::DischargeObligation {
        cursor_slot: 1,
        due_slot: 2,
        amount_slot: 3,
        period: 1,
        amount: 50,
    }]);
    let total_before = u64::MAX - 10;
    let wrapped = total_before.wrapping_add(50); // = 39, the pre-fix "expected" total
    let mut old = CellState::new(0);
    old.fields[1] = field_from_u64(0);
    old.fields[2] = field_from_u64(0);
    old.fields[3] = field_from_u64(total_before);
    let mut new_s = CellState::new(0);
    new_s.fields[1] = field_from_u64(1); // cursor advances honestly (reaches the total gate)
    new_s.fields[2] = field_from_u64(0);
    new_s.fields[3] = field_from_u64(wrapped); // the forged, wraparound-satisfying total
    assert!(
        p.evaluate(&new_s, Some(&old), Some(&ctx_at(10))).is_err(),
        "a wraparound-satisfying discharged total must be REFUSED (no-wrap, fail closed)"
    );
}

/// THE CURSOR WRAPAROUND, now UNSAT: `cursor_before = u64::MAX`, `period = 1` overflows.
/// Pre-fix the wrapped cursor `0` was accepted; the `checked_add` gate now refuses it.
#[test]
fn discharge_obligation_cursor_wraparound_is_refused() {
    let p = CellProgram::Predicate(vec![StateConstraint::DischargeObligation {
        cursor_slot: 1,
        due_slot: 2,
        amount_slot: 3,
        period: 1,
        amount: 50,
    }]);
    let mut old = CellState::new(0);
    old.fields[1] = field_from_u64(u64::MAX); // cursor_before at the ceiling
    old.fields[2] = field_from_u64(0);
    old.fields[3] = field_from_u64(100);
    let mut new_s = CellState::new(0);
    new_s.fields[1] = field_from_u64(0); // the wrapped cursor a pre-fix prover would set
    new_s.fields[2] = field_from_u64(0);
    new_s.fields[3] = field_from_u64(150);
    assert!(
        p.evaluate(&new_s, Some(&old), Some(&ctx_at(10))).is_err(),
        "a wraparound-satisfying cursor advance must be REFUSED (no-wrap, fail closed)"
    );
}
