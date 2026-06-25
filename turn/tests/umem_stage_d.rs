//! **umem Stage D — the working/service domain + composable umems**
//! (UMEM-PRIMITIVE.md §3, §5, §7).
//!
//! Purely additive over the proven base — NO new soundness argument. Both legs
//! are the keystone (`boundary_init_root_bound`,
//! `metatheory/Dregg2/Crypto/UniversalMemory.lean:475`) applied at a new seam:
//!
//!  * **Working domain (§3).** A service cell's transient scratch is a
//!    `UDomain::Working` umem. It participates in the ONE memcheck trace — so it
//!    is consistent for free (`universal_memory_sound`) — but is NEVER emitted by
//!    `project_cell`/`project_ledger`, so its boundary root never enters the state
//!    commitment (it costs nothing on the consensus path), exactly like
//!    `Registers`.
//!
//!  * **Composable umems (§5).** A service umem holds, at a key, a `UVal::UmemRef`
//!    naming a CHILD cell's committed `heap_root`. The recursive open
//!    (`open_through_umem_ref`) binds the outer root (level 1), reads the child
//!    ref, then binds the child root and opens the child's heap (level 2) — two
//!    independent `boundary_init_root_bound` applications, the keystone composed
//!    with itself. Tag isolation (`consistentFrom_filter`) keeps the levels
//!    disjoint: the outer cells live in the `Working` domain, the child in `Heap`.

use std::collections::BTreeMap;

use dregg_cell::{Cell, Ledger};
use dregg_turn::umem::{
    RecursiveOpenError, UDomain, UKey, UProjection, UVal, UmemKind, UmemOp, disciplined, fold,
    open_through_umem_ref, project_cell, project_ledger, working_umem_root,
};

fn cell_seeded(seed: u8) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    Cell::with_balance(pk, [0u8; 32], 0)
}

fn bytes(n: u8) -> [u8; 32] {
    let mut b = [0u8; 32];
    b[0] = n;
    b
}

/// THE TWO-LEVEL OPEN — a working umem-of-roots → a child cell's heap, binding
/// BOTH roots; tag isolation keeps the two levels disjoint.
#[test]
fn two_level_open_binds_both_roots() {
    // -- the CHILD: a cell with a heap. Its committed heap_root is the level-2
    //    boundary. --
    let mut child = cell_seeded(10);
    child.state.set_heap(3, 7, bytes(42));
    child.state.set_heap(3, 9, bytes(13));
    let child_id = child.id();
    let child_root = child.state.heap_root;

    // project the child cell — this carries its `Heap` plane (the preimage the
    // level-2 bind re-folds), but NOT a separate `HeapRoot` cell.
    let mut proj = UProjection::new();
    project_cell(&child, &mut proj);
    assert_eq!(
        proj.get(&UKey::HeapRoot(child_id)),
        None,
        "heap_root is the derived commitment, not a projected cell"
    );

    // -- the SERVICE: a transient working umem holding the child's root as a
    //    UmemRef at (collection 1, key 0). --
    let service = cell_seeded(20);
    let service_id = service.id();
    proj.insert(
        UKey::Working {
            service: service_id,
            collection: 1,
            key: 0,
        },
        UVal::UmemRef(child_root),
    );
    // the outer boundary is derivable on demand (the §4 checkpoint), never
    // published.
    let service_root = working_umem_root(&proj, service_id);

    // THE RECURSIVE OPEN: bind the service umem (level 1), read the child ref,
    // bind the child heap (level 2), open the key.
    assert_eq!(
        open_through_umem_ref(&proj, service_id, service_root, 1, 0, child_id, 3, 7),
        Ok(Some(bytes(42))),
        "two-level open returns the child heap value"
    );
    // an absent child key opens to None (the Merkle-free freshness leg).
    assert_eq!(
        open_through_umem_ref(&proj, service_id, service_root, 1, 0, child_id, 3, 99),
        Ok(None),
        "an absent child key opens to None through both binds"
    );

    // -- TAMPER LEVEL 1: a forged working cell moves the outer root, so the
    //    outer bind refuses (the keystone's anti-forgery tooth at level 1). --
    let mut forged_outer = proj.clone();
    forged_outer.insert(
        UKey::Working {
            service: service_id,
            collection: 9,
            key: 9,
        },
        UVal::UmemRef(bytes(0xAA)),
    );
    match open_through_umem_ref(
        &forged_outer,
        service_id,
        service_root,
        1,
        0,
        child_id,
        3,
        7,
    ) {
        Err(RecursiveOpenError::OuterBindRefused {
            service,
            committed,
            derived,
        }) => {
            assert_eq!(service, service_id);
            assert_eq!(committed, service_root);
            assert_ne!(
                derived, service_root,
                "the tampered outer image moved the root"
            );
        }
        other => panic!("level-1 tamper must refuse with OuterBindRefused, got {other:?}"),
    }

    // -- TAMPER LEVEL 2: a forged child heap cell moves the child root, so the
    //    child bind refuses against the root the (untampered) ref named. --
    let mut forged_child = proj.clone();
    forged_child.insert(
        UKey::Heap {
            cell: child_id,
            collection: 3,
            key: 7,
        },
        UVal::Bytes32(bytes(0xBB)),
    );
    match open_through_umem_ref(
        &forged_child,
        service_id,
        service_root,
        1,
        0,
        child_id,
        3,
        7,
    ) {
        Err(RecursiveOpenError::ChildBindRefused(e)) => {
            assert_eq!(e.cell, child_id);
            assert_eq!(e.committed, child_root);
            assert_ne!(
                e.derived, child_root,
                "the tampered child image moved the root"
            );
        }
        other => panic!("level-2 tamper must refuse with ChildBindRefused, got {other:?}"),
    }

    // -- a value that is NOT a UmemRef at the ref address cannot be descended. --
    let mut not_a_ref = proj.clone();
    not_a_ref.insert(
        UKey::Working {
            service: service_id,
            collection: 1,
            key: 0,
        },
        UVal::Bytes32(child_root),
    );
    let nr_root = working_umem_root(&not_a_ref, service_id);
    assert!(matches!(
        open_through_umem_ref(&not_a_ref, service_id, nr_root, 1, 0, child_id, 3, 7),
        Err(RecursiveOpenError::RefNotAUmemRef { .. })
    ));
}

/// TAG ISOLATION — the two levels live in disjoint domains and can never alias;
/// two services get disjoint working scratch.
#[test]
fn levels_and_services_are_tag_isolated() {
    let child = cell_seeded(11);
    let svc_a = cell_seeded(21).id();
    let svc_b = cell_seeded(22).id();

    let working_key = UKey::Working {
        service: svc_a,
        collection: 1,
        key: 0,
    };
    let heap_key = UKey::Heap {
        cell: child.id(),
        collection: 1,
        key: 0,
    };
    // the working level and the heap level are different domains — disjoint by
    // tag, so a write in one can never cancel a claim in the other.
    assert_eq!(working_key.domain(), UDomain::Working);
    assert_eq!(heap_key.domain(), UDomain::Heap);
    assert_ne!(working_key.domain(), heap_key.domain());
    assert_eq!(
        UDomain::Working.code(),
        5,
        "working is a dedicated wire tag"
    );

    // two services keyed distinctly get disjoint scratch (same in-domain
    // collection/key, different owners ⇒ different cells).
    let a = UKey::Working {
        service: svc_a,
        collection: 1,
        key: 0,
    };
    let b = UKey::Working {
        service: svc_b,
        collection: 1,
        key: 0,
    };
    assert_ne!(a, b, "distinct services do not alias their working scratch");

    // a working cell carries NO owning cell — a CreateCell birth never pulls
    // transient scratch into the born cell's bundle.
    assert_eq!(working_key.cell(), None);
}

/// THE WORKING DOMAIN PUBLISHES NO BOUNDARY — it never appears in any projection
/// of persistent state, so its root never enters the state commitment (it costs
/// nothing on the consensus path), exactly like `Registers`.
#[test]
fn working_domain_publishes_no_boundary() {
    let mut child = cell_seeded(12);
    child.state.set_heap(1, 1, bytes(5));
    let service = cell_seeded(23).id();

    // a cell projection carries ZERO working cells.
    let mut proj = UProjection::new();
    project_cell(&child, &mut proj);
    assert!(
        proj.keys().all(|k| !matches!(k, UKey::Working { .. })),
        "project_cell never emits a working cell"
    );

    // neither does a whole-ledger projection.
    let mut ledger = Ledger::new();
    ledger.insert_cell(child.clone()).unwrap();
    let lproj = project_ledger(&ledger);
    assert!(
        lproj.keys().all(|k| !matches!(k, UKey::Working { .. })),
        "project_ledger never emits a working cell — no boundary on the consensus path"
    );

    // the working root is derivable on demand but is purely a function of the
    // (unpublished) working cells — empty service ⇒ the empty-heap root.
    let empty = working_umem_root(&proj, service);
    assert_eq!(
        empty,
        dregg_cell::state::compute_heap_root(&BTreeMap::new()),
        "an empty working umem derives the empty-heap root"
    );
}

/// THE WORKING DOMAIN RIDES THE BALANCE — a working-domain write goes through the
/// SAME memcheck machinery (`fold`/`disciplined`) as any domain; consistency is
/// free via `universal_memory_sound`, regardless of whether a boundary is
/// published.
#[test]
fn working_domain_participates_in_the_trace() {
    let service = cell_seeded(24).id();
    let pre = UProjection::new();

    let key = UKey::Working {
        service,
        collection: 2,
        key: 4,
    };
    let ops = vec![
        UmemOp {
            kind: UmemKind::Write,
            key: key.clone(),
            val: Some(UVal::UmemRef(bytes(77))),
            prev_val: None, // fresh transient cell
            prev_serial: 0,
        },
        UmemOp {
            kind: UmemKind::Read,
            key: key.clone(),
            val: Some(UVal::UmemRef(bytes(77))),
            prev_val: Some(UVal::UmemRef(bytes(77))),
            prev_serial: 1,
        },
    ];

    // the trace is disciplined and the fold installs the working cell.
    assert!(disciplined(&ops), "the working-domain trace is disciplined");
    let post = fold(&pre, &ops);
    assert_eq!(
        post.get(&key),
        Some(&UVal::UmemRef(bytes(77))),
        "the working cell rides the one trace and folds like any domain"
    );
    // sanity: it is genuinely in the Working domain.
    assert_eq!(key.domain(), UDomain::Working);
}
