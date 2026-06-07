//! SGM ADMISSION ⟷ LEAN DIFFERENTIAL — the mirror-drift tooth for `sgm_admit`.
//!
//! `src/lib.rs::sgm_admit` is a HAND-PORT of the proven Lean `sgmAdmitM`
//! (`metatheory/Dregg2/Apps/StorageGatewayMandate/Core.lean`): op-allowlist ∧ prefix-on-PUT ∧
//! clearance-on-GET ∧ Stingray volume-debit. A hand port can SILENTLY DRIFT (drop the
//! clearance leg, flip the debit `≤` to `<`, mis-order the op gates) and the proven
//! `sgmAdmitM` theorems would never notice the Rust copy diverged — exactly the out-of-band
//! seam this test kills.
//!
//! The Lean side now emits a `#guard`-PINNED decision vector `sgmDiffCorpus` over a fixed grid
//! of `(mandate, request, spent)`. This test enumerates the IDENTICAL grid through `sgm_admit`
//! and asserts the SAME vector (`SGM_LEAN_DECISIONS`, copied from the Lean `#guard`). Drift on
//! EITHER side fails:
//!   * `sgm_admit` changes        → Rust vector ≠ `SGM_LEAN_DECISIONS`            → FAIL here;
//!   * `sgmAdmitM` changes         → its `#guard sgmDiffCorpus == [...]` trips at Lean build,
//!     forcing a re-pin that re-exposes any Rust drift.
//!
//! Grid (matches Lean `sgmDiffMandates × sgmDiffReqs × sgmDiffSpents`, row-major):
//!   mandates = [demo (PUT/GET/LIST, clearance✓), guest (clearance✗), putOnly (PUT-only)]
//!   requests = [PUT uploads/a (cost 5), PUT secret/a (bad prefix), GET uploads/a (cost 1),
//!               LIST x (cost 2)]
//!   spents   = [0, 4, 8, 10]   (ceiling fixed at 10)

use starbridge_storage_gateway_mandate::{
    DEFAULT_KEY_PREFIX, DEFAULT_READ_COMPARTMENT, DEFAULT_VOLUME_CEILING, StorageOp, sgm_admit,
};
use starbridge_storage_gateway_mandate::{FieldElement, field_from_bytes};

/// Read-compartment label hash (the Lean `readCompartment = Label.named "storage-read"`).
fn read_compartment() -> FieldElement {
    field_from_bytes(DEFAULT_READ_COMPARTMENT.as_bytes())
}

/// Actor labels carrying clearance (demo / putOnly mandates: `mayRead` resolves ✓).
fn cleared_labels() -> Vec<FieldElement> {
    vec![read_compartment()]
}

/// Actor labels WITHOUT clearance (guest mandate: `mayRead` resolves ✗).
fn uncleared_labels() -> Vec<FieldElement> {
    vec![field_from_bytes(b"guest")]
}

/// A mandate row: which ops are allowed, whether the actor has read clearance.
struct MandateProfile {
    allowed: Vec<StorageOp>,
    cleared: bool,
}

fn mandate_profiles() -> Vec<MandateProfile> {
    vec![
        // demoMandate: PUT/GET/LIST, clearance✓
        MandateProfile {
            allowed: vec![StorageOp::Put, StorageOp::Get, StorageOp::List],
            cleared: true,
        },
        // guestMandate: same allowlist, clearance✗
        MandateProfile {
            allowed: vec![StorageOp::Put, StorageOp::Get, StorageOp::List],
            cleared: false,
        },
        // putOnlyMandate: PUT only, clearance✓ (irrelevant — GET not allowed)
        MandateProfile {
            allowed: vec![StorageOp::Put],
            cleared: true,
        },
    ]
}

/// (op, key) request grid — same order as Lean `sgmDiffReqs`.
fn reqs() -> Vec<(StorageOp, &'static str)> {
    vec![
        (StorageOp::Put, "uploads/a"),
        (StorageOp::Put, "secret/a"),
        (StorageOp::Get, "uploads/a"),
        (StorageOp::List, "x"),
    ]
}

const SPENTS: [u64; 4] = [0, 4, 8, 10];

/// The PINNED 48-row decision vector, copied VERBATIM from the Lean
/// `Dregg2.Apps.StorageGatewayMandate.sgmDiffCorpus` `#guard`. Each entry is
/// `(admitted, new_spent)`; `new_spent = 0` on reject. Row-major over mandates × reqs × spents.
#[rustfmt::skip]
const SGM_LEAN_DECISIONS: [(bool, u64); 48] = [
    // demoMandate (PUT/GET/LIST, prefix uploads/, clearance✓; put5 get1 list2)
    (true, 5),  (true, 9),  (false, 0), (false, 0), // PUT uploads/a (cost 5)
    (false, 0), (false, 0), (false, 0), (false, 0), // PUT secret/a (bad prefix)
    (true, 1),  (true, 5),  (true, 9),  (false, 0), // GET uploads/a (cost 1, clearance✓)
    (true, 2),  (true, 6),  (true, 10), (false, 0), // LIST x (cost 2)
    // guestMandate (clearance✗)
    (true, 5),  (true, 9),  (false, 0), (false, 0), // PUT uploads/a
    (false, 0), (false, 0), (false, 0), (false, 0), // PUT secret/a (bad prefix)
    (false, 0), (false, 0), (false, 0), (false, 0), // GET uploads/a (NO clearance)
    (true, 2),  (true, 6),  (true, 10), (false, 0), // LIST x
    // putOnlyMandate (PUT only)
    (true, 5),  (true, 9),  (false, 0), (false, 0), // PUT uploads/a
    (false, 0), (false, 0), (false, 0), (false, 0), // PUT secret/a (bad prefix)
    (false, 0), (false, 0), (false, 0), (false, 0), // GET uploads/a (op not allowed)
    (false, 0), (false, 0), (false, 0), (false, 0), // LIST x (op not allowed)
];

/// THE MIRROR-DRIFT TOOTH: the Rust `sgm_admit` decision over the grid must equal the
/// Lean-pinned `sgmDiffCorpus` exactly. A drift in either the hand-ported Rust admission or the
/// proven Lean predicate is caught here.
#[test]
fn sgm_admit_matches_lean_corpus() {
    let prefix = DEFAULT_KEY_PREFIX;
    let ceiling = DEFAULT_VOLUME_CEILING;
    assert_eq!(ceiling, 10, "corpus pinned to ceiling 10");
    let rc = read_compartment();

    let mut rust: Vec<(bool, u64)> = Vec::with_capacity(48);
    for profile in mandate_profiles() {
        let labels = if profile.cleared {
            cleared_labels()
        } else {
            uncleared_labels()
        };
        for (op, key) in reqs() {
            for &spent in &SPENTS {
                let verdict = sgm_admit(
                    spent,
                    ceiling,
                    key,
                    prefix,
                    op,
                    &profile.allowed,
                    &labels,
                    rc,
                );
                match verdict {
                    Some(new_spent) => rust.push((true, new_spent)),
                    None => rust.push((false, 0)),
                }
            }
        }
    }

    assert_eq!(
        rust.as_slice(),
        &SGM_LEAN_DECISIONS[..],
        "Rust sgm_admit DRIFTED from the proven Lean sgmAdmitM (sgmDiffCorpus). The hand-ported \
         admission no longer matches the verified predicate — a client-protecting guarantee \
         (op-allowlist / prefix / clearance / volume budget) may be broken. Reconcile lib.rs \
         sgm_admit with Core.lean sgmAdmitM."
    );
}

/// Spot teeth: the load-bearing rejections the executor MUST make.
#[test]
fn sgm_admit_rejects_no_clearance_get() {
    // GET with uncleared labels: rejected regardless of budget.
    assert_eq!(
        sgm_admit(
            0,
            10,
            "uploads/a",
            DEFAULT_KEY_PREFIX,
            StorageOp::Get,
            &[StorageOp::Get],
            &uncleared_labels(),
            read_compartment(),
        ),
        None
    );
}

#[test]
fn sgm_admit_rejects_bad_prefix_put() {
    assert_eq!(
        sgm_admit(
            0,
            10,
            "secret/a",
            DEFAULT_KEY_PREFIX,
            StorageOp::Put,
            &[StorageOp::Put],
            &cleared_labels(),
            read_compartment(),
        ),
        None
    );
}

#[test]
fn sgm_admit_rejects_over_budget() {
    // PUT cost 5 at spent 8 → 13 > 10: rejected.
    assert_eq!(
        sgm_admit(
            8,
            10,
            "uploads/a",
            DEFAULT_KEY_PREFIX,
            StorageOp::Put,
            &[StorageOp::Put],
            &cleared_labels(),
            read_compartment(),
        ),
        None
    );
}
