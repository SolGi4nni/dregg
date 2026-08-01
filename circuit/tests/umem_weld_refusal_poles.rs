//! **THE WELD'S REFUSAL POLES.** Two things the 2026-07-31 derivation cutover has to be able to do
//! that the shape it replaced could not, and one it must keep doing.
//!
//! 1. The canonicity-boundary check **goes RED**. It used to be a `debug_assert!` — a fail-closed
//!    check compiled out of release — so on a shipping build it could not fail at all. It is a
//!    plain `assert!` now, and these cases drive it red on a LOCAL COPY of a real member (nothing
//!    in the shared tree is mutated, and no scaffold is left behind).
//! 2. An OFF-REGISTRY host is **refused**, not welded at a guessed index.
//! 3. A leg whose weld does not match its key — the wrong domain, the classic producer bug — is not
//!    equal to any grounded welded member, which is exactly the predicate
//!    `circuit_prove::ivc_turn_chain::admit_welded_leg` refuses on.

use dregg_circuit::descriptor_ir2::{EffectVmDescriptor2, VmConstraint2, parse_vm_descriptor2};
use dregg_circuit::effect_vm_descriptors::{
    UMEM_WELD_TABLE, WIDE_REGISTRY_STAGED_TSV, derive_welded_wide_member, umem_weld_row,
    weld_umem_into_rotated_descriptor, weld_umem_into_wide_descriptor,
};

fn bare_wide(key: &str) -> EffectVmDescriptor2 {
    let json = WIDE_REGISTRY_STAGED_TSV
        .lines()
        .find_map(|line| {
            let mut it = line.splitn(3, '\t');
            if it.next() == Some(key) {
                let _display = it.next();
                it.next()
            } else {
                None
            }
        })
        .unwrap_or_else(|| panic!("{key} is a wide registry key"));
    parse_vm_descriptor2(json).expect("parses")
}

fn refusal_message<F: FnOnce() -> R + std::panic::UnwindSafe, R>(f: F) -> String {
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let out = std::panic::catch_unwind(f);
    std::panic::set_hook(prev);
    let err = out.err().expect("the weld must REFUSE, not return");
    err.downcast_ref::<String>()
        .cloned()
        .or_else(|| err.downcast_ref::<&str>().map(|s| (*s).to_string()))
        .unwrap_or_default()
}

/// POLE A(i) — the boundary check fires when the trailing constraint is not the canonicity block's
/// range lookup. One extra constraint at the tail is enough: the splice then lands one short of the
/// block and the weld would put the `umemOp` INSIDE it, minting a different AIR under a name the
/// emit committed. In release, before this commit, that was silent.
#[test]
fn a_tail_that_is_not_the_canonicity_block_refuses_the_weld_in_every_profile() {
    let mut host = bare_wide("transferVmDescriptor2R24");
    let last = host.constraints.last().cloned().expect("non-empty");
    assert!(
        matches!(last, VmConstraint2::Lookup(_)),
        "sanity: a committed member ends on the canonicity block's range lookup"
    );
    // Append a row-local gate so the tail is no longer the block.
    let a_gate = host
        .constraints
        .iter()
        .find(|c| matches!(c, VmConstraint2::WindowGate(_)))
        .cloned()
        .expect("a member declares window gates");
    host.constraints.push(a_gate);

    let msg = refusal_message(move || weld_umem_into_rotated_descriptor(&host, 1));
    assert!(
        msg.contains("is not the fields-canonicity boundary"),
        "the refusal must name the boundary it could not find, got: {msg}"
    );
}

/// POLE A(ii) — and it fires on the other half of the boundary shape too (the splice must land on a
/// row-local gate, not on a lookup).
#[test]
fn a_splice_landing_on_a_lookup_refuses_the_weld() {
    let mut host = bare_wide("transferVmDescriptor2R24");
    let split = host.constraints.len() - 2 * 8 * (7 + 12);
    let a_lookup = host
        .constraints
        .last()
        .cloned()
        .expect("the trailing range lookup");
    // Insert a lookup AT the boundary and drop one from the tail, so the block length is unchanged
    // but the constraint at the splice is a lookup rather than a gate.
    host.constraints.insert(split, a_lookup);
    host.constraints.pop();

    let msg = refusal_message(move || weld_umem_into_rotated_descriptor(&host, 1));
    assert!(
        msg.contains("is not the fields-canonicity boundary"),
        "the refusal must name the boundary, got: {msg}"
    );
}

/// POLE B — an OFF-REGISTRY wide host has no Lean-emitted contract row, so there is no defensible
/// splice for it. The weld refuses instead of reconstructing one.
#[test]
fn an_off_registry_wide_host_is_refused_rather_than_welded_at_a_guessed_index() {
    let mut host = bare_wide("transferVmDescriptor2R24");
    host.name.push_str("-not-a-committed-member");

    let msg = refusal_message(move || weld_umem_into_wide_descriptor(&host, 1));
    assert!(
        msg.contains("matches NO row in the Lean-emitted UMEM_WELD_TABLE"),
        "the refusal must say the host is off-registry, got: {msg}"
    );
}

/// POLE B(ii) — and a host that keeps a committed NAME but not the committed SHAPE is off-registry
/// too. This is the sharp case: name alone would have resolved a row and welded at a stale index.
#[test]
fn a_committed_name_with_a_drifted_shape_is_still_refused() {
    let mut host = bare_wide("transferVmDescriptor2R24");
    host.constraints.truncate(host.constraints.len() - 1);

    let msg = refusal_message(move || weld_umem_into_wide_descriptor(&host, 1));
    assert!(
        msg.contains("matches NO row in the Lean-emitted UMEM_WELD_TABLE"),
        "a shape-drifted host must be refused, got: {msg}"
    );
}

/// POLE C — **a leg whose weld does not match its key is not a grounded member.** The producer bug
/// this guards is welding at the wrong universal-memory plane: `setPerms` reconciles `caps` (2), and
/// a leg welded at `heap` (1) binds NO descriptor on the wire. The predicate here is exactly the one
/// `admit_welded_leg` refuses on — equality against the derived member for the leg's own name.
#[test]
fn a_leg_welded_at_the_wrong_domain_matches_no_grounded_member() {
    let mut checked = 0usize;
    for row in UMEM_WELD_TABLE {
        // The other plane: caps <-> heap.
        let wrong = if row.domain == 1 { 2 } else { 1 };
        let host = bare_wide(row.key);
        let forged = weld_umem_into_wide_descriptor(&host, wrong);
        let grounded = derive_welded_wide_member(row.key).expect("derives");
        assert_ne!(
            forged, grounded,
            "{}: a leg welded at domain {wrong} must NOT equal the grounded member (domain {})",
            row.key, row.domain
        );
        // …and it matches no OTHER grounded member either — the whole accept set, not just its own.
        assert!(
            UMEM_WELD_TABLE
                .iter()
                .filter_map(|r| derive_welded_wide_member(r.key))
                .all(|d| d != forged),
            "{}: a wrong-domain weld must be off-registry against the ENTIRE grounded set",
            row.key
        );
        checked += 1;
        // The full 57×57 sweep is quadratic in descriptor derivation; three representatives of each
        // plane are enough to pin the property, and the per-key half above runs for all 57.
        if checked >= 6 {
            break;
        }
    }
    // The cheap half, for every member.
    for row in UMEM_WELD_TABLE {
        let wrong = if row.domain == 1 { 2 } else { 1 };
        let forged = weld_umem_into_wide_descriptor(&bare_wide(row.key), wrong);
        assert_ne!(forged, derive_welded_wide_member(row.key).expect("derives"));
    }
    assert_eq!(UMEM_WELD_TABLE.len(), 57);
}

/// POLE C(ii) — the honest counterpart, so C is not vacuous: welded at its OWN domain, every member
/// IS the grounded member.
#[test]
fn a_leg_welded_at_its_own_domain_is_exactly_the_grounded_member() {
    for row in UMEM_WELD_TABLE {
        let honest = weld_umem_into_wide_descriptor(&bare_wide(row.key), row.domain);
        assert_eq!(
            honest,
            derive_welded_wide_member(row.key).expect("derives"),
            "{}: the honest weld IS the grounded member",
            row.key
        );
        assert_eq!(umem_weld_row(row.key).expect("row").splice, row.splice);
    }
}
