//! End-to-end DRIVEN proof of the [`NamesOffering`] — every move is a REAL executor
//! turn over the `starbridge-nameservice` per-name sovereign-cell substrate. Nothing is
//! mocked: a register is a signed turn the executor admits IFF `WriteOnce(NAME_HASH)`
//! passes; a transfer is admitted IFF the owner-authorization caveats bind `ctx.sender`
//! to the current owner.

use dreggnet_names::{NameOp, NamesOffering};
use dreggnet_offerings::{Offering, Outcome, SessionConfig};

/// A free name commits a real `TurnReceipt` and resolves to the claimant; registering a
/// TAKEN name — by the SAME actor OR a different one — is refused by the WriteOnce
/// first-claim tooth (non-vacuous: the free claim landed).
#[test]
fn register_free_lands_taken_refused() {
    let off = NamesOffering::new();
    let mut s = off
        .open(SessionConfig::with_seed(7))
        .expect("registry opens");
    let alice = s.enroll();
    let bob = s.enroll();

    // Alice claims a free name → a real committed receipt.
    let out = off.register(&mut s, "alice.dregg", &alice);
    let Outcome::Landed { receipt, .. } = out else {
        panic!("free registration must land, got {out:?}");
    };
    assert_eq!(receipt.action_count, 1, "register is one committed action");
    assert!(
        !receipt.emitted_events.is_empty(),
        "register emits name-registered"
    );

    // It resolves to Alice.
    assert_eq!(
        s.resolve_owner("alice.dregg").as_ref(),
        Some(&alice),
        "the name resolves to the claimant"
    );

    // Bob tries to claim the SAME name → refused by WriteOnce(NAME_HASH) (first-claim).
    let out = off.register(&mut s, "alice.dregg", &bob);
    assert!(
        matches!(out, Outcome::Refused(_)),
        "a taken name must be refused by the first-claim tooth, got {out:?}"
    );
    // Ownership is unchanged — Bob's forged claim committed nothing (anti-ghost).
    assert_eq!(
        s.resolve_owner("alice.dregg").as_ref(),
        Some(&alice),
        "the refused claim did not move ownership"
    );
}

/// The current owner transfers a name (propose + accept, two real turns); it re-resolves
/// to the new owner. A NON-owner's transfer is refused by the owner-authorization caveats.
#[test]
fn owner_transfers_nonowner_refused() {
    let off = NamesOffering::new();
    let mut s = off
        .open(SessionConfig::with_seed(11))
        .expect("registry opens");
    let alice = s.enroll();
    let bob = s.enroll();
    let carol = s.enroll();

    off.register(&mut s, "handle.dregg", &alice)
        .landed()
        .then_some(())
        .expect("alice registers");
    assert_eq!(s.resolve_owner("handle.dregg").as_ref(), Some(&alice));

    // A NON-owner (Carol) tries to seize the name → refused at the propose half.
    let out = off.transfer(&mut s, "handle.dregg", &carol, &bob);
    assert!(
        matches!(out, Outcome::Refused(_)),
        "a non-owner transfer must be refused by the owner-auth caveats, got {out:?}"
    );
    assert_eq!(
        s.resolve_owner("handle.dregg").as_ref(),
        Some(&alice),
        "the refused transfer moved nothing"
    );

    // The OWNER (Alice) transfers to Bob → commits; re-resolves to Bob.
    let out = off.transfer(&mut s, "handle.dregg", &alice, &bob);
    assert!(out.landed(), "the owner's transfer must land, got {out:?}");
    assert_eq!(
        s.resolve_owner("handle.dregg").as_ref(),
        Some(&bob),
        "the name re-resolves to the new owner"
    );

    // And now Bob (the NEW owner) can transfer it onward; Alice (the FORMER owner) cannot.
    let out = off.transfer(&mut s, "handle.dregg", &alice, &carol);
    assert!(
        matches!(out, Outcome::Refused(_)),
        "the former owner can no longer transfer, got {out:?}"
    );
    let out = off.transfer(&mut s, "handle.dregg", &bob, &carol);
    assert!(out.landed(), "the new owner transfers onward, got {out:?}");
    assert_eq!(s.resolve_owner("handle.dregg").as_ref(), Some(&carol));
}

/// A resolve is a real executor-refereed turn whose receipt carries the committed owner.
#[test]
fn resolve_emits_a_real_receipt() {
    let off = NamesOffering::new();
    let mut s = off
        .open(SessionConfig::with_seed(13))
        .expect("registry opens");
    let alice = s.enroll();

    off.register(&mut s, "site.dregg", &alice)
        .landed()
        .then_some(())
        .expect("register");

    let out = off.resolve(&mut s, "site.dregg", &alice);
    let Outcome::Landed { receipt, .. } = out else {
        panic!("resolve must land a receipt, got {out:?}");
    };
    let ev = receipt
        .emitted_events
        .first()
        .expect("resolve emits name-resolved");
    // data = [name_hash, owner_pk, expiry] — the owner field is Alice's raw pubkey.
    let owner_pk = ev.data[1];
    assert_eq!(
        dregg_app_framework::hex_encode_32(&owner_pk),
        alice.as_str(),
        "the resolve receipt carries the committed owner"
    );

    // Resolving an unregistered name is refused.
    assert!(matches!(
        off.resolve(&mut s, "ghost.dregg", &alice),
        Outcome::Refused(_)
    ));
}

/// `verify()` re-drives the whole committed op-log against a FRESH substrate and holds;
/// a FORGED log (a duplicate register of a taken name; a non-owner transfer) fails replay
/// at the same executor teeth (non-vacuous — the authentic log verifies).
#[test]
fn verify_holds_forged_claim_fails_replay() {
    let off = NamesOffering::new();
    let mut s = off
        .open(SessionConfig::with_seed(17))
        .expect("registry opens");
    let alice = s.enroll();
    let bob = s.enroll();

    off.register(&mut s, "alice.dregg", &alice)
        .landed()
        .then_some(())
        .expect("alice registers");
    off.register(&mut s, "bob.dregg", &bob)
        .landed()
        .then_some(())
        .expect("bob registers");
    off.transfer(&mut s, "alice.dregg", &alice, &bob)
        .landed()
        .then_some(())
        .expect("alice transfers alice.dregg to bob");
    off.resolve(&mut s, "bob.dregg", &alice)
        .landed()
        .then_some(())
        .expect("resolve");

    // The authentic log re-verifies by replay.
    let report = off.verify(&s);
    assert!(
        report.verified,
        "the authentic registry chain must re-verify: {}",
        report.detail
    );
    assert!(
        report.turns >= 5,
        "genesis-free: 2 registers + transfer(2) + resolve"
    );

    // FORGE 1 — a duplicate register of an already-taken name by an impostor. Replay must
    // reject it (WriteOnce(NAME_HASH) first-claim).
    let mut forged = s.log().to_vec();
    forged.push(NameOp::Register {
        name: "bob.dregg".to_string(),
        by: alice.clone(),
    });
    let report = s.replay(&forged);
    assert!(
        !report.verified,
        "a forged duplicate registration must fail replay: {}",
        report.detail
    );

    // FORGE 2 — a transfer of a name by someone who is not its owner. Replay must reject it
    // (owner-authorization caveats).
    let mut forged = s.log().to_vec();
    forged.push(NameOp::Transfer {
        name: "bob.dregg".to_string(),
        by: alice.clone(), // alice does NOT own bob.dregg (bob transferred nothing to alice)
        to: alice.clone(),
    });
    let report = s.replay(&forged);
    assert!(
        !report.verified,
        "a forged non-owner transfer must fail replay: {}",
        report.detail
    );
}

/// The offering renders a deos affordance surface listing the registered names.
#[test]
fn render_lists_registered_names() {
    let off = NamesOffering::new();
    let mut s = off
        .open(SessionConfig::with_seed(19))
        .expect("registry opens");
    let alice = s.enroll();
    off.register(&mut s, "one.dregg", &alice)
        .landed()
        .then_some(())
        .expect("register");

    let surface = off.render(&s);
    // The surface is a real deos ViewNode tree (a Section titled for the registry).
    match surface.view() {
        deos_view::ViewNode::Section { title, .. } => {
            assert!(title.contains("DreggNet Names"), "titled for the registry");
        }
        other => panic!("expected a Section surface, got {other:?}"),
    }
    assert!(off.actions(&s).iter().any(|a| a.turn == "register"));
}
