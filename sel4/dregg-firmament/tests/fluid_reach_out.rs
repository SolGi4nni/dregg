//! The ACCEPTANCE test for the fluid reach-out.
//!
//! `docs/FIRMAMENT.md §3` ("The fluid reach-out") promises: a program runs
//! first-class locally holding local caps, and when it reaches the network the
//! firmament resolves the SAME `(target, rights)` handle through the
//! executor→net path with no seam — only the bounds relax along `n`.
//!
//! This test PROVES it: a single "app" function `run_app` is written ONCE
//! against the [`Router`] trait. It does not branch on backing. We hand it:
//!
//!   1. a LOCAL capability (target = an seL4 CNode slot), and
//!   2. a DISTRIBUTED capability (target = a real dregg cell),
//!
//! and the SAME app code invokes + attenuates + delegates BOTH through ONE
//! router. The local leg resolves via the seL4 syscall-boundary model; the
//! distributed leg resolves via a GENUINE [`dregg_turn::TurnExecutor`] turn
//! with the REAL `granted ⊆ held` attenuation. The ONLY observable difference
//! is the [`Bounds`] (immediate/synchronous locally; relaxing as `n` rises).

use dregg_firmament::router::{Recipient, Router};
use dregg_firmament::{
    AuthRequired, Backing, Bounds, Capability, DistributedBacking, FirmamentRouter, LocalBacking,
    Resolution, ResolveError,
};

/// The houyhnhnm APP — written ONCE, backing-agnostic. It does not know and
/// cannot tell whether `cap` is local or distributed: it just invokes it,
/// attenuates it, and delegates the attenuated copy. The returned resolution
/// carries the bounds, which is the only thing that varies.
fn run_app<R: Router>(
    router: &mut R,
    cap: &Capability,
    recipient: Recipient,
) -> Result<(Resolution, Capability), ResolveError> {
    // 1. INVOKE the held capability.
    let resolution = router.resolve(cap)?;

    // 2. ATTENUATE it (Either -> Signature, a genuine narrowing) and DELEGATE
    //    the narrowed copy. The app names the SAME verb regardless of backing.
    let delegated = router.attenuate_and_grant(cap, AuthRequired::Signature, recipient)?;

    Ok((resolution, delegated))
}

#[test]
fn one_handle_resolves_local_and_distributed() {
    // ---- Build the firmament's two backings. ----
    let mut local = LocalBacking::new();
    // The firmament minted a cap over a local endpoint into the app's CNode.
    let local_slot = local.install("endpoint:ctrl", AuthRequired::Either);

    let mut dist = DistributedBacking::new(); // n = 1 (single-machine)
    let app_cell = dist.seed_cell(0); // the app's own cell (the holder)
    let remote_cell = dist.seed_cell(2); // the cell the cap targets
    let recipient_cell = dist.seed_cell(1); // who we delegate to
    // The firmament granted the app a cap over the remote cell.
    dist.install(app_cell, remote_cell, AuthRequired::Either);

    let mut router = FirmamentRouter::new(local, dist).with_holder(app_cell);

    // ---- The SAME app, two handles. ----

    // (a) The LOCAL handle: target is a CNode slot.
    let local_cap = Capability::local(local_slot, AuthRequired::Either);
    assert_eq!(FirmamentRouter::backing_of(&local_cap), Backing::LocalKernel);

    let (local_res, local_deleg) =
        run_app(&mut router, &local_cap, Recipient::LocalChild).expect("local app run");

    // It resolved via the kernel path, with the STRONG n=1 bounds.
    assert_eq!(local_res.backing, Backing::LocalKernel);
    assert_eq!(local_res.bounds, Bounds::LOCAL);
    assert!(local_res.bounds.revocation_immediate);
    assert!(local_res.bounds.commit_synchronous);
    // The delegated handle is a real minted child slot with narrowed rights.
    assert!(local_deleg.target.is_local());
    assert_eq!(local_deleg.rights, AuthRequired::Signature);
    // The minted child slot is LIVE in the CNode (a real seL4_CNode_Mint).
    if let dregg_firmament::Target::Local { slot } = local_deleg.target {
        assert!(router.local.is_live(slot));
    }

    // (b) The DISTRIBUTED handle: target is a dregg cell. SAME app code.
    let dist_cap = Capability::distributed(remote_cell, AuthRequired::Either);
    assert_eq!(
        FirmamentRouter::backing_of(&dist_cap),
        Backing::DistributedTurn
    );

    let (dist_res, dist_deleg) =
        run_app(&mut router, &dist_cap, Recipient::DistributedCell(recipient_cell))
            .expect("distributed app run");

    // It resolved via a REAL TURN. At n=1 the bounds COLLAPSE to the strong
    // local ones — the fluid reach-out's headline: first-class locally.
    assert_eq!(dist_res.backing, Backing::DistributedTurn);
    assert_eq!(dist_res.bounds, Bounds::LOCAL); // n = 1 collapse
    // The delegated handle points at the same cell with narrowed rights, and
    // the recipient cell ACTUALLY HOLDS it (a real committed GrantCapability
    // turn through the executor — the real `granted ⊆ held`).
    assert_eq!(dist_deleg.rights, AuthRequired::Signature);
    assert!(router
        .distributed
        .holds_cap(recipient_cell, remote_cell));
    assert_eq!(
        router.distributed.rights_held(recipient_cell, remote_cell),
        Some(AuthRequired::Signature)
    );

    // ---- THE ACCEPTANCE CLAIM ----
    // The SAME app function (`run_app`) drove BOTH a local kernel object AND a
    // distributed dregg cell through ONE router, ONE `(target, rights)` handle
    // type, the SAME invoke/attenuate/delegate verbs. The app never branched
    // on backing. The only difference between the two runs is which backing
    // resolved them and the bounds — which at n=1 are IDENTICAL. That is the
    // fluid reach-out, in code.
    println!(
        "FLUID REACH-OUT: local={:?} dist={:?} (n=1 bounds identical: {})",
        local_res.note,
        dist_res.note,
        local_res.bounds == dist_res.bounds
    );
}

#[test]
fn bounds_relax_when_the_target_is_far() {
    // The SAME distributed handle, but the federation now spans n=5 machines
    // (the app reached out to the wire). The verbs are unchanged; ONLY the
    // bounds relax — eventual revocation, quorum commit.
    let local = LocalBacking::new();
    let mut dist = DistributedBacking::new().with_distance(5);
    let app_cell = dist.seed_cell(0);
    let remote_cell = dist.seed_cell(2);
    dist.install(app_cell, remote_cell, AuthRequired::Either);

    let router = FirmamentRouter::new(local, dist).with_holder(app_cell);
    let dist_cap = Capability::distributed(remote_cell, AuthRequired::Either);

    let res = router.resolve(&dist_cap).expect("far resolve");
    assert_eq!(res.bounds.n, 5);
    assert!(!res.bounds.revocation_immediate); // eventual — the epoch lift must propagate
    assert!(!res.bounds.commit_synchronous); // quorum-gated finality
    // But the app still just called `router.resolve(&handle)` — no seam.
}

#[test]
fn amplification_refused_at_both_backings() {
    // A widening (Signature -> Either) is refused identically whether the
    // target is local or distributed — the unified `granted ⊆ held` law.
    let mut local = LocalBacking::new();
    let local_slot = local.install("endpoint:ctrl", AuthRequired::Signature);

    let mut dist = DistributedBacking::new();
    let app_cell = dist.seed_cell(0);
    let remote_cell = dist.seed_cell(2);
    let recipient_cell = dist.seed_cell(1);
    dist.install(app_cell, remote_cell, AuthRequired::Signature);

    let mut router = FirmamentRouter::new(local, dist).with_holder(app_cell);

    let local_cap = Capability::local(local_slot, AuthRequired::Signature);
    let err_local =
        router.attenuate_and_grant(&local_cap, AuthRequired::Either, Recipient::LocalChild);
    assert!(matches!(err_local, Err(ResolveError::Unauthorized(_))));

    let dist_cap = Capability::distributed(remote_cell, AuthRequired::Signature);
    let err_dist = router.attenuate_and_grant(
        &dist_cap,
        AuthRequired::Either,
        Recipient::DistributedCell(recipient_cell),
    );
    assert!(matches!(err_dist, Err(ResolveError::Unauthorized(_))));
    // Neither backing mutated: the recipient never received the widened cap.
    assert!(!router.distributed.holds_cap(recipient_cell, remote_cell));
}
