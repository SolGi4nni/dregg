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
    Resolution, ResolveError, SurfaceBacking, Target,
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

// ===========================================================================
// THE GLASS — `docs/DREGG-DESKTOP-OS.md` R0: a window IS a surface capability.
//
// These two tests are the desktop-OS first slice: they make "a window =
// `Capability{ target: Surface(cell), rights }`" REAL and load-bearing. A
// surface cap attenuates / delegates / is-rejected-when-widened through the
// EXACT SAME `is_attenuation` (`granted ⊆ held`) gate and the EXACT SAME real
// `TurnExecutor` as every other firmament cap — with zero new authority, zero
// special-casing, zero drivers. Validated by a turn against the REAL executor,
// exactly as the executor-state bridge (#180) and channels (#181) validated
// theirs.
// ===========================================================================

#[test]
fn surface_attenuate_is_backing_agnostic() {
    // The SAME `Capability::attenuate` gate that a local seL4 cap and a
    // distributed cell use, on a SURFACE handle — no special-casing. A window
    // narrows (a writable surface → a read-only mirror) and refuses to widen
    // (a read-only mirror cannot promote itself to writable), through the REAL
    // `is_attenuation` lattice.
    fn cid(b: u8) -> Target {
        let mut k = [0u8; 32];
        k[0] = b;
        Target::surface(dregg_firmament::CellId::derive_raw(&k, &[0u8; 32]))
    }
    let window = if let Target::Surface { cell } = cid(9) {
        cell
    } else {
        unreachable!()
    };

    // A writable (Either) window narrows to a read-only mirror (Signature) —
    // the SAME genuine narrowing the local/distributed handles make.
    let writable = Capability::surface(window, AuthRequired::Either);
    let mirror = writable
        .attenuate(AuthRequired::Signature)
        .expect("Either -> Signature is a genuine surface narrowing");
    assert_eq!(mirror.rights, AuthRequired::Signature);
    // The narrowed handle keeps the SAME Surface target — only rights moved.
    assert_eq!(mirror.target, writable.target);
    assert!(mirror.target.is_surface());

    // A read-only mirror (Signature) CANNOT widen to writable (Either): the
    // SAME `granted ⊆ held` gate refuses it — backing-agnostic, identical to
    // the local-cap and distributed-cell rejections.
    let mirror_only = Capability::surface(window, AuthRequired::Signature);
    assert!(mirror_only.attenuate(AuthRequired::Either).is_none());

    // backing_of routes a surface through the executor-turn path (a surface IS
    // a cell), exactly like a distributed cell.
    assert_eq!(
        FirmamentRouter::backing_of(&writable),
        Backing::DistributedTurn
    );
}

#[test]
fn surface_delegate_through_real_executor_and_widening_rejected() {
    // Hand a window to another app through the firmament router. The narrowing
    // share COMMITS via a GENUINE `Effect::GrantCapability` turn; a WIDENING
    // share is REJECTED by the REAL executor (DelegationDenied), and the other
    // app gets nothing. This is the real distributed half of "a window is a
    // capability" — byte-for-byte the deployed attenuation semantics, on glass.
    let local = LocalBacking::new();
    let dist = DistributedBacking::new();

    let mut surfaces = SurfaceBacking::new(); // n = 1
    let app_cell = surfaces.seed_surface(0); // the app holding the window
    let window = surfaces.seed_surface(2); // the surface (window) cell
    let other_app = surfaces.seed_surface(1); // who we share the window with
    // The compositor granted the app a WRITABLE (Either) surface cap.
    surfaces.install(app_cell, window, AuthRequired::Either);

    let mut router = FirmamentRouter::new(local, dist)
        .with_surface(surfaces)
        .with_holder(app_cell);

    // ---- INVOKE: presenting/drawing into the window resolves via a turn, with
    //      the n=1 collapse (immediate, synchronous — the glass is on this box).
    let win_cap = Capability::surface(window, AuthRequired::Either);
    let res = router.resolve(&win_cap).expect("present surface");
    assert_eq!(res.backing, Backing::DistributedTurn);
    assert_eq!(res.bounds, Bounds::LOCAL); // n = 1 collapse: a surface revoke is immediate
    assert!(res.bounds.revocation_immediate);
    assert!(res.bounds.commit_synchronous);

    // ---- SHARE (narrowing): hand a read-only mirror (Either -> Signature) to
    //      the other app. Commits via the REAL executor turn.
    let shared = router
        .attenuate_and_grant(
            &win_cap,
            AuthRequired::Signature,
            Recipient::SurfaceCell(other_app),
        )
        .expect("narrowing surface share commits through the real executor");
    // The shared handle is the SAME window with narrowed rights — still a surface.
    assert!(shared.target.is_surface());
    assert_eq!(shared.target, win_cap.target);
    assert_eq!(shared.rights, AuthRequired::Signature);
    // The other app ACTUALLY HOLDS the mirror now (a committed GrantCapability
    // turn — the real `granted ⊆ held`).
    assert!(router.surface.holds_cap(other_app, window));
    assert_eq!(
        router.surface.rights_held(other_app, window),
        Some(AuthRequired::Signature)
    );

    // ---- WIDENING SHARE is REJECTED. The other app now holds only Signature
    //      over the window; trying to re-share it as a WIDER Either grant is
    //      refused by the SAME gate (here at the backing-agnostic pre-check),
    //      so a window cannot leak more authority than it carries. We rebind a
    //      router whose holder IS that read-only-mirror app and have it attempt
    //      the widen.
    let local2 = LocalBacking::new();
    let dist2 = DistributedBacking::new();
    let mut fab2 = SurfaceBacking::new();
    let mirror_app = fab2.seed_surface(1); // holds only Signature over the window
    let w = fab2.seed_surface(2); // == `window` (deterministic seed)
    let victim = fab2.seed_surface(3); // who the mirror app tries to widen-share to
    fab2.install(mirror_app, w, AuthRequired::Signature);
    let mut router2 = FirmamentRouter::new(local2, dist2)
        .with_surface(fab2)
        .with_holder(mirror_app);

    let widen_cap = Capability::surface(w, AuthRequired::Signature);
    let err = router2.attenuate_and_grant(
        &widen_cap,
        AuthRequired::Either, // wider than the held Signature — must be refused
        Recipient::SurfaceCell(victim),
    );
    assert!(matches!(err, Err(ResolveError::Unauthorized(_))));
    assert!(!router2.surface.holds_cap(victim, w));
}

#[test]
fn surface_n_equals_one_collapse() {
    // The surface fabric's `n = 1` collapse made concrete: a surface on THIS
    // box (compositor + apps co-located) gets the strong local bounds —
    // immediate dark-on-revoke, synchronous present — and a remote window
    // (n > 1) relaxes them with the VERBS UNCHANGED.
    let local = LocalBacking::new();
    let dist = DistributedBacking::new();

    // n = 1: a local window.
    let mut near = SurfaceBacking::new();
    let app = near.seed_surface(0);
    let window = near.seed_surface(2);
    near.install(app, window, AuthRequired::Either);
    let router = FirmamentRouter::new(local, dist)
        .with_surface(near)
        .with_holder(app);
    let win_cap = Capability::surface(window, AuthRequired::Either);
    let res = router.resolve(&win_cap).expect("near surface");
    assert_eq!(res.bounds, Bounds::LOCAL);
    assert_eq!(res.bounds.n, 1);
    assert!(res.bounds.revocation_immediate);
    assert!(res.bounds.commit_synchronous);

    // n = 5: a REMOTE window (its backing cell lives on another machine). The
    // bounds relax — eventual revocation, quorum present — but the app still
    // just called `router.resolve(&handle)`; no seam, same Surface verb.
    let local2 = LocalBacking::new();
    let dist2 = DistributedBacking::new();
    let mut far = SurfaceBacking::new().with_distance(5);
    let app2 = far.seed_surface(0);
    let rwindow = far.seed_surface(2);
    far.install(app2, rwindow, AuthRequired::Either);
    let router_far = FirmamentRouter::new(local2, dist2)
        .with_surface(far)
        .with_holder(app2);
    let rwin_cap = Capability::surface(rwindow, AuthRequired::Either);
    let rres = router_far.resolve(&rwin_cap).expect("far surface");
    assert_eq!(rres.bounds.n, 5);
    assert!(!rres.bounds.revocation_immediate);
    assert!(!rres.bounds.commit_synchronous);
}

// ===========================================================================
// THE FIVE-VERB WINDOW LIFECYCLE — `docs/DREGG-DESKTOP-OS.md §5`: a window's
// whole life is `create-surface → present → embed → grant-input → revoke`,
// each routed through the REAL executor + the SAME `granted ⊆ held` gate, with
// `embed` authorized by the REAL three-party Introduce. One green test against
// the deployed executor proves the five cap-confined verbs are real and
// load-bearing — the surface op-set the R0 keystone promised, before pixels.
// ===========================================================================

#[test]
fn surface_five_verb_window_lifecycle_through_the_real_executor() {
    let mut fab = SurfaceBacking::new(); // n = 1

    // The actors: a window-manager (the L6 shell), an app it frames, and a
    // second app a child surface is embedded into.
    let wm = fab.seed_surface(0);
    let app = fab.seed_surface(1);
    let framed = fab.seed_surface(2);

    // ── CREATE-SURFACE: the powerbox births a window and hands the app the
    //    Viewport (a writable surface cap). ──
    let window = fab.create_surface(app, 10, AuthRequired::Either);
    assert!(fab.holds_cap(app, window), "create-surface hands the app the window");

    // ── PRESENT: the app draws into its own window — synchronous at n=1. ──
    let res = fab
        .present(app, window, &AuthRequired::Either)
        .expect("the app holds draw rights — present commits");
    assert_eq!(res.bounds, Bounds::LOCAL, "present is synchronous at n=1");

    // ── EMBED: the window-manager embeds the app's window as a child surface of
    //    a `framed` app, via the REAL Introduce. Premises: the wm holds caps to
    //    both the framed app (connectivity) and the window (holds-target). ──
    fab.install(wm, framed, AuthRequired::None); // connectivity to the framed app
    fab.install(wm, window, AuthRequired::Either); // the wm holds the window
    fab.embed(wm, framed, window, AuthRequired::Signature)
        .expect("an attenuating embed commits via the real Introduce");
    assert!(
        fab.holds_cap(framed, window),
        "embed gave the framed app a (read-only) Viewport over the child window"
    );
    assert_eq!(fab.rights_held(framed, window), Some(AuthRequired::Signature));

    // ── GRANT-INPUT: the wm grants the app a narrowed input-receive facet over
    //    the window (focus is a capability) — rides `granted ⊆ held`. ──
    let other = fab.seed_surface(3);
    fab.grant_input(wm, other, window, AuthRequired::Signature)
        .expect("an attenuating input grant commits");
    assert!(fab.holds_cap(other, window), "grant-input handed the input facet");

    // ── REVOKE: the app's window cap is dropped; the glass goes dark instantly
    //    (n=1), and a subsequent present finds nothing held. ──
    assert!(fab.revoke(app, window), "revoke removes the app's window cap");
    assert!(
        fab.present(app, window, &AuthRequired::Either).is_err(),
        "a revoked window cannot paint even one more frame at n=1"
    );

    // The whole lifecycle ran through the deployed executor + the real
    // `is_attenuation` gate — a window IS a dregg cell's surface capability.
}

#[test]
fn surface_embed_widening_rejected_by_real_introduce() {
    // The anti-amplification tooth at the embed edge: an introducer holding only
    // a read-only mirror of a child CANNOT embed it with wider rights — the real
    // Introduce refuses (amplification denied), byte-for-byte the deployed
    // semantics. Mirrors `real_executor_rejects_amplifying_delegate` for the
    // surface-tree edge.
    let mut fab = SurfaceBacking::new();
    let wm = fab.seed_surface(0);
    let app = fab.seed_surface(1);
    let child = fab.seed_surface(2);

    fab.install(wm, app, AuthRequired::None); // connectivity
    fab.install(wm, child, AuthRequired::Signature); // wm holds only a read-only mirror

    // Embedding the child with WIDER (None) rights than the wm holds is REJECTED.
    let r = fab.embed(wm, app, child, AuthRequired::None);
    assert!(r.is_err(), "a widening embed must be rejected by the real Introduce");
    assert!(!fab.holds_cap(app, child), "the recipient gets nothing on a refused embed");
}
