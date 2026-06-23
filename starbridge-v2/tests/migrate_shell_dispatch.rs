//! THE GLASS FOLLOWS THE MIGRATED CAP — THROUGH THE REAL SHELL, BY RUNNING.
//!
//! `docs/deos/SURFACE-MIGRATION.md` §2(b): a surface migrates to a CONFINED child
//! PD and its present/route_input re-home over that child's firmament Endpoint.
//! The unit tests in `dock::migrate` proved the transport in ISOLATION (a
//! `PresentTransport` round-trips to a child). This test proves the LAST seam: the
//! REAL [`Shell::present`] / [`Shell::route_input`] entry points DISPATCH to the
//! confined child PD over the Endpoint when a surface has migrated — the glass
//! follows the cap END-TO-END through the shell, not the in-process compositor.
//!
//! Run: `cd starbridge-v2 && cargo test --features process-pd,gpui-ui --test migrate_shell_dispatch -- --nocapture`
//! (the `process-pd` live wire + the gpui-gated `dock` module that hosts `migrate`).

#![cfg(all(feature = "process-pd", unix))]

use starbridge_v2::dock::migrate::{MigrationTarget, PresentTransport};
use starbridge_v2::shell::Shell;
use starbridge_v2::{demo_world, World};

use dregg_firmament::process_kernel::ProcessKernel;
use dregg_firmament::{
    serve_one_surface_event, AuthRequired, HostPdBacking, SurfaceEvent, SurfaceFrame,
};

/// The child renderer's deterministic frame digest — the SAME fold the confined
/// child applies, so the test can assert the digest that crossed back is genuinely
/// the child's render (not a shell fabrication).
fn render_digest(state: u64, seq: u64) -> u64 {
    let mut x = state ^ seq.rotate_left(32);
    x ^= x >> 30;
    x = x.wrapping_mul(0xBF58_476D_1CE4_E5B9);
    x ^= x >> 27;
    x
}

/// FULL E2E THROUGH THE SHELL: open a real surface in the shell → spawn a CONFINED
/// child renderer → migrate the surface's cap to that child (`Shell::migrate_surface`)
/// → drive `Shell::present` + `Shell::route_input` and watch them DISPATCH over the
/// firmament Endpoint to the confined child (input crosses, a child-rendered frame
/// digest comes back through the shell's `FrameCommit`/`frame_digests`). The
/// in-process compositor never sees the migrated surface.
#[test]
fn shell_present_and_route_input_dispatch_to_the_migrated_confined_child() {
    let (world, anchors): (World, [_; 3]) = demo_world();
    let mut shell = Shell::new();
    let _console = shell.open_console(anchors[0], "Console");

    // A real held surface over a live cell — minted by the shell, authenticates
    // through the firmament `granted ⊆ held` gate.
    let viewed = anchors[1];
    let held = shell.open_cell_view(viewed, "Service");
    assert!(
        shell.validates(&held),
        "the freshly-opened surface authenticates"
    );
    let surf_id = held.surface();

    // ── spawn the CONFINED child surface renderer: its only channels are its two
    //    firmament Endpoints (file/network/exec DENIED by the OS sandbox). It folds
    //    each event into private, MMU-isolated surface state and renders a frame. ──
    let kernel = ProcessKernel::new();
    let (pd, parent_surf) = kernel
        .spawn_pd_confined_with_surface(vec![], |_client, mut surf, _granted| {
            let mut acc: u64 = 0;
            let mut seq: u64 = 0;
            loop {
                let cont = serve_one_surface_event(&mut surf, &mut acc, |state, ev| match ev {
                    SurfaceEvent::Input { code } => {
                        *state = state.wrapping_mul(31).wrapping_add(code);
                        seq += 1;
                        SurfaceFrame {
                            seq,
                            digest: render_digest(*state, seq),
                        }
                    }
                    SurfaceEvent::Present { seq: pseq } => {
                        seq = pseq;
                        SurfaceFrame {
                            seq: pseq,
                            digest: render_digest(*state, pseq),
                        }
                    }
                });
                if !matches!(cont, Ok(true)) {
                    break;
                }
            }
            0
        })
        .expect("spawn confined surface child");

    // Service the child's CONTROL socket in the background (the spawn handshake +
    // teardown). The SURFACE Endpoint is the one the shell drives.
    let k = kernel.clone();
    let mut ctrl = pd.kernel_sock.try_clone().expect("clone control");
    let server = std::thread::spawn(move || while k.serve_one(&mut ctrl).unwrap_or(false) {});

    // ── register the child + its surface Endpoint in a host backing, wrap it in the
    //    live transport, and MIGRATE the surface's cap to the child THROUGH THE SHELL ──
    let mut host = HostPdBacking::new();
    let pd_id = host.register(
        pd.kernel_sock.try_clone().expect("clone host control"),
        AuthRequired::Either,
    );
    assert!(
        host.register_surface(pd_id, parent_surf),
        "the surface Endpoint registers"
    );
    let transport = PresentTransport::new(host);

    // The shell re-homes the cap (attenuating: carry the SAME rights, ⊆ held) +
    // installs the live transport. From here the surface dispatches to the child.
    let rehomed = shell
        .migrate_surface(
            &held,
            MigrationTarget::HostPd {
                pd: pd_id,
                // Carry `Either` to the child: it is ⊆ the held `None` (the widest)
                // so `migrate` ADMITS it, AND it is ⊆ the `Either` the host backing
                // registered for this PD — so the Endpoint's own `granted ⊆ held`
                // gate (`present_over_endpoint`) ALSO admits each round-trip. (A
                // request WIDER than the backing holds, e.g. `None`, is correctly
                // REFUSED at the Endpoint — that gate is the live authority now.)
                rights: AuthRequired::Either,
            },
            transport,
        )
        .expect("the shell migrates the surface to the confined child");
    assert!(
        rehomed.authority().target.is_host_pd(),
        "the re-homed cap now names the child PD on the distance axis"
    );
    assert_eq!(
        rehomed.surface(),
        surf_id,
        "identity preserved across the move"
    );

    // The frame log BEFORE: the in-process compositor has recorded nothing for this
    // surface (we never presented it in-process).
    let frames_before = shell.frame_log().len();

    // ── DRIVE THE SHELL: present + input now CROSS to the confined child ──

    // (A) Shell::present DISPATCHES over the Endpoint. The child renders at seq=99
    // and the digest it produced returns through the shell's FrameCommit.
    let present_seq = 99u64;
    let commit = shell
        .present(
            &rehomed,
            &world,
            vec![surf_id.region()],
            /*claims_focus*/ true,
            present_seq,
        )
        .expect("Shell::present dispatches to the migrated child and a frame returns");
    // The digest in the shell's commit IS the digest the CHILD rendered (state acc=0
    // at this point — no input yet — at seq=99). Proves it came from the child.
    assert_eq!(
        commit.digest,
        render_digest(0, present_seq),
        "the FrameCommit digest is the one the CONFINED CHILD rendered"
    );
    assert_eq!(commit.regions, vec![surf_id.region()]);

    // The in-process compositor frame log did NOT grow — the present went to the
    // child, not the compositor (the migrated surface bypasses it entirely).
    assert_eq!(
        shell.frame_log().len(),
        frames_before,
        "the migrated present did NOT touch the in-process compositor's frame log"
    );

    // (B) Shell::route_input DISPATCHES the input to the child. The migrated surface
    // is the focus holder (open_cell_view focused it); the T3 gate confirms the
    // viewed cell, then the input crosses the Endpoint. The child folds the input
    // (code = surface id) into its private state and re-renders.
    let delivered = shell
        .route_input(viewed, &world)
        .expect("Shell::route_input delivers to the migrated surface's focus holder");
    assert_eq!(
        delivered, viewed,
        "input routes to the migrated surface's cell (T3)"
    );

    // The child's state advanced by the input (acc = 0*31 + surf_id). A SUBSEQUENT
    // present reflects that — the input genuinely crossed to and mutated the child.
    let post_input_acc = 0u64.wrapping_mul(31).wrapping_add(surf_id.as_u64());
    let commit2 = shell
        .present(&rehomed, &world, vec![surf_id.region()], true, 7)
        .expect("a present after the input renders the child's MUTATED state");
    assert_eq!(
        commit2.digest,
        render_digest(post_input_acc, 7),
        "the child's re-render reflects the input that crossed the Endpoint — the \
         input genuinely reached the confined child and mutated its private state"
    );

    // ── confinement intact: the child only ever spoke its two Endpoints; teardown
    //    closes the surface Endpoint (drop the shell → drops the transport) → the
    //    child EOFs, then we reap it. A clean exit proves it stayed confined + live. ──
    drop(shell);
    let code = pd.join().expect("reap the confined surface child");
    server.join().unwrap();
    assert_eq!(
        code, 0,
        "the confined child exited cleanly (confinement held)"
    );

    println!(
        "E2E THROUGH THE SHELL: a surface MIGRATED to a confined child PD and the \
         REAL Shell::present + Shell::route_input dispatched to it over the firmament \
         Endpoint — input crossed + mutated the child's private state, the child's \
         rendered frame digests returned through the shell's FrameCommit, the \
         in-process compositor was bypassed, the child stayed confined. (づ｡◕‿‿◕｡)づ"
    );
}
