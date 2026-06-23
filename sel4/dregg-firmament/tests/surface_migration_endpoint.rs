//! THE LIVE-TRANSPORT RE-HOME ACCEPTANCE TEST — a migrated surface's glass
//! follows its cap to a confined child PD (`docs/deos/SURFACE-MIGRATION.md`
//! §2(b), the live transport half of the `migrate` verb).
//!
//! The authority half (`migrate(surface_cap, HostPd{pd})` re-minting the cap)
//! lives in `starbridge-v2/src/dock/migrate.rs`. THIS test proves the OTHER
//! half: once a surface is migrated to a confined child PD, its present/input
//! round-trips cross the child's firmament SURFACE Endpoint — the child renders
//! in its OWN MMU-isolated memory and the frame crosses back. The glass follows
//! the cap.
//!
//! The slice, by RUNNING:
//!   1. spawn a CONFINED child PD that holds a dedicated surface Endpoint (its
//!      ONLY channels are the control socket + the surface socket; file/network/
//!      exec are denied), running a surface renderer over the surface Endpoint;
//!   2. register that child's surface Endpoint in the host backing (the
//!      compositor-side re-home — what the migrated cap names);
//!   3. drive an Input event and a Present request across the Endpoint and read
//!      back the frames the CHILD rendered — proving input/output cross to the
//!      confined child and the glass follows.
//!
//! Gated behind `--features process-pd,process-pd-sandbox` (Unix only). Run:
//!   `cargo test --features process-pd,process-pd-sandbox --test surface_migration_endpoint -- --nocapture`

#![cfg(all(feature = "process-pd-sandbox", unix))]

use dregg_cell::AuthRequired;
use dregg_firmament::process_kernel::ProcessKernel;
use dregg_firmament::{
    serve_one_surface_event, HostPdBacking, SurfaceEvent, SurfaceFrame,
};

/// THE GLASS-FOLLOWS-THE-CAP TEST: a confined child PD hosts a surface renderer
/// over its firmament SURFACE Endpoint; an input event and a present request
/// cross the Endpoint and the frames the child rendered come back. The child is
/// confined (its only channels are its two Endpoints — no file/network/exec).
#[test]
fn migrated_surface_glass_follows_the_cap_to_a_confined_child() {
    let kernel = ProcessKernel::new();

    // Spawn the CONFINED child surface renderer. It holds the kernel control
    // socket AND the surface Endpoint; it runs a tiny renderer over the surface
    // socket: a private accumulator (its surface state, MMU-isolated) folds each
    // Input and a Present digests the current state. The frame `digest` is a
    // deterministic function of the accumulator, so the parent can verify the
    // frame genuinely reflects the events the child received.
    let (pd, parent_surf) = kernel
        .spawn_pd_confined_with_surface(vec![], |_client, mut surf, _granted| {
            // The surface's PRIVATE state — lives in the child's own page tables;
            // the compositor reaches it ONLY by driving events over the Endpoint.
            let mut acc: u64 = 0;
            let mut seq: u64 = 0;
            loop {
                let cont = serve_one_surface_event(&mut surf, &mut acc, |state, ev| {
                    match ev {
                        SurfaceEvent::Input { code } => {
                            // Fold the input into the surface state and re-render.
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
                    }
                });
                match cont {
                    Ok(true) => continue,
                    // Clean EOF (compositor closed the surface Endpoint) or error
                    // → the surface is done; exit cleanly.
                    Ok(false) => break,
                    Err(_) => break,
                }
            }
            0
        })
        .expect("spawn confined surface-renderer child");

    // The kernel services the child's CONTROL socket in the background (the
    // child does not use it here, but a real PD would; keep it serviced so a
    // control round-trip never wedges).
    let k = kernel.clone();
    let mut ctrl = pd.kernel_sock.try_clone().expect("clone control sock");
    let server = std::thread::spawn(move || while k.serve_one(&mut ctrl).unwrap_or(false) {});

    // ── THE COMPOSITOR-SIDE RE-HOME ──
    // Register the child's surface Endpoint in the host backing under a HostPd
    // id (the id a migrated `Capability::host_pd(id, rights)` names). This is
    // what `migrate(surface_cap, HostPd{pd})` re-minted the cap to point at;
    // here we bind that id to the LIVE surface Endpoint — the glass re-home.
    let mut host = HostPdBacking::new();
    // The control endpoint registers the PD (rights = Either, the held authority).
    let pd_id = host.register(
        pd.kernel_sock.try_clone().expect("clone for host register"),
        AuthRequired::Either,
    );
    // The surface Endpoint re-home: the compositor's end of the surface socket.
    assert!(
        host.register_surface(pd_id, parent_surf),
        "the surface Endpoint must bind to the registered host-PD"
    );

    // ── DRIVE INPUT ACROSS THE ENDPOINT ──
    // An input event reaches the confined child over the surface Endpoint; the
    // child folds it into its private state and renders a frame that crosses
    // back. This is the input half of "the glass follows the cap".
    let f1 = host
        .present_over_endpoint(pd_id, &AuthRequired::Either, SurfaceEvent::Input { code: 7 })
        .expect("input crosses to the confined child and a frame returns");
    // The frame digest matches what a child that received exactly code=7 renders.
    let expected_acc = 0u64.wrapping_mul(31).wrapping_add(7);
    assert_eq!(
        f1,
        SurfaceFrame {
            seq: 1,
            digest: render_digest(expected_acc, 1)
        },
        "the frame must reflect the input the CHILD received (the glass followed)"
    );

    // A second input compounds the surface state in the child.
    let f2 = host
        .present_over_endpoint(pd_id, &AuthRequired::Either, SurfaceEvent::Input { code: 13 })
        .expect("second input round-trips");
    let expected_acc2 = expected_acc.wrapping_mul(31).wrapping_add(13);
    assert_eq!(f2.seq, 2);
    assert_eq!(f2.digest, render_digest(expected_acc2, 2));

    // ── DRIVE A PRESENT ACROSS THE ENDPOINT ──
    // A present request renders the current surface state at a sequence; the
    // OUTPUT (frame) comes back from the child — the output half of the glass
    // following the cap.
    let f3 = host
        .present_over_endpoint(pd_id, &AuthRequired::Either, SurfaceEvent::Present { seq: 42 })
        .expect("present renders the child's surface and the frame returns");
    assert_eq!(f3.seq, 42);
    assert_eq!(
        f3.digest,
        render_digest(expected_acc2, 42),
        "the present frame reflects the accumulated child state at seq=42"
    );

    // ── THE CONFINEMENT TOOTH (carried by the gate) ──
    // A present carrying rights WIDER than held is refused by the SAME
    // `granted ⊆ held` gate — the migrated surface cannot amplify its authority
    // over the child even on the live transport path.
    let widened = host.present_over_endpoint(
        pd_id,
        &AuthRequired::None, // None is broader than the held Either → refused
        SurfaceEvent::Present { seq: 99 },
    );
    assert!(
        widened.is_err(),
        "a present widening the migrated surface's authority must be refused"
    );

    // Close the compositor's end (drop `host` → drops the surface socket) so the
    // child sees EOF and exits, then reap.
    drop(host);
    let code = wait_pid(pd.pid);
    server.join().unwrap();
    assert_eq!(code, 0, "the confined surface-renderer child exits cleanly");

    println!(
        "GLASS FOLLOWS THE CAP: input + present crossed the firmament SURFACE \
         Endpoint to a CONFINED child PD; the frames it rendered came back. The \
         migrated surface's glass re-homed. ( ⌐■_■ )"
    );
}

/// The renderer's deterministic frame digest — a pure function of the surface
/// state + sequence, so the parent can verify a returned frame genuinely
/// reflects the events the child received (the same function on both sides).
fn render_digest(state: u64, seq: u64) -> u64 {
    let mut x = state ^ seq.rotate_left(32);
    x ^= x >> 30;
    x = x.wrapping_mul(0xBF58_476D_1CE4_E5B9);
    x ^= x >> 27;
    x
}

/// Wait for a child pid and return its exit code.
fn wait_pid(pid: libc::pid_t) -> i32 {
    let mut status: libc::c_int = 0;
    let rc = unsafe { libc::waitpid(pid, &mut status, 0) };
    if rc < 0 {
        return -1;
    }
    if status & 0x7f == 0 {
        (status >> 8) & 0xff
    } else {
        -(status & 0x7f)
    }
}
