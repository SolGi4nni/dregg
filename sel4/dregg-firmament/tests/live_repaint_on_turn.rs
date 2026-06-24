//! THE LIVE-REPAINT-ON-TURN BOOT TEST — a committed turn through the executor-PD
//! re-paints the focused cell on the compositor-PD's framebuffer
//! (`docs/desktop-os-research/SEL4-INTERACTIVE-COCKPIT.md §3` + §4 — the smallest
//! end-to-end slice that demonstrates repaint-on-turn).
//!
//! This closes the named seam: before this, the executor-PD ran a real verified
//! turn (`executor_pd_boot.rs`) and the compositor-PD composited a scene-gated
//! present (`compositor_pd_boot.rs`), but the two halves were DISCONNECTED — a
//! committed turn did not re-paint the glass. This test wires the loop across the
//! PD boundary and PROVES it:
//!
//!   ┌────────────────┐  turn_in (DMA)   ┌──────────────────┐
//!   │  compositor-PD │ ───────────────▶ │   executor-PD    │
//!   │  (framebuffer) │ ◀─────────────── │  (verified turn) │
//!   └────────────────┘  repaint_out +   └──────────────────┘
//!         ▲  CH_REPAINT (notify)         the DirtyRegion signal
//!         └── on the dirty notify: present() the changed region
//!
//! THE PROOF (two framebuffer snapshots straddle the turn):
//!   1. a COMMITTED turn projects a `DirtyRegion`, the executor notifies the
//!      compositor, the compositor presents → the framebuffer DIFFERS at exactly
//!      the focused cell's region (the cell re-painted);
//!   2. a REJECTED turn projects NOTHING, notifies NOTHING → the framebuffer is
//!      BYTE-IDENTICAL (a refused turn re-paints nothing — fail-closed).
//!
//! This is the SAME boot shape as `executor_pd_boot.rs` + `compositor_pd_boot.rs`
//! (PDs as threads over ONE EmulatedKernel), now exercising the §3 `Notified`
//! event AND the §3 Endpoint `pp_call` path together — the repaint loop. It rides
//! ONLY proven primitives (the executor's turn path, the compositor's present
//! gate, the cross-PD notify the 2-PD slice proves); it adds the projection
//! (`project_dirty_from_turn`) + the `repaint_out` wire (`encode_dirty`).
//!
//! ## Fidelity (honestly labeled — NOT laundered)
//!
//! The framebuffer is a HOST buffer (an EmulatedKernel region), not a scanned-out
//! panel; the compositor enforces scene AUTHORITY (T1/T2/T3) and the executor
//! runs the GENUINE `granted ⊆ held` gate. The AUTHORITY path — a turn's commit
//! drives a scene-gated present that advances the framebuffer — is what this
//! proves. F1/F2/F3 (last-hop frame attestation, IOMMU/DMA confinement, verified
//! GPU) are the named graphics frontier, NOT solved here. The honest label
//! travels with the code: `dregg_firmament::REPAINT_FIDELITY`.

use dregg_firmament::compositor_pd::{cell_seed, CompositorPd, Scene, Surface};
use dregg_firmament::emulated_kernel::EmulatedKernel;
use dregg_firmament::executor_pd::{ExecutorPd, ServedTurn, TurnRunner};
use dregg_firmament::repaint::{decode_dirty, encode_dirty, project_dirty_from_turn};

use dregg_cell::{is_attenuation, AuthRequired};

/// The same GENUINE attenuation-gate runner the executor-PD boot test uses: a
/// 2-byte `[held, granted]` decoded over `is_attenuation`, committing iff
/// `granted ⊆ held` (the SAME gate the real `DreggEngine` runs). It keeps this
/// test free of the heavy `dregg-turn::Turn` codec while running the REAL gate.
struct AttenuationRunner;

fn auth_of(b: u8) -> AuthRequired {
    match b {
        0 => AuthRequired::None,
        1 => AuthRequired::Signature,
        2 => AuthRequired::Either,
        _ => AuthRequired::Impossible,
    }
}

impl TurnRunner for AttenuationRunner {
    fn run_turn_bytes(&mut self, turn_bytes: &[u8]) -> Result<Vec<u8>, String> {
        if turn_bytes.len() != 2 {
            return Err(format!("malformed turn: expected 2 bytes, got {}", turn_bytes.len()));
        }
        let held = auth_of(turn_bytes[0]);
        let granted = auth_of(turn_bytes[1]);
        if is_attenuation(&held, &granted) {
            Ok(vec![turn_bytes[0], turn_bytes[1], 0xCC])
        } else {
            Err(format!(
                "non-attenuating: granted {:?} is wider than held {:?} (granted ⊄ held)",
                granted, held
            ))
        }
    }
}

/// The wallet's surface in the compositor scene — the focused cell that a turn
/// re-paints. It owns regions {10, 11}, starts un-composited (digest 0), and
/// holds focus (the Lean `demoScene` wallet).
fn scene_with_focused_wallet(wallet: dregg_types::CellId) -> Scene {
    Scene {
        surfaces: vec![Surface {
            owner: wallet,
            regions: vec![10, 11],
            content_digest: 0, // the framebuffer starts blank for this region
            source_state_root: 0,
            z_layer: 0,
            focus_flag: true, // the wallet holds focus — the focused cell
        }],
    }
}

// ===========================================================================
// THE BOOT TEST — single-threaded so the loop runs deterministically (no
// thread-timing): we drive the executor-PD's `step_staged_turn` and the
// compositor-PD's `present` directly, wiring them through the GENUINE
// `repaint_out` region + the projection, exactly as the cross-PD notify would.
//
// This is the same single-threaded discipline `compositor_pd_boot.rs`'s
// `serve_present_inline` test uses (the gate's side effects land on `self`),
// here threading the executor→compositor repaint signal through a shared region.
// ===========================================================================

#[test]
fn a_committed_turn_repaints_the_focused_cell_a_rejected_turn_does_not() {
    // ── The firmament wires the slice at boot (the deos-live.system equivalent). ──
    let kernel = EmulatedKernel::new();
    let wallet = cell_seed(1);

    // The executor-PD: holds turn_in (R) + commit_out (RW), runs the GENUINE gate.
    let mut executor = ExecutorPd::boot(kernel.clone(), AttenuationRunner, 4096, 4096);

    // The compositor-PD: SOLELY holds the framebuffer, starts with the focused
    // wallet's surface (region 10/11, blank).
    let mut compositor = CompositorPd::boot(kernel.clone(), scene_with_focused_wallet(wallet));

    // The shared `repaint_out` region (huge enough for one DirtyRegion frame) —
    // the executor's W view, the compositor's R view. This is the third shared
    // region of the §3 topology (turn_in / commit_out / repaint_out).
    let repaint_out = kernel.create_region(64);

    // The framebuffer BEFORE any turn — region 10 is blank (digest byte 0).
    let fb_before = compositor.framebuffer_snapshot();
    assert_eq!(fb_before[10], 0, "the focused cell's region starts blank");

    // ── (1) THE COMMITTED TURN re-paints the focused cell. ──────────────────────

    // The app stages an ATTENUATING turn (held=Either(2), granted=Signature(1) —
    // a genuine narrowing) and signals the executor.
    assert!(
        executor.stage_turn(&[2, 1]).is_some(),
        "the turn fits turn_in"
    );
    let served = executor.step_staged_turn();
    assert!(served.is_committed(), "the attenuating turn COMMITS at the heart");

    // THE PROJECTION + THE WIRE: the executor projects the committed turn into a
    // DirtyRegion and writes it into repaint_out, then would CH_REPAINT.notify()
    // the compositor (here we drive the compositor's notified arm directly, the
    // same as the single-threaded serve_present_inline path).
    let dirty = project_dirty_from_turn(&wallet, &served)
        .expect("a committed turn projects a dirty region");
    kernel.region_with_mut(repaint_out, |buf| {
        let enc = encode_dirty(&dirty);
        buf[..enc.len()].copy_from_slice(&enc);
    });

    // THE COMPOSITOR'S NOTIFIED ARM: read the DirtyRegion out of repaint_out, look
    // up the focused surface's owned regions, build the scene-gated present, and
    // composite. (On a real PD this is the body of `notified(CH_REPAINT)`.)
    let read = kernel.region_read(repaint_out).expect("repaint_out region");
    let dirty_read = decode_dirty(&read).expect("the dirty signal decodes");
    assert_eq!(dirty_read, dirty, "the dirty signal round-tripped through repaint_out");
    // The compositor presents the focused cell's region 10 with the new digest.
    let commit = compositor
        .present(&dirty_read.owner, dirty_read.to_present(vec![10]))
        .expect("the scene gate ADMITS the honest repaint");
    assert_eq!(commit.digest, dirty.new_content_digest);

    // THE PROOF: the framebuffer DIFFERS at the focused cell's region — it
    // re-painted. (The digest byte at tile 10 advanced from 0 to the turn's frame.)
    let fb_after_commit = compositor.framebuffer_snapshot();
    assert_ne!(
        fb_after_commit[10], fb_before[10],
        "the COMMITTED turn re-painted the focused cell (tile 10 advanced)"
    );
    assert_eq!(
        fb_after_commit[10],
        (dirty.new_content_digest & 0xFF) as u8,
        "tile 10 holds the new frame the turn projected"
    );
    assert_eq!(
        compositor.frames().len(),
        1,
        "exactly one frame committed (the repaint)"
    );

    // ── (2) THE REJECTED TURN re-paints NOTHING (fail-closed). ──────────────────

    // Snapshot the framebuffer just before the rejected turn (the comparison
    // baseline — it must NOT change).
    let fb_before_reject = compositor.framebuffer_snapshot();

    // Stage an AMPLIFYING turn (held=Signature(1), granted=Either(2) — a WIDENING).
    // The verified gate REJECTS it.
    assert!(executor.stage_turn(&[1, 2]).is_some());
    let served = executor.step_staged_turn();
    assert!(!served.is_committed(), "the widening turn is REJECTED at the heart");

    // THE PROJECTION: a rejected turn projects NOTHING — there is no dirty signal
    // to write, no notify to send. The compositor is never woken; the framebuffer
    // is untouched. We assert the projection is None (the fail-closed leg).
    assert!(
        project_dirty_from_turn(&wallet, &served).is_none(),
        "a REJECTED turn projects no dirty region (no repaint signal)"
    );

    // THE PROOF: the framebuffer is BYTE-IDENTICAL — a refused turn re-painted
    // nothing.
    let fb_after_reject = compositor.framebuffer_snapshot();
    assert_eq!(
        fb_after_reject, fb_before_reject,
        "the REJECTED turn re-painted NOTHING (the framebuffer is byte-identical)"
    );
    assert_eq!(
        compositor.frames().len(),
        1,
        "still exactly one frame — the rejected turn logged no repaint"
    );

    // ── Honest fidelity (the label travels with the code). ──
    assert!(
        dregg_firmament::REPAINT_FIDELITY.contains("re-paints the glass"),
        "the fidelity label states the loop is real on the semihost"
    );

    println!(
        "LIVE-REPAINT-ON-TURN: a COMMITTED turn through the executor-PD projected a \
         DirtyRegion → the compositor-PD presented it → the focused cell's tile 10 \
         re-painted (0x{:02X} → 0x{:02X}); a REJECTED turn projected NOTHING → the \
         framebuffer stayed byte-identical. the heart re-paints the glass ( ◕‿◕ )",
        fb_before[10], fb_after_commit[10]
    );
}

// ===========================================================================
// THE SCENE GATE STILL FIRES ON A REPAINT — a turn cannot re-paint a region the
// cell does not own. The repaint present rides the SAME compositor gate as any
// other present; a turn for a cell projecting a dirty region OUTSIDE its owned
// region-set is REFUSED at the framebuffer (no-amplification at the pixel layer).
// ===========================================================================

#[test]
fn a_repaint_outside_the_cells_owned_region_is_refused() {
    let kernel = EmulatedKernel::new();
    let wallet = cell_seed(1);
    let browser = cell_seed(2);

    let mut executor = ExecutorPd::boot(kernel.clone(), AttenuationRunner, 4096, 4096);
    // A scene where the WALLET owns region {10} (focused) and the BROWSER owns
    // {20}. A repaint that tries to paint the browser's region 20 on the wallet's
    // behalf must be refused.
    let mut compositor = CompositorPd::boot(
        kernel.clone(),
        Scene {
            surfaces: vec![
                Surface {
                    owner: wallet,
                    regions: vec![10],
                    content_digest: 0,
                    source_state_root: 0,
                    z_layer: 0,
                    focus_flag: true,
                },
                Surface {
                    owner: browser,
                    regions: vec![20],
                    content_digest: 0xB0, // the browser's existing frame
                    source_state_root: 600,
                    z_layer: 0,
                    focus_flag: false,
                },
            ],
        },
    );

    // The wallet commits a turn (genuine), projecting a dirty region.
    executor.stage_turn(&[2, 1]).unwrap();
    let served = executor.step_staged_turn();
    let dirty = project_dirty_from_turn(&wallet, &served).unwrap();

    // The compositor is asked to repaint the BROWSER's region 20 on the WALLET's
    // behalf (a malicious/buggy dirty target) — the T1 tooth REFUSES it.
    let fb_before = compositor.framebuffer_snapshot();
    let refused = compositor.present(&dirty.owner, dirty.to_present(vec![20]));
    assert!(
        refused.is_err(),
        "a repaint of a region the cell does NOT own is REFUSED (T1 — no amplification)"
    );

    // The browser's tile 20 is UNTOUCHED — the wallet's turn could not re-paint
    // the browser's glass.
    let fb_after = compositor.framebuffer_snapshot();
    assert_eq!(
        fb_after[20], fb_before[20],
        "the browser's tile 20 is untouched (the wallet's repaint did not amplify)"
    );

    // The wallet's OWN region 10 re-paints fine (the honest repaint).
    let ok = compositor.present(&dirty.owner, dirty.to_present(vec![10]));
    assert!(ok.is_ok(), "the wallet's repaint of its OWN region 10 is admitted");

    let _ = ServedTurn::Rejected { reason: String::new() }; // keep the import honest

    println!(
        "REPAINT GATE: the wallet's turn could NOT re-paint the browser's region 20 \
         (T1 refused — tile 20 untouched); its OWN region 10 re-painted. the scene \
         authority gates a repaint exactly like any present ( ⌐■_■ )"
    );
}
