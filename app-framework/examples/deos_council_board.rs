//! `deos_council_board` — a deos-native **approval board** where a button lights ONLY
//! when caps AND live state both pass (the cap∧state conjunction; the htmx-on-crack
//! tooth). The concrete exemplar of the freshly-wired `GatedAffordance` — the Rust twin
//! of the Lean rung `metatheory/Dregg2/Deos/GatedAffordance.lean`.
//!
//! `docs/deos/DEOS.md` §"htmx on crack" + `docs/deos/DEOS-APPS.md` §"the deos app
//! model". This is the council/approval-board the EVOLUTION asks for: it EXEMPLIFIES
//! the deosic ambition that "who may press the button" (caps) and "may the button be
//! pressed RIGHT NOW" (state) are ONE in-band verdict — and that the surface REACTS to
//! the cell, not to a session cookie.
//!
//! THE SCENE. A council reviews a proposal cell (slot 0 = `status`: PENDING=1,
//! RESOLVED=2). The board exposes:
//!   - `approve` — a GATED affordance: requires the approver cap (`Either`) AND the
//!     proposal in PENDING. The cap∧state conjunction. The button is the htmx-on-crack
//!     element with teeth in TWO dimensions.
//!   - `comment` — a cap-only affordance (anyone with a signature may comment, any
//!     state). The baseline, for contrast.
//!
//! WHAT IT DEMONSTRATES (each a verified property, not a UI flag):
//!   1. **The per-viewer, per-STATE projection.** Three viewers — an APPROVER, a plain
//!      MEMBER, an incomparable OUTSIDER — project a DIFFERENT button-set off the SAME
//!      board. The framework reads the cell's LIVE state from the embedded executor;
//!      the author threads NO `(old, new)`.
//!   2. **The htmx tooth** — the SAME approver's `approve` button is LIT while the
//!      proposal is PENDING and goes DARK the instant it RESOLVES. Same viewer, same
//!      caps, different verdict — because the cell transitioned. The surface is live.
//!   3. **The cap tooth (anti-ghost)** — a MEMBER firing `approve` (right state, wrong
//!      caps) is REFUSED IN-BAND (`FireError::Unauthorized`); nothing is submitted.
//!   4. **The state tooth (anti-ghost)** — an APPROVER firing `approve` after the
//!      proposal RESOLVED (right caps, wrong state) is REFUSED IN-BAND
//!      (`FireError::StateConditionUnmet`), EVEN for a fully-authorized actor; nothing
//!      is submitted. This is the half a cap-only gate could never express.
//!   5. **A real verified turn** — when caps AND state both pass, the gated fire goes
//!      through the EmbeddedExecutor and yields the executor's OWN `TurnReceipt`.
//!   6. **The frustum-snapshot rehydrates per-viewer** — a cold snapshot of the board
//!      re-expands a DIFFERENT view for the approver vs. an incomparable identity (the
//!      membrane mints no projection for the latter), carrying its DERIVED liveness-type.
//!
//! Run it:
//! ```sh
//! cargo run -p dregg-app-framework --example deos_council_board            # narrate, exit 0
//! cargo run -p dregg-app-framework --example deos_council_board -- --serve # + HTTP surface
//! ```

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CapTpServer, CellAffordance, DeosApp, DeosCell,
    EmbeddedExecutor, FederationId, GatedAffordance, InteractionLog,
};
use dregg_cell::state::{CellState, FieldElement};
use dregg_cell::{CellProgram, StateConstraint};
use dregg_turn::action::{Effect, Event};

/// Slot 0 of the proposal cell carries its `status`.
const STATUS_SLOT: usize = 0;
const PENDING: u64 = 1;
const RESOLVED: u64 = 2;

/// A field element holding `n` big-endian in its last 8 bytes (the comparison the
/// field's `FieldEquals` atom reads).
fn fe(n: u64) -> FieldElement {
    let mut b = [0u8; 32];
    b[24..32].copy_from_slice(&n.to_be_bytes());
    b
}

/// The live-state condition for `approve` — the affordance's PRECONDITION: the
/// proposal must currently be in PENDING (`slot[0] == PENDING`). A real `CellProgram`
/// — the SAME predicate language the executor enforces every turn — evaluated by the
/// gate against the cell's CURRENT state. (This gates "may the button fire NOW"; it is
/// NOT the cell's lifetime invariant — that is [`proposal_invariant`].)
fn pending_precondition() -> CellProgram {
    CellProgram::Predicate(vec![StateConstraint::FieldEquals {
        index: STATUS_SLOT as u8,
        value: fe(PENDING),
    }])
}

/// The proposal cell's installed lifetime INVARIANT (enforced by the executor on the
/// POST-state of EVERY turn): `status` is monotonic — a proposal may resolve
/// (PENDING=1 → RESOLVED=2) but never un-resolve (2 → 1 is rejected by the executor).
/// This is the genuine state-machine of the cell, distinct from the affordance's
/// precondition; the `approve` turn (1 → 2) satisfies it, so the gated fire commits.
fn proposal_invariant() -> CellProgram {
    CellProgram::Predicate(vec![StateConstraint::Monotonic {
        index: STATUS_SLOT as u8,
    }])
}

/// Set the proposal cell's `status` slot directly in the embedded ledger (so the
/// demo can move the cell between PENDING and RESOLVED and watch the button react).
/// This stands in for the council's resolving turn; the gate reads the result back
/// through `EmbeddedExecutor::cell_state`.
fn set_status(executor: &EmbeddedExecutor, proposal: dregg_types::CellId, status: u64) {
    executor.with_ledger_mut(|ledger| {
        if let Some(cell) = ledger.get_mut(&proposal) {
            cell.state.set_field(STATUS_SLOT, fe(status));
        }
    });
}

fn main() {
    let serve = std::env::args().any(|a| a == "--serve");

    // The SDK surface: a cipherclerk + an embedded executor (the in-process verified
    // ledger). The proposal cell is the agent's OWN cell (so the embedded ledger holds
    // it and fires execute through the real executor).
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0xC0; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let proposal = cclerk.cell_id();

    // Install the proposal's lifetime INVARIANT (status monotonic: may resolve, never
    // un-resolve) on the cell AND seed it PENDING. The executor enforces this on every
    // turn's post-state; the `approve` transition (1 → 2) satisfies it.
    executor.install_program(proposal, proposal_invariant());
    set_status(&executor, proposal, PENDING);

    // ── The board, declaratively. The author writes affordances; the framework wires
    //    the verified state read, the gate, the projection, and the dispatch. ──
    //
    // `approve` is GATED (cap∧state): approver cap `Either` AND proposal == PENDING.
    // `comment` is cap-only (Signature, any state) — the contrast.
    let approve = GatedAffordance::new(
        CellAffordance::new(
            "approve",
            AuthRequired::Either,
            Effect::SetField {
                cell: proposal,
                index: STATUS_SLOT,
                value: fe(RESOLVED),
            },
        ),
        pending_precondition(),
    );
    let comment = CellAffordance::new(
        "comment",
        AuthRequired::Signature,
        Effect::EmitEvent {
            cell: proposal,
            event: Event {
                topic: [0xC0; 32],
                data: vec![],
            },
        },
    );

    let board = DeosCell::new(proposal, "proposal")
        .affordance(comment)
        .gated(approve)
        .publish(AuthRequired::Signature); // exported into the web-of-cells

    let captp = CapTpServer::new(FederationId([0xC0; 32]));
    let app = DeosApp::builder("council-board", cclerk.clone(), executor.clone())
        .web_of_cells(captp)
        .discoverable(vec!["council".into(), "approval-board".into()])
        .cell(board)
        .build();
    let board = app.cells()[0].clone();

    // The three viewers, by the authority they HOLD (the REAL is_attenuation lattice):
    //   - the APPROVER holds `Either` (a signature OR a proof satisfies `approve`);
    //   - the MEMBER holds only `Signature` (enough to `comment`, NOT to `approve`);
    //   - the OUTSIDER holds an incomparable `Custom` identity (neither attenuates the
    //     others — the structural no-peek).
    let approver = AuthRequired::Either;
    let member = AuthRequired::Signature;
    let outsider = AuthRequired::Custom {
        vk_hash: [0x9E; 32],
    };

    println!("== council-board — a deos approval board (cap∧state gated) ==\n");

    // 1) THE PER-VIEWER, PER-STATE PROJECTION (proposal PENDING). The framework reads
    //    the cell's live state; the author threads nothing.
    println!(
        "proposal is PENDING. each viewer projects a DIFFERENT button-set off the SAME board:"
    );
    print_projection(&board, "approver (Either)   ", &approver, &executor);
    print_projection(&board, "member   (Signature)", &member, &executor);
    print_projection(&board, "outsider (Custom)   ", &outsider, &executor);
    println!("  → the approver's `approve` LIGHTS (cap ∧ state both pass); the member sees");
    println!("    only `comment` (cap tooth darkens approve); the outsider sees nothing\n");

    // 5) A REAL VERIFIED TURN — the approver fires `approve` while PENDING; both teeth
    //    bite, the gate dispatches through the executor, the receipt is the real one.
    println!("the approver fires `approve` while PENDING (caps ∧ state both pass):");
    match board.fire_gated_through_executor("approve", &approver, &cclerk, &executor) {
        Ok(receipt) => println!(
            "  → CONFIRMED — a real verified turn through the EmbeddedExecutor (turn {}…)\n",
            hex8(&receipt.turn_hash)
        ),
        Err(e) => println!("  → unexpectedly refused: {e:?}\n"),
    }

    // 2) THE HTMX TOOTH — the fire above resolved the proposal. The SAME approver now
    //    sees `approve` DARK: same viewer, same caps, the surface REACTED to the cell.
    println!("the proposal is now RESOLVED (the approve turn set status=2).");
    println!("the SAME approver re-projects — `approve` has gone DARK (the htmx tooth):");
    print_projection(&board, "approver (Either)   ", &approver, &executor);
    println!("  → same viewer, same caps, DIFFERENT verdict — because the cell transitioned\n");

    // 4) THE STATE TOOTH (anti-ghost) — the approver fires `approve` again, now stale.
    //    Right caps, wrong state ⇒ REFUSED IN-BAND; nothing reaches the executor.
    println!("the approver fires `approve` AGAIN, now that it is RESOLVED (stale state):");
    match board.fire_gated_through_executor("approve", &approver, &cclerk, &executor) {
        Err(e) => println!(
            "  → REFUSED in-band: {e}\n    (the STATE tooth — even a fully-authorized actor; nothing submitted)\n"
        ),
        Ok(_) => println!("  → ??unexpectedly fired a stale-state approve\n"),
    }

    // 3) THE CAP TOOTH (anti-ghost) — reset to PENDING, then a MEMBER fires `approve`.
    //    Right state, wrong caps ⇒ REFUSED IN-BAND; nothing reaches the executor.
    set_status(&executor, proposal, PENDING);
    println!("reset to PENDING. a MEMBER (signature only) fires `approve`:");
    match board.fire_gated_through_executor("approve", &member, &cclerk, &executor) {
        Err(e) => println!(
            "  → REFUSED in-band: {e}\n    (the CAP tooth — the right state is not enough; nothing submitted)\n"
        ),
        Ok(_) => println!("  → ??unexpectedly let a member approve\n"),
    }

    // 6) THE FRUSTUM-SNAPSHOT REHYDRATES PER-VIEWER. A cold snapshot of the board
    //    re-expands a DIFFERENT view per identity; an incomparable identity gets none.
    let log = InteractionLog::new().record(dregg_app_framework::Interaction::witnessed_turn(
        board.cell(),
        [0xC0; 32],
    ));
    let snap = board.snapshot(log, /* sources_reachable */ false);
    println!(
        "a frustum-snapshot of the board (lineage {:?}, liveness: {}):",
        snap.lineage,
        snap.liveness().badge()
    );
    match board.rehydrate(&snap, approver.clone()) {
        Ok(view) => println!(
            "  the approver rehydrates {:?} (per-viewer, lattice-respecting)",
            view.visible_names()
        ),
        Err(e) => println!("  the approver could not rehydrate: {e:?}"),
    }
    match board.rehydrate(&snap, outsider.clone()) {
        Err(_) => println!(
            "  the outsider (incomparable identity): CANNOT peek — the membrane mints no projection\n"
        ),
        Ok(_) => println!("  ??the outsider unexpectedly rehydrated\n"),
    }

    // The manifest carries the gated affordances with their STATE GATE described, so
    // the cap∧state posture is visible to any client (htmx-on-crack discovery).
    let manifest = app.manifest();
    if let Some(cell0) = manifest.get("cells").and_then(|c| c.get(0)) {
        if let Some(gated) = cell0.get("gatedAffordances").and_then(|g| g.as_array()) {
            println!("manifest advertises {} gated affordance(s):", gated.len());
            for g in gated {
                println!(
                    "  {} — requires {}, state-gate: {}",
                    g.get("name").and_then(|v| v.as_str()).unwrap_or("?"),
                    g.get("requiredRights")
                        .and_then(|v| v.as_str())
                        .unwrap_or("?"),
                    g.get("stateGate").and_then(|v| v.as_str()).unwrap_or("?"),
                );
            }
            println!();
        }
    }

    if serve {
        serve_board(app, cclerk, executor);
    } else {
        println!("(run with --serve to bind the composed router over HTTP)");
    }
}

/// Print one viewer's projected (lit) button-set against the proposal cell's LIVE state.
fn print_projection(
    board: &DeosCell,
    label: &str,
    held: &AuthRequired,
    executor: &EmbeddedExecutor,
) {
    // The cap-only `comment` lives on the plain surface; the gated `approve` on the
    // gated surface (read against live state). Show the union the viewer can actually
    // fire right now.
    let mut lit: Vec<String> = board.surface().visible_names(held);
    lit.extend(board.gated_fireable_names(held, executor));
    lit.sort();
    lit.dedup();
    println!("  {label}  lit buttons: {lit:?}");
}

#[tokio::main(flavor = "current_thread")]
async fn serve_board(app: DeosApp, cclerk: AppCipherclerk, executor: EmbeddedExecutor) {
    use dregg_app_framework::server::{AppConfig, AppServer};
    let config = AppConfig::default().with_listen("127.0.0.1:0");
    let addr = AppServer::new(config)
        .service_name("council-board")
        .with_health()
        .with_cors()
        .with_cipherclerk(cclerk)
        .with_embedded_executor(executor)
        .routes(app.mount())
        .serve_background()
        .await
        .expect("bind");
    println!("serving the council board on http://{addr}");
    println!("  try:  curl http://{addr}/manifest");
    println!("        curl http://{addr}/surface.js");
    println!("(ctrl-c to stop)");
    tokio::signal::ctrl_c().await.ok();
}

fn hex8(bytes: &[u8; 32]) -> String {
    let mut s = String::with_capacity(16);
    for b in bytes.iter().take(8) {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

// A small static assertion that the demo's types line up with the framework surface.
#[allow(dead_code)]
fn _types(_: CellState) {}
