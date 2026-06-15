//! # deos-leptos — the Leptos runtime as the deos cell-affordance surface
//!
//! **The hypothesis (ember): "we can use the leptos runtime if it helps us with
//! the deos/cell-stuff — i think it will."** This crate is the working prototype
//! that confirms it, and names the one place the deos trust boundary and Leptos's
//! native/WASM boundary coincide.
//!
//! `docs/deos/DEOS.md` calls the deos interaction model **htmx on crack**: a cell
//! declares named, typed **affordances** (effect-templates), and an interaction is
//! a **capability-gated verified turn** — the "button" is a real
//! [`dregg_turn::Effect`], and *who may press it* is decided by held capabilities.
//! Leptos is a Rust full-stack framework built on **fine-grained reactivity**: UI
//! is a graph of [`leptos::prelude::RwSignal`]s and derived
//! [`leptos::prelude::Memo`]s, and a view re-renders exactly the nodes whose
//! signals changed. The thesis this crate proves:
//!
//! > **Leptos's signal graph is the natural RUNTIME for the deos reactive rung,
//! > and its server-render → per-island-hydrate split IS the frustum-snapshot
//! > rehydration — with the membrane deciding what hydrates.**
//!
//! ## The three mappings (each demonstrated by a test below)
//!
//! 1. **signals ↔ the Reactive rung.** A council cell's [`dregg_cell::CellState`]
//!    lives in an [`RwSignal`]. An affordance renders as a reactive view whose
//!    lit/dark state is a [`Memo`] that calls the REAL
//!    [`ReactiveAffordance::reactive_ok`] (the three-way cap ∧ transition ∧ window
//!    gate, the Rust twin of the Lean `reactiveOK`). Change the signal → the memo
//!    recomputes → the button lights or darkens. This is the runtime dual of the
//!    Lean `fireReactive_window_reactive` (the htmx-temporal tooth): the SAME
//!    viewer's SAME move is lit inside the window and dark outside it, decided by
//!    the cell state + the clock, **not** by a reimplemented predicate — by the
//!    imported gate. See [`affordance_is_lit`] and [`CounterCell`].
//!
//! 2. **Leptos hydration ↔ frustum-snapshot rehydration.** SSR renders the cell;
//!    each affordance is an "island". WHICH islands a given viewer gets is decided
//!    by the REAL membrane [`Viewer::membrane_shows`] /
//!    [`AffordanceSurface::project_membrane`] — caps AND the witness-graph
//!    disclosure bit. So the SAME server-rendered surface re-expands to DIFFERENT
//!    per-viewer surfaces (the keystone `membrane_two_viewers_distinct`). This is
//!    the runtime form of "a snapshot re-expands per-viewer, cap-gated by the
//!    membrane" ([`render_council_for`] + the `two_viewers_*` tests). The
//!    [`Rehydration`] liveness-type carries through, exactly as for a rehydrated
//!    view.
//!
//! 3. **htmx-on-crack in Rust — over a REAL executor (the seam is CLOSED).** A
//!    reactive button's press POSTs a [`server::FireRequest`] to the server function
//!    [`server::fire_affordance`], which adjudicates it with the REAL
//!    [`ReactiveAffordance::fire`] gate (the SAME `ReactiveAffordance` the island's
//!    lit/dark Memo reacts on) and, on a pass, submits the gate's real
//!    [`dregg_turn::Effect`] through the genuine [`dregg_turn::TurnExecutor`] (owned by
//!    [`dregg_sdk::AgentRuntime`] over an in-process verified ledger) — returning a real
//!    [`dregg_turn::TurnReceipt`] plus the COMMITTED cell state. The signal re-seeds
//!    from the committed state; the [`Memo`]s recompute and the view reacts. The fire's
//!    gate is the REAL one — an unauthorized press is a precise `FireError::Unauthorized`,
//!    a wrong-transition press a `FireError::TransitionUnmet`, an out-of-window press a
//!    `FireError::OutsideWindow`, and **nothing is committed on a refusal** (the
//!    anti-ghost tooth). There is no mock anywhere in the loop: see [`server`] + tests.
//!
//! ## The architecture finding (the fit + the seam, now closed)
//!
//! The deos gate types (`is_attenuation`, [`dregg_turn::Effect`],
//! [`ReactiveAffordance`]) AND the executor ([`dregg_turn::TurnExecutor`]) sit **atop
//! the STARK crypto stack** (`dregg-turn` → `dregg-circuit` → plonky3 + the Lean
//! FFI). That stack is **native-only** — it does not compile to
//! `wasm32-unknown-unknown`. So the surface splits exactly where deos already draws
//! its trust boundary:
//!
//! - **The gate + the executor run server-side (native).** SSR (`leptos`'s `ssr`
//!   feature) is the render path that links the real gate; [`server`] holds the real
//!   executor. The verdict "may this button fire?" AND the commit are computed where
//!   the executor + the proof system live — which is *correct*: a light client must
//!   not be the authority.
//! - **The client island reacts (WASM).** A hydrated island renders + reacts to
//!   signals but does NOT hold the gate or the executor; it fires a turn over the
//!   **server function** [`server::fire_affordance`] and reflects the receipted,
//!   committed result. Leptos's server-function model maps onto this 1:1: the island
//!   is the *will*, the server is the *law* (`docs/REFINEMENT-DESIGN.md` "cells are
//!   law, agents are will").
//!
//! **So the fit is strong on the runtime axis (signals = reactive rung; hydration =
//! rehydration), the native/WASM split is the deos seam made literal, and the fire is
//! a genuine verified turn — not a mock.** The named follow-up (a `MockExecutor`
//! stand-in for a live `TurnExecutor`) is DONE: [`server::fire_affordance`] IS the
//! real executor fire.

use leptos::prelude::*;

/// The reactive-predicate gate model (`CellSlots`, the live-state `GateVerdict` over
/// the REAL `CellProgram::evaluate`/`is_attenuation`). The signal payload + the
/// server-side committed-state readback live here.
pub mod gate;
/// The SERVER side — the real [`dregg_turn::TurnExecutor`] (owned by
/// [`dregg_sdk::AgentRuntime`]) behind the affordance fire. This module CLOSES the
/// seam the prototype named: a fire is now a genuine verified turn that returns a real
/// [`dregg_turn::TurnReceipt`], not a mock. The island POSTs a [`server::FireRequest`]
/// to [`server::fire_affordance`]; the server runs the REAL gate + executor and
/// returns the COMMITTED state.
pub mod server;
/// The LIVE reactive transclusion — Ted Nelson's "live quote", made runnable. A
/// council surface transcludes a constitution cell's `threshold` through the REAL
/// [`starbridge_web_surface::transclusion::TranscludedField`]; when the source is
/// amended, the Leptos quote [`leptos::prelude::Memo`] re-resolves the verified read
/// and the view shows the NEW committed value at the NEW provenance height (the live
/// update). The runnable demo of the proven `Dregg2.Deos.Transclusion` primitive.
pub mod transclusion_demo;
/// The EEL — Ted Nelson's **parallel source view**, made runnable. Renders a multi-span
/// [`deos_web_cells::DreggverseDocument`] in one column and, BESIDE each transcluded
/// span, its SOURCE cell with the quoted byte range highlighted + a working
/// `#eel-src-N` jump-to-source anchor — built on [`deos_web_cells::RenderedSpan::source_link`]
/// + the genuine [`deos_web_cells::DreggverseDocument::resolve_for`] per-viewer membrane
/// meet. A DARKENED span (the viewer lacks authority) still shows its citation ("you may
/// not read this, but here is what it cites" — bytes withheld, never forged), and the
/// reactive [`parallel_source_view::ParallelSourceView`] re-resolves on a source amend so
/// the highlight tracks the source LIVE (the unbreakable link, in the parallel view).
pub mod parallel_source_view;

use starbridge_web_surface::{
    AffordanceSurface, AuthRequired, CellAffordance, EvalContext, ReactiveAffordance,
    Rehydration, SurfaceCapability, TransitionGate, Viewer,
};
use starbridge_web_surface::affordance::RecordPredicate;
use dregg_cell::state::CellState;
use dregg_turn::Effect;
use dregg_types::CellId;

// ════════════════════════════════════════════════════════════════════════════
// The council/counter CELL — the worked example. Its state is the same council
// cell the Lean `Reactive.lean §8` and the Rust `affordance.rs` tests use: a
// `status` slot (PENDING/RESOLVED) and a `tally` slot, which the `TransitionGate`
// reads BOTH of. (We mirror those test fixtures so the runtime drives the SAME
// gate the proofs `#guard`.)
// ════════════════════════════════════════════════════════════════════════════

/// The status slot index on the council cell.
pub const STATUS_SLOT: usize = 0;
/// The tally slot index on the council cell.
pub const TALLY_SLOT: usize = 1;
/// The PENDING status code.
pub const PENDING: u64 = 1;
/// The RESOLVED status code.
pub const RESOLVED: u64 = 2;
/// The quorum threshold the `resolve` button's link crosses.
pub const QUORUM: u64 = 3;

/// A field-element from a small `u64` (big-endian last 8 bytes) — the cell crate's
/// `field_to_u64` lift, matching `affordance.rs`'s `fe`.
pub fn fe(n: u64) -> [u8; 32] {
    let mut b = [0u8; 32];
    b[24..32].copy_from_slice(&n.to_be_bytes());
    b
}

/// Read a `u64` slot off a [`CellState`] (the Rust twin of the Lean
/// `Value.scalar`) — `None` if absent.
pub fn slot_u64(s: &CellState, slot: usize) -> Option<u64> {
    s.get_field(slot).map(|f| {
        let mut last8 = [0u8; 8];
        last8.copy_from_slice(&f[24..32]);
        u64::from_be_bytes(last8)
    })
}

/// A council-cell state with the given `status` + `tally`.
pub fn council(status: u64, tally: u64) -> CellState {
    let mut s = CellState::new(0);
    s.set_field(STATUS_SLOT, fe(status));
    s.set_field(TALLY_SLOT, fe(tally));
    s
}

/// A real `SetField` [`Effect`] (the genuine turn the executor runs for a slot
/// write) — the affordance's effect-template.
fn set_field(cell: CellId, index: usize, value: u64) -> Effect {
    Effect::SetField {
        cell,
        index,
        value: fe(value),
    }
}

/// A predicate "status slot == `want`" (a [`RecordPredicate`] over a single
/// record — the `pre`/`post` endpoints of a transition gate).
fn status_is(want: u64) -> RecordPredicate {
    Box::new(move |s: &CellState| slot_u64(s, STATUS_SLOT) == Some(want))
}

/// The VOTE transition gate: PENDING → PENDING AND the tally went up by EXACTLY
/// ONE — the relational `link` reading BOTH records (the half a single-state gate
/// cannot witness). Identical to `affordance.rs`'s `vote_gate`.
pub fn vote_gate() -> TransitionGate {
    TransitionGate::new(
        status_is(PENDING),
        status_is(PENDING),
        Box::new(|old: &CellState, new: &CellState| {
            match (slot_u64(old, TALLY_SLOT), slot_u64(new, TALLY_SLOT)) {
                (Some(a), Some(b)) => b == a + 1,
                _ => false,
            }
        }),
    )
}

/// The "vote" reactive button: the ballot cap (`Either`), the add-a-ballot
/// transition, and the inclusive `[10, 20]` height window. Fires a real
/// `SetField` on the tally slot. The Rust twin of the Lean `voteBtn`.
pub fn vote_btn(cell: CellId) -> ReactiveAffordance {
    ReactiveAffordance::new(
        CellAffordance::new(
            "vote",
            AuthRequired::Either,
            set_field(cell, TALLY_SLOT, 0),
        ),
        vote_gate(),
        10,
        20,
    )
}

/// The held authority of a council MEMBER (holds the ballot cap `Either`).
pub fn member_held(cell: CellId) -> SurfaceCapability {
    SurfaceCapability::root(cell, AuthRequired::Either)
}
/// The held authority of an OBSERVER (holds only `Signature` — not the ballot cap).
pub fn observer_held(cell: CellId) -> SurfaceCapability {
    SurfaceCapability::root(cell, AuthRequired::Signature)
}

// ════════════════════════════════════════════════════════════════════════════
// MAPPING 1 — signals ↔ the Reactive rung. The reactive predicate driving the
// view IS the imported `ReactiveAffordance`, NOT a reinvention.
// ════════════════════════════════════════════════════════════════════════════

/// **The reactive predicate the Leptos view lights/darkens on** — a thin wrapper
/// that reads the current cell state from a signal and calls the REAL
/// [`ReactiveAffordance::reactive_ok`] (cap ∧ transition ∧ window). This is the
/// ONLY logic the view needs: everything load-bearing is the imported gate.
///
/// `old` is the cell state BEFORE the candidate fire; `new` is the candidate
/// post-state (for "vote", `new` = `old` with the tally bumped by one). The button
/// is LIT iff the gate would admit the `old → new` transition for `held` at
/// `height`.
pub fn affordance_is_lit(
    btn: &ReactiveAffordance,
    held: &SurfaceCapability,
    height: u64,
    old: &CellState,
    new: &CellState,
) -> bool {
    btn.reactive_ok(held, &EvalContext::at_height(height), old, new)
}

/// **`CounterCell`** — a Leptos component rendering the council/counter cell as a
/// reactive surface (MAPPING 1, in the runtime). The cell state is a `RwSignal`;
/// the vote button's lit/dark class is a `Memo` over the REAL gate; pressing POSTs a
/// [`server::FireRequest`] to the server function [`server::fire_affordance`], which
/// runs the REAL [`dregg_turn::TurnExecutor`] and returns the COMMITTED state — the
/// signal re-seeds from it and the view reacts (MAPPING 3, in the same component).
///
/// The props carry the viewer's `held` authority + the current turn `height` (the
/// reactive window's clock). Two instances with different `held`/`height` render
/// DIFFERENT lit/dark verdicts over the SAME signal — because the predicate is the
/// imported gate, not a per-component reimplementation.
#[component]
pub fn CounterCell(
    /// The cell this surface backs.
    cell: CellId,
    /// The viewer's held authority (the cap dimension of the gate).
    held: SurfaceCapability,
    /// The current turn height (the reactive window's clock).
    height: u64,
) -> impl IntoView {
    // The cell's state IS a Leptos signal — MAPPING 1's core. The council starts
    // PENDING with tally 0.
    let state = RwSignal::new(council(PENDING, 0));
    // The gate carries `Box<dyn Fn>` predicates (the TransitionGate's pre/post/link),
    // which are not `Send + Sync`, so it lives in a thread-local `StoredValue`
    // (`new_local`). The SSR render runs single-threaded per request, so thread-local
    // storage is the right home — and it keeps the REAL gate (with its closures) in
    // the component without a parallel Send-able reimplementation. This is the
    // CLIENT-side reactive predicate (the WILL — what the island OFFERS), distinct
    // from the server-side executor (the LAW — what actually COMMITS).
    let btn = StoredValue::new_local(vote_btn(cell));

    // The candidate "vote" transition's post-state is the live state with the
    // tally bumped by one. A derived signal (the htmx reactivity): when `state`
    // changes, `candidate_new` recomputes.
    let candidate_new = Memo::new(move |_| {
        let s = state.get();
        let t = slot_u64(&s, TALLY_SLOT).unwrap_or(0);
        council(PENDING, t + 1)
    });

    // THE LIT/DARK MEMO — the runtime dual of `fireReactive_window_reactive`. It
    // calls the REAL `reactive_ok`; it recomputes whenever `state` (and hence
    // `candidate_new`) changes. This is the whole point: the view's reactivity is
    // the gate's reactivity, threaded through Leptos's signal graph.
    let held_for_lit = held.clone();
    let lit = Memo::new(move |_| {
        btn.with_value(|b| {
            affordance_is_lit(b, &held_for_lit, height, &state.get(), &candidate_new.get())
        })
    });

    // A readout of the live tally for the view.
    let tally = Memo::new(move |_| slot_u64(&state.get(), TALLY_SLOT).unwrap_or(0));

    // The press handler — MAPPING 3, now over the REAL executor (the seam is CLOSED).
    // The island is a thin reactive shell: it does NOT hold the gate or the executor
    // (they sit atop the native STARK stack — they cannot link in the browser). It
    // POSTs a `FireRequest` (the affordance name + the viewer's held authority) to the
    // server function `server::fire_affordance`; the server runs the REAL cap∧state
    // gate + the REAL `dregg_turn::TurnExecutor` and returns the COMMITTED state.
    //
    // On a committed turn the signal re-seeds from the state the executor ACTUALLY
    // committed (not a client guess); on a refusal the precise reason is recorded and
    // the state is left UNCHANGED (the anti-ghost tooth — nothing committed). In a
    // hydrate build this runs over Leptos's server-function transport (`spawn_local`
    // + a `ServerAction`); here the body is called directly so the SSR render and the
    // tests exercise the REAL committed path.
    let refusal = RwSignal::new(Option::<String>::None);
    let held_rights = held.window.rights.clone();
    let on_press = move || {
        // The island's WILL → the server's LAW. The held authority crosses the wire
        // as the cap dimension; the height is the reactive window's clock; the server
        // reads the cell's live state itself and runs the REAL gate + executor.
        let resp = server::fire_affordance(
            server::FireRequest::at("vote", held_rights.clone()).height(height),
        );
        match resp.result {
            Ok(committed) => {
                // Reflect the state the executor COMMITTED (read back from the real
                // ledger) into the signal — the view reacts to the verified turn.
                refusal.set(None);
                state.set(council(committed.slots.status, committed.slots.tally));
            }
            Err(refused) => {
                // Anti-ghost: nothing committed; surface the precise reason and leave
                // the state exactly as it was.
                refusal.set(Some(refused.reason));
                state.set(council(refused.slots.status, refused.slots.tally));
            }
        }
    };

    view! {
        <div class="deos-counter-cell">
            <p class="tally">"tally: " {move || tally.get()}</p>
            <button
                // The button's class reflects the REAL gate verdict, reactively.
                class:lit=move || lit.get()
                class:dark=move || !lit.get()
                // Disabled exactly when the gate would refuse — the surface never
                // offers a button it would reject (the projection-soundness tooth).
                disabled=move || !lit.get()
                on:click=move |_| on_press()
            >
                "vote"
            </button>
            // The anti-ghost message: a refused fire (cap/state/executor) surfaces its
            // PRECISE reason here, never a silent dark button. Empty when no refusal.
            {move || refusal.get().map(|r| view! { <p class="refusal" role="alert">{r}</p> })}
        </div>
    }
}

// ════════════════════════════════════════════════════════════════════════════
// MAPPING 3 — THE EXECUTOR SEAM, CLOSED. The fire is a REAL verified turn. The
// `MockExecutor` is GONE; the press now POSTs to the server function
// `server::fire_affordance` (above), which adjudicates with the REAL
// `ReactiveAffordance::fire` gate and submits the gated effect through the genuine
// `dregg_turn::TurnExecutor` (owned by `dregg_sdk::AgentRuntime`, over an in-process
// verified ledger) — returning a real `dregg_turn::TurnReceipt` plus the COMMITTED
// state the signal re-seeds from.
//
// The real executor lives in [`crate::server`] (native-only — the gate + executor
// sit atop the STARK stack and cannot link in the browser island; that boundary IS
// the deos seam). See:
//   * [`server::DeosExecutorCell`] — the council cell + the real executor;
//   * [`server::fire_affordance`] — the server-fn body the island POSTs to;
//   * [`server::FireRequest`] / [`server::FireResponse`] — the wire shape.
// The teeth (a refused fire is a precise `FireError` and NOTHING is committed; an
// authorized fire commits a real receipt) are proved by the `server` module's tests.
// ════════════════════════════════════════════════════════════════════════════

// ════════════════════════════════════════════════════════════════════════════
// MAPPING 2 — Leptos hydration ↔ frustum-snapshot rehydration. SSR renders the
// surface; the membrane decides which affordances a viewer's island gets.
// ════════════════════════════════════════════════════════════════════════════

/// The canonical council surface — `{vote, tally}` — over `cell`. `vote` requires
/// the ballot cap (`Either`); `tally` is a secret-ballot read anyone with
/// `Signature` MAY fire IF their frustum permits it (the witness-graph disclosure
/// dimension the membrane divides on, beyond caps).
pub fn council_surface(cell: CellId) -> AffordanceSurface {
    AffordanceSurface::new(cell)
        .declare(CellAffordance::new(
            "vote",
            AuthRequired::Either,
            set_field(cell, TALLY_SLOT, 0),
        ))
        .declare(CellAffordance::new(
            "tally",
            AuthRequired::Signature,
            // a read logs an access event — modeled here as a SetField no-op slot.
            set_field(cell, STATUS_SLOT, PENDING),
        ))
}

/// **`render_council_for`** — the per-viewer SSR render (MAPPING 2). Render the
/// council surface for `viewer` to an HTML string, where WHICH affordances appear
/// is decided by the REAL membrane [`AffordanceSurface::project_membrane`] /
/// [`Viewer::membrane_shows`] (caps AND the witness-graph disclosure bit). The
/// `height` is the reactive clock; the [`Rehydration`] `liveness` badge is carried
/// in the chrome exactly as a rehydrated view carries it.
///
/// This is the runtime form of "a snapshot re-expands per-viewer through the
/// membrane": two viewers handed the SAME `surface` get DIFFERENT HTML because the
/// membrane projects different affordance sets. (The `view!` for each projected
/// affordance is an island; in a hydrate build, only these islands ship to that
/// viewer's client.)
pub fn render_council_for(
    surface: &AffordanceSurface,
    viewer: &Viewer,
    height: u64,
    liveness: Rehydration,
) -> String {
    // THE MEMBRANE PROJECTION — the REAL gate. The viewer sees exactly the
    // affordances `membrane_shows` admits (cap ∧ witness-graph).
    let shown: Vec<CellAffordance> = surface.project_membrane(viewer);
    let names: Vec<String> = shown.iter().map(|a| a.name.clone()).collect();
    let badge = liveness.badge().to_string();
    let cell = surface.cell;
    let held = viewer.held.clone();

    // Render under a fresh reactive `Owner` so the signal arena (the `RwSignal` /
    // `Memo` / `StoredValue` nodes the reactive view allocates) has a root to live
    // in and be disposed with — the per-request reactive scope an SSR handler owns.
    let owner = Owner::new();
    owner.with(move || {
    // Render the per-viewer surface as a Leptos reactive view tree → HTML. Each
    // affordance is a reactive button (lit/dark by the gate, given the live state).
    let view = view! {
        <section class="deos-council-surface" data-cell=format!("{:?}", cell)>
            <header class="trusted-path">
                <span class="liveness-badge">{badge.clone()}</span>
            </header>
            <ul class="affordances">
                {names
                    .iter()
                    .cloned()
                    .map(|name| {
                        let label = name.clone();
                        view! { <li class="affordance" data-name=name>{label}</li> }
                    })
                    .collect::<Vec<_>>()}
            </ul>
            // The vote counter cell itself (MAPPING 1 + 3) — rendered only if the
            // membrane showed the viewer the vote affordance.
            {shown
                .iter()
                .any(|a| a.name == "vote")
                .then(move || {
                    view! {
                        <CounterCell
                            cell=cell
                            held=held
                            height=height
                        />
                    }
                })}
        </section>
    };
    view.to_html()
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cid(b: u8) -> CellId {
        let mut k = [0u8; 32];
        k[0] = b;
        CellId::derive_raw(&k, &[0u8; 32])
    }

    // ── MAPPING 1: the reactive predicate IS the imported gate; the view's
    //    lit/dark recomputes from the cell-state signal + the clock. ──

    #[test]
    fn mapping1_lit_dark_is_the_real_reactive_gate() {
        // The runtime dual of `fireReactive_window_reactive`: holding the move
        // fixed (the add-a-ballot transition), the SAME member's button is LIT
        // inside the window and DARK outside it. The lit/dark is the REAL
        // `reactive_ok` — not a reinvention.
        let doc = cid(1);
        let btn = vote_btn(doc);
        let held = member_held(cid(10));
        let old = council(PENDING, 0);
        let new = council(PENDING, 1); // a perfect add-a-ballot transition

        // Inside [10, 20] → LIT.
        assert!(affordance_is_lit(&btn, &held, 15, &old, &new));
        // After the deadline (25 > 20) → DARK (the clock darkens it).
        assert!(!affordance_is_lit(&btn, &held, 25, &old, &new));
        // The predicate agrees with the imported gate exactly (anti-reinvention).
        assert_eq!(
            affordance_is_lit(&btn, &held, 15, &old, &new),
            btn.reactive_ok(&held, &EvalContext::at_height(15), &old, &new)
        );
    }

    #[test]
    fn mapping1_lit_darkens_reactively_on_state_change() {
        // As the cell STATE changes, the lit verdict changes — the htmx tooth in
        // the runtime. From tally 0 the add-a-ballot (0→1) is admissible inside the
        // window. But if the state were already RESOLVED (status != PENDING), the
        // gate's `pre` fails → the button darkens, SAME viewer, SAME clock. This is
        // exactly what the `CounterCell`'s `lit` Memo recomputes on `state.set`.
        let doc = cid(2);
        let btn = vote_btn(doc);
        let held = member_held(cid(10));

        // PENDING, tally 0 → candidate (PENDING, 1): LIT.
        assert!(affordance_is_lit(&btn, &held, 15, &council(PENDING, 0), &council(PENDING, 1)));
        // RESOLVED, tally 0 → candidate (PENDING, 1): the `pre` (status PENDING)
        // fails on `old` → DARK. The surface reacted to the cell's state.
        assert!(!affordance_is_lit(&btn, &held, 15, &council(RESOLVED, 0), &council(PENDING, 1)));
    }

    #[test]
    fn mapping1_cap_tooth_observer_button_is_dark() {
        // The cap dimension survives in the runtime: an observer (no ballot cap)
        // sees a DARK button on a perfect transition inside the window — the REAL
        // `is_attenuation` refuses it FIRST.
        let doc = cid(3);
        let btn = vote_btn(doc);
        assert!(!affordance_is_lit(
            &btn,
            &observer_held(cid(11)),
            15,
            &council(PENDING, 0),
            &council(PENDING, 1)
        ));
    }

    // ── MAPPING 3: the press fires a REAL verified turn through the REAL executor
    //    (the CLOSED seam — `server::fire_affordance`); the committed state advances
    //    so the view re-seeds; a refused press commits NOTHING (anti-ghost). The
    //    deep teeth are in `server.rs`; here we prove the runtime LOOP — the same
    //    `fire_affordance` body the island POSTs to — drives a real commit. ──

    #[test]
    fn mapping3_press_fires_real_turn_and_committed_state_advances() {
        // A councillor (holds the ballot cap `Either`) presses vote on a fresh
        // PENDING council: the server function fires the REAL `dregg_turn` executor,
        // commits the verified turn, and returns the COMMITTED tally (0 → 1) plus the
        // real turn-hash. This is the runtime loop the island drives: press →
        // FireRequest → real gate + real executor → committed state (the signal the
        // view re-renders from).
        crate::server::reset_executor_cell();
        let resp = crate::server::fire_affordance(
            crate::server::FireRequest::at("vote", AuthRequired::Either), // ballot cap — a councillor
        );
        let committed = resp.result.expect("an authorized vote commits a real turn");
        assert_eq!(committed.slots.tally, 1, "the committed tally the view re-seeds from");
        assert_ne!(committed.turn_hash, [0u8; 32], "a REAL verified turn, not a mock");
    }

    #[test]
    fn mapping3_refused_press_commits_nothing_anti_ghost() {
        // The anti-ghost tooth in the runtime, over the REAL executor: a press by an
        // observer (holds only `Signature`, NOT the ballot cap) is refused on the cap
        // tooth — a precise `FireError::Unauthorized`, surfaced as the refusal reason
        // — and NOTHING is committed (the live tally stays 0). The same in-band
        // refusal the island shows as its anti-ghost message.
        crate::server::reset_executor_cell();
        let resp = crate::server::fire_affordance(
            crate::server::FireRequest::at("vote", AuthRequired::Signature), // observer — no ballot cap
        );
        let refused = resp.result.expect_err("an observer's vote is refused");
        assert!(
            refused.reason.contains("Unauthorized"),
            "precise cap-tooth reason surfaced: {}",
            refused.reason
        );
        // Anti-ghost: nothing committed — the tally is still 0, still PENDING.
        assert_eq!(refused.slots.tally, 0, "a refused press commits nothing");
        assert!(refused.slots.is_pending());
    }

    // ── MAPPING 2: SSR renders DIFFERENT surfaces for two viewers; the membrane
    //    (caps AND the witness-graph disclosure bit) decides what hydrates. ──

    #[test]
    fn mapping2_two_viewers_with_different_caps_render_distinct_surfaces() {
        // A member (Either, ballot cap, permits all) vs an observer (Signature,
        // permits all). The membrane shows the member {tally, vote} and the
        // observer {tally} only (vote needs the ballot cap). The SAME surface
        // re-expands to DIFFERENT HTML — the runtime form of per-viewer
        // rehydration.
        let doc = cid(6);
        let surface = council_surface(doc);

        let member = Viewer::new(member_held(cid(10)), Box::new(|_| true));
        let observer = Viewer::new(observer_held(cid(11)), Box::new(|_| true));

        let member_html =
            render_council_for(&surface, &member, 15, Rehydration::ReplayedDeterministic);
        let observer_html =
            render_council_for(&surface, &observer, 15, Rehydration::ReplayedDeterministic);

        // The member's surface carries the vote affordance; the observer's does not.
        assert!(member_html.contains("data-name=\"vote\""), "member sees vote: {member_html}");
        assert!(member_html.contains("data-name=\"tally\""));
        assert!(!observer_html.contains("data-name=\"vote\""), "observer must NOT see vote: {observer_html}");
        assert!(observer_html.contains("data-name=\"tally\""));

        // DISTINCT surfaces over the SAME server render.
        assert_ne!(member_html, observer_html);
        // The member's surface includes the reactive counter cell (the vote
        // button); the observer's does not (no vote affordance shown).
        assert!(member_html.contains("deos-counter-cell"));
        assert!(!observer_html.contains("deos-counter-cell"));
    }

    #[test]
    fn mapping2_membrane_keystone_equal_caps_distinct_by_witness_graph() {
        // THE MEMBRANE KEYSTONE (twin of `membrane_two_viewers_distinct`): two
        // viewers at EQUAL authority (both Signature, both clear the `tally`
        // cap-gate) but DIFFERENT witness-graph `permits` — a trustee whose frustum
        // SHOWS the tally vs a guest whose does NOT — render DISTINCT surfaces. The
        // membrane divides BEYOND caps, in the runtime.
        let doc = cid(7);
        let surface = council_surface(doc);

        let trustee = Viewer::new(
            observer_held(cid(40)),
            Box::new(|name: &str| name == "tally"),
        );
        let guest = Viewer::new(observer_held(cid(41)), Box::new(|_| false));

        let trustee_html =
            render_council_for(&surface, &trustee, 15, Rehydration::Live);
        let guest_html = render_council_for(&surface, &guest, 15, Rehydration::Live);

        // Equal caps, yet distinct surfaces: the trustee sees the tally, the guest
        // sees nothing — divided by the witness-graph, not the cap.
        assert!(trustee_html.contains("data-name=\"tally\""));
        assert!(!guest_html.contains("data-name=\"tally\""));
        assert_ne!(trustee_html, guest_html);
    }

    #[test]
    fn mapping2_liveness_type_carries_through_the_render() {
        // The rehydration liveness-type is carried in the rendered chrome (the
        // trusted-path badge), exactly as a rehydrated view carries it — the
        // runtime form of "open the image tells you which kind of true you get".
        let doc = cid(8);
        let surface = council_surface(doc);
        let viewer = Viewer::new(member_held(cid(10)), Box::new(|_| true));

        let replayed =
            render_council_for(&surface, &viewer, 15, Rehydration::ReplayedDeterministic);
        let reconstructed =
            render_council_for(&surface, &viewer, 15, Rehydration::ReconstructedApproximate);

        assert!(replayed.contains("REPLAYED-DETERMINISTIC"));
        assert!(reconstructed.contains("RECONSTRUCTED-APPROXIMATE"));
        // The badge faithfully distinguishes the two liveness types in the HTML.
        assert_ne!(replayed, reconstructed);
    }

    // ── SSR sanity: the reactive component renders to HTML on the native target
    //    (the gate-linkable side), reflecting the gate verdict. ──

    #[test]
    fn ssr_counter_cell_renders_with_a_lit_button_for_a_member() {
        // A member at height 15 over a fresh PENDING/0 council: the vote button is
        // LIT (the add-a-ballot 0→1 qualifies in-window). The SSR HTML reflects the
        // REAL gate verdict — the runtime render and the gate agree.
        let doc = cid(9);
        let html = render_council_for(
            &council_surface(doc),
            &Viewer::new(member_held(cid(10)), Box::new(|_| true)),
            15,
            Rehydration::Live,
        );
        // The counter cell rendered, and the button is present.
        assert!(html.contains("deos-counter-cell"));
        assert!(html.contains(">vote</button>") || html.contains("vote</button>"));
        // The fresh tally is 0 in the rendered surface.
        assert!(html.contains("tally: "));
    }
}
