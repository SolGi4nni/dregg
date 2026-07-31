//! **THE PULSE** — the desktop's background beat over the World's dynamics stream.
//!
//! Extracted verbatim from `deos_desktop/mod.rs` so that the reactivity work owns one
//! file rather than a line-range inside an 8,700-line module. No behaviour change: the
//! beat, the cursor, the toast aging and the vat tap are exactly as they were.
//!
//! ⚠ THE BEAT IS FOUR CONCERNS, AND ONLY ONE OF THEM IS EVENT-DRIVEN. Retiring the
//! timer in favour of a commit-driven wake edge must keep the other three, or they
//! fail SILENTLY:
//!   1. `toast_rack.beat()` — toast TTL is counted in beats; without it toasts never retire.
//!   2. `pump_vat_stream()` — an SSE drain from a REMOTE Dregg Computer that never passes
//!      through `commit_turn`, so no local wake can ever carry it.
//!   3. the quiet-half glow retirement — without it every dirty-glow tint stays lit forever.
//!   4. the `since(pulse_cursor)` fold — the ONLY part a wake edge can replace.

use super::*;

impl DeosDesktop {
    /// One beat of THE PULSE — consume the dynamics stream past [`Self::pulse_cursor`].
    /// If the World moved, refresh the icon census (cells born outside the desktop
    /// appear without a reopen) and repaint every open surface off the live ledger.
    /// Foreign residents' committed turns land as green toasts + the status line;
    /// REFUSALS land as amber toasts (the ocap guarantee firing deserves a card).
    /// The rack also ages one beat here — toasts retire themselves.
    pub(super) fn pump_dynamics(&mut self, cx: &mut Context<Self>) {
        use crate::dynamics::WorldEvent;
        let aged = self.toast_rack.beat();
        // THE VAT TAP — drain the attached Dregg Computer's SSE receipt stream
        // (if any) into its feed each beat, so the Receipts face advances LIVE
        // while you watch (the remote half of the pulse; zero when unattached
        // or snapshot-only).
        let vat_new = self.pump_vat_stream();
        // THE PULSE→SIGNALS WELD, quiet half — every beat, even when the World did not
        // move: retire last beat's dirty-glow tint on every open content-IR pane AND
        // every open attached-World card, and catch up turns a surface's OWN backing
        // committed between beats (a button fired on the surface itself). See
        // `viewnode_pane::pulse_panes_quiet` + `card_pulse::pulse_cards_quiet`.
        #[cfg(feature = "card-pane")]
        let weld_quiet = viewnode_pane::pulse_panes_quiet(&self.viewnode_panes, cx)
            | card_pulse::pulse_cards_quiet(&self.card_panes, cx);
        #[cfg(not(feature = "card-pane"))]
        let weld_quiet = false;
        let (cursor, announce, arrivals, cells, field_sets, cell_events, receipts) = {
            let w = self.world.borrow();
            let d = w.dynamics();
            let cursor = d.cursor();
            // The dynamics log is a BOUNDED ring (CORE-AUDIT #11): once it exceeds
            // its retained cap it evicts the oldest events, advancing `base`. If our
            // pulse cursor fell BEHIND that floor between beats, `since` can only
            // hand us the retained tail — the evicted span's FieldSet/CellMutated
            // teeth are gone. Capture the floor now so the loud half can recover
            // conservatively rather than silently under-invalidate.
            let base = d.base();
            if cursor == self.pulse_cursor {
                drop(w);
                if aged || weld_quiet || vat_new > 0 {
                    cx.notify();
                }
                return;
            }
            let mut announce = None;
            let mut arrivals: Vec<(toasts::ToastKind, String)> = Vec::new();
            // The beat's `(cell, slot)` writes — projected into the exact shape the
            // signal registry invalidates on (`deos_js::signals::SourceEvent`), so the
            // weld's loud half can broadcast them to every open content-IR pane + card.
            let mut field_sets: Vec<(CellId, usize)> = Vec::new();
            // The beat's CELL-WIDE mutations (a cell named, no slot): `CellMutated`
            // (nonce bump / sovereign flip / permissions write / cap reshape) and
            // `CapabilityRevoked` — folded through the registries' conservative
            // `invalidate_cell` tooth (wave 3 left them unprojected).
            let mut cell_events: Vec<CellId> = Vec::new();
            for e in d.since(self.pulse_cursor) {
                match e {
                    WorldEvent::TurnCommitted {
                        agent,
                        height,
                        computrons,
                        ..
                    } if *agent != self.user => {
                        let line = format!(
                            "resident {} committed turn #{height} · {computrons}cu",
                            id_short(agent)
                        );
                        announce = Some(format!("⋯ {line}"));
                        arrivals.push((toasts::ToastKind::Committed, line));
                    }
                    WorldEvent::TurnRejected { agent, reason } => {
                        arrivals.push((
                            toasts::ToastKind::Refused,
                            format!("{} — {reason}", id_short(agent)),
                        ));
                    }
                    WorldEvent::FieldSet { cell, index } => field_sets.push((*cell, *index)),
                    WorldEvent::CapabilityRevoked { cell, .. } => cell_events.push(*cell),
                    WorldEvent::CellMutated { cell } => cell_events.push(*cell),
                    _ => {}
                }
            }
            let mut cells: Vec<CellId> = w.ledger().iter().map(|(id, _)| *id).collect();
            cells.sort();
            let receipts = w.receipts().len() as u64;
            // CONSERVATIVE RECOVERY across dynamics eviction (CORE-AUDIT #11). If the
            // pulse lagged MORE than the whole retained cap behind, the beat's `since`
            // slice is only the retained tail — the evicted FieldSet/CellMutated teeth
            // for the lost span never reached `field_sets`/`cell_events`, so a
            // fine-grained invalidation would UNDER-invalidate and leave stale paint
            // (violating "cache soundness = dynamics completeness"). Rather than miss
            // dirty rows, name EVERY live cell as cell-wide dirty so every open
            // pane/card re-reads its binds through the conservative `invalidate_cell`
            // tooth. Only the cosmetic activity-feed toasts for the evicted span are
            // lost (they were never a correctness invariant). In practice this branch
            // never fires — a ~250ms beat cannot emit a full retained cap of events —
            // it is the fail-safe that makes eviction SOUND, not merely cheap.
            if self.pulse_cursor < base {
                cell_events = cells.clone();
            }
            (
                cursor,
                announce,
                arrivals,
                cells,
                field_sets,
                cell_events,
                receipts,
            )
        };
        self.pulse_cursor = cursor;
        self.cells = cells;
        // THE PULSE→SIGNALS WELD, loud half — the World moved: broadcast the beat's
        // FieldSets + cell-wide mutations into every pane's AND every open card's
        // signal registry (exactly the dirty binds re-read), and mirror the moved
        // census into the World-Status panel as receipted tracking turns. The shipped
        // surfaces' binds finally track the live World.
        #[cfg(feature = "card-pane")]
        {
            let census = viewnode_pane::WorldCensus {
                cells: self.cells.len() as u64,
                receipts,
            };
            viewnode_pane::pulse_panes(&self.viewnode_panes, &field_sets, &cell_events, census, cx);
            card_pulse::pulse_cards(&self.card_panes, &field_sets, &cell_events, cx);
        }
        #[cfg(not(feature = "card-pane"))]
        let _ = (&field_sets, &cell_events, receipts);
        for (kind, line) in arrivals {
            self.toast_rack.push(kind, line);
        }
        if let Some(line) = announce {
            self.say(line);
        }
        cx.notify();
    }
}

/// Spawn THE PULSE — the 250 ms background beat, self-stopping when the view drops
/// (the weak update fails). Called once from [`DeosDesktop::new`].
pub(super) fn spawn_pulse(cx: &mut Context<DeosDesktop>) {
    cx.spawn(async move |this, cx| loop {
        cx.background_executor()
            .timer(std::time::Duration::from_millis(250))
            .await;
        if this
            .update(cx, |desk: &mut DeosDesktop, cx| desk.pump_dynamics(cx))
            .is_err()
        {
            break;
        }
    })
    .detach();
}
