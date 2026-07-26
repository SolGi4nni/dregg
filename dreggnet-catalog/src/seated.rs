//! # `seated::SeatedTug` — THE one seat-claiming multiway-tug adapter (skeleton).
//!
//! [`dregg_multiway_tug::TugOffering`] names its two seats by fixed canonical strings
//! (`"multiway-tug:seat-A"` / `"…seat-B"`), while every frontend's user is a *derived*
//! [`DreggIdentity`] key — so an unadapted tug refuses every real user's move as
//! "actor holds no seat". Four byte-peer copies of the fix exist today:
//!
//! - `dreggnet-web/src/seated.rs` (the port source — read in full, 126 lines),
//! - `dreggnet-telegram/src/seated.rs`,
//! - `dreggnet-wechat/src/seated.rs`,
//! - `discord-bot/src/commands/portfolio.rs` (`SeatedTug`, ~line 60).
//!
//! The adapter is frontend-agnostic (it speaks only `DreggIdentity`/`Action`/`Outcome`), so its
//! ONE home is here, beside the catalog that registers it under the `"tug"` key. Phase B turns
//! each frontend copy into `pub use dreggnet_catalog::seated::SeatedTug;`.
//!
//! The bodies are the verbatim port of `dreggnet-web/src/seated.rs` (claim-first-free-seat in
//! `advance`, seat-mapped `render_for` fog, straight delegation for the rest) — the adapter
//! changes NOTHING in `dregg-multiway-tug`.

use dregg_multiway_tug::{Player, TugOffering, TugSession};
use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingError, Outcome, RunCost, SessionConfig, Surface,
    VerifyReport,
};

/// The multiway-tug offering with **claimable seats** for any frontend's derived identities.
/// First two distinct identities to act get seat A then seat B; a third is a spectator
/// (refused, nothing commits). Changes NOTHING in `dregg-multiway-tug`.
pub struct SeatedTug {
    inner: TugOffering,
}

impl SeatedTug {
    /// A fresh seated tug offering.
    pub fn new() -> Self {
        SeatedTug { inner: TugOffering }
    }
}

impl Default for SeatedTug {
    fn default() -> Self {
        SeatedTug::new()
    }
}

/// A live tug round plus its seat claims (which identity holds seat A / seat B).
pub struct SeatedTugSession {
    inner: TugSession,
    seats: [Option<DreggIdentity>; 2],
}

impl SeatedTugSession {
    /// The seat `who` holds, if they have claimed one.
    pub fn seat_of(&self, who: &DreggIdentity) -> Option<Player> {
        for p in [Player::A, Player::B] {
            if self.seats[p.idx()].as_ref() == Some(who) {
                return Some(p);
            }
        }
        None
    }

    /// The seat `who` holds, CLAIMING the first free one (A, then B) if they hold none. `None` when
    /// both seats are held by other identities (a spectator).
    fn claim(&mut self, who: &DreggIdentity) -> Option<Player> {
        if let Some(p) = self.seat_of(who) {
            return Some(p);
        }
        for p in [Player::A, Player::B] {
            if self.seats[p.idx()].is_none() {
                self.seats[p.idx()] = Some(who.clone());
                return Some(p);
            }
        }
        None
    }

    /// The seat a not-yet-seated viewer would claim on their first accepted
    /// move. This is read-only: rendering never reserves a seat.
    fn claimable_seat(&self) -> Option<Player> {
        [Player::A, Player::B]
            .into_iter()
            .find(|seat| self.seats[seat.idx()].is_none())
    }

    /// The live tug round (read-only).
    pub fn inner(&self) -> &TugSession {
        &self.inner
    }
}

impl Offering for SeatedTug {
    type Session = SeatedTugSession;

    fn open(&self, cfg: SessionConfig) -> Result<Self::Session, OfferingError> {
        Ok(SeatedTugSession {
            inner: self.inner.open(cfg)?,
            seats: [None, None],
        })
    }

    fn actions(&self, session: &Self::Session) -> Vec<Action> {
        self.inner.actions(&session.inner)
    }

    /// Claim a seat for `actor` (first-come: A, then B), then resolve the move on the REAL executor
    /// as that seat. A third identity is a spectator — refused, nothing commits.
    fn advance(&self, session: &mut Self::Session, input: Action, actor: DreggIdentity) -> Outcome {
        let existing = session.seat_of(&actor);
        let Some(seat) = existing.or_else(|| session.claimable_seat()) else {
            return Outcome::Refused("both seats are taken — you are a spectator".to_string());
        };
        let outcome =
            self.inner
                .advance(&mut session.inner, input, TugOffering::seat_identity(seat));
        // A refusal commits nothing, including no lobby ownership. This closes
        // the ghost-seat attack where an invalid first press permanently
        // occupied a seat despite producing no receipt.
        if existing.is_none() && outcome.landed() {
            let claimed = session.claim(&actor);
            debug_assert_eq!(claimed, Some(seat));
        }
        outcome
    }

    fn verify(&self, session: &Self::Session) -> VerifyReport {
        self.inner.verify(&session.inner)
    }

    fn render(&self, session: &Self::Session) -> Surface {
        self.inner.render(&session.inner)
    }

    /// The per-viewer surface: a claimed seat sees its OWN hidden hand
    /// (`render_for` as the seat identity); anyone else sees the public fog (`render`).
    fn render_for(&self, session: &Self::Session, viewer: &DreggIdentity) -> Surface {
        match session.seat_of(viewer) {
            Some(seat) => self
                .inner
                .render_for(&session.inner, &TugOffering::seat_identity(seat)),
            None => match session.claimable_seat() {
                Some(seat) => session.inner.surface_claim(seat),
                None => self.inner.render(&session.inner),
            },
        }
    }

    /// **The affordances THIS seat may fire right now** — the per-seat projection of
    /// [`Offering::actions`].
    ///
    /// The tug ALTERNATES, but `actions` paints one anonymous list, so before this override both
    /// seats were shown the same lit action menu and the seat whose turn it was not learned that
    /// only by pressing and being refused.
    ///
    /// It is also the only oracle a host outside this crate has for **which seat owes the next
    /// move**: the `Offering` boundary erases `TugSession`, so `dreggnet-web`'s table clock cannot
    /// call [`dregg_multiway_tug::TugSession::to_move`] directly. It asks THIS once per seat
    /// instead, and forfeits the seat still being offered something after the deadline.
    ///
    /// Every turn NAME is still emitted, disabled rather than dropped, so a frontend validating a
    /// POST against this list still reaches the executor and gets ITS refusal ("not your turn").
    /// The executor remains the sole referee; `enabled` is decoration.
    fn actions_for(&self, session: &Self::Session, viewer: &DreggIdentity) -> Vec<Action> {
        // ⚑ ROUTE THROUGH THE WRAPPED GAME'S OWN PER-VIEWER PROJECTION. This used to be
        // `inner.actions(...)` — the seat TO MOVE, whose row labels name the exact favors that press
        // would put up, off that seat's committed hand — and it only dimmed `enabled`. So the
        // OPPONENT's page (and any spectator's) printed the live cut in the button text: the same
        // hole `TugSession::surface_claim` closed, at the affordance door. A viewer who does not HOLD
        // the seat is handed the cut-free rows even when the seat they would claim is the one to
        // move, because on a seat-locked table the other player is free to open the watch link.
        let held = session.seat_of(viewer);
        let mut all = match held {
            Some(seat) => self
                .inner
                .actions_for(&session.inner, &TugOffering::seat_identity(seat)),
            None => self.inner.actions_for(&session.inner, viewer),
        };
        if all.is_empty() {
            return all;
        }
        // The seat this viewer holds, or the one they would claim by acting — the same rule
        // `advance` applies, so a first-time visitor is offered what their first press would use.
        let seat = held.or_else(|| session.claimable_seat());
        let owes = match seat {
            // Every turn of the round is spent (8 actions + 4 responses) and it is waiting to be
            // revealed and scored. Either seat may fire that, so both owe it.
            //
            // Was `scheduled_action().is_none()`, which asked "is there a NEXT SCHEDULED action"
            // — a question that only had an answer while the engine ran a fixed per-seat order.
            // The seat now CHOOSES its action, so the honest form of the same question is
            // "are there any decisions left to make".
            Some(_) if session.inner.legal_decisions().is_empty() => !session.inner.ended(),
            Some(seat) => seat == session.inner.to_move(),
            // Both seats are held by other identities: a spectator.
            None => false,
        };
        // `enabled` is set in BOTH directions, because the cut-free rows a not-yet-seated viewer now
        // receives arrive inert (a seatless actor is refused outright by the bare `TugOffering`),
        // and a prospective CLAIMANT here does own the next press. `arg >= 0` is the wrapped game's
        // own "this row is a real decision" marker, so this reproduces its verdict rather than
        // inventing one. The executor remains the sole referee; `enabled` is decoration.
        for action in &mut all {
            action.enabled = owes && action.arg >= 0;
        }
        all
    }

    /// The seat adapter hides exactly what the wrapped game hides — the seat lookup only decides
    /// WHOSE projection to serve, never whether one carries secrets.
    fn hidden_information(&self) -> bool {
        self.inner.hidden_information()
    }

    fn price(&self, input: &Action) -> RunCost {
        self.inner.price(input)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn actor(name: &str) -> DreggIdentity {
        DreggIdentity(format!("player:{name}"))
    }

    #[test]
    fn refused_first_press_does_not_ghost_claim_a_seat() {
        let offering = SeatedTug::new();
        let mut session = offering.open(SessionConfig::with_seed(0x51)).expect("open");
        let alice = actor("alice");
        let bob = actor("bob");

        // A press whose METHOD and INDEX disagree is refused, and claims nothing. (`arg` now
        // indexes the seat's `legal_decisions()`; index 0 is a Secret, so naming it "gift" is a
        // spliced press. This used to be an out-of-SCHEDULE press — there is no schedule now,
        // so the mismatch a transport could actually produce is the one worth testing.)
        let refused = offering.advance(
            &mut session,
            Action::new("wrong", "gift", 0, true),
            alice.clone(),
        );
        assert!(matches!(refused, Outcome::Refused(_)));
        assert_eq!(session.seat_of(&alice), None, "a refusal owns no seat");

        // A press taken from the surface's OWN affordance list lands and claims the seat.
        // Derived rather than hardcoded: with the action order free, no fixed `(method, arg)`
        // pair is guaranteed to be the legal one.
        let offered = offering.actions_for(&session, &bob);
        let press = offered
            .into_iter()
            .find(|a| a.enabled)
            .expect("the claimable seat is offered a real decision");
        let landed = offering.advance(&mut session, press, bob.clone());
        assert!(landed.landed());
        assert_eq!(session.seat_of(&bob), Some(Player::A));
        assert_eq!(session.seat_of(&alice), None);
        assert!(offering.verify(&session).verified);
    }
}
