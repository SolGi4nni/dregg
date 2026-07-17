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
        let Some(seat) = session.claim(&actor) else {
            return Outcome::Refused("both seats are taken — you are a spectator".to_string());
        };
        self.inner
            .advance(&mut session.inner, input, TugOffering::seat_identity(seat))
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
            None => self.inner.render(&session.inner),
        }
    }

    fn price(&self, input: &Action) -> RunCost {
        self.inner.price(input)
    }
}
