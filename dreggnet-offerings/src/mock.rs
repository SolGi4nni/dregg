//! **A reference [`Frontend`] for tests** — a headless affordance-renderer that records what
//! it was asked to present and maps a synthetic interaction event back into a typed offering
//! [`Action`]. It is the frontend-agnostic proof: the SAME [`Surface`] / [`Action`]s the core
//! produces round-trip through a renderer with **no Discord / serenity** anywhere. A real
//! frontend (the discord-bot's `deos_surface.rs`, a Telegram bot, the web surface) is the same
//! shape with a live surface instead of an in-memory map.

use std::collections::HashMap;

use crate::{Action, DreggIdentity, Frontend, SessionId, Surface};

/// A synthetic platform interaction — a press of a presented affordance. Stands in for a
/// Discord `ComponentInteraction` / a Telegram `CallbackQuery` / a web POST. Carries the
/// session it targets, the platform user who fired it, and the affordance `{turn, arg}` pressed.
#[derive(Debug, Clone)]
pub struct MockEvent {
    /// The session the press targets.
    pub session: SessionId,
    /// The platform user id (mapped to a [`DreggIdentity`] via [`MockFrontend::identity`]).
    pub user: String,
    /// The pressed affordance's verb (matches [`Action::turn`]).
    pub turn: String,
    /// The pressed affordance's argument (matches [`Action::arg`]).
    pub arg: i64,
    /// The **free text the presser supplied** with this actuation, if any — the real-frontend
    /// analogue of a Discord modal field / a web form textarea / a Telegram reply the user typed.
    /// `None` is a plain button press (no text field); `Some(t)` is a text-bearing press whose
    /// string [`collect`](MockFrontend::collect) overlays onto the collected [`Action::text`]. A
    /// `None` press is byte-identical to the pre-text behaviour (the presented action is returned
    /// untouched).
    pub text: Option<String>,
}

impl MockEvent {
    /// A **text-free** press of `(turn, arg)` in `session` by `user` — a plain button press.
    pub fn press(
        session: &SessionId,
        user: impl Into<String>,
        turn: impl Into<String>,
        arg: i64,
    ) -> Self {
        MockEvent {
            session: session.clone(),
            user: user.into(),
            turn: turn.into(),
            arg,
            text: None,
        }
    }

    /// A **text-bearing** press: `(turn, arg)` plus the free `text` the user supplied (the modal
    /// field / form textarea). [`collect`](MockFrontend::collect) reproduces this string on the
    /// collected [`Action::text`], so a text-shaped move (a doc edit's prose, a Hermes prompt)
    /// round-trips present -> collect losslessly.
    pub fn press_text(
        session: &SessionId,
        user: impl Into<String>,
        turn: impl Into<String>,
        arg: i64,
        text: impl Into<String>,
    ) -> Self {
        MockEvent {
            session: session.clone(),
            user: user.into(),
            turn: turn.into(),
            arg,
            text: Some(text.into()),
        }
    }
}

/// What the mock frontend last presented for a session — the deos [`Surface`] and the
/// cap-gated [`Action`]s beside it (what a real frontend paints as buttons/menu-rows).
#[derive(Debug, Clone)]
pub struct Presented {
    /// The presented deos affordance surface (the view-tree a renderer would walk).
    pub surface: Surface,
    /// The affordances presented alongside it (the ballot options / buttons).
    pub actions: Vec<Action>,
}

/// A headless [`Frontend`] recording presented surfaces + actions per session. Platform user =
/// a `String` id; a platform event = a [`MockEvent`]. Identity is derived deterministically
/// (blake3 of the user id) so the SAME user → the SAME [`DreggIdentity`] — the frontend-agnostic
/// stand-in for a Discord `UserCipherclerk` derivation.
#[derive(Debug, Default)]
pub struct MockFrontend {
    presented: HashMap<SessionId, Presented>,
}

impl MockFrontend {
    /// A fresh mock frontend with no open sessions.
    pub fn new() -> Self {
        MockFrontend::default()
    }

    /// What was last presented for `session` (the surface + its actions), if any.
    pub fn presented(&self, session: &SessionId) -> Option<&Presented> {
        self.presented.get(session)
    }

    /// The affordances last presented for `session` (the buttons a real frontend would paint).
    pub fn presented_actions(&self, session: &SessionId) -> &[Action] {
        self.presented
            .get(session)
            .map(|p| p.actions.as_slice())
            .unwrap_or(&[])
    }

    /// Whether a surface slot is currently open for `session`.
    pub fn is_open(&self, session: &SessionId) -> bool {
        self.presented.contains_key(session)
    }
}

impl Frontend for MockFrontend {
    type PlatformUser = String;
    type PlatformEvent = MockEvent;

    /// Derive `user`'s [`DreggIdentity`] — blake3(user) hex. Deterministic: the SAME user id
    /// always maps to the SAME identity (the frontend-agnostic analogue of the Discord
    /// `UserCipherclerk::derive(...).public_key_hex()` the bot uses).
    fn identity(&self, user: String) -> DreggIdentity {
        DreggIdentity(blake3::hash(user.as_bytes()).to_hex().to_string())
    }

    /// Open an (empty) surface slot for `session`.
    fn spin_session(&mut self, session: SessionId) {
        self.presented.entry(session).or_insert(Presented {
            surface: Surface(deos_view::ViewNode::VStack(Vec::new())),
            actions: Vec::new(),
        });
    }

    /// Record the presented surface + actions (a real frontend would paint them).
    fn present(&mut self, session: &SessionId, surface: &Surface, actions: &[Action]) {
        self.presented.insert(
            session.clone(),
            Presented {
                surface: surface.clone(),
                actions: actions.to_vec(),
            },
        );
    }

    /// Map a [`MockEvent`] press back to the offering [`Action`] it names: find the presented
    /// affordance matching `(turn, arg)` and return it with the firing actor's identity. `None`
    /// if the session is unknown or the affordance was not presented (an event the frontend did
    /// not offer).
    fn collect(&self, ev: MockEvent) -> Option<(SessionId, Action, DreggIdentity)> {
        let presented = self.presented.get(&ev.session)?;
        let mut action = presented
            .actions
            .iter()
            .find(|a| a.turn == ev.turn && a.arg == ev.arg)
            .cloned()?;
        // A text-bearing press carries the user-supplied free text (the modal field / form
        // textarea); it overlays the presented affordance's default [`Action::text`]. A text-free
        // press (`ev.text == None`) leaves the presented action untouched — byte-identical to the
        // pre-text behaviour, so a plain fixed-arg affordance collects exactly as before.
        if let Some(t) = ev.text {
            action.text = Some(t);
        }
        Some((ev.session.clone(), action, self.identity(ev.user)))
    }

    /// Close `session`'s surface slot (archive on completion).
    fn teardown(&mut self, session: &SessionId) {
        self.presented.remove(session);
    }
}
