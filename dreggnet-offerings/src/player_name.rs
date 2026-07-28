//! # `player_name` — the name a ROSTER shows, beside the identity a turn is attributed to.
//!
//! ## The hole
//!
//! A [`DreggIdentity`] is an opaque handle — for the web's unsigned players, `blake3(label)` in hex;
//! for a phrase-backed one, the Ed25519 public key in hex. That is the right thing to route, gate
//! and attribute a turn with, and it is exactly the wrong thing to print in a column headed
//! **Holder**. The shared party lobby printed it anyway (`short_identity(seat.identity())`), so a
//! player who invited a friend read `71b278f3dc43444…` where the friend's name belongs — a machine
//! id in the one place on the page that is about people, and precisely the raw-hex-run shape
//! [`crate::refusal::audit_player_text`] forbids in every refusal.
//!
//! ## What this is, stated exactly
//!
//! A **presentation lookup**: the display name a FRONTEND attributed to an identity, remembered so a
//! surface can render it. It is not authority and it is not evidence.
//!
//! * **It is asserted, and that is already the model.** `Attribution::Asserted { label }` documents
//!   its label as *"every legacy attribution (`"web:alice"`, a blake3 handle, …)"* — a human-readable
//!   asserted label is not a new trust claim, it is the same one the page already prints under the
//!   board: *"This page takes your player name at face value and checks no signature."* Two players
//!   asserting one label see one name, exactly as they already see one identity.
//! * **It never touches a record.** The lobby journal, its hash chain and its replay verification
//!   are untouched — a name is resolved at RENDER, from this table, and a process that has never
//!   seen the name renders [`readable_handle`] instead. So the same journal replays to the same
//!   state everywhere; only the label on the screen differs, which is the honest consequence of the
//!   name being a frontend's assertion rather than part of the record.
//! * **The fallback is never a hex run.** `player 71b278` — short, sayable, and visibly a stand-in
//!   rather than a person's name. That is the property the roster needed and did not have.
//!
//! ## Bounded on purpose
//!
//! A raw `?user=` is attacker-choosable, so this table is capped at [`MAX_REMEMBERED_NAMES`] with
//! oldest-first eviction: a `?user=1,2,…,N` flood costs a bounded table, and an evicted name simply
//! falls back to the handle. Names are filtered at the door — a name is accepted only if it is one
//! short printable line ([`MAX_NAME_CHARS`], no control characters), because the Holder column is
//! person-shaped and a four-kilobyte label is not a person. Rendering escapes it regardless (the
//! deos web backend escapes every text node), so this filter is about the column staying readable,
//! not about the markup staying safe.

use std::collections::{HashMap, VecDeque};
use std::sync::{Mutex, OnceLock};

use crate::DreggIdentity;

/// The most identities whose display name is remembered at once. An eviction costs a name, never a
/// turn: the roster falls back to [`readable_handle`].
pub const MAX_REMEMBERED_NAMES: usize = 4096;

/// The longest display name a roster will show. Longer, and the surface shows the handle instead —
/// a Holder column is one short line.
pub const MAX_NAME_CHARS: usize = 32;

/// How many characters of the identity the fallback handle carries.
const HANDLE_CHARS: usize = 6;

type NameTable = (HashMap<String, String>, VecDeque<String>);

fn table() -> &'static Mutex<NameTable> {
    static NAMES: OnceLock<Mutex<NameTable>> = OnceLock::new();
    NAMES.get_or_init(|| Mutex::new((HashMap::new(), VecDeque::new())))
}

/// Is `name` one short printable line a roster can show as a person?
///
/// Rejects the empty/whitespace-only name, anything over [`MAX_NAME_CHARS`], and any control
/// character (a newline would break the column; the rest are not names). Deliberately permissive
/// about everything else: a player's chosen name is theirs, and the renderer escapes it.
pub fn is_showable_name(name: &str) -> bool {
    let trimmed = name.trim();
    !trimmed.is_empty()
        && trimmed.chars().count() <= MAX_NAME_CHARS
        && !trimmed.chars().any(char::is_control)
}

/// **Remember the display name a frontend attributes to `identity`.** Call it wherever the frontend
/// resolves a viewer — that is the one place both halves are in scope. A name that is not
/// [`is_showable_name`] is dropped (the roster then shows [`readable_handle`]), and the table is
/// capped at [`MAX_REMEMBERED_NAMES`] with oldest-first eviction.
///
/// A name that is itself an IDENTIFIER is dropped: the identity echoed back, or any all-hex token
/// (a visitor cookie, a truncated key). Remembering one would re-create, one layer up, the hex
/// column this module exists to remove — the roster shows [`readable_handle`] for those instead.
pub fn remember_player_name(identity: &DreggIdentity, name: &str) {
    let name = name.trim();
    if !is_showable_name(name) || name == identity.0 || name.chars().all(|c| c.is_ascii_hexdigit())
    {
        return;
    }
    let mut guard = table().lock().unwrap_or_else(|p| p.into_inner());
    let (map, order) = &mut *guard;
    if map.insert(identity.0.clone(), name.to_string()).is_none() {
        order.push_back(identity.0.clone());
        while order.len() > MAX_REMEMBERED_NAMES {
            if let Some(evicted) = order.pop_front() {
                map.remove(&evicted);
            }
        }
    }
}

/// The remembered display name for `identity`, if a frontend has attributed one in this process.
pub fn player_name(identity: &DreggIdentity) -> Option<String> {
    table()
        .lock()
        .unwrap_or_else(|p| p.into_inner())
        .0
        .get(&identity.0)
        .cloned()
}

/// **The name a roster shows** — the frontend-attributed one, else [`readable_handle`]. This is the
/// call a surface makes; it always returns something a person can read out loud.
pub fn display_name(identity: &DreggIdentity) -> String {
    player_name(identity).unwrap_or_else(|| readable_handle(&identity.0))
}

/// The same, for a surface holding the identity as a `&str` (the shape a lobby seat stores).
pub fn display_name_of(identity: &str) -> String {
    display_name(&DreggIdentity(identity.to_string()))
}

/// **The stand-in for an unnamed identity** — `player 71b278`. Short, sayable, stable, and
/// unmistakably a label rather than a person's name; the six-character tag is far under any
/// raw-hex-run threshold and reads as an identifier, which is what it is.
///
/// A short identity (an already-human label) is returned as itself: there is nothing to stand in
/// for.
pub fn readable_handle(identity: &str) -> String {
    let trimmed = identity.trim();
    if trimmed.is_empty() {
        return "player".to_string();
    }
    if trimmed.chars().count() <= MAX_NAME_CHARS && !trimmed.chars().all(|c| c.is_ascii_hexdigit())
    {
        return trimmed.to_string();
    }
    format!(
        "player {}",
        trimmed.chars().take(HANDLE_CHARS).collect::<String>()
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn an_unnamed_identity_renders_a_readable_handle_and_never_a_hex_run() {
        let hex = "71b278f3dc43444a".repeat(4);
        let shown = display_name(&DreggIdentity(hex.clone()));
        assert_eq!(shown, "player 71b278");
        // The property that matters: no run of hex long enough to read as a key.
        let longest = shown
            .split(|c: char| !c.is_ascii_hexdigit())
            .map(|run| run.chars().count())
            .max()
            .unwrap_or(0);
        assert!(
            longest < 12,
            "the stand-in must not be a hex run a player has to read: {shown}"
        );
    }

    #[test]
    fn a_remembered_name_is_shown_and_an_unshowable_one_is_not() {
        let id = DreggIdentity("aa".repeat(32));
        remember_player_name(&id, "alice");
        assert_eq!(display_name(&id), "alice");

        let noisy = DreggIdentity("bb".repeat(32));
        remember_player_name(&noisy, "line one\nline two");
        remember_player_name(&noisy, "   ");
        remember_player_name(&noisy, &"x".repeat(MAX_NAME_CHARS + 1));
        assert_eq!(
            display_name(&noisy),
            "player bbbbbb",
            "a name that is not one short printable line must not reach the roster"
        );
    }

    #[test]
    fn remembering_an_identifier_as_a_name_is_refused() {
        let id = DreggIdentity("cc".repeat(32));
        remember_player_name(&id, &id.0);
        assert_eq!(
            display_name(&id),
            "player cccccc",
            "echoing the identity back as its display name would re-create the hex column"
        );

        // A short all-hex label (`?user=deadbeefcafe`, a truncated key) is an identifier too.
        let hexish = DreggIdentity("dd".repeat(32));
        remember_player_name(&hexish, "deadbeefcafe");
        assert_eq!(display_name(&hexish), "player dddddd");
    }

    #[test]
    fn a_short_human_label_needs_no_stand_in() {
        assert_eq!(readable_handle("alice"), "alice");
        // …but an all-hex short label is still an identifier, not a name.
        assert_eq!(readable_handle("deadbeefcafe"), "player deadbe");
    }
}
