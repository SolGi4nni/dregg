//! **THE SHELF GATE** — the SECOND filter in front of a browse list.
//!
//! Two independent questions stand between "an offering is registered" and "a menu paints a live
//! control for it", and they must not be folded together:
//!
//! 1. **Do we advertise it?** — CURATION. `dreggnet_catalog::SHIPPED_KEYS` decides, and
//!    [`OfferingHost::set_advertised`] stamps the verdict onto the host as
//!    [`OfferingInfo::advertised`]. Off the ship list means "not on a shelf"; it is not a rule
//!    about safety and an unadvertised offering stays fully openable by key.
//! 2. **Can THIS SURFACE host it at all?** — CAPABILITY, which is what this module answers. It is
//!    a property of the (offering, surface) pair, not of the catalog: the same offering is a live
//!    control in a DM and must not be one in a group.
//!
//! Keeping them separate is the point. Folding rule 2 into the ship list would take a game off
//! *every* shelf — including the DMs where it plays perfectly — and would make a capability rule
//! look like a product decision. Folding rule 1 into rule 2 would make a curation edit read as a
//! privacy claim. So the ship list stays in `dreggnet-catalog` and the gate lives here, beside the
//! declaration it reads.
//!
//! ## Why a shelf can decide this BEFORE it paints
//! [`Offering::hidden_information`](crate::Offering::hidden_information) is answered **without a
//! session** — deliberately, and the trait doc says so. So a menu does not have to open anything
//! to know that pressing would be refused: the verdict is available at paint time, which is the
//! only time it is useful. A shelf that paints an enabled control and *then* refuses the press has
//! told the player nothing until they have already been told no.
//!
//! ## What this module does NOT do
//! It does not gate anything. The refusal at the open ([`crate::host::OfferingHost`] callers such
//! as `dreggnet_telegram::host::TelegramHost::open`) remains the enforcement, and it must: a
//! captured callback, a stale keyboard, or a typed `/open <key>` all reach the open without ever
//! consulting a shelf. This is the **advance warning**, so the menu stops lying; the gate is
//! elsewhere and stays there.

use crate::host::{OfferingHost, OfferingInfo};

/// **Who reads the surface a shelf is about to be painted onto.**
///
/// Not "which transport" — the same transport has both: a Telegram DM is [`Private`](Self::Private)
/// and a Telegram group / forum topic is [`Shared`](Self::Shared). What matters is the reader
/// count, because a per-viewer projection is safe on exactly one of them.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ShelfSurface {
    /// **One reader.** A DM, a WeChat 1:1 OA conversation, one browser tab holding one identity's
    /// session, a Discord ephemeral response. A per-viewer projection reaches exactly the person
    /// it is about, so nothing is withheld here.
    Private,
    /// **More than one reader.** A Telegram group or forum topic (whose session is ONE message
    /// every member reads, edited in place on each move), a projector, a stream.
    Shared,
}

impl ShelfSurface {
    /// Lift the `is_collective()`-shaped booleans the frontends already compute.
    pub const fn shared_if(shared: bool) -> Self {
        if shared { Self::Shared } else { Self::Private }
    }

    /// Whether this surface has more than one reader.
    pub const fn is_shared(self) -> bool {
        matches!(self, Self::Shared)
    }
}

/// **Why a shelf must not paint a LIVE control** for an offering on the surface it is painting.
///
/// An enum rather than a string because the *reason* is shared and the *route out of it* is not:
/// "DM me and send `/open tug`" is Telegram's sentence, "open it in a browser tab" is the web's.
/// [`why`](Self::why) authors the constraint once; each host appends its own route.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ShelfBlock {
    /// The offering DECLARES hidden information
    /// ([`Offering::hidden_information`](crate::Offering::hidden_information)) and the surface has
    /// more than one reader. Its per-viewer projection is the game — a hand, a sealed move — so
    /// serving it here would deal it to every reader, and serving the viewer-blind projection
    /// instead is not a playable surface. It needs a single-reader surface.
    PrivateSurfaceOnly,
}

impl ShelfBlock {
    /// **The constraint in the player's own words**, naming the game and stopping short of the
    /// route (which is the caller's, because only the caller knows how to get somewhere private
    /// on its transport).
    ///
    /// Written for someone who has never heard of a "projection": it says what the game needs and
    /// what this chat is, and leaves the machinery out.
    pub fn why(self, name: &str) -> String {
        match self {
            ShelfBlock::PrivateSurfaceOnly => format!(
                "{name} has to keep part of the game hidden from the other player, and the board \
                 here is ONE thing everybody in the room reads, so it only runs somewhere with a \
                 single reader."
            ),
        }
    }

    /// **A short tag for the dimmed control's own label**, where a sentence will not fit. Pairs
    /// with the full [`why`](Self::why) in the surrounding text.
    pub fn tag(self) -> &'static str {
        match self {
            ShelfBlock::PrivateSurfaceOnly => "private chat only",
        }
    }
}

/// One row of a shelf, **with the audience verdict already taken**.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShelfEntry {
    /// The offering's position in [`OfferingHost::list_offerings`] — the **FULL-list** index.
    ///
    /// ⚑ Deliberately the full-list position and not the position in this shelf: a frontend whose
    /// menu buttons carry a POSITION (Telegram's `callback_data`, WeChat's reply numbers) resolves
    /// a press against the full list, so an index minted from a filtered list would open the wrong
    /// offering the moment the shelf changed shape — and this gate changes the shelf's shape *per
    /// chat*, which is exactly the renumbering hazard the full-list index exists to avoid.
    pub catalog_index: usize,
    /// The offering's registry entry (key, title, advertised, live sessions).
    pub info: OfferingInfo,
    /// `None` — paint a live control. `Some(block)` — paint it INERT, with
    /// [`ShelfBlock::why`] beside it.
    pub block: Option<ShelfBlock>,
}

impl ShelfEntry {
    /// Whether this row may be painted as a live control on the surface it was gated for.
    pub fn live(&self) -> bool {
        self.block.is_none()
    }

    /// The offering's **short display name** — [`headline`] of its title.
    pub fn name(&self) -> &str {
        headline(&self.info.title)
    }
}

/// **The short display name inside a catalog title.** Every registered title in this workspace is
/// `"<name> · <tagline>"` (`"Automatafl · two players move at the same time, in secret, …"`), so a
/// sentence that needs to *name* the game takes the part before the separator; a title without one
/// is already short and is returned whole.
///
/// ⚑ BOTH separators are accepted. The registry was written with an em dash and moved to the
/// interpunct in the 2026-07-26 punctuation pass; a title that still carries the old glyph — one
/// typed at a call site, or registered by a crate that has not been swept — must keep parsing, or
/// its short name silently becomes the whole tagline on every shelf.
pub fn headline(title: &str) -> &str {
    title
        .split_once(" · ")
        .or_else(|| title.split_once(" — "))
        .map_or(title, |(name, _)| name)
        .trim()
}

/// **The gate for ONE key.** `None` = safe to paint live here.
///
/// Reads the declaration through the erasure boundary
/// ([`OfferingHost::hidden_information`]) — never a render differential, which answers "safe"
/// right up until the first hand is dealt. An unregistered key is not blocked: it is not on any
/// shelf either, and inventing a block for it would hide a routing bug behind a privacy notice.
pub fn shelf_block(host: &OfferingHost, key: &str, surface: ShelfSurface) -> Option<ShelfBlock> {
    (surface.is_shared() && host.hidden_information(key).unwrap_or(false))
        .then_some(ShelfBlock::PrivateSurfaceOnly)
}

/// **The advertised shelf, with the audience gate applied** — what a browse list on `surface`
/// should paint, each row already carrying its verdict and its stable full-list index.
///
/// The two filters compose in one place and stay legible: the ROWS are the ship list
/// (`OfferingInfo::advertised`), and the LIVENESS is this gate. Nothing is dropped for being
/// blocked — a filtered game is invisible and reads as one that does not exist, while a dimmed one
/// teaches the constraint and can point at the fix.
pub fn advertised_shelf(host: &OfferingHost, surface: ShelfSurface) -> Vec<ShelfEntry> {
    host.list_offerings()
        .into_iter()
        .enumerate()
        .filter(|(_, info)| info.advertised)
        .map(|(catalog_index, info)| {
            let block = shelf_block(host, &info.key, surface);
            ShelfEntry {
                catalog_index,
                info,
                block,
            }
        })
        .collect()
}

/// The shelf rows that must NOT be painted live, in shelf order.
pub fn blocked(rows: &[ShelfEntry]) -> Vec<&ShelfEntry> {
    rows.iter().filter(|e| !e.live()).collect()
}

/// The shelf rows that MAY be painted live, in shelf order.
pub fn playable(rows: &[ShelfEntry]) -> Vec<&ShelfEntry> {
    rows.iter().filter(|e| e.live()).collect()
}

/// **`"a"` / `"a and b"` / `"a, b and c"`** — the shelf's own list-of-names comma rule, so every
/// host's advance warning reads as a sentence instead of a debug print.
pub fn name_list(names: &[&str]) -> String {
    match names {
        [] => String::new(),
        [one] => (*one).to_string(),
        [head @ .., last] => format!("{} and {last}", head.join(", ")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        Action, DreggIdentity, Offering, OfferingError, Outcome, RunCost, SessionConfig, Surface,
        VerifyReport,
    };
    use deos_view::ViewNode;

    /// A minimal offering whose hidden-information declaration is a construction parameter, so the
    /// gate is exercised in BOTH directions without depending on which shipped game is which.
    struct Declares(bool);

    impl Offering for Declares {
        type Session = ();

        fn open(&self, _cfg: SessionConfig) -> Result<Self::Session, OfferingError> {
            Ok(())
        }

        fn actions(&self, _session: &Self::Session) -> Vec<Action> {
            vec![Action::new("move", "move", 0, true)]
        }

        fn advance(
            &self,
            _session: &mut Self::Session,
            _input: Action,
            _actor: DreggIdentity,
        ) -> Outcome {
            Outcome::Refused("not used".to_string())
        }

        fn verify(&self, _session: &Self::Session) -> VerifyReport {
            VerifyReport::ok(0)
        }

        fn render(&self, _session: &Self::Session) -> Surface {
            Surface(ViewNode::Text("board".to_string()))
        }

        fn hidden_information(&self) -> bool {
            self.0
        }

        fn price(&self, _input: &Action) -> RunCost {
            RunCost::free()
        }
    }

    fn host() -> OfferingHost {
        let mut host = OfferingHost::new();
        host.register(
            "public",
            "Open Board — everything is on the table",
            Declares(false),
        );
        host.register(
            "secret",
            "Sealed Hand — your cards are yours",
            Declares(true),
        );
        host.register("unlisted", "Unlisted — not on the shelf", Declares(true));
        host.set_advertised("unlisted", false);
        host
    }

    /// **A shared surface blocks exactly the declared offerings, and a private one blocks none.**
    /// Read off the declaration, so it cannot go stale when a game changes its mind.
    #[test]
    fn the_gate_follows_the_declaration_and_the_surface() {
        let host = host();
        for (key, declared) in [("public", false), ("secret", true)] {
            assert_eq!(
                host.hidden_information(key),
                Some(declared),
                "the fixture's own declaration"
            );
            assert_eq!(
                shelf_block(&host, key, ShelfSurface::Private),
                None,
                "a single-reader surface can host `{key}`"
            );
            assert_eq!(
                shelf_block(&host, key, ShelfSurface::Shared).is_some(),
                declared,
                "a shared surface blocks `{key}` exactly when it declares hidden information"
            );
        }
    }

    /// The shelf keeps the FULL-list index, not its own row number — the property a
    /// position-carrying frontend depends on, and the one a per-chat filter would have broken.
    #[test]
    fn the_shelf_carries_the_full_list_index_and_never_drops_a_blocked_row() {
        let host = host();
        let full = host.list_offerings();
        for surface in [ShelfSurface::Private, ShelfSurface::Shared] {
            let shelf = advertised_shelf(&host, surface);
            assert_eq!(
                shelf.len(),
                2,
                "the shelf is the SHIP LIST in both audiences — a blocked row is dimmed, not dropped"
            );
            for entry in &shelf {
                assert_eq!(
                    full[entry.catalog_index].key, entry.info.key,
                    "the carried index addresses the same offering in the FULL list"
                );
            }
        }
        let shared = advertised_shelf(&host, ShelfSurface::Shared);
        assert_eq!(
            blocked(&shared)
                .iter()
                .map(|e| e.info.key.as_str())
                .collect::<Vec<_>>(),
            ["secret"],
        );
        assert_eq!(
            playable(&shared)
                .iter()
                .map(|e| e.info.key.as_str())
                .collect::<Vec<_>>(),
            ["public"],
        );
        assert!(
            blocked(&advertised_shelf(&host, ShelfSurface::Private)).is_empty(),
            "a DM shelf offers everything on the ship list"
        );
    }

    /// The copy helpers: a name is the headline, and a list of names reads as English.
    #[test]
    fn the_copy_helpers_produce_prose() {
        // ⚑ THE LIVE SHAPE. Every registered title carries the interpunct since the 2026-07-26
        // punctuation pass, so this case — not the em-dash one below it — is the one the shipped
        // registry exercises.
        assert_eq!(
            headline("Automatafl · two players move at once"),
            "Automatafl"
        );
        // The old glyph still parses: a title typed at a call site, or registered by an unswept
        // crate, must not silently return its whole tagline as the game's short name.
        assert_eq!(
            headline("Automatafl — two players move at once"),
            "Automatafl"
        );
        assert_eq!(headline("Bare Title"), "Bare Title");
        assert_eq!(name_list(&[]), "");
        assert_eq!(name_list(&["a"]), "a");
        assert_eq!(name_list(&["a", "b"]), "a and b");
        assert_eq!(name_list(&["a", "b", "c"]), "a, b and c");
        let why = ShelfBlock::PrivateSurfaceOnly.why("Sealed Hand");
        assert!(
            why.starts_with("Sealed Hand"),
            "the reason names the game: {why}"
        );
        assert!(!why.contains("projection"), "no machinery words: {why}");
    }
}
