//! # TRUST LABELLING — the requirement most likely to rot, pinned in one module.
//!
//! DREGG-QUIET-UPGRADE.md §5: *"A person must always be able to tell WHO CHECKED THIS. The
//! semantic web's failure was that an asserted claim looked identical to a true one."*
//!
//! This surface is tier **`server`** — §7's bottom rung, the one for a person with nothing
//! installed. [`TIER`] is a constant, not a computation: no amount of server-side gate
//! passing promotes it, because the tier names *who ran the gates*, and here that is never
//! the reader. Every function in this module is asserted on by `tests/mirror_router.rs`
//! precisely so the language cannot quietly drift into a green check mark.
//!
//! The three rules this module exists to hold:
//!
//! 1. **The badge carries §5's qualifier verbatim.** The string is
//!    `✓ verified by <origin> (trust the origin)`. The `✓` is never allowed to travel
//!    without `(trust the origin)` beside it, and the badge is styled in the tier's own
//!    amber — `tier-extension`'s green is reserved for the rung where the reader's own
//!    agent checked, and is never emitted by this crate on its own badge.
//! 2. **The page says who checked, in plain words.** [`WHO_CHECKED_HEADING`] /
//!    [`who_checked_body`] — not a footnote, not a tooltip.
//! 3. **The upgrade path is on the page.** The canonical `dregg://…` string to copy, and
//!    a pointer to the extension, so the reader can move to the tier where they check it
//!    themselves ([`UPGRADE_HEADING`]).

use crate::uri;

/// The tier this surface serves at. A CONSTANT — see the module doc.
pub const TIER: &str = "server";

/// §5's badge for `trust="server"`, with the serving origin substituted for the spec's
/// literal `dregg.net`. The `(trust the origin)` qualifier is not optional decoration —
/// it is the entire honest content of the line.
pub fn tier_badge(origin: &str) -> String {
    format!("✓ verified by {origin} (trust the origin)")
}

/// §5's badge for the absent / `[error]` tier — what a fail-closed page shows.
pub const TIER_NONE_BADGE: &str = "⚠ unverified · original link shown";

/// The CSS class for this surface's badge. Distinct from `tier-extension` by construction:
/// a test asserts the extension class never appears on the mirror's own badge.
pub const BADGE_CLASS: &str = "tier-badge tier-server";

/// Heading of the block that answers §5's question.
pub const WHO_CHECKED_HEADING: &str = "Who checked this?";

/// The plain-language body. States the residual honestly in both directions: what the
/// content address really does buy the reader (the origin cannot change the object or its
/// tally under this link), and what it does not (the origin can refuse, stall, serve a
/// stale-but-valid object, or lie about the checks below).
pub fn who_checked_body(origin: &str) -> String {
    format!(
        "This page is tier <code>{TIER}</code>, the weakest rung. \
         <strong>{origin} checked this object. You did not.</strong> \
         Everything here, including the report of the checks below, is this origin's word, \
         and you have no independent evidence for any of it.</p>\
         <p>What the content address does buy you: the object's bytes, including its tally, \
         are inside the address, so this origin cannot show you different content or a \
         different number under this same link without breaking the digest. \
         What it does not buy you: this origin can still refuse to serve, stall, serve a \
         stale-but-valid object, or misreport what it checked. \
         Nothing on this page is evidence you hold."
    )
}

/// Heading of the upgrade block.
pub const UPGRADE_HEADING: &str = "Check it yourself";

/// The upgrade instruction. Names the tier the reader moves to and what changes there.
pub const UPGRADE_BODY: &str = "Copy the canonical reference and open it with your own agent. \
     With the extension installed, the object resolves and verifies in <em>your</em> \
     context: content address, serve-receipt, stream root and federation quorum are all \
     re-checked by software you control, the render happens in a closed shadow root the \
     host page cannot read or rewrite, and the badge becomes \
     <span class=\"tier-badge tier-cipherclerk\">verified by your cipherclerk</span>. \
     That is the difference between this page and evidence.";

/// Why the object's affordances are inert on this surface. Stated, never merely implied by
/// a dead button: a control that looks live and does nothing is the same lie in a different
/// costume.
pub const INERT_NOTE: &str = "Read-only. Every control below is disabled on this surface. \
     Acting on a dregg object is a cap-gated turn that needs custody, and custody lives in \
     your agent, never on this server. This page also loads no in-tab executor, so nothing \
     here is pretending it could fire.";

/// One rung of §7's degradation ladder, for the table the page prints.
pub struct Rung {
    /// The `trust=` value / tier name.
    pub tier: &'static str,
    /// §7's "person has" column.
    pub person_has: &'static str,
    /// §7's "what they see" column.
    pub sees: &'static str,
    /// §5's badge language for that tier.
    pub badge: &'static str,
}

/// §7's degradation ladder verbatim, best rung first, so the reader can see exactly where
/// this page sits and what is above it.
pub const LADDER: &[Rung] = &[
    Rung {
        tier: "extension",
        person_has: "the extension",
        sees: "a live element, can act (custody), self-verified in a closed shadow root",
        badge: "✓ verified by your cipherclerk",
    },
    Rung {
        tier: "sdk",
        person_has: "a page that bundles @dregg/sdk",
        sees: "a live element, verified locally; acting needs a passkey or the extension",
        badge: "✓ verified in this page",
    },
    Rung {
        tier: "server",
        person_has: "nothing installed · YOU ARE HERE",
        sees: "this server-rendered view",
        badge: "✓ verified by the origin (trust the origin)",
    },
    Rung {
        tier: "—",
        person_has: "a broken or mangled link",
        sees: "plaintext; nothing pretends to be verified",
        badge: "⚠ unverified",
    },
];

/// The canonical reference a reader copies off the page: `dregg://<kind>/b3_<hex>` — always
/// the FULL address, never the short prefix the link may have arrived as.
pub fn canonical_for(kind: &str, addr_hex: &str) -> String {
    uri::canonical_uri(kind, addr_hex)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_check_never_travels_without_its_qualifier() {
        let b = tier_badge("dregg.gg");
        assert!(b.contains('✓'));
        assert!(
            b.contains("(trust the origin)"),
            "§5's qualifier is the entire honest content of the badge"
        );
    }

    #[test]
    fn the_tier_is_a_constant_not_a_computation() {
        assert_eq!(TIER, "server");
        assert!(!BADGE_CLASS.contains("tier-extension"));
    }

    #[test]
    fn the_ladder_marks_where_the_reader_is() {
        let here: Vec<_> = LADDER
            .iter()
            .filter(|r| r.person_has.contains("YOU ARE HERE"))
            .collect();
        assert_eq!(here.len(), 1);
        assert_eq!(here[0].tier, TIER);
    }
}
