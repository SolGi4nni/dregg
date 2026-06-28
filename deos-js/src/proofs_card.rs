//! **THE PROOFS CARD** — the cockpit's PROOFS surface (the proof-attach + STARK
//! verification-status board), reborn as a deos-js card.
//!
//! Today the cockpit's proofs surface is hardcoded Rust gpui: its UI is *compiled code*
//! (`Cockpit::proofs_panel`). This module makes it a **deos-js card** — a `view-tree`
//! ([`crate::card_editor::ViewTree`], the same `{kind, props, children}` shape
//! [`deos-view`] renders) generated from a verification-status survey of the live World's
//! committed turns:
//!
//!   - a **summary row** of [`ViewTree::Pill`] badges (how many turns are
//!     verified-by-construction / executor-signed / STARK-attached), and
//!   - one [`ViewTree::Section`] per committed turn (most-recent-first), titled
//!     `h{height} · {receipt}`, tinted by the turn's verification tier, carrying its
//!     one-line proof summary + (when present) the honest "→ next" upgrade route.
//!
//! The proofs surface is **read-only** (it never mints a multi-second STARK inside a paint
//! — the honest stance the panel doc names), so the card carries no affordance buttons; it
//! is a pure projection of the live verification posture. The card is gpui-free DATA, so it
//! renders identically through `deos-view`'s native (gpui) and web (HTML) backends, and it
//! is reshapeable from within (the [`crate::card_editor::CardEditor`] patch route the mode
//! cards share).
//!
//! The starbridge-v2 side (`dock::card_surface::ModeCard::Proofs`) builds the
//! [`ProofCardRow`] list from `starbridge_v2::proofs::ProofBoard` and calls
//! [`proofs_view`]; this crate stays gpui-free + `cargo test`-able.

use crate::card_editor::{PillProps, SectionProps, TextProps, ViewTree};

/// One committed turn's verification posture, as the card reads it — the renderer-agnostic
/// shape the cockpit lifts from `starbridge_v2::proofs::ProofEntry`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofCardRow {
    /// The turn's local chain height.
    pub height: u64,
    /// The turn's receipt hash, short-form (the provenance-chain link).
    pub receipt_short: String,
    /// The verification tier's operator-legible label (`verified-by-construction`/…).
    pub tier_label: String,
    /// The styling accent for this tier (`good` STARK / `accent` signed / `muted` by-construction).
    pub tag: String,
    /// The one-line proof summary (tier · attach · pre→post).
    pub summary: String,
    /// The honest route to the next-stronger tier, or `None` at the top.
    pub route: Option<String>,
}

/// **Generate the proofs view-tree** from a verification survey: a title, a summary pill
/// row, then one section per committed turn. The pure function the cockpit's
/// `ModeCard::Proofs` calls (the surface IS this data).
pub fn proofs_view(
    by_construction: usize,
    signed: usize,
    stark_attached: usize,
    rows: &[ProofCardRow],
) -> ViewTree {
    let mut top: Vec<ViewTree> = Vec::new();
    top.push(text(&format!("Proofs · {} committed turn(s)", rows.len())));

    // The summary badge row — the three honest tiers as pills.
    top.push(ViewTree::Row {
        children: vec![
            pill(&format!("{by_construction} by-construction"), "muted"),
            pill(&format!("{signed} signed"), "accent"),
            pill(&format!("{stark_attached} STARK"), "good"),
        ],
    });

    if rows.is_empty() {
        top.push(text("(no committed turns yet)"));
        return ViewTree::VStack { children: top };
    }

    // One section per turn: a tier-tinted title, the proof summary, the upgrade route.
    for row in rows {
        let mut body: Vec<ViewTree> = vec![text(&row.summary), pill(&row.tier_label, &row.tag)];
        if let Some(route) = &row.route {
            body.push(text(&format!("→ next: {route}")));
        }
        top.push(section(
            &format!("h{} · {}", row.height, row.receipt_short),
            &row.tag,
            body,
        ));
    }

    ViewTree::VStack { children: top }
}

fn text(s: &str) -> ViewTree {
    ViewTree::Text {
        props: TextProps {
            text: s.to_string(),
        },
    }
}

fn pill(text: &str, tag: &str) -> ViewTree {
    ViewTree::Pill {
        props: PillProps {
            text: text.to_string(),
            tag: tag.to_string(),
        },
    }
}

fn section(title: &str, tag: &str, children: Vec<ViewTree>) -> ViewTree {
    ViewTree::Section {
        props: SectionProps {
            title: title.to_string(),
            tag: tag.to_string(),
        },
        children,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn row(h: u64, tier: &str, tag: &str, route: Option<&str>) -> ProofCardRow {
        ProofCardRow {
            height: h,
            receipt_short: format!("rh{h}"),
            tier_label: tier.into(),
            tag: tag.into(),
            summary: format!("h{h} · {tier} · attached"),
            route: route.map(|s| s.to_string()),
        }
    }

    #[test]
    fn empty_board_renders_a_calm_placeholder() {
        let tree = proofs_view(0, 0, 0, &[]);
        assert!(
            tree.walk()
                .iter()
                .any(|n| n.label() == Some("(no committed turns yet)")),
            "an empty proofs board shows the honest placeholder"
        );
        // Even empty it carries the three summary pills.
        assert_eq!(
            tree.walk()
                .iter()
                .filter(|n| matches!(n, ViewTree::Pill { .. }))
                .count(),
            3,
            "the summary pill row is always present"
        );
    }

    #[test]
    fn each_turn_becomes_a_tier_tinted_section_with_its_route() {
        let rows = [
            row(2, "STARK-attached", "good", None),
            row(
                1,
                "verified-by-construction",
                "muted",
                Some("attach a signature"),
            ),
        ];
        let tree = proofs_view(1, 0, 1, &rows);
        // One section per turn, titled by height + receipt.
        assert!(tree.walk().iter().any(|n| n.label() == Some("h2 · rh2")));
        assert!(tree.walk().iter().any(|n| n.label() == Some("h1 · rh1")));
        // The upgrade route surfaces honestly for the lower tier.
        assert!(
            tree.walk()
                .iter()
                .any(|n| n.label() == Some("→ next: attach a signature")),
            "the honest upgrade route is shown"
        );
        // The summary header counts the turns.
        assert!(tree
            .walk()
            .iter()
            .any(|n| n.label() == Some("Proofs · 2 committed turn(s)")));
    }
}
