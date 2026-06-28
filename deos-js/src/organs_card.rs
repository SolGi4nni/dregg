//! **THE ORGANS CARD** — the cockpit's ORGANS surface (live organ cell-state), reborn as a
//! deos-js card.
//!
//! Today the cockpit's organs surface is hardcoded Rust gpui (`Cockpit::organs_panel`): a
//! hand-built column of `section_title` headers and bordered rows. This module makes it a
//! **deos-js card** — a `view-tree` ([`crate::card_editor::ViewTree`]) generated from a
//! survey of the live World's organ cells, using the authoring vocabulary's
//! [`ViewTree::Section`] for the three organ groups the panel draws by hand:
//!
//!   - **TRUSTLINES (live)** — embed-core trustline organs (each a glyph + short id + a
//!     one-line collateral/draw summary),
//!   - **FLASH WELLS (live)** — embed-core flash-well organs, and
//!   - **REMOTE-PATH** — organs surfaced honestly as behind-captp (kind · seam · route),
//!     never faked state.
//!
//! The organs surface is **read-only** (a reflection of organ state), so the card carries
//! no affordance buttons; it is a pure projection. As gpui-free DATA it renders identically
//! through `deos-view`'s native + web backends and is reshapeable from within.
//!
//! The starbridge-v2 side (`dock::card_surface::ModeCard::Organs`) builds the
//! [`OrganCardRow`] lists from `starbridge_v2::organs::OrganSurvey` and calls
//! [`organs_view`]; this crate stays gpui-free + `cargo test`-able.

use crate::card_editor::{SectionProps, TextProps, ViewTree};

/// One organ as the card reads it — a glyph, a short id, and a one-line summary. The
/// renderer-agnostic shape the cockpit lifts from the organ reflections.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OrganCardRow {
    /// A leading glyph (`⬡` for an embed-core organ; the remote rows use their kind).
    pub glyph: String,
    /// A short operator-legible id (or the remote organ's kind/seam).
    pub short: String,
    /// The one-line state summary (collateral/draw for a trustline; principal/fee for a
    /// flash well; seam · route for a remote organ).
    pub summary: String,
}

/// **Generate the organs view-tree** from the live survey: a title, then one section per
/// organ group (trustlines · flash wells · remote-path), each listing its organs or an
/// honest "(none)" placeholder. The pure function the cockpit's `ModeCard::Organs` calls.
pub fn organs_view(
    live_count: usize,
    remote_count: usize,
    trustlines: &[OrganCardRow],
    flash_wells: &[OrganCardRow],
    remote: &[OrganCardRow],
) -> ViewTree {
    let top: Vec<ViewTree> = vec![
        text(&format!(
            "Organs · {live_count} live (embed-core) · {remote_count} remote-path"
        )),
        organ_section(
            "TRUSTLINES (live)",
            "good",
            trustlines,
            "(no trustline organ)",
        ),
        organ_section(
            "FLASH WELLS (live)",
            "good",
            flash_wells,
            "(no flash-well organ)",
        ),
        organ_section("REMOTE-PATH", "muted", remote, "(no remote-path organ)"),
    ];
    ViewTree::VStack { children: top }
}

/// One organ group as a [`ViewTree::Section`]: a header (the group title), then a row per
/// organ (a `glyph short` line + its summary), or the empty placeholder.
fn organ_section(title: &str, tag: &str, rows: &[OrganCardRow], empty: &str) -> ViewTree {
    let mut children: Vec<ViewTree> = Vec::new();
    if rows.is_empty() {
        children.push(text(empty));
    } else {
        for r in rows {
            children.push(ViewTree::VStack {
                children: vec![text(&format!("{} {}", r.glyph, r.short)), text(&r.summary)],
            });
        }
    }
    ViewTree::Section {
        props: SectionProps {
            title: title.to_string(),
            tag: tag.to_string(),
        },
        children,
    }
}

fn text(s: &str) -> ViewTree {
    ViewTree::Text {
        props: TextProps {
            text: s.to_string(),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn organ(short: &str) -> OrganCardRow {
        OrganCardRow {
            glyph: "⬡".into(),
            short: short.into(),
            summary: format!("{short} · line 100 · drawn 40"),
        }
    }

    #[test]
    fn the_three_groups_become_sections() {
        let tree = organs_view(1, 1, &[organ("ab12")], &[], &[organ(" rmt")]);
        // Three sections, titled by group.
        for title in ["TRUSTLINES (live)", "FLASH WELLS (live)", "REMOTE-PATH"] {
            assert!(
                tree.walk()
                    .iter()
                    .any(|n| matches!(n, ViewTree::Section { props, .. } if props.title == title)),
                "the {title} section is present"
            );
        }
        // The live trustline shows up; the empty flash-well group shows the placeholder.
        assert!(tree.walk().iter().any(|n| n.label() == Some("⬡ ab12")));
        assert!(tree
            .walk()
            .iter()
            .any(|n| n.label() == Some("(no flash-well organ)")));
    }

    #[test]
    fn the_header_counts_live_and_remote() {
        let tree = organs_view(2, 3, &[organ("a")], &[organ("b")], &[]);
        assert!(tree
            .walk()
            .iter()
            .any(|n| n.label() == Some("Organs · 2 live (embed-core) · 3 remote-path")));
    }
}
