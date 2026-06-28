//! **THE HOME CARD** — the cockpit's HOME surface (the warm landing portal / boot view),
//! reborn as a deos-js card.
//!
//! Today the cockpit's home surface is hardcoded Rust gpui (`Cockpit::home_panel`): a
//! masthead with liveness pills + one bordered card per portal section. This module makes it
//! a **deos-js card** — a `view-tree` ([`crate::card_editor::ViewTree`]) generated from
//! `starbridge_v2::landing::LandingPortal` (built fresh from the live World, so its numbers
//! are the running image's actual numbers):
//!
//!   - a **masthead** — the big greeting headline + subtitle + a row of liveness
//!     [`ViewTree::Pill`]s (● live · h{height} · {n} cells · {n} receipts), and
//!   - one [`ViewTree::Section`] per portal section (where you are · the image · the
//!     verified heart · the receipt nervous system · the organs · how to begin), each a
//!     stack of the section's lines, and
//!   - a closing invitation line.
//!
//! Home is **read-only** (the alive front door), so the card carries no affordance buttons.
//! As gpui-free DATA it renders identically through `deos-view`'s native + web backends and
//! is reshapeable from within.
//!
//! The starbridge-v2 side (`dock::card_surface::ModeCard::Home`) lifts the portal into the
//! [`HomeSection`]/[`HomeLine`]/pill inputs and calls [`home_view`]; this crate stays
//! gpui-free + `cargo test`-able.

use crate::card_editor::{PillProps, SectionProps, TextProps, ViewTree};

/// One line of a portal section — its text + whether it is a heading (rendered a touch
/// larger). The renderer-agnostic mirror of `starbridge_v2::landing::PortalLine`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HomeLine {
    pub text: String,
    /// A heading-weight line (else body/muted prose). The card carries the distinction; the
    /// renderer styles it (a heading reuses the section's accent).
    pub heading: bool,
}

/// One portal section — a title + its lines. Becomes a [`ViewTree::Section`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HomeSection {
    pub title: String,
    pub lines: Vec<HomeLine>,
}

/// **Generate the home view-tree** from the live portal: the masthead (headline · subtitle ·
/// liveness pills), one section per portal section, then the closing invitation. The pure
/// function the cockpit's `ModeCard::Home` calls (the front door IS this data).
pub fn home_view(
    headline: &str,
    subtitle: &str,
    pills: &[(String, String)],
    sections: &[HomeSection],
    invitation: &str,
) -> ViewTree {
    let mut top: Vec<ViewTree> = Vec::new();

    // The masthead: the big greeting, the subtitle, and the liveness pill row.
    let pill_row = ViewTree::Row {
        children: pills.iter().map(|(t, tag)| pill(t, tag)).collect(),
    };
    top.push(section(headline, "accent", vec![text(subtitle), pill_row]));

    // One section per portal section — each a stack of its lines.
    for s in sections {
        let children: Vec<ViewTree> = s.lines.iter().map(|l| text(&l.text)).collect();
        top.push(section(&s.title, "", children));
    }

    // The closing call-to-action.
    top.push(text(invitation));

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

    #[test]
    fn the_masthead_carries_the_headline_and_liveness_pills() {
        let pills = vec![
            ("● live".into(), "good".into()),
            ("h7".into(), "accent".into()),
        ];
        let tree = home_view(
            "you have arrived",
            "a sovereign image is running",
            &pills,
            &[],
            "click anything to begin",
        );
        // The headline is the masthead section's title.
        assert!(tree.walk().iter().any(
            |n| matches!(n, ViewTree::Section { props, .. } if props.title == "you have arrived")
        ));
        // Two liveness pills present.
        assert_eq!(
            tree.walk()
                .iter()
                .filter(|n| matches!(n, ViewTree::Pill { .. }))
                .count(),
            2
        );
        // The invitation closes the card.
        assert!(tree
            .walk()
            .iter()
            .any(|n| n.label() == Some("click anything to begin")));
    }

    #[test]
    fn each_portal_section_becomes_a_section_with_its_lines() {
        let sections = vec![HomeSection {
            title: "WHERE YOU ARE".into(),
            lines: vec![
                HomeLine {
                    text: "a verified image".into(),
                    heading: true,
                },
                HomeLine {
                    text: "every turn leaves a receipt".into(),
                    heading: false,
                },
            ],
        }];
        let tree = home_view("hi", "sub", &[], &sections, "go");
        let sec = tree
            .walk()
            .into_iter()
            .find(
                |n| matches!(n, ViewTree::Section { props, .. } if props.title == "WHERE YOU ARE"),
            )
            .expect("the portal section is present");
        assert_eq!(sec.children().len(), 2, "both lines landed in the section");
        assert!(tree
            .walk()
            .iter()
            .any(|n| n.label() == Some("every turn leaves a receipt")));
    }
}
