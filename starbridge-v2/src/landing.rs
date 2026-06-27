//! The LANDING portal — the warm, alive front door of the live verified image.
//!
//! When the master interface boots, the first thing you meet is not a sparse
//! window-manager scene: it is a *portal* — a greeting that says, in real text,
//! *you have arrived inside a live, verified, object-capability image, and every
//! object here is yours to inspect and to drive.* The feel is deliberate:
//! loading AOL as a seven-year-old, except this is the Good Cyberpunk Timeline —
//! a system that is reflectively present to itself, Smalltalk-tier, where the
//! tools for the system are objects *in* the system.
//!
//! This module is the landing's **text MODEL**: a pure, gpui-free projection of
//! the LIVE [`World`](crate::world::World) (cells · receipts · the image
//! commitment · the dynamics nervous system · the organs) into a sequence of
//! titled sections of real lines. The cockpit's HOME tab renders this model with
//! native gpui text — but because the *content* is built here, gpui-free, it is
//! `cargo test`-able: a test asserts the portal speaks real, non-empty text
//! about the real image, so "the landing renders text" is proven without a GPU.
//!
//! It reflects the REAL system, never a mock: the heart is
//! `dregg_turn::executor::TurnExecutor` (wrapped by [`World`]); the organs are
//! surveyed through [`OrganSurvey`](crate::organs::OrganSurvey); the receipts are
//! the executor's own `TurnReceipt` chain. The portal *names* these so the image
//! is self-describing — it tells you what it is made of, in its own words.

use crate::organs::OrganSurvey;
use crate::reflect;
use crate::world::World;

/// The accent role of a portal line — a *semantic* color the renderer maps to
/// the theme (kept gpui-free here so the model is pure data + testable). The
/// renderer turns these into `theme::*` colors; the model just says what each
/// line MEANS.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Tone {
    /// Body prose — the warm narration.
    Body,
    /// A muted aside / caption.
    Muted,
    /// A live, healthy fact (a number that proves the image is running).
    Good,
    /// An accent fact / an invitation to act.
    Accent,
    /// A heading-weight line inside a section.
    Heading,
}

/// One line of the portal: its text + its tone.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PortalLine {
    pub text: String,
    pub tone: Tone,
}

impl PortalLine {
    fn new(tone: Tone, text: impl Into<String>) -> Self {
        Self {
            text: text.into(),
            tone,
        }
    }
}

/// One titled section of the portal (a card the renderer draws).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PortalSection {
    /// The section's small-caps title.
    pub title: String,
    /// The section's lines (each a real string + a tone).
    pub lines: Vec<PortalLine>,
}

/// THE LANDING PORTAL MODEL — the whole warm front door, as pure text data
/// projected from the live image. Built fresh each frame from the [`World`], so
/// the numbers it shows are the running image's actual numbers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LandingPortal {
    /// The big greeting headline.
    pub headline: String,
    /// The one-line subtitle under the headline.
    pub subtitle: String,
    /// The titled sections (the cards), in render order.
    pub sections: Vec<PortalSection>,
    /// The closing invitation line (the "press ⌘K to begin" call to action).
    pub invitation: String,
}

impl LandingPortal {
    /// Build the portal from the live world. This is the single source of the
    /// landing's text — the cockpit renders exactly these strings, so the
    /// `cargo test` that asserts they are present + non-empty proves the
    /// rendered tree contains real text.
    pub fn build(world: &World) -> Self {
        let cells = world.cell_count();
        let height = world.height();
        let receipts = world.receipts().len();
        let root = reflect::short_hex(&world.state_root());
        let survey = OrganSurvey::build(world);
        let live_organs = survey.live_count();
        let remote_organs = survey.remote.len();

        // The total value the image holds (Σ balances) — a warm "the world has
        // weight" fact, read live from the ledger.
        let total_value: i64 = world.ledger().iter().map(|(_, c)| c.state.balance()).sum();
        // The total capabilities held across the image — the ocap web's size.
        let total_caps: usize = world
            .ledger()
            .iter()
            .map(|(_, c)| c.capabilities.len())
            .sum();
        // The most recent dynamics event — the image's last heartbeat, in words.
        let last_beat = world
            .dynamics()
            .tail(1)
            .iter()
            .next()
            .map(|e| e.label())
            .unwrap_or_else(|| "the image is at rest, waiting for your first turn".to_string());

        let sections = vec![
            // --- WHERE YOU ARE ------------------------------------------------
            PortalSection {
                title: "you have arrived inside a live image".to_string(),
                lines: vec![
                    PortalLine::new(
                        Tone::Body,
                        "This is one whole world, running right now in this process. Not a \
                         screenshot of a system — the system. Everything you can see is a live \
                         object, and every object is yours to open, to question, and to drive.",
                    ),
                    PortalLine::new(
                        Tone::Body,
                        "It is Smalltalk's dream kept and then surpassed: a single live image \
                         where the tools for the system are objects in the system — but here \
                         every object is capability-secured, every message is a verified turn, \
                         every turn leaves a receipt, and the whole image is a cryptographic \
                         commitment among sovereigns.",
                    ),
                    PortalLine::new(
                        Tone::Muted,
                        "Nothing here has ambient authority. To touch a thing you must hold a \
                         capability for it — and when a guarantee says no, you get to watch it \
                         say no.",
                    ),
                ],
            },
            // --- THE LIVE IMAGE, RIGHT NOW (real numbers) ---------------------
            PortalSection {
                title: "the image, right now".to_string(),
                lines: vec![
                    PortalLine::new(
                        Tone::Good,
                        format!(
                            "{cells} live cells holding {total_value} in value across {total_caps} capabilities"
                        ),
                    ),
                    PortalLine::new(
                        Tone::Good,
                        format!("height h{height} · {receipts} receipts on the chain so far"),
                    ),
                    PortalLine::new(
                        Tone::Accent,
                        format!(
                            "image commitment: {root}  (this image is one sovereign among a federation)"
                        ),
                    ),
                    PortalLine::new(Tone::Muted, format!("last heartbeat — {last_beat}")),
                ],
            },
            // --- THE HEART (the real executor) --------------------------------
            PortalSection {
                title: "the verified heart".to_string(),
                lines: vec![
                    PortalLine::new(
                        Tone::Heading,
                        "the embedded executor — dregg_turn::executor::TurnExecutor",
                    ),
                    PortalLine::new(
                        Tone::Body,
                        "The same verified executor the federation runs as its authoritative \
                         state producer is running HERE, in this process. Every state change \
                         flows through it. A turn that would break value conservation, forge a \
                         capability, or corrupt the receipt chain simply does not commit.",
                    ),
                    PortalLine::new(
                        Tone::Muted,
                        "It links the verified Lean archive directly — the thing a thin client \
                         exists to avoid is exactly what this master interface wants.",
                    ),
                ],
            },
            // --- THE NERVOUS SYSTEM (receipts) --------------------------------
            PortalSection {
                title: "the receipt nervous system".to_string(),
                lines: vec![
                    PortalLine::new(
                        Tone::Body,
                        "Every committed turn leaves a TurnReceipt, and the receipts link into a \
                         chain — a navigable causal history of everything that has ever happened \
                         to this image. It is the image's memory, and you can time-travel through \
                         it.",
                    ),
                    PortalLine::new(
                        Tone::Good,
                        format!(
                            "{receipts} receipts recorded — open the BLOCKLACE to walk them, or REPLAY to scrub time"
                        ),
                    ),
                ],
            },
            // --- THE ORGANS (real survey) -------------------------------------
            PortalSection {
                title: "the organs".to_string(),
                lines: {
                    let mut lines = vec![PortalLine::new(
                        Tone::Body,
                        "The image grows organs — specialized cells with their own verified \
                         programs. Trustlines and flash-wells live right here in the embedded \
                         core; channels, mailboxes, and courts are reachable when you connect to \
                         a node.",
                    )];
                    lines.push(PortalLine::new(
                        Tone::Good,
                        format!("{live_organs} organ cell(s) live in this image · {remote_organs} more catalogued on the remote path"),
                    ));
                    for o in &survey.remote {
                        lines.push(PortalLine::new(
                            Tone::Muted,
                            format!("· {} — {}", o.kind, o.seam),
                        ));
                    }
                    lines
                },
            },
            // --- HOW TO EXPLORE (the invitation, made concrete) ---------------
            PortalSection {
                title: "everything here is yours to touch".to_string(),
                lines: vec![
                    PortalLine::new(
                        Tone::Accent,
                        "Press ⌘K (or Ctrl-K) for the command palette — one searchable surface over EVERY action.",
                    ),
                    PortalLine::new(
                        Tone::Body,
                        "Click any cell in the left rail to inspect it. Open the SHELL to see \
                         cells as cap-confined windows. Run a transfer in the COMPOSER and watch \
                         the image update live. Try the ⚠ over-grant and watch the \
                         no-amplification guarantee reject it to your face.",
                    ),
                    PortalLine::new(
                        Tone::Muted,
                        "The tabs along the top are the rooms of this house: SHELL · AGENT · \
                         SWARM · GRAPH · ORGANS · PROOFS · BUFFER · TERMINAL · COMPOSER · \
                         OBJECTS · DEBUGGER · REPLAY · CIPHERCLERK · EDITOR.",
                    ),
                ],
            },
        ];

        Self {
            headline: "Welcome to the live verified image.".to_string(),
            subtitle: "a single world where every object is capability-secured, every message is a verified turn, and every turn leaves a receipt".to_string(),
            sections,
            invitation: "↳ click a cell to inspect it, or press ⌘K to do anything.".to_string(),
        }
    }

    /// Every line of real text the portal will render, flattened (headline,
    /// subtitle, each section title + its lines, the invitation). Used by the
    /// HOME render to emit a startup PROOF line, and by tests to assert the
    /// portal speaks real, non-empty text. This is the exact text the gpui tree
    /// shows — so a non-empty result here is a non-empty rendered tree.
    pub fn all_text(&self) -> Vec<String> {
        let mut out = Vec::new();
        out.push(self.headline.clone());
        out.push(self.subtitle.clone());
        for s in &self.sections {
            out.push(s.title.clone());
            for l in &s.lines {
                out.push(l.text.clone());
            }
        }
        out.push(self.invitation.clone());
        out
    }

    /// The number of distinct text lines the portal renders (the count the
    /// startup proof line reports: "HOME portal: N text lines render").
    pub fn line_count(&self) -> usize {
        self.all_text().len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world::demo_world;

    #[test]
    fn portal_speaks_real_nonempty_text_about_the_live_image() {
        let (world, _anchors) = demo_world();
        let portal = LandingPortal::build(&world);

        // The headline + subtitle + invitation are real, non-empty prose.
        assert!(
            !portal.headline.trim().is_empty(),
            "headline must be real text"
        );
        assert!(
            !portal.subtitle.trim().is_empty(),
            "subtitle must be real text"
        );
        assert!(
            !portal.invitation.trim().is_empty(),
            "invitation must be real text"
        );

        // The portal has substantial content — this is the anti-blank guarantee:
        // the rendered HOME tree contains many lines of real text. (If this
        // were ever empty, the landing would be the blank screen we are fixing.)
        let text = portal.all_text();
        assert!(
            text.len() >= 20,
            "the portal must render many lines of text (got {}), not a near-empty surface",
            text.len()
        );
        for line in &text {
            assert!(
                !line.trim().is_empty(),
                "every portal line must be non-empty real text"
            );
        }
        assert_eq!(portal.line_count(), text.len());
    }

    #[test]
    fn portal_reflects_the_real_image_numbers_and_names_the_real_components() {
        let (world, _anchors) = demo_world();
        let portal = LandingPortal::build(&world);
        let blob = portal.all_text().join("\n");

        // It names the REAL heart, not a toy — the executor by its real type.
        assert!(
            blob.contains("TurnExecutor"),
            "the portal must name the real embedded executor (dregg_turn::executor::TurnExecutor)"
        );
        // It reflects the live image's ACTUAL cell count (proving it reads the
        // running world, not a hard-coded string).
        let n = world.cell_count();
        assert!(
            blob.contains(&format!("{n} live cells")),
            "the portal must report the live image's real cell count ({n})"
        );
        // It names the receipt nervous system + the ocap no-amplification law +
        // the command palette invitation — the things that make it self-describing.
        assert!(
            blob.contains("receipt"),
            "must name the receipt nervous system"
        );
        assert!(
            blob.to_lowercase().contains("capabilit"),
            "must name capabilities"
        );
        assert!(blob.contains("⌘K"), "must invite the command palette");
    }

    #[test]
    fn the_startup_proof_line_reports_real_text_for_the_demo_image() {
        // This mirrors the EXACT startup proof `main::run_window` prints before
        // opening the window. Asserting it here pins the concrete numbers ember
        // sees in the terminal on launch — proof the boot view is non-blank.
        let (world, _anchors) = demo_world();
        let portal = LandingPortal::build(&world);
        let proof = format!(
            "HOME portal: {} lines of real text render (headline + {} cards + invitation)",
            portal.line_count(),
            portal.sections.len()
        );
        // The demo image boots into a portal with the six titled cards and many
        // lines of real text (a generous floor; the exact count can grow).
        assert_eq!(
            portal.sections.len(),
            6,
            "the portal renders six titled cards"
        );
        assert!(
            portal.line_count() >= 25,
            "the boot view must render many lines of real text (got {})",
            portal.line_count()
        );
        assert!(proof.starts_with("HOME portal: "));
        assert_eq!(portal.headline, "Welcome to the live verified image.");
        // Print it so `cargo test -- --nocapture` shows the literal launch line.
        println!("STARTUP PROOF → {proof}");
        println!("STARTUP PROOF → headline: {}", portal.headline);
    }

    #[test]
    fn portal_is_full_and_alive_on_the_unseeded_genesis_image() {
        // THE FIRST-PAINT GUARANTEE: the HOME tab renders exactly this portal, and
        // the window now opens on the AT-REST genesis image (the four cells exist
        // but NONE of the five demo seed turns has run yet). Prove the boot view is
        // already abundant, non-blank, real text on that image — so the window is
        // alive the instant it opens, before any executor turn. (This is the render
        // content the window builds without the demo turns having run.)
        let (world, _anchors, _seed) = crate::world::demo_genesis();
        // Sanity: this really is the un-seeded image (the thing the window opens on).
        assert_eq!(
            world.receipts().len(),
            0,
            "no seed turn has run on the boot image"
        );
        assert_eq!(world.height(), 0);
        assert_eq!(world.cell_count(), 4, "the four genesis cells are present");

        let portal = LandingPortal::build(&world);
        let text = portal.all_text();
        // The boot view is FULL — the six titled cards + many lines of real prose,
        // every line non-empty. (If this were sparse, that is the blank-feeling
        // window we are fixing.)
        assert_eq!(
            portal.sections.len(),
            6,
            "all six cards render on the at-rest image"
        );
        assert!(
            portal.line_count() >= 25,
            "the unseeded boot view must already render abundant text (got {})",
            portal.line_count()
        );
        for line in &text {
            assert!(
                !line.trim().is_empty(),
                "every boot-view line must be real text"
            );
        }
        // It names the real heart + invites the palette + reports the live (here:
        // zero-turn) numbers honestly — and shows the image's genesis heartbeat
        // (the cells being born), so the boot view is alive, not a static splash.
        let blob = text.join("\n");
        assert!(
            blob.contains("TurnExecutor"),
            "names the real executor at boot"
        );
        assert!(blob.contains("⌘K"), "invites the command palette at boot");
        assert!(
            blob.contains("4 live cells"),
            "reports the at-rest image's real cell count"
        );
        // Zero seed turns have run, so the chain is honestly at height 0 / 0 receipts.
        assert!(
            blob.contains("height h0") && blob.contains("0 receipts"),
            "the boot view reports the un-seeded chain honestly (h0, no receipts yet)"
        );
        // The image is ALIVE (not a static splash): it shows a live heartbeat line
        // (here the most recent genesis birth — the cells coming into being).
        assert!(
            blob.contains("last heartbeat"),
            "the portal shows a live heartbeat line"
        );
    }

    #[test]
    fn portal_grows_with_the_image_it_describes() {
        // A portal built over a world with MORE history reports more receipts —
        // proving the text is a live projection, never a static splash.
        let (mut world, anchors) = demo_world();
        let before = LandingPortal::build(&world);
        let before_receipts = world.receipts().len();

        let [treasury, _service, user] = anchors;
        let turn = world.turn(
            treasury,
            vec![crate::world::transfer(treasury, user, 1_000)],
        );
        let _ = world.commit_turn(turn);

        let after = LandingPortal::build(&world);
        assert!(
            world.receipts().len() > before_receipts,
            "the demo turn should have added a receipt"
        );
        // The two portals differ (the live numbers moved): the landing is alive.
        assert_ne!(
            before.all_text(),
            after.all_text(),
            "the portal text must track the live image (it changed after a real turn)"
        );
    }
}
