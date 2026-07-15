//! # `CheevoShowcase` — a **read-surface** over [`dreggnet_cheevo`] earned achievements.
//!
//! The earned, un-fakeable, SOULBOUND achievements + their proofs, rendered as a `Table`: the
//! predicate (reached-depth / no-death / speed / champion), who earned it, the WITNESS (why — the
//! peak depth, the turn count), the verified turns-to-win, and the soulbound seal. Each row is a
//! real [`Cheevo`] earned only by a run that passed the ugc no-cheat verify AND satisfied the
//! predicate over the run's real committed trajectory — a proof you earned it, not a badge.
//!
//! Read-only: an achievement is earned by *playing* (the game Offerings), not on this surface;
//! `render` is the payload. [`demo`](CheevoShowcase::demo) seeds REAL earned cheevos (a genuine
//! verified descent run) for the web/discord register state.

use dreggnet_cheevo::{Achievement, Cheevo, CheevoLedger, Witness};
use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingError, Outcome, RunCost, SessionConfig, Surface,
    VerifyReport,
};
use ugc_dregg::{Completion, Universe, WinCondition, record_playthrough};

use crate::{pill, row, section, short_hex, text};
use deos_view::ViewNode;

/// A tiny authored descent world (a `depth` counter + a `gold`-seizing win) — the demo run source.
/// The deep route increments `depth` three times; both routes seize the relic (`gold == 500`) and
/// END, so a real verified win genuinely earns a reached-depth + a speed cheevo.
const DESCENT: &str = r#"---
id: surfaces-cheevo-descent
title: Surfaces Descent Trial
weight: 1
---

=== mouth

You stand at the mouth of a black pit. A shaft plunges down; a side crack hugs the wall.

* [Descend the deep shaft]
  ~ depth += 1
  -> deep1

* [Slip through the side crack]
  -> shallow

=== deep1

The shaft narrows. Cold air rises.

* [Descend deeper]
  ~ depth += 1
  -> deep2

=== deep2

Deeper still. The dark is total.

* [Descend to the vault floor]
  ~ depth += 1
  -> vault

=== shallow

The crack opens onto a ledge above the vault.

* [Creep along the ledge to the vault]
  -> vault

=== vault

A relic gleams on a plinth.

* [Seize the relic and escape]
  ~ gold += 500
  -> END
"#;

/// The deep winning route: descend, descend, descend, seize — reaches `depth == 3` in 4 turns.
const DEEP_MOVES: [usize; 4] = [0, 0, 0, 0];

/// A human "why" from a cheevo's witness (the proof's evidence).
fn why(w: &Witness) -> String {
    match w {
        Witness::Depth { peak, min } => format!("reached depth {peak} (≥ {min})"),
        Witness::NoDeath { flag } => format!("flawless — `{flag}` never tripped"),
        Witness::Speed { turns, max_turns } => format!("won in {turns} turns (≤ {max_turns})"),
        Witness::Champion { top_n, rank, turns } => {
            format!("season champion #{rank} of top-{top_n} ({turns} turns)")
        }
        Witness::Threshold { var, observed } => format!("`{var}` reached {observed}"),
        Witness::Composite { parts } => {
            let inner: Vec<String> = parts.iter().map(why).collect();
            format!("all held — {}", inner.join("; "))
        }
    }
}

/// A friendly title for an achievement predicate.
fn achievement_title(a: &Achievement) -> String {
    match a {
        Achievement::ReachedDepth { min, .. } => format!("Deep Delver (≥{min})"),
        Achievement::NoDeathClear { .. } => "Flawless Clear".to_string(),
        Achievement::SpeedClear { max_turns } => format!("Speedrunner (≤{max_turns})"),
        Achievement::SeasonChampion { top_n } => format!("Season Champion (top-{top_n})"),
        // Authored predicates carry the author's own display name.
        Achievement::VarThreshold { label, .. } => label.clone(),
        Achievement::All { label, parts } => format!("{label} ({}×)", parts.len()),
    }
}

/// **A live showcase session** — the earned cheevos to render (soulbound proofs).
pub struct CheevoSession {
    cheevos: Vec<Cheevo>,
}

impl CheevoSession {
    /// How many achievements are shown.
    pub fn len(&self) -> usize {
        self.cheevos.len()
    }
    /// Whether the showcase is empty.
    pub fn is_empty(&self) -> bool {
        self.cheevos.is_empty()
    }
}

/// **The cheevo showcase offering** — a read-surface factory over a set of earned cheevos.
pub struct CheevoShowcase {
    cheevos: Vec<Cheevo>,
}

impl CheevoShowcase {
    /// An EMPTY showcase (the empty-state surface).
    pub fn empty() -> Self {
        CheevoShowcase {
            cheevos: Vec::new(),
        }
    }

    /// A showcase over an explicit set of earned cheevos (e.g. a driver's own ledger).
    pub fn from_cheevos(cheevos: Vec<Cheevo>) -> Self {
        CheevoShowcase { cheevos }
    }

    /// A DEMO showcase — earns REAL cheevos from a genuine verified descent run (the no-cheat gate
    /// runs; the predicates hold over the run's real trajectory), so the web/discord register state
    /// shows actual soulbound proofs. Panics only if the built-in descent world is malformed
    /// (it is not — it is the same authored-scene shape `dreggnet-cheevo`'s own tests drive).
    pub fn demo() -> Self {
        let universe = Universe::authored(
            "Surfaces Descent Trial",
            "surfaces-cheevo",
            DESCENT,
            WinCondition::ended_with(&[("gold", 500)]),
        )
        .expect("the descent world is a valid, deployable universe");
        let play = record_playthrough(&universe, &DEEP_MOVES)
            .expect("the deep winning run drives cleanly");
        let completion = Completion {
            universe: universe.id(),
            player: "Ada".to_string(),
            play,
            claimed_turns: DEEP_MOVES.len(),
        };

        let mut ledger = CheevoLedger::new();
        let mut cheevos = Vec::new();
        // A reached-depth cheevo (the run really peaked at depth 3) …
        if let Ok(c) = ledger.earn(
            &universe,
            &completion,
            Achievement::ReachedDepth {
                var: "depth".to_string(),
                min: 3,
            },
        ) {
            cheevos.push(c);
        }
        // … and a speed cheevo (the run won in 4 turns).
        if let Ok(c) = ledger.earn(
            &universe,
            &completion,
            Achievement::SpeedClear { max_turns: 4 },
        ) {
            cheevos.push(c);
        }
        CheevoShowcase::from_cheevos(cheevos)
    }
}

impl Offering for CheevoShowcase {
    type Session = CheevoSession;

    fn open(&self, _cfg: SessionConfig) -> Result<CheevoSession, OfferingError> {
        Ok(CheevoSession {
            cheevos: self.cheevos.clone(),
        })
    }

    /// A read-surface exposes no moves.
    fn actions(&self, _s: &CheevoSession) -> Vec<Action> {
        Vec::new()
    }

    /// Read-only: an achievement is earned by playing, not on this surface.
    fn advance(&self, _s: &mut CheevoSession, _input: Action, _actor: DreggIdentity) -> Outcome {
        Outcome::Refused("the showcase is a read-only surface — earn a cheevo by playing".into())
    }

    /// The cheap integrity check available without the run: every shown cheevo's seal re-derives
    /// (a re-bound / edited record no longer matches its content-addressed seal). The full
    /// [`CheevoLedger::reverify_run`] (re-run the no-cheat verify + re-hold the predicate) is the
    /// driver's deeper check when it holds the universe + completion.
    fn verify(&self, s: &CheevoSession) -> VerifyReport {
        for c in &s.cheevos {
            if !c.seal_intact() {
                return VerifyReport::broken(
                    s.cheevos.len(),
                    format!("`{}`'s seal does not match its fields (tampered)", c.player),
                );
            }
        }
        VerifyReport::ok(s.cheevos.len())
    }

    fn render(&self, s: &CheevoSession) -> Surface {
        let mut children: Vec<ViewNode> = Vec::new();

        children.push(section(
            "Showcase",
            "muted",
            vec![text(format!("{} achievement(s) earned", s.len()))],
        ));

        if s.is_empty() {
            children.push(section(
                "Achievements",
                "muted",
                vec![text("No achievements earned yet — clear a verified run.")],
            ));
        } else {
            let mut rows: Vec<ViewNode> = vec![row(vec![
                text("Achievement"),
                text("Player"),
                text("Why (witness)"),
                text("Turns"),
                text("Seal"),
            ])];
            for c in &s.cheevos {
                rows.push(row(vec![
                    pill(achievement_title(&c.achievement), "accent"),
                    text(&c.player),
                    text(why(&c.witness)),
                    text(c.turns.to_string()),
                    pill(
                        short_hex(&c.seal),
                        if c.seal_intact() { "good" } else { "bad" },
                    ),
                ]));
            }
            children.push(section(
                "Achievements",
                "accent",
                vec![ViewNode::Table(rows)],
            ));
        }

        Surface(section("Achievements — earned proofs", "accent", children))
    }

    fn price(&self, _input: &Action) -> RunCost {
        RunCost::free()
    }
}
