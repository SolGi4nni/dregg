//! The DISTRIBUTED TIME-TRAVEL demo — collaborative rewind, fork, and stitch, headless.
//!
//! # The dream made operable
//!
//! fare's Houyhnhnm Computing: *"all destructive experiments happen in branches never merged into
//! official reality — the errors remain imaginary."* This module is the runnable, gpui-free scenario
//! of that dream as a two-party collaboration over ONE shared event-structure world:
//!
//!   1. Two parties (`main` and `peer`) share a timeline — an ordered sequence of committed configs,
//!      each a snapshot of the value-bearing document state. The timeline IS the shared blocklace
//!      (here, a linearized event-structure: each tick is a config the parties agreed on).
//!   2. One party SCRUBS to a PAST config and `EnterVirtualization`s a branch off it — a cap-confined
//!      `Virtual` timeline (`branch_stitch::VirtualBranch`). The branch holds NO main-cap, so its
//!      edits are *structurally imaginary* — they cannot drain/corrupt main (the integrity tooth,
//!      `branch_cannot_drain_main`).
//!   3. The party EDITS the divergent branch across several turns — an alternate history.
//!   4. The party `Stitch`es the good parts back. The reconciliation is the PUSHOUT (least upper
//!      bound) of the main leg and the branch leg (`branch_stitch::Stitch` / `stitch_is_pushout`),
//!      and authority is checked AT THE SETTLEMENT TIP, not at branch time
//!      (`SettlementSoundness.settlement_soundness`): a stitch conferring a cap the author no longer
//!      holds at settlement (e.g. revoked while the branch was open) is REFUSED.
//!
//! # The collaborative-rewind UX this drives
//!
//! *Drag the shared timeline → fork an alternate history → merge the good parts.* The
//! [`SharedTimeline`] is the draggable scrubber (welds onto `time_travel::TimeCockpitModel`'s
//! `cursor`/`ticks`); [`SharedTimeline::branch_at`] is the fork-here gesture (the collaborative
//! generalization of the cockpit's single-turn `replay_fork_here`); [`AlternateHistory::stitch_into`]
//! is the merge-the-good-parts gesture, settlement-gated.
//!
//! # Census-first WELD, not reinvention (the toy-disease lesson)
//!
//! Nothing here re-derives an algebra. It composes the landed organs into a scenario:
//!
//!   * the confinement tooth + the pushout + the settlement gate  ← [`crate::branch_stitch`]
//!     (`VirtualBranch`, `DocGraph`, `Stitch`, `SettleOutcome`) — itself the operable face of the
//!     proven Lean `Dregg2.Deos.BranchStitch` + `Dregg2.Circuit.SettlementSoundness` keystones.
//!   * the cross-party hole / late resolution  ← [`crate::held_promise`] (the I-confluent parts
//!     merge clean; a genuine conflict awaits the other party's fill — a guarded hole).
//!   * the timeline / scrubber / verified-landing shape  ← [`crate::time_travel`] / [`crate::replay`]
//!     (`ScrubTick`/`TimelineEntry` — a config per landing).
//!
//! This module adds only the *shared-world stateful scenario* that ties them into a collaborative
//! rewind: the timeline of agreed configs, the branch-off-a-past-config, the multi-turn divergent
//! edit, and the settlement-gated stitch back — with BOTH polarities (a compatible stitch lands; an
//! authority-violating stitch is refused at the settlement tip).
//!
//! # What this is NOT
//!
//! Not the executor, the circuit, the ledger, or consensus. It is the control/scenario model: the
//! shared event-structure timeline, the confined fork, and the pushout-correct settlement-gated
//! stitch. The cap gate is the Lean `Exec.Kernel`; the merge is the Lean `DocMerge`; the
//! authority-at-settlement is the Lean `SettlementSoundness`. This carries exactly enough structure
//! to make the two teeth bite end-to-end in a runnable two-party scenario.

use std::collections::{BTreeMap, BTreeSet};

use crate::branch_stitch::{
    Atom, BranchCap, DocGraph, MainFrontier, SettleOutcome, Stitch, StitchCap, VirtualBranch,
};

/// A party in the shared world. The demo runs two; the protocol is symmetric.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Party {
    /// The party that owns the MAIN frontier (official reality).
    Main,
    /// The collaborating peer that opens a branch off a past config.
    Peer,
}

impl Party {
    /// The party's name, for timeline labels.
    pub fn name(self) -> &'static str {
        match self {
            Party::Main => "main",
            Party::Peer => "peer",
        }
    }
}

/// One landing on the SHARED timeline: a config the parties agreed on, plus the turn-label that
/// produced it. This is the event-structure node both parties hold — the demo's linearized blocklace
/// tick. Mirrors [`crate::time_travel::ScrubTick`] / [`crate::replay::TimelineEntry`]: a config per
/// landing, scrubbable.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tick {
    /// The step index on the shared timeline (`0` = genesis config).
    pub step: usize,
    /// The agreed document config AT this landing (the value-bearing atom layer).
    pub config: DocGraph,
    /// A short human label for the turn that produced this config (or "genesis").
    pub label: String,
    /// Who authored the turn that produced this config (`None` for genesis).
    pub author: Option<Party>,
}

/// **The SHARED TIMELINE — the draggable scrubber over agreed configs.** An append-only, ordered
/// sequence of [`Tick`]s the parties share (the linearized event-structure). The cursor is where a
/// party has dragged the scrubber; [`branch_at`](Self::branch_at) forks a confined branch off the
/// config at the cursor.
///
/// This is the collaborative generalization of [`crate::time_travel::TimeCockpitModel`]: the same
/// scrubbable-ticks shape, but shared across parties and forkable into a divergent branch.
#[derive(Clone, Debug)]
pub struct SharedTimeline {
    /// The ordered configs both parties agree on. `ticks[0]` is genesis.
    ticks: Vec<Tick>,
    /// The MAIN frontier: the set of cells official reality owns (a branch must be confined away
    /// from these). In the doc model the "cells" index the value-bearing keys main controls.
    main: MainFrontier,
}

impl SharedTimeline {
    /// Open a shared timeline at a genesis config, with `main` the frontier official reality owns.
    pub fn genesis(config: DocGraph, main: MainFrontier) -> Self {
        Self {
            ticks: vec![Tick {
                step: 0,
                config,
                label: "genesis".into(),
                author: None,
            }],
            main,
        }
    }

    /// Append an agreed turn to the shared timeline: a new config the parties commit to, authored by
    /// `party`. This is a MAINLINE turn (it settles into official reality) — distinct from a branch
    /// edit, which stays imaginary until stitched.
    pub fn commit(&mut self, config: DocGraph, label: impl Into<String>, party: Party) {
        let step = self.ticks.len();
        self.ticks.push(Tick {
            step,
            config,
            label: label.into(),
            author: Some(party),
        });
    }

    /// The number of landings on the shared timeline (genesis included).
    pub fn len(&self) -> usize {
        self.ticks.len()
    }

    /// Whether the timeline holds only genesis.
    pub fn is_empty(&self) -> bool {
        self.ticks.len() <= 1
    }

    /// The head step (the live present — the latest agreed config).
    pub fn head(&self) -> usize {
        self.ticks.len() - 1
    }

    /// The config at step `k` (clamped to the head). The scrubber's reconstruction.
    pub fn config_at(&self, k: usize) -> &DocGraph {
        &self.ticks[k.min(self.head())].config
    }

    /// The whole tick list (for the scrubber UI to draw).
    pub fn ticks(&self) -> &[Tick] {
        &self.ticks
    }

    /// The MAIN frontier official reality owns.
    pub fn main_frontier(&self) -> &MainFrontier {
        &self.main
    }

    /// **`EnterVirtualization` — fork a CONFINED branch off the PAST config at step `k`.** The peer
    /// drags the scrubber to a past landing and forks an alternate history. The branch is a
    /// [`VirtualBranch`] confined away from `main` (it holds only the branch-caps passed in
    /// `branch_caps`, NONE reaching a main cell), so its edits are structurally imaginary
    /// (`branch_cannot_drain_main`). The branch's starting config is a COPY of the config at `k` —
    /// the past the peer rewound to.
    ///
    /// Returns the divergent [`AlternateHistory`] the peer edits, or `None` if `k` is out of range.
    pub fn branch_at(
        &self,
        k: usize,
        author: u64,
        branch_caps: Vec<BranchCap>,
    ) -> Option<AlternateHistory> {
        if k >= self.ticks.len() {
            return None;
        }
        let branch = VirtualBranch::enter(author, self.main.clone(), branch_caps);
        Some(AlternateHistory {
            branched_from: k,
            base_config: self.ticks[k].config.clone(),
            current: self.ticks[k].config.clone(),
            branch,
            edits: Vec::new(),
        })
    }
}

/// One edit the peer makes on the branch — a divergent-history turn. Records what changed (for the
/// scrubber to draw the alternate timeline) and whether it was structurally imaginary (a main-debit
/// the confinement refused) vs a real branch-local edit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BranchEdit {
    /// A human label for the edit.
    pub label: String,
    /// `true` iff this edit attempted to touch MAIN and was refused (structurally imaginary —
    /// the branch *believes* it acted, but official reality is untouched). `false` for a real
    /// branch-local edit that lands in the divergent config.
    pub imaginary: bool,
}

/// **The ALTERNATE HISTORY — a confined branch the peer edits, divergent from main.** Welds the
/// [`VirtualBranch`] confinement tooth onto a running divergent config the peer mutates across
/// several turns. Its edits cannot drain main (integrity); the only door back is [`stitch_into`].
#[derive(Clone, Debug)]
pub struct AlternateHistory {
    /// The shared-timeline step this branch forked off.
    pub branched_from: usize,
    /// The config the branch started from (the past the peer rewound to) — for the divergence diff.
    pub base_config: DocGraph,
    /// The branch's current divergent config (the peer's alternate history).
    pub current: DocGraph,
    /// The confinement object: the branch holds only branch-caps (`branch_cannot_drain_main`).
    pub branch: VirtualBranch,
    /// The edits the peer made, in order (for the alternate-timeline scrubber).
    pub edits: Vec<BranchEdit>,
}

impl AlternateHistory {
    /// **A real branch-local edit** — write `atom` at `key` in the divergent config. This is a turn
    /// the branch author owns (the branch is its own world); it lands in `current`. Use this for the
    /// peer's alternate-history discoveries and deletions.
    pub fn edit(&mut self, key: u64, atom: Atom, label: impl Into<String>) {
        self.current.atoms.insert(key, atom);
        self.edits.push(BranchEdit {
            label: label.into(),
            imaginary: false,
        });
    }

    /// **An attempted MAIN edit — the confinement tooth in action.** The branch *tries* to mutate a
    /// cell in the main frontier. If the branch is confined (it is, by construction), the kernel gate
    /// would REFUSE the debit — so the edit is *structurally imaginary*: it is recorded as an attempt
    /// but does NOT change the divergent config that a stitch could carry into main. Returns `true`
    /// iff the edit was imaginary (refused). This is the operable `debit_is_imaginary` /
    /// `branch_cannot_drain_main` at the scenario level.
    ///
    /// (We model the "drain main" attempt as a debit whose `src` is the main cell; a confined branch
    /// cannot author it, so nothing lands.)
    pub fn try_edit_main(&mut self, main_cell: u64, label: impl Into<String>) -> bool {
        let debit = crate::branch_stitch::BranchDebit {
            actor: self.branch.author,
            src: main_cell,
        };
        let imaginary = self.branch.debit_is_imaginary(debit);
        self.edits.push(BranchEdit {
            label: label.into(),
            imaginary,
        });
        imaginary
    }

    /// Whether the branch is HONESTLY confined (the `EnterVirtualization` well-formedness predicate —
    /// `BranchHonest`). A branch that fails this is a protocol violation (it holds a main-cap) and its
    /// edits are NOT imaginary — surfaced, never laundered.
    pub fn confined(&self) -> bool {
        self.branch.confined()
    }

    /// The divergence of the branch from its base config — the keys the alternate history changed.
    /// (What the scrubber draws as the "alternate timeline" diverging from the fork point.)
    pub fn divergence(&self) -> BTreeMap<u64, (Option<Atom>, Atom)> {
        let mut d = BTreeMap::new();
        for (&k, &v) in &self.current.atoms {
            let before = self.base_config.atoms.get(&k).copied();
            if before != Some(v) {
                d.insert(k, (before, v));
            }
        }
        d
    }

    /// **`Stitch` — merge the good parts back into main, settlement-gated.** The peer reconciles the
    /// divergent `current` config against the live `main_config` of the shared timeline. The result
    /// is the PUSHOUT (`Stitch::settle` → `stitch_is_pushout`): the least upper bound of the two legs,
    /// optionally after an explicit author drop (`keep`).
    ///
    /// AUTHORITY IS CHECKED AT THE SETTLEMENT TIP: `settlement_held` is the author's caps as read at
    /// the FINALIZED commitment (after any revocation that happened while the branch was open). A
    /// stitch conferring a cap not in `settlement_held` is OVER-AUTHORIZED and REFUSED — the operable
    /// shadow of `SettlementSoundness.settlement_soundness`. (`conferred` = the caps the branch claims
    /// its discoveries justify carrying into main.)
    ///
    /// On acceptance, returns the settled config to commit as the new shared-timeline head.
    pub fn stitch_into(
        &self,
        main_config: &DocGraph,
        conferred: Vec<StitchCap>,
        settlement_held: &[StitchCap],
        keep: Option<&BTreeSet<u64>>,
    ) -> SettleOutcome {
        let stitch = Stitch {
            main: main_config.clone(),
            branch: self.current.clone(),
            conferred,
        };
        stitch.settle(settlement_held, keep)
    }
}

// ===========================================================================
// The runnable two-party SCENARIO (the headless demo entry point).
// ===========================================================================

/// The outcome of a full distributed-time-travel run: what the peer found, whether the stitch
/// settled, and the resulting shared timeline head. Returned by [`run_collaborative_rewind`] so a
/// test (or the cockpit) can inspect the whole arc.
#[derive(Clone, Debug)]
pub struct RewindRun {
    /// The shared timeline AFTER the run (the new head is the settled config, iff the stitch landed).
    pub timeline: SharedTimeline,
    /// The step the peer branched off.
    pub branched_from: usize,
    /// The peer's divergence (the alternate history's changed keys).
    pub divergence: BTreeMap<u64, (Option<Atom>, Atom)>,
    /// Whether every main-touching branch edit was structurally imaginary (the integrity tooth held
    /// for the whole branch session).
    pub branch_stayed_imaginary: bool,
    /// The settlement outcome of the stitch back.
    pub settle: SettleOutcome,
}

impl RewindRun {
    /// Whether the stitch settled (the good parts merged into main).
    pub fn settled(&self) -> bool {
        matches!(self.settle, SettleOutcome::Settled(_))
    }

    /// The settled config, if the stitch landed.
    pub fn settled_config(&self) -> Option<&DocGraph> {
        match &self.settle {
            SettleOutcome::Settled(g) => Some(g),
            SettleOutcome::Refused { .. } => None,
        }
    }
}

/// **THE COLLABORATIVE-REWIND SCENARIO.** A self-contained run of the distributed time-travel demo:
///
///   1. Build a shared timeline of `mainline` agreed configs (the parties' shared past).
///   2. The peer SCRUBS to `branch_step` and `EnterVirtualization`s a confined branch.
///   3. The peer applies `branch_edits` (divergent-history turns) — including, if `probe_main` is
///      set, an attempted MAIN edit that the confinement should refuse (proving imaginariness).
///   4. The peer `Stitch`es back, conferring `conferred`, gated by `settlement_held` (the
///      authority as read at the SETTLEMENT TIP).
///   5. On acceptance, the settled config is committed as the new shared head.
///
/// Returns a [`RewindRun`] capturing the whole arc, so both polarities (a clean stitch lands; an
/// over-authorized stitch is refused at settlement) are inspectable from one entry point.
#[allow(clippy::too_many_arguments)]
pub fn run_collaborative_rewind(
    genesis: DocGraph,
    main: MainFrontier,
    mainline: Vec<(DocGraph, String, Party)>,
    branch_step: usize,
    peer_author: u64,
    branch_caps: Vec<BranchCap>,
    branch_edits: Vec<(u64, Atom, String)>,
    probe_main: Option<u64>,
    conferred: Vec<StitchCap>,
    settlement_held: Vec<StitchCap>,
    keep: Option<BTreeSet<u64>>,
) -> RewindRun {
    // 1. The shared past: the parties commit a sequence of agreed configs.
    let mut timeline = SharedTimeline::genesis(genesis, main);
    for (config, label, party) in mainline {
        timeline.commit(config, label, party);
    }

    // 2. The peer scrubs to a past config and forks a confined branch.
    let mut alt = timeline
        .branch_at(branch_step, peer_author, branch_caps)
        .expect("branch step within range");

    // 3. The peer edits the divergent branch.
    let mut stayed_imaginary = true;
    if let Some(main_cell) = probe_main {
        // An attempted MAIN edit — the confinement tooth must refuse it (imaginary).
        let imaginary = alt.try_edit_main(main_cell, "peer probes main (must be imaginary)");
        stayed_imaginary &= imaginary;
    }
    for (key, atom, label) in branch_edits {
        alt.edit(key, atom, label);
    }

    let divergence = alt.divergence();

    // 4. The peer stitches back, gated by authority read at the settlement tip.
    let main_config = timeline.config_at(timeline.head()).clone();
    let settle = alt.stitch_into(&main_config, conferred, &settlement_held, keep.as_ref());

    // 5. On acceptance, commit the settled config as the new shared head.
    if let SettleOutcome::Settled(ref settled) = settle {
        timeline.commit(settled.clone(), "stitch back (settled)", Party::Peer);
    }

    RewindRun {
        timeline,
        branched_from: branch_step,
        divergence,
        branch_stayed_imaginary: stayed_imaginary,
        settle,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: a DocGraph from `(key, atom)` pairs.
    fn doc(atoms: &[(u64, Atom)]) -> DocGraph {
        DocGraph {
            atoms: atoms.iter().copied().collect(),
        }
    }

    fn frontier(cells: &[u64]) -> MainFrontier {
        cells.iter().copied().collect()
    }

    // ── THE HEADLINE: a full collaborative rewind, both polarities ──────────────────────────────

    /// **POLARITY 1 — a COMPATIBLE branch edit stitches CLEAN.** Two parties share a 3-config past.
    /// The peer rewinds to step 1, forks a confined branch, makes a compatible discovery (a new atom
    /// + a deletion main also wants), and stitches back conferring only authority it holds at the
    ///   settlement tip. The stitch SETTLES to the pushout: nothing main had is lost, the branch's
    ///   discovery is kept, and the conflict (main Dead vs branch Alive at key 0) resolves Dead-wins.
    #[test]
    fn compatible_branch_stitches_clean() {
        let run = run_collaborative_rewind(
            // genesis: key 0 alive.
            doc(&[(0, Atom::Alive)]),
            frontier(&[0, 1]), // main owns cells 0 and 1
            vec![
                // mainline: main works on its own atoms (the shared past).
                (
                    doc(&[(0, Atom::Alive), (1, Atom::Alive)]),
                    "main adds atom 1".into(),
                    Party::Main,
                ),
                (
                    doc(&[(0, Atom::Dead), (1, Atom::Alive)]),
                    "main deletes atom 0".into(),
                    Party::Main,
                ),
            ],
            1,  // the peer rewinds to step 1 (before main deleted atom 0)
            77, // the peer's branch author cell
            vec![BranchCap {
                target: 99,
                debit_reach: true,
            }], // only a branch-cap (off-main) ⇒ confined
            vec![
                // the peer's divergent edits: a new discovery atom 5, and revive atom 0 in-branch.
                (5, Atom::Alive, "peer discovers atom 5".into()),
                (0, Atom::Alive, "peer revives atom 0 in branch".into()),
            ],
            None, // no main-probe this run
            vec![BranchCap {
                target: 5,
                debit_reach: true,
            }], // confers authority over its discovery
            vec![BranchCap {
                target: 5,
                debit_reach: true,
            }], // …which it HELD at the settlement tip
            None, // no explicit drop — the full pushout
        );

        assert!(
            run.settled(),
            "a well-authorized, compatible stitch settles"
        );
        let settled = run.settled_config().unwrap();
        // The conflict at key 0: main says Dead (head config), branch says Alive ⇒ Dead-wins.
        assert_eq!(
            settled.atoms.get(&0),
            Some(&Atom::Dead),
            "Dead-wins settles the revive/delete clash"
        );
        // The branch's discovery is KEPT (nothing the branch found is dropped).
        assert_eq!(
            settled.atoms.get(&5),
            Some(&Atom::Alive),
            "the branch discovery is merged in"
        );
        // Main's atom 1 survives (nothing main had is lost).
        assert_eq!(
            settled.atoms.get(&1),
            Some(&Atom::Alive),
            "main's value is preserved (the cocone)"
        );
        // The settled config is the new shared head.
        assert_eq!(run.timeline.config_at(run.timeline.head()), settled);
        assert_eq!(run.branched_from, 1);
    }

    /// **POLARITY 2 — an AUTHORITY-VIOLATING stitch is REFUSED at the settlement tip.** Same setup,
    /// but the peer's cap over its discovery was REVOKED while the branch was open — so it is NOT in
    /// the settlement-tip authority. The stitch tries to confer it anyway. Settlement Soundness
    /// REFUSES: authority is read at settlement, not at branch time. The shared head is UNCHANGED.
    #[test]
    fn authority_violating_stitch_refused_at_settlement() {
        let run = run_collaborative_rewind(
            doc(&[(0, Atom::Alive)]),
            frontier(&[0, 1]),
            vec![
                (
                    doc(&[(0, Atom::Alive), (1, Atom::Alive)]),
                    "main adds atom 1".into(),
                    Party::Main,
                ),
                (
                    doc(&[(0, Atom::Dead), (1, Atom::Alive)]),
                    "main deletes atom 0".into(),
                    Party::Main,
                ),
            ],
            1,
            77,
            vec![BranchCap {
                target: 99,
                debit_reach: true,
            }],
            vec![(5, Atom::Alive, "peer discovers atom 5".into())],
            None,
            vec![BranchCap {
                target: 5,
                debit_reach: true,
            }], // the peer CLAIMS authority over atom 5…
            // …but at the SETTLEMENT tip it holds nothing reaching cell 5 (revoked while branch open).
            vec![BranchCap {
                target: 99,
                debit_reach: true,
            }],
            None,
        );

        assert_eq!(
            run.settle,
            SettleOutcome::Refused {
                over_authorized_target: 5
            },
            "a cap not held at the settlement tip ⇒ the stitch is refused (Settlement Soundness)"
        );
        assert!(
            !run.settled(),
            "an authority-violating stitch does not settle"
        );
        // The shared head is UNCHANGED — official reality untouched by the refused stitch.
        assert_eq!(
            run.timeline.head(),
            2,
            "the timeline head is still main's last agreed config"
        );
        assert_eq!(
            run.timeline.config_at(2),
            &doc(&[(0, Atom::Dead), (1, Atom::Alive)]),
            "official reality is exactly main's pre-stitch config — nothing conjured"
        );
    }

    /// **THE INTEGRITY TOOTH end-to-end — a branch's main-probe stays IMAGINARY.** The peer, in its
    /// confined branch, *tries* to drain a main cell. The confinement refuses it: the edit is
    /// structurally imaginary, official reality is never touched by it, and the branch still stitches
    /// its legitimate (branch-local) discovery back. This runs `branch_cannot_drain_main` end-to-end
    /// inside the collaborative scenario.
    #[test]
    fn branch_main_probe_stays_imaginary() {
        let run = run_collaborative_rewind(
            doc(&[(0, Atom::Alive)]),
            frontier(&[0, 1]),
            vec![(
                doc(&[(0, Atom::Alive), (1, Atom::Alive)]),
                "main adds atom 1".into(),
                Party::Main,
            )],
            1,
            77,
            vec![BranchCap {
                target: 99,
                debit_reach: true,
            }], // confined
            vec![(5, Atom::Alive, "peer's real branch-local discovery".into())],
            Some(1), // the peer PROBES main cell 1 — must be imaginary
            vec![BranchCap {
                target: 5,
                debit_reach: true,
            }],
            vec![BranchCap {
                target: 5,
                debit_reach: true,
            }],
            None,
        );

        assert!(
            run.branch_stayed_imaginary,
            "the branch's main-probe was structurally imaginary"
        );
        assert!(
            run.settled(),
            "the legitimate branch-local discovery still stitches back"
        );
        // The divergence carries ONLY the real branch-local edit (atom 5), never a main cell.
        assert!(
            run.divergence.contains_key(&5),
            "the real discovery diverged"
        );
        assert!(
            !run.divergence.contains_key(&1) && !run.divergence.contains_key(&0),
            "the imaginary main-probe never entered the divergent config"
        );
    }

    /// **THE INTEGRITY TOOTH is load-bearing (the FALSE polarity).** Drop confinement — let the
    /// "branch" hold a debit-cap to a MAIN cell (a protocol violation). Now the branch is NOT confined,
    /// the main-probe is NOT imaginary (it would drain main), and `confined()` reports the violation.
    /// This refutes any reading of the imaginary tooth as vacuous.
    #[test]
    fn unconfined_branch_probe_is_not_imaginary() {
        let timeline = SharedTimeline::genesis(doc(&[(0, Atom::Alive)]), frontier(&[1]));
        // The "branch" illicitly holds a debit-cap to main cell 1.
        let mut alt = timeline
            .branch_at(
                0,
                77,
                vec![BranchCap {
                    target: 1,
                    debit_reach: true,
                }],
            )
            .unwrap();
        assert!(
            !alt.confined(),
            "holding a debit-cap to main breaks confinement (a violation)"
        );
        let imaginary = alt.try_edit_main(1, "probe main 1");
        assert!(
            !imaginary,
            "an un-confined branch's main-drain is REAL, not imaginary (load-bearing)"
        );
    }

    /// **THE EXPLICIT DROP — merge only the GOOD parts.** The peer found two atoms in its branch but
    /// decides only one is worth keeping; it stitches with an explicit `keep` set. The dropped atom is
    /// gone (strict loss), the kept one lands, and the result lies below the full pushout (no value
    /// conjured). This is "merge the good parts" as the linear-logic-forced explicit drop.
    #[test]
    fn stitch_keeps_only_the_good_parts() {
        let keep: BTreeSet<u64> = [5].into_iter().collect();
        let run = run_collaborative_rewind(
            doc(&[(0, Atom::Alive)]),
            frontier(&[0]),
            vec![],
            0,
            77,
            vec![BranchCap {
                target: 99,
                debit_reach: true,
            }],
            vec![
                (5, Atom::Alive, "a good discovery".into()),
                (
                    6,
                    Atom::Alive,
                    "a discovery the peer decides to drop".into(),
                ),
            ],
            None,
            vec![], // confer nothing ⇒ the settlement gate trivially passes
            vec![],
            Some(keep),
        );

        assert!(run.settled(), "the explicit-drop stitch settles");
        let settled = run.settled_config().unwrap();
        assert_eq!(
            settled.atoms.get(&5),
            Some(&Atom::Alive),
            "the GOOD part (atom 5) is kept"
        );
        assert!(
            !settled.atoms.contains_key(&6),
            "the dropped part (atom 6) is explicitly gone"
        );
    }

    /// The shared timeline is scrubbable: every past config is addressable, and branching off step k
    /// starts the alternate history from EXACTLY the config at k (the past the peer rewound to).
    #[test]
    fn scrub_and_branch_lands_on_the_past_config() {
        let mut tl = SharedTimeline::genesis(doc(&[(0, Atom::Alive)]), frontier(&[0]));
        tl.commit(
            doc(&[(0, Atom::Alive), (1, Atom::Alive)]),
            "add 1",
            Party::Main,
        );
        tl.commit(
            doc(&[(0, Atom::Dead), (1, Atom::Alive)]),
            "del 0",
            Party::Main,
        );
        assert_eq!(tl.head(), 2);

        // Branch off step 1 — the config BEFORE main deleted atom 0.
        let alt = tl.branch_at(1, 77, vec![]).unwrap();
        assert_eq!(
            alt.base_config,
            *tl.config_at(1),
            "the branch starts from the scrubbed-to past"
        );
        assert_eq!(
            alt.base_config.atoms.get(&0),
            Some(&Atom::Alive),
            "atom 0 is still alive at step 1"
        );
        // Out-of-range branch is rejected.
        assert!(
            tl.branch_at(99, 77, vec![]).is_none(),
            "branching past the head is rejected"
        );
    }
}
