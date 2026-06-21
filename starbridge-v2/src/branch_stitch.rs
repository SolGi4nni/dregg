//! Branch-and-stitch turns — the operable protocol of distributed time-travel as two
//! first-class effects: `EnterVirtualization` and `Stitch`.
//!
//! # The through-line
//!
//! A turn is the exercise of an attenuable proof-carrying token over owned state, leaving a
//! verifiable receipt. *Branch-and-stitch* lets parties co-consent to fork a PAST config into a
//! cap-confined VIRTUAL world, experiment destructively there with the integrity guarantee that
//! the branch's side-effects are **structurally imaginary** (it holds no cap to main, so it cannot
//! drain main), and reconcile back through ONE narrow door — the `Stitch` — which is a
//! pushout-correct, explicitly-lossy settlement gated by Settlement Soundness (authority evaluated
//! at the SETTLEMENT tip, not at branch time).
//!
//! This module is the gpui-free CONTROL model of the two turns. It does not re-derive any algebra:
//! it is the operable Rust face of the two proven Lean keystones, named in the same vocabulary.
//!
//! # What rides what (census-first weld, NOT reinvention)
//!
//! * **`EnterVirtualization` / the confinement check** mirrors
//!   `Dregg2.Deos.BranchStitch.branch_cannot_drain_main` (= `Confinement.confined_cannot_debit_attacker`
//!   restated for the branch/main split). The well-formedness predicate `BranchHonest M caps author`
//!   is *exactly* `Confinement.Confined M caps author`: the branch author owns no MAIN cell and
//!   reaches none by cap — it holds only branch-caps. Under that hypothesis NO branch turn can debit
//!   (drain) a main cell. The `VirtualBranch::confined` check below is the operable form of that
//!   predicate; `VirtualBranch::admits_debit` is the operable form of the no-drain tooth.
//!   Recursion (`branch_in_branch_cannot_drain`): a branch-in-branch is the SAME `Confined`
//!   hypothesis one stratum down — confinement composes, modeled by [`VirtualBranch::nest`].
//!
//! * **`Stitch`** mirrors `Dregg2.Deos.BranchStitch.stitch_is_pushout` (= `DocMerge.merge_is_lub`):
//!   the settled result is the LEAST UPPER BOUND of the main leg and the branch leg in document
//!   inclusion — both legs included (nothing main had silently lost, nothing the branch found
//!   silently dropped) AND below every common upper bound (no value conjured). The I-confluent part
//!   merges clean; a genuine conflict is resolved by an EXPLICIT, linear-logic-forced DROP
//!   (`stitch_drop_explicit` / `stitch_drop_is_below`: the kept keys are exactly `K`, and a drop can
//!   only lose, never conjure). Cross-party reconciliation is a partial turn with HOLES — reusing the
//!   guarded-hole shape of [`crate::held_promise`] (`holeFill_binds_in_circuit`).
//!
//! * The settlement GATE — that an over-authorized stitch is REFUSED — is the operable shadow of
//!   `Dregg2.Circuit.SettlementSoundness.settlement_soundness`: a stitch may only confer authority the
//!   author held AT THE SETTLEMENT TIP. A stitch that tries to carry a cap the author did not hold
//!   (or that the settlement view has revoked) is rejected — authority is read at settlement, not at
//!   the branch.
//!
//! # What this is NOT
//!
//! Not the executor, the circuit, the ledger, or the cap kernel. It is the two-turn control model:
//! the `VirtualBranch` type, the confinement check, and the (pushout-shaped, explicitly-lossy)
//! stitch with its settlement gate. The real cap gate is the Lean `Exec.Kernel`; the real merge is
//! the Lean `DocMerge`. This module carries only enough structure to make the two teeth bite
//! (a branch side-effect is imaginary until stitched; an over-authorized stitch is refused).

use std::collections::BTreeMap;

/// A capability the branch author holds. Modeled at the granularity the confinement check needs:
/// a cap names a target cell and whether it confers write/debit reach to that cell.
///
/// This is the operable shadow of `Confinement.reachesCell` over `Authority.Caps`: a cap with
/// `debit_reach = true` to a MAIN cell is exactly what `BranchHonest`/`Confined` forbids (the
/// endpoint-with-write disjunct of `authorizedB_src_forces_reach`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BranchCap {
    /// The cell this cap reaches.
    pub target: u64,
    /// Whether the cap confers debit (drain) reach to `target`. A node-cap or a write-endpoint cap
    /// over `target` sets this; a read-only view does not.
    pub debit_reach: bool,
}

/// The MAIN frontier: the set of cells that belong to official reality (the cells a branch must be
/// confined away from). Mirrors `Confinement.attackerFrontier : Finset CellId` — here the "attacker"
/// is the branch, and the frontier is main.
pub type MainFrontier = std::collections::BTreeSet<u64>;

/// A single attempted branch turn: an actor debiting a `src` cell.
///
/// The confinement check governs whether the kernel `authorizedB` gate would grant the debit. We
/// model just the (`actor`, `src`) the gate inspects — the rest of the turn is irrelevant to the
/// no-drain tooth.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BranchDebit {
    /// The cell authoring the turn (the branch author).
    pub actor: u64,
    /// The cell being debited (drained).
    pub src: u64,
}

/// **The `EnterVirtualization` effect, as a control object.** A cap-confined fork of a PAST config
/// into a `Virtual` world. The branch holds ONLY branch-caps; its confinement away from `main` is
/// the well-formedness fact that makes its side-effects structurally imaginary.
///
/// `stratum` records the depth in the firmament cap-tower: a top-level branch is `stratum = 0`; a
/// branch-in-branch is `stratum = 1`, confined away from a frontier that INCLUDES the outer main
/// (confinement composes — `branch_in_branch_cannot_drain`).
#[derive(Clone, Debug)]
pub struct VirtualBranch {
    /// The author of this branch (the forking party).
    pub author: u64,
    /// The MAIN frontier this branch must be confined away from. For a nested branch this includes
    /// the outer frontier (the larger `M₂ ⊇ M₁` of `branch_in_branch_cannot_drain`).
    pub main: MainFrontier,
    /// The branch-caps the author holds. For `EnterVirtualization` to be HONEST, none of these may
    /// confer debit reach to a `main` cell.
    pub caps: Vec<BranchCap>,
    /// Depth in the firmament cap-tower (0 = top-level branch).
    pub stratum: u32,
}

impl VirtualBranch {
    /// Open a top-level virtual branch off a past config, confined away from `main`.
    pub fn enter(author: u64, main: MainFrontier, caps: Vec<BranchCap>) -> Self {
        Self { author, main, caps, stratum: 0 }
    }

    /// **The confinement check — `BranchHonest M caps author`.** True iff the author is confined
    /// away from `main`: it is not itself a main cell (owns none of them as identity) AND it reaches
    /// no main cell via a debit-cap. This is *exactly* `Confinement.Confined`:
    /// `actor ∉ A ∧ ∀ a ∈ A, ¬ reachesCell caps actor a`.
    ///
    /// An `EnterVirtualization` whose author is NOT confined is a protocol violation (the
    /// `unconfined_branch_can_drain` polarity) — such a "branch" CAN drain main and must be refused.
    pub fn confined(&self) -> bool {
        // (i) the author is not itself a main cell.
        if self.main.contains(&self.author) {
            return false;
        }
        // (ii) no held cap confers debit reach to a main cell.
        !self.caps.iter().any(|c| c.debit_reach && self.main.contains(&c.target))
    }

    /// **The no-drain tooth — the operable `branch_cannot_drain_main`.** Decides whether the kernel
    /// gate would ADMIT this debit. A confined branch may debit a cell it owns or reaches, but NEVER
    /// a main cell — so a debit whose `src ∈ main` is REFUSED whenever the author is confined.
    ///
    /// Returns `true` iff the debit is admitted. The contract proved in Lean:
    /// `confined() ∧ src ∈ main ⟹ admits_debit == false` (a confined branch cannot drain main).
    pub fn admits_debit(&self, debit: BranchDebit) -> bool {
        debug_assert_eq!(debit.actor, self.author, "the branch debit must be authored by the branch");
        let src_is_main = self.main.contains(&debit.src);
        if self.confined() && src_is_main {
            // confined + main src ⇒ the gate refuses (no ownership, no reaching cap): IMAGINARY.
            return false;
        }
        // Otherwise the gate consults ownership/reach. The branch may debit a cell it owns…
        if debit.src == self.author {
            return true;
        }
        // …or one it reaches by a debit-cap.
        self.caps.iter().any(|c| c.debit_reach && c.target == debit.src)
    }

    /// Whether the given `src`-debit is **structurally imaginary** in this branch: the branch
    /// believes it acted, but no main cell was drained. True iff the debit targets main AND the
    /// branch is confined (so the gate refuses, yet the branch's local view records the experiment).
    /// This is the "errors remain imaginary" integrity claim — a `src ∈ main` debit never reaches
    /// official reality.
    pub fn debit_is_imaginary(&self, debit: BranchDebit) -> bool {
        self.main.contains(&debit.src) && !self.admits_debit(debit)
    }

    /// **Nest a branch-in-branch (one stratum down the cap-tower).** The nested branch is confined
    /// away from a frontier that INCLUDES the outer one (`outer ⊆ main` of the nested branch), so
    /// the no-drain tooth holds at the deeper level by the same check — confinement composes
    /// (`branch_in_branch_cannot_drain`). The nested frontier is the union of the outer frontier and
    /// any inner-parent cells passed in `inner_parent`.
    pub fn nest(&self, nested_author: u64, inner_parent: MainFrontier, nested_caps: Vec<BranchCap>) -> Self {
        let mut nested_main = self.main.clone();
        nested_main.extend(inner_parent);
        Self {
            author: nested_author,
            main: nested_main,
            caps: nested_caps,
            stratum: self.stratum + 1,
        }
    }
}

// ── The HONEST residual (named, never laundered) ──────────────────────────────────────────────
//
// Confinement confines DRAINING and AUTHORITY, NOT INFORMATION. A `confined()` branch can still
// CREDIT (deposit into) a main cell — the *-property "write up" the cap model does not stop
// (`Confinement.confined_can_credit_attacker`, surfaced in BranchStitch as `branch_may_signal_main`).
// So `debit_is_imaginary` is the INTEGRITY claim (main cannot be drained/corrupted by the branch),
// precise and true; it is NOT a confidentiality claim. The deposit-signal and refusal-timing covert
// channels remain open (a deposit-discipline/quota would close them). We do not model a credit here
// precisely because it is NOT confined — modeling it as "imaginary" would be the laundering we refuse.

/// An atom of document state, keyed by an id, carrying a liveness status. Mirrors the `DocGraph`
/// atom layer (`Status` = `.alive` / `.dead`) where conservation conflicts live — the value-bearing
/// layer the stitch reconciles.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Atom {
    /// The atom is present/alive.
    Alive,
    /// The atom is tombstoned (a deletion the branch or main committed).
    Dead,
}

impl Atom {
    /// The `atomJoin` of two optional atoms: Dead-wins over Alive, present-wins over absent. This is
    /// the lattice join `DocMerge.atomJoin` (a deletion is irreversible; the merge settles Dead).
    fn join(a: Option<Atom>, b: Option<Atom>) -> Option<Atom> {
        match (a, b) {
            (None, x) | (x, None) => x,
            (Some(Atom::Dead), _) | (_, Some(Atom::Dead)) => Some(Atom::Dead),
            (Some(Atom::Alive), Some(Atom::Alive)) => Some(Atom::Alive),
        }
    }
}

/// A document graph: the atom layer, keyed. Mirrors `DocMerge.DocGraph` (atoms; the order/fields
/// layers pass through the stitch unchanged, so we model only the value-bearing atom layer the
/// conflict resolution acts on).
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct DocGraph {
    /// Present atoms, keyed by atom id. Absent keys are `none` (not in the map).
    pub atoms: BTreeMap<u64, Atom>,
}

impl DocGraph {
    /// Document inclusion `⊑`: every atom present in `self` is present-and-≤ in `other` (Alive ≤
    /// Alive, anything ≤ Dead — a deletion is "more settled"). The order `DocMerge.⊑` restricts to
    /// the atom layer here.
    pub fn included_in(&self, other: &DocGraph) -> bool {
        self.atoms.iter().all(|(k, &v)| match other.atoms.get(k) {
            None => false,
            Some(&w) => status_le(v, w),
        })
    }

    /// **`merge m b` — the pushout / least upper bound.** Key-wise `atomJoin`. This is
    /// `DocMerge.merge`; `stitch_is_pushout` proves it is the LUB: both legs included, below every
    /// common upper bound.
    pub fn merge(m: &DocGraph, b: &DocGraph) -> DocGraph {
        let mut atoms = BTreeMap::new();
        let keys = m.atoms.keys().chain(b.atoms.keys()).copied();
        for k in keys {
            if let Some(j) = Atom::join(m.atoms.get(&k).copied(), b.atoms.get(&k).copied()) {
                atoms.insert(k, j);
            }
        }
        DocGraph { atoms }
    }

    /// **`restrict K g` — the author's EXPLICIT drop.** Keep `g`'s atom at `i` iff `i ∈ keep`, else
    /// tombstone-by-omission. This is `DocMerge`/`BranchStitch.restrict`: the kept set is EXACTLY
    /// `keep` (`stitch_drop_explicit`) and the result lies BELOW the full graph
    /// (`stitch_drop_is_below`) — you cannot conjure value by dropping; the omission is visible.
    pub fn restrict(&self, keep: &std::collections::BTreeSet<u64>) -> DocGraph {
        DocGraph {
            atoms: self.atoms.iter().filter(|(k, _)| keep.contains(k)).map(|(&k, &v)| (k, v)).collect(),
        }
    }
}

/// `Status.le`: Alive ≤ Alive, x ≤ Dead, Dead ≰ Alive. The atom-layer order of `DocMerge`.
fn status_le(a: Atom, b: Atom) -> bool {
    matches!((a, b), (Atom::Alive, Atom::Alive) | (_, Atom::Dead))
}

/// A cap a stitch would confer back into main — the authority the settlement carries. The
/// settlement gate checks this against what the author HELD AT THE SETTLEMENT TIP.
pub type StitchCap = BranchCap;

/// **The `Stitch` effect, as a control object.** Reconcile a branch graph `b` into a main graph `m`,
/// optionally conferring back caps the branch produced, gated by Settlement Soundness.
///
/// The result is the pushout `merge(m, b)` (optionally an explicit author drop). The settlement gate
/// (`settle`) refuses any conferred cap the author did not hold at the settlement tip — authority is
/// read at SETTLEMENT, not at branch time.
#[derive(Clone, Debug)]
pub struct Stitch {
    /// The main graph the branch reconciles against.
    pub main: DocGraph,
    /// The branch's reconciliation graph (its discoveries + experiments).
    pub branch: DocGraph,
    /// The caps the stitch would confer back into main (the branch's claimed new authority).
    pub conferred: Vec<StitchCap>,
}

/// The outcome of a settlement gate check.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SettleOutcome {
    /// The stitch settled: here is the pushout-correct merged graph.
    Settled(DocGraph),
    /// The stitch was REFUSED: a conferred cap was not held at the settlement tip (over-authorized),
    /// naming the offending target. Authority is read at settlement, not at the branch.
    Refused { over_authorized_target: u64 },
}

impl Stitch {
    /// The clean (non-dropped) pushout of `main` and `branch`: `merge(m, b)`. Proven the LUB by
    /// `stitch_is_pushout`. (The settlement gate is applied separately by [`Self::settle`].)
    pub fn pushout(&self) -> DocGraph {
        DocGraph::merge(&self.main, &self.branch)
    }

    /// **The settlement gate — the operable shadow of `settlement_soundness`.** A stitch may confer
    /// only authority the author HELD AT THE SETTLEMENT TIP. `settlement_held` is the author's
    /// authority as read at the finalized tip (the settlement view, after any revocation). A
    /// conferred cap whose target/reach is not in `settlement_held` is OVER-AUTHORIZED and the whole
    /// stitch is REFUSED — authority is evaluated at settlement, not at branch time.
    ///
    /// On acceptance, returns the pushout, optionally after an explicit author drop `keep`.
    pub fn settle(
        &self,
        settlement_held: &[StitchCap],
        keep: Option<&std::collections::BTreeSet<u64>>,
    ) -> SettleOutcome {
        // The settlement gate: every conferred cap must be held at the settlement tip.
        for c in &self.conferred {
            let held = settlement_held
                .iter()
                .any(|h| h.target == c.target && (h.debit_reach || !c.debit_reach));
            if !held {
                return SettleOutcome::Refused { over_authorized_target: c.target };
            }
        }
        let merged = self.pushout();
        let result = match keep {
            Some(k) => merged.restrict(k),
            None => merged,
        };
        SettleOutcome::Settled(result)
    }
}

/// A cross-party stitch is a partial turn with HOLES: the I-confluent parts merge clean, but a
/// genuine conflict awaits the *other* party's resolution value. We reuse the held-promise guarded
/// hole shape ([`crate::held_promise::Hole`]) — the resolution is EAGER in shape (which atom, whose
/// write, under which guard) and LAZY in value (the other party's late fill). A strong (open-δ) hole
/// is inexpressible, exactly as in `held_promise`.
///
/// This is a thin alias to make the reuse explicit at the type level; the lifecycle lives in
/// [`crate::held_promise::HeldPromise`].
pub type CrossPartyResolution = crate::held_promise::HeldPromise;

#[cfg(test)]
mod tests {
    use super::*;

    fn main_frontier(cells: &[u64]) -> MainFrontier {
        cells.iter().copied().collect()
    }

    // ── TOOTH 1 — a branch side-effect is IMAGINARY until stitched (both polarities) ────────────

    /// TRUE polarity: a CONFINED branch's debit of a MAIN cell is refused — structurally imaginary.
    /// `confined() ∧ src ∈ main ⟹ ¬admits_debit ∧ debit_is_imaginary`. The integrity half of
    /// `branch_cannot_drain_main`.
    #[test]
    fn confined_branch_main_debit_is_imaginary() {
        // Author cell 7, confined away from main = {1, 2}; holds only a branch-cap to cell 99.
        let branch = VirtualBranch::enter(
            7,
            main_frontier(&[1, 2]),
            vec![BranchCap { target: 99, debit_reach: true }],
        );
        assert!(branch.confined(), "the author owns no main cell and reaches none — confined");

        let drain_main = BranchDebit { actor: 7, src: 1 }; // src = 1 ∈ main
        assert!(!branch.admits_debit(drain_main), "a confined branch cannot drain a main cell");
        assert!(branch.debit_is_imaginary(drain_main), "the main-debit is structurally imaginary");
    }

    /// FALSE polarity (the hypothesis is LOAD-BEARING): drop confinement — let the "branch" hold a
    /// debit-cap to a MAIN cell (a protocol violation) — and the SAME main-debit IS admitted. This
    /// is `unconfined_branch_can_drain`: without `BranchHonest`/`Confined`, main CAN be drained, so
    /// the tooth is not vacuous.
    #[test]
    fn unconfined_branch_can_drain_main() {
        // Same author, but now it illicitly holds a debit-cap to main cell 1.
        let branch = VirtualBranch::enter(
            7,
            main_frontier(&[1, 2]),
            vec![BranchCap { target: 1, debit_reach: true }], // reaches a MAIN cell ⇒ NOT confined
        );
        assert!(!branch.confined(), "holding a debit-cap to main breaks confinement (a violation)");

        let drain_main = BranchDebit { actor: 7, src: 1 };
        assert!(branch.admits_debit(drain_main), "an un-confined branch CAN drain main (load-bearing)");
        assert!(!branch.debit_is_imaginary(drain_main), "the drain is REAL — not imaginary");
    }

    /// A confined branch may still act WITHIN itself: debiting a cell it owns (or reaches off-main)
    /// is admitted and is NOT imaginary. So "imaginary" is precisely the main-debit, never the
    /// branch-local one (the branch spends only branch value — `branch_main_src_clean`).
    #[test]
    fn confined_branch_local_debit_is_real() {
        let branch = VirtualBranch::enter(
            7,
            main_frontier(&[1, 2]),
            vec![BranchCap { target: 99, debit_reach: true }],
        );
        let own = BranchDebit { actor: 7, src: 7 }; // debit a cell it owns
        assert!(branch.admits_debit(own), "the branch may spend its own value");
        assert!(!branch.debit_is_imaginary(own), "a branch-local debit is real, not imaginary");

        let reach = BranchDebit { actor: 7, src: 99 }; // debit a branch cell it reaches
        assert!(branch.admits_debit(reach), "the branch may debit a branch cell it reaches");
        assert!(!branch.debit_is_imaginary(reach), "a reached branch-debit is real (off-main)");
    }

    /// Confinement COMPOSES: a branch-in-branch confined away from a frontier INCLUDING the outer
    /// main cannot drain the OUTER main either (`branch_in_branch_cannot_drain`). The tooth holds one
    /// stratum down — the firmament cap-tower is fractal.
    #[test]
    fn nested_branch_cannot_drain_outer_main() {
        let outer = VirtualBranch::enter(7, main_frontier(&[1]), vec![]);
        // Inner branch authored by cell 8, with inner-parent {50} added to the frontier.
        let inner = outer.nest(8, main_frontier(&[50]), vec![]);
        assert_eq!(inner.stratum, 1, "one stratum down the cap-tower");
        assert!(inner.confined(), "the nested branch is confined away from the union frontier");
        assert!(inner.main.contains(&1), "the nested frontier INCLUDES the outer main");

        let drain_outer = BranchDebit { actor: 8, src: 1 }; // 1 is the OUTER main cell
        assert!(!inner.admits_debit(drain_outer), "a nested branch cannot drain the OUTER main");
        assert!(inner.debit_is_imaginary(drain_outer), "the outer-main debit is imaginary at depth");
    }

    // ── TOOTH 2 — an over-authorized stitch is REFUSED (both polarities) ────────────────────────

    /// TRUE polarity (refusal bites): a stitch that confers a cap the author did NOT hold at the
    /// settlement tip is REFUSED — authority read at settlement. The operable shadow of
    /// `settlement_soundness`'s authority-live-at-settlement.
    #[test]
    fn over_authorized_stitch_is_refused() {
        let stitch = Stitch {
            main: DocGraph::default(),
            branch: DocGraph::default(),
            // The branch CLAIMS a debit-cap to main cell 1…
            conferred: vec![BranchCap { target: 1, debit_reach: true }],
        };
        // …but the author held NOTHING reaching cell 1 at the settlement tip (e.g. it was revoked).
        let settlement_held: Vec<StitchCap> = vec![BranchCap { target: 42, debit_reach: true }];
        let outcome = stitch.settle(&settlement_held, None);
        assert_eq!(
            outcome,
            SettleOutcome::Refused { over_authorized_target: 1 },
            "a cap not held at settlement is over-authorized ⇒ the stitch is refused"
        );
    }

    /// FALSE polarity (the gate is not always-refuse): a stitch conferring ONLY caps the author held
    /// at the settlement tip SETTLES — and the settled graph is the pushout (the LUB), so the gate
    /// is non-vacuous (it accepts genuine settlements).
    #[test]
    fn well_authorized_stitch_settles_to_pushout() {
        let mut main = DocGraph::default();
        main.atoms.insert(0, Atom::Dead); // main deleted atom 0
        let mut branch = DocGraph::default();
        branch.atoms.insert(0, Atom::Alive); // branch revived it (a conflict)
        branch.atoms.insert(1, Atom::Alive); // branch's discovery

        let stitch = Stitch {
            main: main.clone(),
            branch: branch.clone(),
            conferred: vec![BranchCap { target: 1, debit_reach: true }],
        };
        // The author DID hold a cap reaching cell 1 at the settlement tip.
        let settlement_held: Vec<StitchCap> = vec![BranchCap { target: 1, debit_reach: true }];

        let outcome = stitch.settle(&settlement_held, None);
        let settled = match outcome {
            SettleOutcome::Settled(g) => g,
            SettleOutcome::Refused { .. } => panic!("a well-authorized stitch must settle"),
        };
        // The pushout: Dead-wins at key 0 (a real conflict resolution), branch discovery kept.
        assert_eq!(settled.atoms.get(&0), Some(&Atom::Dead), "Dead-wins join settles the conflict");
        assert_eq!(settled.atoms.get(&1), Some(&Atom::Alive), "the branch discovery is kept (no silent drop)");
        // Pushout legs: both main and branch are included in the settled graph (the cocone).
        assert!(main.included_in(&settled), "nothing main had is silently lost (main leg)");
        assert!(branch.included_in(&settled), "nothing the branch found is dropped (branch leg)");
    }

    /// The explicit, linear-logic-forced DROP: an author resolving by `restrict {0}` STRICTLY loses
    /// the branch discovery at key 1 (`stitch_drop_strict_loss`), and the drop lies BELOW the full
    /// merge (`stitch_drop_is_below`) — you cannot conjure value by dropping; omission is visible.
    #[test]
    fn explicit_drop_strictly_loses_below_the_pushout() {
        let mut main = DocGraph::default();
        main.atoms.insert(0, Atom::Dead);
        let mut branch = DocGraph::default();
        branch.atoms.insert(0, Atom::Alive);
        branch.atoms.insert(1, Atom::Alive);

        let stitch = Stitch { main, branch, conferred: vec![] };
        let full = stitch.pushout();
        let keep: std::collections::BTreeSet<u64> = [0].into_iter().collect();
        let dropped = full.restrict(&keep);

        // Strict loss: atom 1 is gone after the drop, present in the full merge.
        assert!(dropped.atoms.get(&1).is_none(), "the drop removes the branch discovery at key 1");
        assert!(full.atoms.get(&1).is_some(), "the full pushout kept it");
        assert_ne!(dropped, full, "a lossy stitch genuinely loses — the drop is not a no-op");
        // Below: dropping only loses, never conjures.
        assert!(dropped.included_in(&full), "the dropped stitch lies BELOW the full pushout (no conjuring)");
        // Explicit: the kept key is exactly the one in `keep`.
        assert_eq!(dropped.atoms.keys().copied().collect::<Vec<_>>(), vec![0], "kept keys are exactly K");
    }

    /// A non-drop (`keep` covers every present atom) recovers the full pushout — lossiness is opt-in
    /// (`stitch_no_drop_recovers_pushout`).
    #[test]
    fn no_drop_recovers_the_full_pushout() {
        let mut branch = DocGraph::default();
        branch.atoms.insert(0, Atom::Alive);
        branch.atoms.insert(1, Atom::Alive);
        let stitch = Stitch { main: DocGraph::default(), branch, conferred: vec![] };
        let full = stitch.pushout();
        let keep: std::collections::BTreeSet<u64> = full.atoms.keys().copied().collect();
        assert_eq!(full.restrict(&keep), full, "covering every key recovers the full pushout");
    }
}
