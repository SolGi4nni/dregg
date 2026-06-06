/-
# Dregg2.Verify.Contract — the Hatchery's CONTRACT object (HATCHERY.md Tier 3).

Tiers 1+2 (`Verify/Tactics.lean`, `Verify/Frames.lean`) built the Hatchery ENGINE: the
boilerplate-killing tactics (`carry_forever` / `exec_frame`) and the reusable forest-monotone
combinator (`cellNextA_carries_rel` / `livingCellA_carries_rel`) that collapse the hand-typed
`livingCellA_carries` skeleton every shipped crown re-proves. This module is Tier 3: it packages a
verified app invariant into a FIRST-CLASS OBJECT — a `CellContract` — so a crown becomes a *value*
you can name, store, render, and re-use, not a bespoke theorem buried in an app file.

## What a `CellContract` IS (and why it is the right object)

A `CellContract` bundles the EXACT pair the Hatchery's parametric crown
(`Exec.livingCellA_carries`, `Exec/CellCarry.lean:57`) consumes:

* `Inv : RecChainedState → Prop` — a state predicate on the REAL 46-effect kernel state, and
* `step_ob : ∀ s cf, Inv s → Inv (cellNextA s cf)` — the app's ONE real obligation: that a single
  living-cell step (`cellNextA`, the commit-on-`some` / stay-put-on-`none` real executor step,
  `Exec/CellReal.lean:41`) preserves `Inv`.

That is *all* an app author must supply. `CellContract.forever` then hands back the unbounded-time,
EVERY-schedule carry `∀ n, Inv (trajA s sched n)` for FREE, by feeding `(Inv, step_ob)` straight to
`livingCellA_carries`. `CellContract.always` lifts the SAME contract into the LTL `□` modality of
`Proof/Temporal.lean` (`Always Inv s sched`) via `always_of_step_invariant` — so a contract is
*simultaneously* a forever-trajectory invariant and a temporal-logic `□`-formula, with no extra proof.

The `shape : SafetyShape` field is a REAL, used tag — not decoration: it classifies the safety
property (grow-only `monotone`, set-`membership` persistence, `constant` observation, or `other`) for
the downstream proof-badge / contract-card widget (`Dregg2/Widget/ContractView.lean`, which renders a
card *by category*) and for the §-eval demonstration that the three shipped instances carry GENUINELY
DISTINCT shapes (`logAppendOnly = monotone`, `conserved = constant`, `revokedPersists = membership` —
`#guard`-distinguished below). It gates nothing in the proofs; the proofs stand on `Inv`/`step_ob`.

## What this is NOT

A `CellContract` carries a SINGLE state-predicate invariant along the living cell's `trajA`. It is
NOT a Hoare/WP `{P} cf {Q}` over an arbitrary forest (that is `Proof/WP.lean`'s direction, and is not
yet lifted to the forest executor), NOT a branching/bisimulation property (`CoinductiveAdversary`),
and NOT a liveness/fairness statement (`◇`-progress needs a fairness hypothesis on `SchedA`). It is
exactly the reusable, first-class form of the SAFETY (`□`) crowns the Hatchery mechanizes.

Discipline: NO `sorry`/`admit`/`native_decide`/SMT. Every keystone (`CellContract.forever`,
`CellContract.always`, the three concrete contracts) is `#assert_axioms`-pinned to the kernel triple
`{propext, Classical.choice, Quot.sound}` at the foot of the file.
-/
import Dregg2.Verify.Tactics
import Dregg2.Exec.CellExecutor
import Dregg2.Proof.Temporal
import Dregg2.Apps.NameService
import Dregg2.Apps.Subscription

namespace Dregg2.Verify

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (fma0)
open Dregg2.Exec.FullForest
open Dregg2.Proof.Temporal (Always always_of_step_invariant)

/-! ## §1 — `SafetyShape`: the (real, used) classification tag for the contract card. -/

/-- **`SafetyShape`** — the qualitative shape of a carried safety property. A REAL tag: it is the
category the downstream contract-card widget (`Widget/ContractView.lean`) renders by, and it carries
genuinely distinct information across the shipped instances (`#guard`-distinguished in §4). It gates
NOTHING in the proofs — `CellContract`'s force is entirely in `Inv`/`step_ob` — but it is not
decorative either: it is consumed by the widget layer and by the non-triviality demonstration.

* `monotone`   — a grow-only field (append-only log, grow-only registry): `base R proj`, `R` reflexive-
  transitive, the field only moves forward (e.g. `logAppendOnly`, the registry-grow crowns).
* `membership` — a set-membership persistence (`x ∈ field` stays true): the OS revocation
  root-of-trust shape (`revokedPersists`).
* `constant`   — an observation never drifts (`obs · = obs s`): the per-asset conservation badge
  (`conserved`).
* `other`      — any other state-predicate safety. -/
inductive SafetyShape
  | monotone
  | membership
  | constant
  | other
  deriving DecidableEq, Repr

/-! ## §2 — `CellContract`: the first-class verified-invariant object. -/

/-- **`CellContract E`** — a verified app invariant on executor `E`, packaged as a value. -/
structure CellContract (E : CellExecutor) where
  Inv : RecChainedState → Prop
  step_ob : ∀ s c, Inv s → Inv (E.next s c)
  shape : SafetyShape := .other

/-- Lift a contract along a one-step preservation implication. -/
def CellContract.lift {E E' : CellExecutor} (C : CellContract E)
    (lift_pres : ∀ s c, C.Inv s → C.Inv (E'.next s c)) : CellContract E' where
  Inv := C.Inv
  step_ob := lift_pres
  shape := C.shape

namespace CellContract

/-- Forever carry — parametric over any `CellExecutor` with a `CellCarries` instance. -/
theorem forever {E : CellExecutor} [CellCarries E] (C : CellContract E) {s : RecChainedState}
    (h : C.Inv s) (sched : E.TurnSched) :
    ∀ n, C.Inv (E.traj s sched n) :=
  CellCarries.carries C.Inv C.step_ob s h sched

end CellContract

namespace Production

noncomputable abbrev Executor := CellExecutor.production
abbrev Sched := SchedG
abbrev Contract := CellContract Executor

theorem always (C : Contract) {s : RecChainedState} (h : C.Inv s) (sched : Sched) :
    AlwaysG C.Inv s sched :=
  alwaysG_of_step_invariant C.Inv C.step_ob s h sched

/-- Lift a kernel-forest contract to production via the commit-path erasure bridge. -/
noncomputable def liftFromKernelForest (C : CellContract CellExecutor.kernelForest) : Contract :=
  C.lift fun s cg h =>
    CellExecutor.production_erases_kernelForest C.Inv
      (fun s' cf h' => by simpa [CellExecutor.kernelForest_next_eq] using C.step_ob s' cf h') s cg h

end Production

/-! Internal: contracts whose `step_ob` is discharged on the auth-stripped kernel forest.
Used only by catalog macro elaboration and the Regression suite's bidirectional witnesses against
legacy `trajA` crowns — NOT the public Hatchery API. -/

namespace KernelForest

noncomputable abbrev Executor := CellExecutor.kernelForest
abbrev Sched := SchedA
abbrev Contract := CellContract Executor

theorem always (C : Contract) {s : RecChainedState} (h : C.Inv s) (sched : Sched) :
    Always C.Inv s sched :=
  always_of_step_invariant C.Inv
    (fun a cf h' => by simpa [CellExecutor.kernelForest_next_eq] using C.step_ob a cf h')
    s h sched

def logAppendOnly (s0 : RecChainedState) : Contract where
  Inv s := s0.log.length ≤ s.log.length
  step_ob s cf h := by
    rw [CellExecutor.kernelForest_next_eq]
    simp only [cellNextA]
    rcases hc : execFullForestA s cf.1 with _ | s'
    · simp only [Option.getD_none]; exact h
    · simp only [Option.getD_some]
      exact le_trans h (execFullForestA_logMono s s' cf.1 hc)
  shape := .monotone

def conserved (s0 : RecChainedState) : Contract where
  Inv s := cellObsA s = cellObsA s0
  step_ob a cf h := by
    rw [CellExecutor.kernelForest_next_eq, cellObsA_next]
    exact h
  shape := .constant

def revokedPersists (x : Nat) : Contract where
  Inv s := x ∈ s.kernel.revoked
  step_ob a cf h := by
    rw [CellExecutor.kernelForest_next_eq]
    unfold cellNextA
    cases hc : execFullForestA a cf.1 with
    | some a' => simp only [Option.getD_some]
                 exact Dregg2.Apps.Identity.execFullForestA_revoked_grow a a' cf.1 hc h
    | none    => simp only [Option.getD_none]; exact h
  shape := .membership

def nameRegisteredContract (name owner : Dregg2.Apps.NameService.Name) : Contract where
  Inv s := Dregg2.Apps.NameService.isRegistered s name owner = true
  step_ob a cf h := by
    rw [CellExecutor.kernelForest_next_eq]
    unfold cellNextA
    cases hc : execFullForestA a cf.1 with
    | some a' => simp only [Option.getD_some]
                 exact Dregg2.Apps.NameService.nameservice_step_preserves a a' cf.1 name owner hc h
    | none    => simp only [Option.getD_none]; exact h
  shape := .membership

def subWFContract : Contract where
  Inv s := Dregg2.Apps.Subscription.subWF s.kernel
  step_ob a cf h := by
    rw [CellExecutor.kernelForest_next_eq]
    unfold cellNextA
    cases hc : execFullForestA a cf.1 with
    | some a' => simp only [Option.getD_some]
                 exact Dregg2.Apps.Subscription.execFullForestA_subWF_preserved a a' cf.1 hc h
    | none    => simp only [Option.getD_none]; exact h
  shape := .other

/-- **`subsetNullifiersContract base` — the `⊆`-shaped grow-only nullifier contract.** -/
def subsetNullifiersContract (base : List Nat) : Contract where
  Inv s := base ⊆ s.kernel.nullifiers
  step_ob a cf h := by
    rw [CellExecutor.kernelForest_next_eq]
    unfold cellNextA
    cases hc : execFullForestA a cf.1 with
    | some a' => simp only [Option.getD_some]
                 exact List.Subset.trans h (execFullForestA_nullifiers_grow a a' cf.1 hc)
    | none    => simp only [Option.getD_none]; exact h
  shape := .membership

/-- **`subsetCommitmentsContract base` — the `⊆`-shaped grow-only commitment contract.** -/
def subsetCommitmentsContract (base : List Nat) : Contract where
  Inv s := base ⊆ s.kernel.commitments
  step_ob a cf h := by
    rw [CellExecutor.kernelForest_next_eq]
    unfold cellNextA
    cases hc : execFullForestA a cf.1 with
    | some a' => simp only [Option.getD_some]
                 exact List.Subset.trans h (execFullForestA_commitments_grow a a' cf.1 hc)
    | none    => simp only [Option.getD_none]; exact h
  shape := .membership

end KernelForest

open Production (Contract Sched liftFromKernelForest)

/-! ## §3 — Production contracts (lifted from kernel-forest proofs via erasure). -/

noncomputable def logAppendOnly (s0 : RecChainedState) : Contract :=
  liftFromKernelForest (KernelForest.logAppendOnly s0)

noncomputable def conserved (s0 : RecChainedState) : Contract :=
  liftFromKernelForest (KernelForest.conserved s0)

noncomputable def revokedPersists (x : Nat) : Contract :=
  liftFromKernelForest (KernelForest.revokedPersists x)

noncomputable def nameRegisteredContract (name owner : Dregg2.Apps.NameService.Name) : Contract :=
  liftFromKernelForest (KernelForest.nameRegisteredContract name owner)

noncomputable def subWFContract : Contract :=
  liftFromKernelForest KernelForest.subWFContract

noncomputable def subsetNullifiersContract (base : List Nat) : Contract :=
  liftFromKernelForest (KernelForest.subsetNullifiersContract base)

noncomputable def subsetCommitmentsContract (base : List Nat) : Contract :=
  liftFromKernelForest (KernelForest.subsetCommitmentsContract base)

/-! ## §3a — The three standing apps, re-expressed as first-class `CellContract`s (HATCHERY.md H3 gate).

`HATCHERY.md`'s H3 gate (`§202`) is *"the 3 apps re-expressed as `CellContract`s, same theorems"* — the
three shipped userspace cell-programs (`Apps/Identity.lean`, `Apps/NameService.lean`,
`Apps/Subscription.lean`), each a hand-written `livingCellA_carries` crown, recovered as a `CellContract`
whose `.forever` reproduces the crown VERBATIM. **Identity** is already covered: it is `revokedPersists`
(`x ∈ ·.kernel.revoked` — the revocation root-of-trust), with its reproduction example in §3′ below. The
other two carry app-specific invariants the bare shape catalog does NOT template (a `commitments.contains`
BOOLEAN; a `∀ q ∈ queues` capacity bound), so each is packaged here as a `CellContract` whose `step_ob`
is the APP'S OWN proved one-step lemma — Tier 3 absorbing an app invariant while still handing back
`forever` for free. NONE is faked: every `step_ob` is a real proof term over the shipped
`execFullForestA`. These two defs are the single source of truth; `Verify/Regression.lean §4–§5` reuses
them for the rigorous BOTH-DIRECTIONS defeq witness against the shipped crowns. -/

/-- **NameService — `.forever` on production trajectories.** The ascribed type IS the
shipped crown's type, so this example witnesses statement-level regression-equality (a registered binding
stays registered at every index of every trajectory), with NO hand temporal proof. -/
example (s : RecChainedState) (name owner : Dregg2.Apps.NameService.Name)
    (hinit : Dregg2.Apps.NameService.isRegistered s name owner = true) (sched : SchedG) :
    ∀ n, Dregg2.Apps.NameService.isRegistered (trajG s sched n) name owner = true :=
  (nameRegisteredContract name owner).forever hinit sched

example (s : RecChainedState) (hinit : Dregg2.Apps.Subscription.subWF s.kernel) (sched : SchedG) :
    ∀ n, Dregg2.Apps.Subscription.subWF (trajG s sched n).kernel :=
  subWFContract.forever hinit sched

/-! ## §3′ — Using a contract: `forever` / `always` are method calls, not re-proofs.

The contract's whole point. Naming a contract and calling `.forever` / `.always` reproduces — with
NO bespoke proof — the shipped hand crowns. These `example`s are build-checked regressions: the
contract object delivers the SAME forever / `□` statements as `CellCarry`, `CellReal`, `Identity`. -/

/-- A contract delivers the hand crown `Exec.livingCellA_logMono`'s statement via `.forever`. -/
example (s : RecChainedState) (sched : SchedG) :
    ∀ n, s.log.length ≤ (trajG s sched n).log.length :=
  (logAppendOnly s).forever (le_refl _) sched

example (s : RecChainedState) (sched : SchedG) :
    AlwaysG (fun s' => s.log.length ≤ s'.log.length) s sched :=
  Production.always (logAppendOnly s) (le_refl _) sched

example (s : RecChainedState) (sched : SchedG) :
    ∀ n, cellObsA (trajG s sched n) = cellObsA s :=
  (conserved s).forever rfl sched

example (x : Nat) (s : RecChainedState) (hinit : x ∈ s.kernel.revoked) (sched : SchedG) :
    ∀ n, x ∈ (trajG s sched n).kernel.revoked :=
  (revokedPersists x).forever hinit sched

/-- Named production crown for widgets / regression (the `revokedPersists` contract's `.forever`). -/
theorem identity_revoked_forever_production (x : Nat) (s : RecChainedState)
    (hinit : x ∈ s.kernel.revoked) (sched : SchedG) :
    ∀ n, x ∈ (trajG s sched n).kernel.revoked :=
  (revokedPersists x).forever hinit sched

theorem spent_note_never_respent_production (nf : Nat) (s : RecChainedState)
    (hinit : nf ∈ s.kernel.nullifiers) (sched : SchedG) :
    ∀ n, nf ∈ (trajG s sched n).kernel.nullifiers :=
  (subsetNullifiersContract [nf]).forever (List.singleton_subset_iff.mpr hinit) sched

theorem no_double_spend_production (nul0 : List Nat) (s : RecChainedState)
    (hinit : nul0 ⊆ s.kernel.nullifiers) (sched : SchedG) :
    ∀ n, nul0 ⊆ (trajG s sched n).kernel.nullifiers :=
  (subsetNullifiersContract nul0).forever hinit sched

theorem commitments_persist_production (com0 : List Nat) (s : RecChainedState)
    (hinit : com0 ⊆ s.kernel.commitments) (sched : SchedG) :
    ∀ n, com0 ⊆ (trajG s sched n).kernel.commitments :=
  (subsetCommitmentsContract com0).forever hinit sched

theorem nameservice_registration_forever_production (s : RecChainedState)
    (name owner : Dregg2.Apps.NameService.Name)
    (hinit : Dregg2.Apps.NameService.isRegistered s name owner = true) (sched : SchedG) :
    ∀ n, Dregg2.Apps.NameService.isRegistered (trajG s sched n) name owner = true :=
  (nameRegisteredContract name owner).forever hinit sched

theorem subscription_wellformed_forever_production (s : RecChainedState)
    (hinit : Dregg2.Apps.Subscription.subWF s.kernel) (sched : SchedG) :
    ∀ n, Dregg2.Apps.Subscription.subWF (trajG s sched n).kernel :=
  subWFContract.forever hinit sched

theorem log_mono_forever_production (s : RecChainedState) (sched : SchedG) :
    ∀ n, s.log.length ≤ (trajG s sched n).log.length :=
  (logAppendOnly s).forever (le_refl _) sched

/-! ## §4 — Non-vacuity guards — the contracts are substantive and the tag carries distinct info.

`logAppendOnly`'s `Inv` bounds a STRICTLY-GROWING quantity: a real committed transfer (`transferCF`,
actor 0 transfers 30 of asset 0 from cell 0 to cell 1) grows the audit log `0 → 1`, so the carried `≤`
is a bound on a quantity that genuinely moves — not a trivially-true `x = x`. And the three shipped
contracts carry three DISTINCT `SafetyShape`s, so the tag is real classifying data, not a constant. -/

#guard (fma0.log.length == 0)
#guard ((execFullForestA fma0 transferCF.1).map (fun s' => s'.log.length) == some 1)
#guard ((execFullForestA fma0 transferCF.1).map
          (fun s' => decide (fma0.log.length < s'.log.length)) == some true)
#guard ((execFullForestA fma0 transferCF.1).map
          (fun s' => decide (fma0.log.length ≤ s'.log.length)) == some true)
#guard ((KernelForest.logAppendOnly fma0).shape == SafetyShape.monotone)
#guard ((KernelForest.conserved fma0).shape == SafetyShape.constant)
#guard ((KernelForest.revokedPersists 42).shape == SafetyShape.membership)
#guard ((KernelForest.logAppendOnly fma0).shape ≠ (KernelForest.conserved fma0).shape)
#guard ((KernelForest.conserved fma0).shape ≠ (KernelForest.revokedPersists 42).shape)
#guard (Dregg2.Apps.NameService.isRegistered fma0
          Dregg2.Apps.NameService.aliceName Dregg2.Apps.NameService.aliceOwner == false)
#guard (Dregg2.Apps.NameService.afterRegister.map (fun s => Dregg2.Apps.NameService.isRegistered s
          Dregg2.Apps.NameService.aliceName Dregg2.Apps.NameService.aliceOwner) == some true)
#guard ((KernelForest.nameRegisteredContract Dregg2.Apps.NameService.aliceName
          Dregg2.Apps.NameService.aliceOwner).shape == SafetyShape.membership)
#guard ((execFullForestA fmaDeleg Dregg2.Apps.Subscription.subForest).map
          (fun s => s.kernel.queues.all (fun q => decide (q.buffer.length ≤ q.capacity))) == some true)
#guard (KernelForest.subWFContract.shape == SafetyShape.other)
#guard ((KernelForest.nameRegisteredContract 1 100).shape ≠ KernelForest.subWFContract.shape)

/-! ## §5 — Axiom hygiene — the contract object + its methods + the instances, kernel-triple clean. -/

#assert_axioms CellContract.forever
#assert_axioms Production.always
#assert_axioms Production.liftFromKernelForest
#assert_axioms logAppendOnly
#assert_axioms conserved
#assert_axioms revokedPersists
#assert_axioms nameRegisteredContract
#assert_axioms subWFContract
#assert_axioms identity_revoked_forever_production
#assert_axioms spent_note_never_respent_production
#assert_axioms no_double_spend_production
#assert_axioms commitments_persist_production
#assert_axioms nameservice_registration_forever_production
#assert_axioms subscription_wellformed_forever_production
#assert_axioms log_mono_forever_production

end Dregg2.Verify
