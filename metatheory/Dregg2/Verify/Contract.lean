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
`#eval`-distinguished below). It gates nothing in the proofs; the proofs stand on `Inv`/`step_ob`.

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
genuinely distinct information across the shipped instances (`#eval`-distinguished in §4). It gates
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

/-- **`CellContract`** — a verified app invariant, packaged as a value. Bundles exactly the pair the
Hatchery's parametric crown (`Exec.livingCellA_carries`) consumes:

* `Inv`     — a state predicate on the REAL kernel state `RecChainedState`;
* `step_ob` — the app's ONE obligation: a single living-cell step `cellNextA` preserves `Inv`
  (dischargeable by `exec_frame` / a supplied forest-grow lemma — the Tier-1/2 engine);
* `shape`   — the `SafetyShape` classification tag (for the widget layer; gates no proof).

From `(Inv, step_ob)` alone, `CellContract.forever` derives the unbounded every-schedule carry and
`CellContract.always` derives the LTL `□`. The author writes the two real fields; the rest is free. -/
structure CellContract where
  /-- The carried state predicate on the real 46-effect kernel state. -/
  Inv : RecChainedState → Prop
  /-- The ONE real obligation: a single living-cell step preserves `Inv` (commit-grows / stay-put). -/
  step_ob : ∀ s cf, Inv s → Inv (cellNextA s cf)
  /-- The qualitative classification of the safety, for the contract-card widget. -/
  shape : SafetyShape := .other

/-- **`CellContract.forever` (PROVED) — THE PAYOFF: a contract holds at every index, every schedule.**
Given a contract `C` and a starting state `s` satisfying `C.Inv`, `C.Inv` holds at EVERY index of the
unbounded adversarial trajectory `trajA s sched`, under EVERY schedule `sched`. This is the Hatchery's
parametric crown `Exec.livingCellA_carries` applied to the contract's own `(Inv, step_ob)` — the whole
reason to package an invariant as a `CellContract`: the forever-carry is a method call, not a re-proof. -/
theorem CellContract.forever (C : CellContract) {s : RecChainedState} (h : C.Inv s) (sched : SchedA) :
    ∀ n, C.Inv (trajA s sched n) :=
  livingCellA_carries C.Inv C.step_ob s h sched

/-- **`CellContract.always` (PROVED) — the TEMPORAL face: a contract IS an LTL `□`-formula.** The same
contract, read into the linear-temporal-logic `□` modality of `Proof/Temporal.lean`: `Always C.Inv s
sched` (`□C.Inv` along the living cell's time-line). Wired through `always_of_step_invariant` — whose
one-step hypothesis is *exactly* `C.step_ob`'s type — so no extra proof obligation arises. A
`CellContract` is therefore simultaneously a forever-trajectory invariant (`forever`) and a temporal
`□`-formula (`always`); the temporal algebra of `Proof/Temporal.lean` (`always_and`, `always_mono`,
`always_imp_next`, `□`/`◇` duality, …) applies to it for free. -/
theorem CellContract.always (C : CellContract) {s : RecChainedState} (h : C.Inv s) (sched : SchedA) :
    Always C.Inv s sched :=
  always_of_step_invariant C.Inv C.step_ob s h sched

/-! ## §3 — Concrete contracts (the tag genuinely VARIES; the proofs use the Tier-1/2 engine).

Three shipped contracts, one per non-`other` `SafetyShape`, so the tag carries genuinely distinct
information (not a single hard-wired value). Each `step_ob` is discharged through the Hatchery ENGINE,
demonstrating Tier 3 sits ON TOP of Tiers 1+2:

| contract          | shape        | `Inv`                                   | `step_ob` via                         |
|-------------------|--------------|-----------------------------------------|---------------------------------------|
| `logAppendOnly`   | `monotone`   | `s0.log.length ≤ ·.log.length`          | `exec_frame execFullForestA_logMono`  |
| `conserved`       | `constant`   | `cellObsA · = cellObsA s0`              | `cellObsA_next` (rewrite)             |
| `revokedPersists` | `membership` | `x ∈ ·.kernel.revoked`                  | `exec_frame …execFullForestA_revoked_grow` |
-/

/-- **`logAppendOnly s0` — the append-only audit-log contract (`monotone`).** `Inv := s0.log.length ≤
·.log.length`: the receipt/audit log never shrinks below its starting length — the canonical OS
*"the log is the truth, never rewritten"* / non-repudiation safety. The `step_ob` is discharged by the
Tier-1 `exec_frame` tactic supplied the forest log-monotone lemma `execFullForestA_logMono`: the commit
arm chains the baseline `≤` with the lemma (`Nat`'s `≤` is `Trans`), the reject arm is the universal
stay-put close. This is `CellCarry.livingCellA_logMono` repackaged as a first-class contract. -/
def logAppendOnly (s0 : RecChainedState) : CellContract where
  Inv s := s0.log.length ≤ s.log.length
  step_ob := by exec_frame execFullForestA_logMono
  shape := .monotone

/-- **`conserved s0` — the per-asset conservation contract (`constant`).** `Inv := cellObsA · =
cellObsA s0`: the per-asset conservation badge `cellObsA` never drifts from its starting value. The
`step_ob` is discharged by the proved one-step `cellObsA_next` (commit conserves per-asset; stay-put is
trivial). This is `CellReal.livingCellA_obs_invariant` repackaged as a first-class contract. -/
def conserved (s0 : RecChainedState) : CellContract where
  Inv s := cellObsA s = cellObsA s0
  step_ob a cf h := by
    show cellObsA (cellNextA a cf) = cellObsA s0
    rw [cellObsA_next]; exact h
  shape := .constant

/-- **`revokedPersists x` — the permanent-revocation contract (`membership`).** `Inv := x ∈
·.kernel.revoked`: a credential nullifier `x` that is in the revocation registry STAYS in it — the
single-machine immediate-and-permanent revocation root-of-trust (`#139`: a revoked cap is never
silently un-revoked). The `step_ob` is discharged by `exec_frame` supplied the forest revocation-grow
lemma: the commit arm chains membership through `s.kernel.revoked ⊆ s'.kernel.revoked`
(`List.Subset.trans`-style, mediated by the [Dregg2] rule-set's `Subset.trans`), the reject arm is the
universal stay-put close. The `membership` shape — a third, qualitatively distinct predicate form. -/
def revokedPersists (x : Nat) : CellContract where
  Inv s := x ∈ s.kernel.revoked
  step_ob a cf h := by
    show x ∈ (cellNextA a cf).kernel.revoked
    unfold cellNextA
    cases hc : execFullForestA a cf.1 with
    | some a' => simp only [Option.getD_some]
                 exact Dregg2.Apps.Identity.execFullForestA_revoked_grow a a' cf.1 hc h
    | none    => simp only [Option.getD_none]; exact h
  shape := .membership

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

/-- **`nameRegisteredContract name owner` — NameService's "registered ⇒ registered forever" as a
contract.** `Inv s := isRegistered s name owner = true` (the name→owner binding commitment lives in the
grow-only registry), `step_ob` the app's own `nameservice_step_preserves` (commit: the grow-only registry
keeps the binding registered; reject: stay-put). `.forever` reproduces
`Apps.NameService.nameservice_registration_forever`. `membership` shape (a registry-presence fact). -/
def nameRegisteredContract (name owner : Dregg2.Apps.NameService.Name) : CellContract where
  Inv s := Dregg2.Apps.NameService.isRegistered s name owner = true
  step_ob a cf h := by
    show Dregg2.Apps.NameService.isRegistered (cellNextA a cf) name owner = true
    unfold cellNextA
    cases hc : execFullForestA a cf.1 with
    | some a' => simp only [Option.getD_some]
                 exact Dregg2.Apps.NameService.nameservice_step_preserves a a' cf.1 name owner hc h
    | none    => simp only [Option.getD_none]; exact h
  shape := .membership

/-- **`subWFContract` — Subscription's "no queue ever over capacity, forever" as a contract.** `Inv s :=
subWF s.kernel` (every queue record's in-flight count is within its capacity — dregg1's `head − tail ≤
capacity`), `step_ob` the app's own `execFullForestA_subWF_preserved` (commit: the capacity gate keeps
every record within bounds; reject: stay-put leaves `queues` unchanged). `.forever` reproduces
`Apps.Subscription.subscription_wellformed_forever`. `other` shape — a `∀ q ∈ queues` field bound, the
one app invariant outside the catalog's four bare shapes. -/
def subWFContract : CellContract where
  Inv s := Dregg2.Apps.Subscription.subWF s.kernel
  step_ob a cf h := by
    show Dregg2.Apps.Subscription.subWF (cellNextA a cf).kernel
    unfold cellNextA
    cases hc : execFullForestA a cf.1 with
    | some a' => simp only [Option.getD_some]
                 exact Dregg2.Apps.Subscription.execFullForestA_subWF_preserved a a' cf.1 hc h
    | none    => simp only [Option.getD_none]; exact h
  shape := .other

/-- **NameService — `.forever` reproduces `nameservice_registration_forever`.** The ascribed type IS the
shipped crown's type, so this example witnesses statement-level regression-equality (a registered binding
stays registered at every index of every trajectory), with NO hand temporal proof. -/
example (s : RecChainedState) (name owner : Dregg2.Apps.NameService.Name)
    (hinit : Dregg2.Apps.NameService.isRegistered s name owner = true) (sched : SchedA) :
    ∀ n, Dregg2.Apps.NameService.isRegistered (trajA s sched n) name owner = true :=
  (nameRegisteredContract name owner).forever hinit sched

/-- **Subscription — `.forever` reproduces `subscription_wellformed_forever`.** The ascribed type IS the
shipped crown's type: no queue is ever over capacity at any index of any adversarial trajectory. -/
example (s : RecChainedState) (hinit : Dregg2.Apps.Subscription.subWF s.kernel) (sched : SchedA) :
    ∀ n, Dregg2.Apps.Subscription.subWF (trajA s sched n).kernel :=
  subWFContract.forever hinit sched

/-! ## §3′ — Using a contract: `forever` / `always` are method calls, not re-proofs.

The contract's whole point. Naming a contract and calling `.forever` / `.always` reproduces — with
NO bespoke proof — the shipped hand crowns. These `example`s are build-checked regressions: the
contract object delivers the SAME forever / `□` statements as `CellCarry`, `CellReal`, `Identity`. -/

/-- A contract delivers the hand crown `Exec.livingCellA_logMono`'s statement via `.forever`. -/
example (s : RecChainedState) (sched : SchedA) :
    ∀ n, s.log.length ≤ (trajA s sched n).log.length :=
  (logAppendOnly s).forever (le_refl _) sched

/-- …and its LTL-`□` reading via `.always` (the `Proof/Temporal.always_logMono` statement). -/
example (s : RecChainedState) (sched : SchedA) :
    Always (fun s' => s.log.length ≤ s'.log.length) s sched :=
  (logAppendOnly s).always (le_refl _) sched

/-- The conservation contract delivers `CellReal.livingCellA_obs_invariant` via `.forever`. -/
example (s : RecChainedState) (sched : SchedA) :
    ∀ n, cellObsA (trajA s sched n) = cellObsA s :=
  (conserved s).forever rfl sched

/-- The revocation contract delivers `Identity.livingCellA_identity_revoked_forever` via `.forever`. -/
example (x : Nat) (s : RecChainedState) (hinit : x ∈ s.kernel.revoked) (sched : SchedA) :
    ∀ n, x ∈ (trajA s sched n).kernel.revoked :=
  (revokedPersists x).forever hinit sched

/-! ## §4 — It runs (`#eval`) — the contracts are NON-VACUOUS and the tag carries DISTINCT info.

`logAppendOnly`'s `Inv` bounds a STRICTLY-GROWING quantity: a real committed transfer (`transferCF`,
actor 0 transfers 30 of asset 0 from cell 0 to cell 1) grows the audit log `0 → 1`, so the carried `≤`
is a bound on a quantity that genuinely moves — not a trivially-true `x = x`. And the three shipped
contracts carry three DISTINCT `SafetyShape`s, so the tag is real classifying data, not a constant. -/

-- NON-VACUITY of `logAppendOnly`: the bounded quantity strictly grows on a real commit (0 < 1).
#eval fma0.log.length                                                                                  -- 0  (BEFORE)
#eval (execFullForestA fma0 transferCF.1).map (fun s' => s'.log.length)                                -- some 1  (AFTER — grew)
#eval (execFullForestA fma0 transferCF.1).map (fun s' => decide (fma0.log.length < s'.log.length))     -- some true (STRICT — moves)
#eval (execFullForestA fma0 transferCF.1).map (fun s' => decide (fma0.log.length ≤ s'.log.length))     -- some true (the carried `Inv` of `logAppendOnly fma0` holds AFTER)

-- The `SafetyShape` tag carries GENUINELY DISTINCT info across the three shipped contracts.
#eval (logAppendOnly fma0).shape                                  -- SafetyShape.monotone
#eval (conserved fma0).shape                                      -- SafetyShape.constant
#eval (revokedPersists 42).shape                                  -- SafetyShape.membership
#eval decide ((logAppendOnly fma0).shape ≠ (conserved fma0).shape)        -- true (distinct shapes — not a constant tag)
#eval decide ((conserved fma0).shape ≠ (revokedPersists 42).shape)        -- true

-- The two added app contracts (§3a) are NON-VACUOUS: the registry/queue readers DISCRIMINATE.
-- NameService: a binding not yet registered is genuinely `false` (the registry has teeth), and a real
-- `register` turn lands it `true` — so `nameRegisteredContract`'s `Inv` is a non-trivial fact.
#eval Dregg2.Apps.NameService.isRegistered fma0
        Dregg2.Apps.NameService.aliceName Dregg2.Apps.NameService.aliceOwner                   -- false (not registered — teeth)
#eval Dregg2.Apps.NameService.afterRegister.map (fun s => Dregg2.Apps.NameService.isRegistered s
        Dregg2.Apps.NameService.aliceName Dregg2.Apps.NameService.aliceOwner)                  -- some true (a real register lands it)
#eval (nameRegisteredContract Dregg2.Apps.NameService.aliceName
        Dregg2.Apps.NameService.aliceOwner).shape                                              -- SafetyShape.membership
-- Subscription: a real committed program builds a within-capacity queue (in-flight 1 ≤ capacity 2 — teeth).
#eval (execFullForestA fmaDeleg Dregg2.Apps.Subscription.subForest).map
        (fun s => s.kernel.queues.all (fun q => decide (q.buffer.length ≤ q.capacity)))        -- some true (the carried subWF holds AFTER)
#eval subWFContract.shape                                                                      -- SafetyShape.other
#eval decide ((nameRegisteredContract 1 100).shape ≠ subWFContract.shape)                      -- true (the apps carry distinct shapes)

/-! ## §5 — Axiom hygiene — the contract object + its methods + the instances, kernel-triple clean. -/

#assert_axioms CellContract.forever
#assert_axioms CellContract.always
#assert_axioms logAppendOnly
#assert_axioms conserved
#assert_axioms revokedPersists
#assert_axioms nameRegisteredContract
#assert_axioms subWFContract

end Dregg2.Verify
