/-
# Dregg2.Verify.Regression — the Hatchery REGRESSION SUITE (HATCHERY.md H4 gate).

This is the proof that the Hatchery **reproduces the crowns, not a weaker shadow**. Tiers 1–4
(`Verify/{Tactics,Frames,Contract,Catalog}.lean`) built the toolkit: the boilerplate-killing tactics,
the `[Dregg2]` aesop rule-set, the first-class `CellContract` object, and the declarative shape catalog
(`monotone_registry%` / `conservation%` / `confinement%` / `automaton_inv%`). H4's gate
(`HATCHERY.md §203`) is: *"each existing crown reduced to a one-line declaration; regression-equal to the
hand proof."* This module discharges that gate against the FULL standing regression suite — the six
shipped hand-written crowns — by re-deriving each through the Hatchery and then **proving the
reproduction is the SAME proposition as the hand crown**, in BOTH directions, with a build-checked
`example` that references the original theorem BY NAME.

## What "regression-equal" means here (the strong reading)

For each crown we do three things:

1. **Reproduce** the crown's `∀ n, Good (trajA …)` statement through the Hatchery — either a catalog
   macro's `.forever`/`.always` (Identity, the single-element nullifier/commitment headlines) or a
   first-class `CellContract` whose `step_ob` is the app's own discharge lemma (NameService,
   Subscription, the `⊆`-shaped no-double-spend / commitment-persistence crowns). NO hand temporal proof
   — `livingCellA_carries` is the free payoff via the contract object.
2. **State the reproduced theorem with the crown's EXACT type** (same binders, same conclusion).
3. **Witness regression-equality both ways**: an `example` of the crown's type closed by OUR theorem,
   and an `example` of OUR type closed by the SHIPPED hand crown (referenced by its real name —
   `Apps.Identity.livingCellA_identity_revoked_forever`, `Exec.livingCellA_no_double_spend`,
   `Apps.NameService.nameservice_registration_forever`, `Apps.Subscription.subscription_wellformed_forever`,
   `Exec.livingCellA_commitments_persist`, `Exec.livingCellA_spent_note_never_respent`). If the Hatchery
   ever drifted from a hand proof's statement, the corresponding direction would fail to typecheck and
   the build would break here. The two `example`s are the H1-style defeq witnesses, scaled to all six.

## The six crowns reproduced

| crown (shipped, hand-written)                                         | reproduced via                          |
|-----------------------------------------------------------------------|-----------------------------------------|
| `Apps.Identity.livingCellA_identity_revoked_forever`                  | `monotone_registry% revoked` `.forever` |
| `Exec.livingCellA_spent_note_never_respent`  (CellNullifier headline) | `monotone_registry% nullifiers` `.forever` |
| `Exec.livingCellA_no_double_spend`  (CellNullifier `⊆` crown)         | `subsetRegistryContract nullifiers` `.forever` |
| `Exec.livingCellA_commitments_persist`  (CellCommit `⊆` crown)        | `subsetRegistryContract commitments` `.forever` |
| `Apps.NameService.nameservice_registration_forever`                   | `nameRegisteredContract` (`CellContract`) `.forever` |
| `Apps.Subscription.subscription_wellformed_forever`                   | `subWFContract` (`CellContract`) `.forever` |

Two crowns (the `⊆`-shaped no-double-spend / commitment-persistence) are stated over a baseline LIST
`com0`/`nul0` rather than the single-element membership the catalog macro covers; for those we build the
analogous first-class `CellContract` (`subsetRegistryContract`) on top of the SAME registered forest-grow
lemmas the macro uses (`execFullForestA_{nullifiers,commitments}_grow`) — Tier 3 generalizing the Tier-4
shape over a subset baseline. NameService (`isRegistered · = true`, a `commitments.contains` boolean) and
Subscription (`subWF ·.kernel`, a `∀ q ∈ queues` bound) are likewise NOT one of the four bare catalog
shapes; each is reproduced via the `CellContract` DEFINED in `Verify/Contract.lean §3a` (the H3
three-apps gate — `nameRegisteredContract` / `subWFContract`, in scope here through the import chain)
whose `step_ob` is the app's own one-step lemma (`nameservice_step_preserves` /
`execFullForestA_subWF_preserved`) — demonstrating the Tier-3 object absorbs app-specific invariants the
bare catalog does not template, while STILL handing back `forever` for free. NONE is faked: every
`step_ob` is a real proof term over the shipped executor.

Discipline (HATCHERY.md §190): NO `sorry`/`admit`/`native_decide`/SMT. Every reproduced crown is
`#assert_axioms`-pinned to the kernel triple `{propext, Classical.choice, Quot.sound}` at the foot.
-/
import Dregg2.Verify.Catalog
import Dregg2.Apps.NameService
import Dregg2.Apps.Subscription

namespace Dregg2.Verify

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (fma0)
open Dregg2.Exec.FullForest
open Dregg2.Proof.Temporal (Always)

/-! ## §1 — Identity: `monotone_registry% revoked` reproduces the revocation crown.

`Apps.Identity.livingCellA_identity_revoked_forever` (`Apps/Identity.lean:593`) — *a revoked credential
stays revoked at every index of every adversarial trajectory* — is the canonical Tier-4 target
(`HATCHERY.md §133`). The catalog `monotone_registry% revoked credNul` builds the membership contract
`credNul ∈ ·.kernel.revoked`; `.forever` is the unbounded carry, with NO hand proof. This is the H4
headline already shown in `Catalog.lean §5`, re-stated here in the regression suite with the explicit
bidirectional defeq witness against the shipped theorem. -/

/-- **REPRODUCED — the Identity revocation crown via the catalog macro.** Identical statement to
`Apps.Identity.livingCellA_identity_revoked_forever`; the proof is the one-line catalog `.forever`. -/
theorem identity_revoked_forever_via_catalog (credNul : Nat) (s : RecChainedState)
    (hinit : credNul ∈ s.kernel.revoked) (sched : SchedA) :
    ∀ n, credNul ∈ (trajA s sched n).kernel.revoked :=
  (monotone_registry% revoked credNul).forever hinit sched

/-- Regression-equality (→): the catalog reproduction discharges the SHIPPED crown's type verbatim. -/
example (credNul : Nat) (s : RecChainedState) (hinit : credNul ∈ s.kernel.revoked) (sched : SchedA) :
    ∀ n, credNul ∈ (trajA s sched n).kernel.revoked :=
  identity_revoked_forever_via_catalog credNul s hinit sched

/-- Regression-equality (←): the SHIPPED hand crown discharges OUR reproduced type — same proposition. -/
example (credNul : Nat) (s : RecChainedState) (hinit : credNul ∈ s.kernel.revoked) (sched : SchedA) :
    ∀ n, credNul ∈ (trajA s sched n).kernel.revoked :=
  Dregg2.Apps.Identity.livingCellA_identity_revoked_forever credNul s hinit sched

/-- …and the LTL `□` reading via `.always` (the same contract, the temporal face). -/
theorem identity_revoked_always_via_catalog (credNul : Nat) (s : RecChainedState)
    (hinit : credNul ∈ s.kernel.revoked) (sched : SchedA) :
    Always (fun s' => credNul ∈ s'.kernel.revoked) s sched :=
  (monotone_registry% revoked credNul).always hinit sched

/-! ## §2 — CellNullifier headline: `monotone_registry% nullifiers` reproduces "spent ⇒ spent forever".

`Exec.livingCellA_spent_note_never_respent` (`Exec/CellNullifier.lean:644`) — *a consumed nullifier `nf`
stays consumed at every index of every trajectory* (the single-element anti-replay headline). This is
EXACTLY the catalog `monotone_registry% nullifiers nf` shape (membership in the grow-only nullifier
set); `.forever` reproduces it with no hand proof. -/

/-- **REPRODUCED — the no-double-spend headline via the catalog macro.** Identical statement to
`Exec.livingCellA_spent_note_never_respent`; the proof is the one-line catalog `.forever`. -/
theorem spent_note_never_respent_via_catalog (nf : Nat) (s : RecChainedState)
    (hinit : nf ∈ s.kernel.nullifiers) (sched : SchedA) :
    ∀ n, nf ∈ (trajA s sched n).kernel.nullifiers :=
  (monotone_registry% nullifiers nf).forever hinit sched

/-- Regression-equality (→): our reproduction discharges the shipped headline's type. -/
example (nf : Nat) (s : RecChainedState) (hinit : nf ∈ s.kernel.nullifiers) (sched : SchedA) :
    ∀ n, nf ∈ (trajA s sched n).kernel.nullifiers :=
  spent_note_never_respent_via_catalog nf s hinit sched

/-- Regression-equality (←): the SHIPPED hand crown discharges our type — same proposition. -/
example (nf : Nat) (s : RecChainedState) (hinit : nf ∈ s.kernel.nullifiers) (sched : SchedA) :
    ∀ n, nf ∈ (trajA s sched n).kernel.nullifiers :=
  Dregg2.Exec.livingCellA_spent_note_never_respent nf s hinit sched

/-! ## §3 — `subsetRegistryContract`: the `⊆`-shaped grow-only crowns as first-class contracts.

The catalog `monotone_registry%` templates the SINGLE-element membership `x ∈ ·.kernel.f`. Two shipped
crowns — `Exec.livingCellA_no_double_spend` and `Exec.livingCellA_commitments_persist` — are stated over
a baseline LIST `nul0`/`com0` with `⊆` (every element of a set stays present). We reproduce them as a
first-class `CellContract` `subsetRegistryContract f base`, built on the SAME registered forest-grow
lemmas the macro uses (`execFullForestA_{nullifiers,commitments}_grow`). This is Tier 3 generalizing the
Tier-4 shape over a subset baseline — the `step_ob` is the commit/stay-put split, the commit arm chained
by `List.Subset.trans` (exactly the hand crowns' one-step body). `.forever` then reproduces each crown. -/

/-- **`subsetNullifiersContract base` — the `⊆`-shaped grow-only nullifier contract.** `Inv s := base ⊆
s.kernel.nullifiers`, carried by `execFullForestA_nullifiers_grow` (commit: chain by `Subset.trans`;
reject: stay-put). The `⊆` generalization of `monotone_registry% nullifiers` over a baseline list. -/
def subsetNullifiersContract (base : List Nat) : CellContract where
  Inv s := base ⊆ s.kernel.nullifiers
  step_ob a cf h := by
    show base ⊆ (cellNextA a cf).kernel.nullifiers
    unfold cellNextA
    cases hc : execFullForestA a cf.1 with
    | some a' => simp only [Option.getD_some]
                 exact List.Subset.trans h (execFullForestA_nullifiers_grow a a' cf.1 hc)
    | none    => simp only [Option.getD_none]; exact h
  shape := .membership

/-- **`subsetCommitmentsContract base` — the `⊆`-shaped grow-only commitment contract.** `Inv s := base ⊆
s.kernel.commitments`, carried by `execFullForestA_commitments_grow`. The `⊆` generalization of
`monotone_registry% commitments`. -/
def subsetCommitmentsContract (base : List Nat) : CellContract where
  Inv s := base ⊆ s.kernel.commitments
  step_ob a cf h := by
    show base ⊆ (cellNextA a cf).kernel.commitments
    unfold cellNextA
    cases hc : execFullForestA a cf.1 with
    | some a' => simp only [Option.getD_some]
                 exact List.Subset.trans h (execFullForestA_commitments_grow a a' cf.1 hc)
    | none    => simp only [Option.getD_none]; exact h
  shape := .membership

/-- **REPRODUCED — `Exec.livingCellA_no_double_spend`** (`Exec/CellNullifier.lean:623`) via the
`⊆`-contract `.forever`. Identical statement; no hand temporal proof. -/
theorem no_double_spend_via_contract (nul0 : List Nat) (s : RecChainedState)
    (hinit : nul0 ⊆ s.kernel.nullifiers) (sched : SchedA) :
    ∀ n, nul0 ⊆ (trajA s sched n).kernel.nullifiers :=
  (subsetNullifiersContract nul0).forever hinit sched

/-- Regression-equality (→): our `⊆`-contract reproduction discharges the shipped crown's type. -/
example (nul0 : List Nat) (s : RecChainedState) (hinit : nul0 ⊆ s.kernel.nullifiers) (sched : SchedA) :
    ∀ n, nul0 ⊆ (trajA s sched n).kernel.nullifiers :=
  no_double_spend_via_contract nul0 s hinit sched

/-- Regression-equality (←): the SHIPPED `Exec.livingCellA_no_double_spend` discharges our type. -/
example (nul0 : List Nat) (s : RecChainedState) (hinit : nul0 ⊆ s.kernel.nullifiers) (sched : SchedA) :
    ∀ n, nul0 ⊆ (trajA s sched n).kernel.nullifiers :=
  Dregg2.Exec.livingCellA_no_double_spend nul0 s hinit sched

/-- **REPRODUCED — `Exec.livingCellA_commitments_persist`** (`Exec/CellCommit.lean:570`) via the
`⊆`-contract `.forever`. Identical statement; no hand temporal proof. -/
theorem commitments_persist_via_contract (com0 : List Nat) (s : RecChainedState) (sched : SchedA)
    (hinit : com0 ⊆ s.kernel.commitments) :
    ∀ n, com0 ⊆ (trajA s sched n).kernel.commitments :=
  (subsetCommitmentsContract com0).forever hinit sched

/-- Regression-equality (→): our reproduction discharges the shipped crown's type. -/
example (com0 : List Nat) (s : RecChainedState) (sched : SchedA)
    (hinit : com0 ⊆ s.kernel.commitments) :
    ∀ n, com0 ⊆ (trajA s sched n).kernel.commitments :=
  commitments_persist_via_contract com0 s sched hinit

/-- Regression-equality (←): the SHIPPED `Exec.livingCellA_commitments_persist` discharges our type. -/
example (com0 : List Nat) (s : RecChainedState) (sched : SchedA)
    (hinit : com0 ⊆ s.kernel.commitments) :
    ∀ n, com0 ⊆ (trajA s sched n).kernel.commitments :=
  Dregg2.Exec.livingCellA_commitments_persist com0 s sched hinit

/-! ## §4 — NameService: `nameRegisteredContract` reproduces "registered ⇒ registered forever".

`Apps.NameService.nameservice_registration_forever` (`Apps/NameService.lean:198`) — *a name→owner binding,
once registered, stays registered at every index of every trajectory*. The invariant `isRegistered ·
name owner = true` is a `commitments.contains (nameCommit name owner)` BOOLEAN, NOT the bare
`x ∈ ·.kernel.commitments` the catalog templates — so we reproduce it as a first-class `CellContract`
whose `step_ob` is the app's OWN one-step lemma `nameservice_step_preserves`. This shows Tier 3 absorbing
an app-specific invariant the bare catalog does not template, while still delivering `forever` free. -/

-- `nameRegisteredContract` is the single source of truth in `Verify/Contract.lean §3a` (the H3
-- three-apps gate); it is in scope here via the import chain `Regression → Catalog → Contract`. We
-- reuse it for the rigorous BOTH-DIRECTIONS defeq witness against the shipped crown below.

/-- **REPRODUCED — `Apps.NameService.nameservice_registration_forever`** via the contract `.forever`.
Identical statement; no hand temporal proof. -/
theorem nameservice_registration_forever_via_contract (s : RecChainedState)
    (name owner : Dregg2.Apps.NameService.Name)
    (hinit : Dregg2.Apps.NameService.isRegistered s name owner = true) (sched : SchedA) :
    ∀ n, Dregg2.Apps.NameService.isRegistered (trajA s sched n) name owner = true :=
  (nameRegisteredContract name owner).forever hinit sched

/-- Regression-equality (→): our reproduction discharges the shipped crown's type. -/
example (s : RecChainedState) (name owner : Dregg2.Apps.NameService.Name)
    (hinit : Dregg2.Apps.NameService.isRegistered s name owner = true) (sched : SchedA) :
    ∀ n, Dregg2.Apps.NameService.isRegistered (trajA s sched n) name owner = true :=
  nameservice_registration_forever_via_contract s name owner hinit sched

/-- Regression-equality (←): the SHIPPED `Apps.NameService.nameservice_registration_forever` discharges
our type — same proposition. -/
example (s : RecChainedState) (name owner : Dregg2.Apps.NameService.Name)
    (hinit : Dregg2.Apps.NameService.isRegistered s name owner = true) (sched : SchedA) :
    ∀ n, Dregg2.Apps.NameService.isRegistered (trajA s sched n) name owner = true :=
  Dregg2.Apps.NameService.nameservice_registration_forever s name owner hinit sched

/-! ## §5 — Subscription: `subWFContract` reproduces "no queue ever over capacity, forever".

`Apps.Subscription.subscription_wellformed_forever` (`Apps/Subscription.lean:819`) — *from a well-formed
start, every subscription stays within capacity at every index of every trajectory* (dregg1's in-flight
bound, `head − tail ≤ capacity`). The invariant `subWF ·.kernel` is a `∀ q ∈ queues, q.buffer.length ≤
q.capacity` bound — a field-relational shape (`HATCHERY.md §138`-flavored) NOT among the four bare
catalog macros, so we reproduce it as a first-class `CellContract` whose `step_ob` is the app's OWN
one-step lemma `execFullForestA_subWF_preserved`. -/

-- `subWFContract` is the single source of truth in `Verify/Contract.lean §3a` (the H3 three-apps
-- gate); in scope here via `Regression → Catalog → Contract`. Reused for the both-directions witness.

/-- **REPRODUCED — `Apps.Subscription.subscription_wellformed_forever`** via the contract `.forever`.
Identical statement; no hand temporal proof. -/
theorem subscription_wellformed_forever_via_contract (s : RecChainedState)
    (hinit : Dregg2.Apps.Subscription.subWF s.kernel) (sched : SchedA) :
    ∀ n, Dregg2.Apps.Subscription.subWF (trajA s sched n).kernel :=
  subWFContract.forever hinit sched

/-- Regression-equality (→): our reproduction discharges the shipped crown's type. -/
example (s : RecChainedState) (hinit : Dregg2.Apps.Subscription.subWF s.kernel) (sched : SchedA) :
    ∀ n, Dregg2.Apps.Subscription.subWF (trajA s sched n).kernel :=
  subscription_wellformed_forever_via_contract s hinit sched

/-- Regression-equality (←): the SHIPPED `Apps.Subscription.subscription_wellformed_forever` discharges
our type — same proposition. -/
example (s : RecChainedState) (hinit : Dregg2.Apps.Subscription.subWF s.kernel) (sched : SchedA) :
    ∀ n, Dregg2.Apps.Subscription.subWF (trajA s sched n).kernel :=
  Dregg2.Apps.Subscription.subscription_wellformed_forever s hinit sched

/-! ## §6 — It runs (`#eval`) — the reproduced crowns carry the SAME moving quantities (non-vacuity).

Each reproduction bounds a quantity the corresponding hand crown's own `#eval` witnesses to be
non-trivial — the Hatchery reproduces the non-vacuous theorems, not vacuities:
* Identity / nullifier membership: the registries have TEETH (`42` revoked, `99` not; spent `[77]`).
* commitment / nullifier `⊆`: a real committed turn GROWS the set (`[] → [77]` for nullifiers).
* NameService: a real `register` lands `isRegistered = true`, and a non-registered binding is `false`.
* Subscription: `subWF` holds on a well-formed start and is preserved across a real committed turn. -/

-- Identity / nullifier headline: the registries discriminate (teeth — not a trivially-true `x = x`).
#eval Dregg2.Apps.Identity.fmaRevoked.kernel.revoked.contains 42            -- true  (42 IS revoked)
#eval Dregg2.Apps.Identity.fmaRevoked.kernel.revoked.contains 99            -- false (99 NOT — teeth)
#eval (execFullForestA fma0 Dregg2.Exec.spendCF).map (fun s' => s'.kernel.nullifiers.contains 77)  -- some true (77 spent)

-- `⊆` crowns: a real committed noteSpend GROWS the nullifier set (the carried `⊆` bounds a moving set).
#eval (execFullForestA fma0 Dregg2.Exec.spendCF).map (fun s' => decide ([77] ⊆ s'.kernel.nullifiers))  -- some true
#eval fma0.kernel.nullifiers                                                -- [] (BEFORE — the set genuinely grows)

-- NameService: a non-registered binding is `false` (the registry discriminates — `isRegistered` has teeth).
#eval Dregg2.Apps.NameService.isRegistered fma0 Dregg2.Apps.NameService.aliceName Dregg2.Apps.NameService.aliceOwner  -- false (not yet registered)
#eval Dregg2.Apps.NameService.afterRegister.map
        (fun s => Dregg2.Apps.NameService.isRegistered s Dregg2.Apps.NameService.aliceName Dregg2.Apps.NameService.aliceOwner)  -- some true (real register lands it)

-- Subscription: a REAL committed program builds a within-capacity queue, and the carried bound has
-- teeth (in-flight 1 ≤ capacity 2). `subWF` is a `∀ q ∈ queues` Prop (not `Decidable`), so we witness
-- it through the equivalent `List.all`/`findQueue` Bool readers — Subscription's own non-vacuity shape.
#eval (execFullForestA fmaDeleg Dregg2.Apps.Subscription.subForest).isSome  -- true (the subscription commits)
#eval (execFullForestA fmaDeleg Dregg2.Apps.Subscription.subForest).map
        (fun s => s.kernel.queues.all (fun q => decide (q.buffer.length ≤ q.capacity)))  -- some true (carried subWF holds AFTER)
#eval (execFullForestA fmaDeleg Dregg2.Apps.Subscription.subForest).bind
        (fun s => (Dregg2.Exec.findQueue s.kernel.queues 7).map (fun q => (q.buffer, q.capacity)))  -- some ([111], 2) (a real queue, in-flight 1 ≤ cap 2 — teeth)

-- The reproduced contracts carry genuinely distinct `SafetyShape`s (not one hard-wired tag).
#eval (subsetNullifiersContract [77]).shape                                 -- SafetyShape.membership
#eval subWFContract.shape                                                   -- SafetyShape.other
#eval decide ((subsetNullifiersContract [77]).shape ≠ subWFContract.shape)  -- true (distinct shapes)

/-! ## §7 — Axiom hygiene — every reproduced crown pinned to the kernel triple `{propext, Classical.choice, Quot.sound}`.

`#assert_axioms` on each reproduced theorem certifies the Hatchery reproductions are ordinary
kernel-checked terms with NO `sorry`/`native_decide`/SMT oracle — the H4 gate's hygiene requirement. -/

#assert_axioms identity_revoked_forever_via_catalog
#assert_axioms identity_revoked_always_via_catalog
#assert_axioms spent_note_never_respent_via_catalog
#assert_axioms no_double_spend_via_contract
#assert_axioms commitments_persist_via_contract
#assert_axioms nameservice_registration_forever_via_contract
#assert_axioms subscription_wellformed_forever_via_contract

end Dregg2.Verify
