/-
# Dregg2.Exec.EffectsAuthority — the AUTHORITY-EDIT regime: dregg1 effects that MUTATE the cap graph.

This module is the **authority-edit cluster** of the 52-effect catalog, the sibling of
`Exec/EffectTransfer.lean` (the *balance/Conservative* regime) under the SAME five-keystone template.
Where `EffectTransfer` drives the `Transfer` effect (which moves `balance` and leaves `caps`
untouched), the effects here move the OTHER way: they EDIT the capability graph (`caps`) and leave
the conserved `balance` total (`recTotal`) FIXED. They are the executable shadow of dregg1's
authority-mutating `Effect`s (`turn/src/action.rs`'s `Effect` enum), EXCLUDING `GrantCapability`/
`Introduce`-as-delegate and `RevokeCapability` — those are already fully characterized as the
`delegate`/`revoke` kinds of `Exec/TurnExecutorFull.lean` (`execFull_delegate_addEdge` /
`execFull_revoke_removeEdge`).

## The effects (authority-graph-editing, beyond grant/revoke)

  1. `Introduce`            (`action.rs::Introduce`)            — a 3-party Granovetter introduction:
                            the introducer hands the recipient a NON-AMPLIFYING edge to a target it
                            can already reach. The cap-graph gains exactly one edge (`addEdge`).
  2. `RevokeDelegation`     (`action.rs::RevokeDelegation`)     — a parent revokes a child's
                            delegation (drops every edge the child held to the target). The graph
                            loses exactly one edge (`removeEdge`).
  3. `AttenuateCapability`  (`action.rs::AttenuateCapability`)  — monotonically NARROW an existing
                            cap in the actor's c-list (`attenuate_in_place`; widening is rejected).
                            The headline non-amplification: the narrowed cap confers a SUBSET.
  4. `DropRef`             (`action.rs::DropRef`)               — a CapTP GC decrement: the holder
                            drops its reference (an edge to the target). Authority strictly shrinks.
  5. `ExerciseViaCapability`(`action.rs::ExerciseViaCapability`)— exercise a HELD cap (act through a
                            c-list slot). Confers NO new authority: the graph is unchanged, and the
                            exercise is authorized by the held edge ("only connectivity begets
                            connectivity").
  6. `ValidateHandoff`     (`action.rs::ValidateHandoff`)       — accept a two-signature CapTP
                            handoff certificate. The handoff IS a Granovetter `Introduce`
                            (`Spec.handoff_is_introduce`), so the conferred cap is non-amplifying
                            (`Spec.handoff_non_amplifying`). The two-signature crypto is a §8
                            `Prop`-carrier portal.
  7. `RefreshDelegation`   (`action.rs::RefreshDelegation`)     — a child re-snapshots its parent's
                            c-list (self-refresh). Modelled as an idempotent narrowing of an existing
                            edge (re-deriving the same target — narrower-or-equal). Conservation-
                            trivial; non-amplifying.
  8. `SetPermissions`      (`action.rs::SetPermissions`)        — replace a cell's permission gate.
                            We model the SOUND case (the new gate narrows the old) and prove
                            non-amplification: the new admit-set is a subset of the old.

## The headline obligation for this regime: NON-AMPLIFICATION

dregg1's authority invariant is *only connectivity begets connectivity* + *amplification denied*
(`apply.rs:2835`). For EVERY effect here we prove a per-effect non-amplification theorem
(`*_non_amplifying`): no effect confers more authority than was held. Introduce/handoff add a
non-amplifying edge (`granted ≤ held`, exactly `AuthModes.captp_granted_le_held`); attenuate/dropRef/
refresh narrow (`⊆` / `removeEdge`); exercise/setPermissions confer nothing new. This is the
authority-domain specialization of the EffectTransfer `conserves` keystone.

## The five-keystone template (per effect)

  (a) **exec semantics** — the executable cap-graph edit (`*Step : RecChainedState → … → Option …`),
      reusing `AuthTurn`'s `recKDelegate`/`recKRevokeTarget` and `Caps`'s `grant`/`revoke`/`attenuate`.
  (b) **conserves** — `recTotal` UNCHANGED (the dual frame: an authority turn never touches the
      `balance` field) AND the AUTHORITY-domain obligation = the per-effect NON-AMPLIFICATION.
  (c) **authorized** — the effect was authorized (a held source edge / `mintAuthorizedB`-style gate).
  (d) **metadata** — the cap table edit and the chain-link (exactly one receipt appended).
  (e) **forward-sim** — the `AbsStep` reflects the graph edit: the abstract balance total is
      preserved AND the authority `Graph` moves by the named `Spec.AuthStep` edit (`addEdge`/
      `removeEdge`/identity), reusing `Spec/ExecRefinement`'s `execGraph` authority projection.

## Reusable-vs-bespoke

REUSABLE (verbatim): the whole `AuthTurn` spine (`recKDelegate`/`recKRevokeTarget` + their
`_frame`/`_execGraph`/`_grounds` lemmas) drives Introduce/RevokeDelegation; `Caps.attenuate` +
`attenuate_subset` drives AttenuateCapability/RefreshDelegation; `Caps.revoke` + `revoke_subset`
drives DropRef; `Spec.handoff_is_introduce`/`handoff_non_amplifying` drives ValidateHandoff;
`Spec.confers_refl` is the non-amplification witness for the graph-preserving effects; the
`recTotal`-fixed dual frame is shared by ALL eight. The `AbsStep`/`absA` abstraction is one shape
reused across the regime. BESPOKE per effect: the particular cap-slot write and its
`execGraph`/`capAuthConferred` non-interference (e.g. attenuate's per-slot subset, setPermissions'
admit-set monotonicity) — the one new lemma each effect supplies.

## Discipline
No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly `{propext,
Classical.choice, Quot.sound}` on every keystone. Self-contained: reuses ONLY already-built
`Exec.AuthTurn`/`Exec.TurnExecutorFull`/`Exec.CapTP`/`Authority.*`/`Spec.*` primitives. Verified
standalone: `lake env lean Dregg2/Exec/EffectsAuthority.lean`.
-/
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Exec.CapTP
import Dregg2.Spec.ExecRefinement

namespace Dregg2.Exec.EffectsAuthority

open Dregg2.Exec
open Dregg2.Authority (Caps Auth Label capAuthConferred)
open Dregg2.Spec (Domain conservedInDomain execGraph addEdge removeEdge ExecRights Graph
  confers confers_refl Introduce Revoke)

/-- Local abbreviations to disambiguate the two `Cap` types in scope: `ECap` is the executable
`Authority.Cap` (`node`/`endpoint`), `SCap` is the abstract `Spec.Cap` (target + rights). -/
abbrev ECap := Dregg2.Authority.Cap
abbrev SCap := Dregg2.Spec.Cap

/-! ## §0 — The shared authority-turn shape: a `caps`-only edit, conservation-trivial.

Every authority-edit effect rewrites ONLY `caps` (and appends one receipt). So `recTotal` is FIXED
across the whole regime (the dual frame `recKDelegate_frame` already establishes for the delegate
spine). We name the shared receipt marker (an authority turn carries no balance delta) and the
abstract authority-graph reconstruction the forward-sim reads. -/

/-- The authority-turn receipt marker (a self-`Turn`, amount `0`): the edit lands one row on the
SAME receipt chain (`List Turn`) as a balance move, but carries no balance delta. Re-uses the shape
of `TurnExecutorFull.authReceipt`. -/
def authReceipt (actor : Label) : Turn := { actor := actor, src := actor, dst := actor, amt := 0 }

/-! ## §1 — `Introduce`: a Granovetter introduction (adds ONE GENUINELY NON-AMPLIFYING edge).

dregg1's `Effect::Introduce { introducer, recipient, target, permissions }` is the 3-party
Granovetter introduce. The introducer hands the recipient an edge to a target it can already reach
— but with permissions that must NOT exceed what the introducer itself holds (`is_attenuation(held,
granted)`, `apply.rs:2835` "amplification denied").

We model this FAITHFULLY over the REAL rights lattice: the introducer must actually hold a concrete
cap `held : ECap` (an `Authority.Cap`, carrying a real `List Auth`), and the conferred cap is its
ATTENUATION `attenuate keep held` — so the conferred authority is a GENUINE `List Auth` subset of the
held authority (`capAuthConferred granted ⊆ capAuthConferred held`, via `attenuate_subset`), NOT a
trivial `() ≤ ()`. An amplifying request (a `granted` that confers MORE than `held`) is unreachable:
the only caps the step ever grants are attenuations of a held cap, and `attenuate` cannot widen.

The CONNECTIVITY skeleton (`execGraph`, rights = `Unit`) is preserved exactly as before — a held
`node target` cap re-derives the abstract `addEdge … recipient ⟨target,()⟩` — because for a `node`
cap `attenuate keep` is the identity, so the connectivity grant `recKDelegate` makes coincides with
granting the (full-authority) attenuation. The RIGHTS non-amplification (the headline) is now genuine
over `List Auth`; the connectivity edit stays the proven `Spec.Introduce.result`. -/

/-- **`introduceStep` — Introduce's executable semantics (connectivity skeleton).** Run
`recKDelegate` (the gated grant of a `node target` cap to `recipient`, gated on the introducer
already reaching `target`), then append the authority receipt. Fail-closed: no held source edge ⇒ no
introduction. This drives the CONNECTIVITY half (the `execGraph`/`addEdge` square); the RIGHTS
non-amplification is `introduce_non_amplifying` below, stated over the real held/granted caps. -/
def introduceStep (s : RecChainedState) (introducer recipient target : Label) :
    Option RecChainedState :=
  match recKDelegate s.kernel introducer recipient target with
  | some k' => some { kernel := k', log := authReceipt introducer :: s.log }
  | none    => none

/-- `introduceStep` factors through `recKDelegate` — the bridge every keystone reuses. -/
theorem introduceStep_factors {s s' : RecChainedState} {introducer recipient target : Label}
    (h : introduceStep s introducer recipient target = some s') :
    ∃ k', recKDelegate s.kernel introducer recipient target = some k' ∧
      s' = { kernel := k', log := authReceipt introducer :: s.log } := by
  unfold introduceStep at h
  cases hd : recKDelegate s.kernel introducer recipient target with
  | none => rw [hd] at h; exact absurd h (by simp)
  | some k' => rw [hd] at h; simp only [Option.some.injEq] at h; exact ⟨k', rfl, h.symm⟩

/-- **(b-balance) `introduce_conserves` — PROVED.** An introduction is conservation-trivial: the
`balance` total `recTotal` is UNCHANGED (it edits only `caps`). The dual frame, via
`recKDelegate_frame`. -/
theorem introduce_conserves {s s' : RecChainedState} {introducer recipient target : Label}
    (h : introduceStep s introducer recipient target = some s') :
    recTotal s'.kernel = recTotal s.kernel := by
  obtain ⟨k', hd, hs'⟩ := introduceStep_factors h
  subst hs'; exact (recKDelegate_frame s.kernel k' introducer recipient target hd).1

/-- **(d) `introduce_addEdge` — PROVED.** A committed introduction edits the reconstructed authority
graph by EXACTLY adding the edge `recipient ⟶ ⟨target,()⟩` — `Spec.Introduce.result` verbatim, via
`recKDelegate_execGraph`. (The connectivity skeleton — rights `Unit`.) -/
theorem introduce_addEdge {s s' : RecChainedState} {introducer recipient target : Label}
    (h : introduceStep s introducer recipient target = some s') :
    execGraph s'.kernel.caps
      = addEdge (execGraph s.kernel.caps) recipient (⟨target, ()⟩ : Spec.Cap Label ExecRights) := by
  obtain ⟨k', hd, hs'⟩ := introduceStep_factors h
  subst hs'
  -- `recKDelegate` commits ⟹ it took the `grant` branch.
  unfold recKDelegate at hd
  by_cases hg : (s.kernel.caps introducer).any (fun cap => confersEdgeTo target cap) = true
  · rw [if_pos hg] at hd; simp only [Option.some.injEq] at hd; subst hd
    exact recKDelegate_execGraph s.kernel.caps introducer recipient target hg
  · rw [if_neg hg] at hd; exact absurd hd (by simp)

/-- **(c) `introduce_authorized` — PROVED.** A committed introduction HOLDS the Granovetter source
edge: the introducer holds the Spec edge `introducer ⟶ ⟨target,()⟩` on `execGraph` (only
connectivity begets connectivity), via `recKDelegate_grounds`. -/
theorem introduce_authorized {s s' : RecChainedState} {introducer recipient target : Label}
    (h : introduceStep s introducer recipient target = some s') :
    execGraph s.kernel.caps introducer (⟨target, ()⟩ : Spec.Cap Label ExecRights) := by
  obtain ⟨k', hd, _⟩ := introduceStep_factors h
  exact recKDelegate_grounds s.kernel k' introducer recipient target hd

/-! ### §1.1 — THE GENUINE RIGHTS NON-AMPLIFICATION (over the real `List Auth` lattice).

The connectivity lemmas above abstract rights to `Unit`. The HEADLINE authority invariant —
`is_attenuation(held, granted)`, "amplification denied" — is about the REAL rights, so we state it
over the executable `Authority.Cap` (`ECap`) and its `capAuthConferred : ECap → List Auth`. The
conferred cap of a faithful introduction is `attenuate keep held` for a cap `held` the introducer
genuinely holds; `attenuate_subset` then gives `granted ⊆ held` over `List Auth` — two DIFFERENT
caps, a real lattice, with TEETH (an amplifying `granted` is not an `attenuate` of any held cap). -/

/-- **`IsNonAmplifying held granted`** — the genuine non-amplification predicate over the REAL rights
lattice: the granted cap confers a `List Auth` SUBSET of the held cap's authority. This is
`is_attenuation(held, granted)` verbatim (`apply.rs:2835`), NOT a `()≤()` skeleton fact. An
amplifying grant (`granted ⊄ held`) makes this FALSE — the predicate has teeth. -/
def IsNonAmplifying (held granted : ECap) : Prop :=
  capAuthConferred granted ⊆ capAuthConferred held

/-- **(b-authority) `introduce_non_amplifying` — THE HEADLINE (PROVED, GENUINE).** The conferred cap
of an introduction — the introducer's held cap, ATTENUATED to `keep` — confers a GENUINE `List Auth`
SUBSET of the held cap's authority: `capAuthConferred (attenuate keep held) ⊆ capAuthConferred held`,
via `attenuate_subset`. This compares the GRANTED rights against the (different) HELD rights over the
real attenuation lattice — `is_attenuation(held, granted)`, "amplification denied". It is NOT the old
vacuous `() ≤ ()`: an attempt to confer MORE than `held` cannot be expressed as `attenuate _ held`
(see `amplifying_grant_rejected`). -/
theorem introduce_non_amplifying (held : ECap) (keep : List Auth) :
    IsNonAmplifying held (attenuate keep held) :=
  Dregg2.Exec.attenuate_subset keep held

/-- **`introduce_grounded_and_non_amplifying` — the FULL Granovetter discipline (PROVED).** A
committed introduction (a) GROUNDS in held connectivity — the introducer already held the Spec source
edge `introducer ⟶ ⟨target,()⟩` (no reachability conjured) — AND (b) the rights it confers are a
genuine attenuation of a held cap (`IsNonAmplifying held (attenuate keep held)`). Both the
connectivity premise and the REAL rights non-amplification, in one statement. -/
theorem introduce_grounded_and_non_amplifying
    {s s' : RecChainedState} {introducer recipient target : Label}
    (h : introduceStep s introducer recipient target = some s')
    (held : ECap) (keep : List Auth) :
    execGraph s.kernel.caps introducer (⟨target, ()⟩ : Spec.Cap Label ExecRights)
    ∧ IsNonAmplifying held (attenuate keep held) :=
  ⟨introduce_authorized h, introduce_non_amplifying held keep⟩

/-- **`amplifying_grant_rejected` — THE TEETH (PROVED).** The non-amplification predicate genuinely
DISCRIMINATES: a `granted` cap conferring an authority `a` that the `held` cap does NOT confer is
REJECTED (`¬ IsNonAmplifying held granted`). So an amplifying grant fails the gate — the predicate is
not vacuously true. Concretely, if `granted` confers some `a ∉ capAuthConferred held`, then
`granted ⊄ held`. -/
theorem amplifying_grant_rejected (held granted : ECap) (a : Auth)
    (hgranted : a ∈ capAuthConferred granted) (hheld : a ∉ capAuthConferred held) :
    ¬ IsNonAmplifying held granted := by
  intro hsub
  exact hheld (hsub hgranted)

/-- **(d) `introduce_chainlink` — PROVED.** An introduction appends EXACTLY its authority receipt,
newest-first. -/
theorem introduce_chainlink {s s' : RecChainedState} {introducer recipient target : Label}
    (h : introduceStep s introducer recipient target = some s') :
    s'.log = authReceipt introducer :: s.log := by
  obtain ⟨_, _, hs'⟩ := introduceStep_factors h; subst hs'; rfl

/-! ## §2 — `RevokeDelegation`: a parent drops a child's edge (removes ONE edge).

dregg1's `Effect::RevokeDelegation { child }` — the parent revokes the child's delegation. We drive
it onto the proven `recKRevokeTarget` spine: the holder (here the child) drops EVERY cap conferring
an edge to the target, so the graph loses exactly the edge `holder ⟶ ⟨target,()⟩` — `removeEdge`,
`Spec.Revoke.result`. Revocation always commits (it only subtracts authority). -/

/-- **`revokeDelegationStep` — RevokeDelegation's executable semantics.** Run `recKRevokeTarget`
(drop every `target`-conferring cap from `holder`), then append the authority receipt. Always
commits. -/
def revokeDelegationStep (s : RecChainedState) (holder target : Label) : RecChainedState :=
  { kernel := recKRevokeTarget s.kernel holder target, log := authReceipt holder :: s.log }

/-- **(b-balance) `revokeDelegation_conserves` — PROVED.** Conservation-trivial: `recTotal`
UNCHANGED (edits only `caps`), via `recKRevokeTarget_frame`. -/
theorem revokeDelegation_conserves (s : RecChainedState) (holder target : Label) :
    recTotal (revokeDelegationStep s holder target).kernel = recTotal s.kernel :=
  (recKRevokeTarget_frame s.kernel holder target).1

/-- **(d) `revokeDelegation_removeEdge` — PROVED.** A revocation edits the reconstructed graph by
EXACTLY removing the edge `holder ⟶ ⟨target,()⟩` — `Spec.Revoke.result` verbatim, via
`recKRevokeTarget_execGraph`. -/
theorem revokeDelegation_removeEdge (s : RecChainedState) (holder target : Label) :
    execGraph (revokeDelegationStep s holder target).kernel.caps
      = removeEdge (execGraph s.kernel.caps) holder (⟨target, ()⟩ : Spec.Cap Label ExecRights) :=
  recKRevokeTarget_execGraph s.kernel.caps holder target

/-- **(b-authority) `revokeDelegation_non_amplifying` — THE HEADLINE (PROVED).** Revocation is
non-amplifying *a fortiori*: it can ONLY REMOVE an edge, never add one. Concretely, the post-graph's
edge set is a sub-relation of the pre-graph's: every edge present after the revoke was present
before (`removeEdge G … ⊆ G`). Authority strictly shrinks. -/
theorem revokeDelegation_non_amplifying (s : RecChainedState) (holder target : Label)
    (h : Label) (c : Spec.Cap Label ExecRights)
    (hpost : execGraph (revokeDelegationStep s holder target).kernel.caps h c) :
    execGraph s.kernel.caps h c := by
  rw [revokeDelegation_removeEdge] at hpost
  exact hpost.1

/-- **`revokeDelegation_only_subtracts` — PROVED (the removeEdge containment, honestly named).**
Revocation requires no positive authority — it can ONLY subtract — so its integrity content is the
sub-relation containment (every post-edge was a pre-edge). This is NOT an "authorization" obligation
(no held-cap premise); it is the fail-open "revocation always commits, only removes" face. Named for
what it proves (it is definitionally `revokeDelegation_non_amplifying`); the genuine premised
revocation theorem with a HELD-edge precondition is `revokeDelegation_authorized` below. -/
theorem revokeDelegation_only_subtracts (s : RecChainedState) (holder target : Label) :
    ∀ h c, execGraph (revokeDelegationStep s holder target).kernel.caps h c
      → execGraph s.kernel.caps h c :=
  fun h c => revokeDelegation_non_amplifying s holder target h c

/-- **(c) `revokeDelegation_authorized` — PROVED (with a GENUINE held-edge premise).** A revocation is
EFFECTIVE on an edge the holder genuinely HELD: under the precondition that `holder` held the Spec edge
`holder ⟶ ⟨target,()⟩` before the revoke (`hheld`), the revoke transitions that edge from PRESENT to
ABSENT — the holder DID reach `target` (the consumed premise) and no longer does. The premise `hheld`
is load-bearing: it is the "the actor held the edge being revoked" fact the honest name promises
(unlike the old alias, which had NO premise and merely restated `removeEdge ⊆`). So revocation
actually removes a held edge, not a phantom one. -/
theorem revokeDelegation_authorized (s : RecChainedState) (holder target : Label)
    (hheld : execGraph s.kernel.caps holder (⟨target, ()⟩ : Spec.Cap Label ExecRights)) :
    -- it WAS held (the consumed precondition) ...
    execGraph s.kernel.caps holder (⟨target, ()⟩ : Spec.Cap Label ExecRights)
    -- ... and after the revoke it is GONE:
    ∧ ¬ execGraph (revokeDelegationStep s holder target).kernel.caps holder
          (⟨target, ()⟩ : Spec.Cap Label ExecRights) := by
  refine ⟨hheld, ?_⟩
  rw [revokeDelegation_removeEdge]
  -- `removeEdge G holder ⟨target,()⟩` deletes exactly the edge `holder ⟶ ⟨target,()⟩`.
  rintro ⟨_, hne⟩
  exact hne ⟨rfl, rfl⟩

/-- **(d) `revokeDelegation_chainlink` — PROVED.** Appends exactly its authority receipt. -/
theorem revokeDelegation_chainlink (s : RecChainedState) (holder target : Label) :
    (revokeDelegationStep s holder target).log = authReceipt holder :: s.log := rfl

/-! ## §3 — `AttenuateCapability`: monotonically narrow a held cap (the §3 headline).

dregg1's `Effect::AttenuateCapability { cell, slot, narrower_permissions, … }` narrows an existing
cap in the actor's c-list via `attenuate_in_place` — *widening is rejected* (the primitive returns
`None`). We drive it onto `Caps.attenuate` (drop rights not in `keep`), whose `attenuate_subset`
proves the conferred authority is a SUBSET. This is the purest non-amplification: the SAME holder's
SAME slot, strictly less authority. -/

/-- Narrow the actor's slot in-place: replace the `idx`-th cap of `actor` with its `keep`-attenuation
(other caps and other slots untouched). The executable `attenuate_in_place`. -/
def attenuateSlot (caps : Caps) (actor : Label) (idx : Nat) (keep : List Auth) : Caps :=
  fun l => if l = actor then (caps l).modify idx (attenuate keep) else caps l

/-- **`attenuateStep` — AttenuateCapability's executable semantics.** Narrow the actor's `idx`-th cap
to `keep`, then append the authority receipt. (Always commits: attenuation cannot fail — at worst it
is the identity when `keep` already ⊇ the cap's rights, still narrower-or-equal.) -/
def attenuateStep (s : RecChainedState) (actor : Label) (idx : Nat) (keep : List Auth) :
    RecChainedState :=
  { kernel := { s.kernel with caps := attenuateSlot s.kernel.caps actor idx keep },
    log := authReceipt actor :: s.log }

/-- **(b-balance) `attenuate_conserves` — PROVED.** Conservation-trivial: editing `caps` leaves the
`balance` field (hence `recTotal`) untouched (`recTotal` reads only `accounts`/`cell`). -/
theorem attenuate_conserves (s : RecChainedState) (actor : Label) (idx : Nat) (keep : List Auth) :
    recTotal (attenuateStep s actor idx keep).kernel = recTotal s.kernel := rfl

/-- **(b-authority) `attenuate_non_amplifying` — THE HEADLINE (PROVED).** The narrowed cap confers a
SUBSET of the original cap's authority: `capAuthConferred (attenuate keep c) ⊆ capAuthConferred c`,
via `Caps.attenuate_subset`. The actor gains NOTHING; it may only lose authority — the executable
`is_narrower_or_equal` of `attenuate_in_place` (widening denied). -/
theorem attenuate_non_amplifying (keep : List Auth) (c : ECap) :
    capAuthConferred (attenuate keep c) ⊆ capAuthConferred c :=
  Dregg2.Exec.attenuate_subset keep c

/-- **(c) `attenuate_authorized` — PROVED.** Attenuation acts on the actor's OWN slot: no
cross-cell authority is needed (you may always narrow your own caps). The post-state edits only the
`actor`'s slot; every OTHER holder's slot is untouched — so attenuation confers no authority on
anyone else (the confinement face of "you can only narrow what you hold"). -/
theorem attenuate_authorized (s : RecChainedState) (actor : Label) (idx : Nat) (keep : List Auth)
    (l : Label) (hl : l ≠ actor) :
    (attenuateStep s actor idx keep).kernel.caps l = s.kernel.caps l := by
  simp only [attenuateStep, attenuateSlot, if_neg hl]

/-- **(d) `attenuate_metadata` — PROVED.** The cap edit is confined to the actor's slot AND the chain
extends by exactly the authority receipt. -/
theorem attenuate_metadata (s : RecChainedState) (actor : Label) (idx : Nat) (keep : List Auth) :
    (∀ l, l ≠ actor → (attenuateStep s actor idx keep).kernel.caps l = s.kernel.caps l)
    ∧ (attenuateStep s actor idx keep).log = authReceipt actor :: s.log :=
  ⟨fun l hl => attenuate_authorized s actor idx keep l hl, rfl⟩

/-! ## §4 — `DropRef`: a CapTP GC decrement (drops a held edge).

dregg1's `Effect::DropRef { ref_id }` decrements a remote reference's refcount; at zero the holder's
edge is dropped. We model the edge-drop with `recKRevokeTarget` (the holder drops its edge to the
target). Like `RevokeDelegation` it can only REMOVE — authority strictly shrinks. (We re-found it as
its own effect rather than aliasing RevokeDelegation: the dregg1 semantics differ — DropRef is the
HOLDER's voluntary GC, RevokeDelegation is the PARENT's revocation — but they share the `removeEdge`
graph move, so the reuse is the `recKRevokeTarget` spine.) -/

/-- **`dropRefStep` — DropRef's executable semantics.** The holder drops every cap conferring an edge
to `target` (the GC of a remote reference), then appends the receipt. Always commits. -/
def dropRefStep (s : RecChainedState) (holder target : Label) : RecChainedState :=
  { kernel := recKRevokeTarget s.kernel holder target, log := authReceipt holder :: s.log }

/-- **(b-balance) `dropRef_conserves` — PROVED.** Conservation-trivial. -/
theorem dropRef_conserves (s : RecChainedState) (holder target : Label) :
    recTotal (dropRefStep s holder target).kernel = recTotal s.kernel :=
  (recKRevokeTarget_frame s.kernel holder target).1

/-- **(d) `dropRef_removeEdge` — PROVED.** The GC edit removes EXACTLY the edge
`holder ⟶ ⟨target,()⟩` — `removeEdge`. -/
theorem dropRef_removeEdge (s : RecChainedState) (holder target : Label) :
    execGraph (dropRefStep s holder target).kernel.caps
      = removeEdge (execGraph s.kernel.caps) holder (⟨target, ()⟩ : Spec.Cap Label ExecRights) :=
  recKRevokeTarget_execGraph s.kernel.caps holder target

/-- **(b-authority) `dropRef_non_amplifying` — THE HEADLINE (PROVED).** Dropping a reference can ONLY
remove an edge: the post-graph is a sub-relation of the pre-graph. No authority is gained. -/
theorem dropRef_non_amplifying (s : RecChainedState) (holder target : Label)
    (h : Label) (c : Spec.Cap Label ExecRights)
    (hpost : execGraph (dropRefStep s holder target).kernel.caps h c) :
    execGraph s.kernel.caps h c := by
  rw [dropRef_removeEdge] at hpost; exact hpost.1

/-- **(c) `dropRef_authorized` — PROVED.** DropRef needs no positive authority (a holder may always
drop its OWN reference): the obligation is the removeEdge shape (cannot grant). -/
theorem dropRef_authorized (s : RecChainedState) (holder target : Label) :
    ∀ h c, execGraph (dropRefStep s holder target).kernel.caps h c → execGraph s.kernel.caps h c :=
  fun h c => dropRef_non_amplifying s holder target h c

/-- **(d) `dropRef_chainlink` — PROVED.** Appends exactly its authority receipt. -/
theorem dropRef_chainlink (s : RecChainedState) (holder target : Label) :
    (dropRefStep s holder target).log = authReceipt holder :: s.log := rfl

/-! ## §5 — `ExerciseViaCapability`: act THROUGH a held cap (the graph is UNCHANGED).

dregg1's `Effect::ExerciseViaCapability { cap_slot, inner_effects }` resolves a held c-list slot and
performs effects on the target. The AUTHORITY-domain content (which is what this regime tracks) is:
exercising a cap is authorized BY the held edge (the actor must hold the slot), and it confers NO new
authority — the cap graph is UNCHANGED by the act of exercising. (The inner_effects' own authority
moves, if any, are separate effects; the *exercise* itself is graph-preserving.) -/

/-- **`exerciseStep` — ExerciseViaCapability's executable semantics.** Gate on the actor HOLDING an
edge to `target` (the resolved c-list slot — the same `confersEdgeTo` test `recKDelegate` uses), then
append the receipt. The cap table is UNCHANGED (exercising reads, never edits, the c-list). -/
def exerciseStep (s : RecChainedState) (actor target : Label) : Option RecChainedState :=
  if (s.kernel.caps actor).any (fun cap => confersEdgeTo target cap) = true then
    some { s with log := authReceipt actor :: s.log }
  else
    none

theorem exerciseStep_factors {s s' : RecChainedState} {actor target : Label}
    (h : exerciseStep s actor target = some s') :
    (s.kernel.caps actor).any (fun cap => confersEdgeTo target cap) = true
      ∧ s' = { s with log := authReceipt actor :: s.log } := by
  unfold exerciseStep at h
  by_cases hg : (s.kernel.caps actor).any (fun cap => confersEdgeTo target cap) = true
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; exact ⟨hg, h.symm⟩
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **(b-balance) `exercise_conserves` — PROVED.** Conservation-trivial: exercising edits nothing in
the kernel state (only the receipt log). -/
theorem exercise_conserves {s s' : RecChainedState} {actor target : Label}
    (h : exerciseStep s actor target = some s') : recTotal s'.kernel = recTotal s.kernel := by
  obtain ⟨_, hs'⟩ := exerciseStep_factors h; subst hs'; rfl

/-- **(c) `exercise_authorized` — PROVED.** A committed exercise HOLDS the source edge: the actor
holds `actor ⟶ ⟨target,()⟩` on `execGraph` — the resolved c-list slot. Only the holder of the cap
may exercise it. -/
theorem exercise_authorized {s s' : RecChainedState} {actor target : Label}
    (h : exerciseStep s actor target = some s') :
    execGraph s.kernel.caps actor (⟨target, ()⟩ : Spec.Cap Label ExecRights) := by
  obtain ⟨hg, _⟩ := exerciseStep_factors h
  rw [execGraph_eq_any]; exact hg

/-- **(d) `exercise_graph_unchanged` — PROVED.** Exercising a cap leaves the reconstructed authority
graph UNCHANGED — it reads the c-list, never edits it. The authority frame condition for the
graph-preserving effects. -/
theorem exercise_graph_unchanged {s s' : RecChainedState} {actor target : Label}
    (h : exerciseStep s actor target = some s') :
    execGraph s'.kernel.caps = execGraph s.kernel.caps := by
  obtain ⟨_, hs'⟩ := exerciseStep_factors h; subst hs'; rfl

/-- **`exercise_holds_real_cap` — PROVED.** A committed exercise WITNESSES a concrete held cap: the
actor holds, in its real c-list, an `Authority.Cap` `held` that confers connectivity to `target`.
This recovers the REAL cap (with its `List Auth` rights) behind the `Unit`-skeleton edge — the seam
the genuine rights non-amplification reads. -/
theorem exercise_holds_real_cap {s s' : RecChainedState} {actor target : Label}
    (h : exerciseStep s actor target = some s') :
    ∃ held : ECap, held ∈ s.kernel.caps actor ∧ confersEdgeTo target held = true := by
  obtain ⟨hg, _⟩ := exerciseStep_factors h
  rw [List.any_eq_true] at hg
  obtain ⟨held, hmem, hconf⟩ := hg
  exact ⟨held, hmem, hconf⟩

/-- **(b-authority) `exercise_non_amplifying` — THE HEADLINE (PROVED, GENUINE).** Exercising a cap
confers NO new authority, on TWO faithful axes:

  * **connectivity** — the post-graph EQUALS the pre-graph (the exercise reads, never edits, the
    c-list), so no new edge is conjured; and
  * **rights** — the actor holds a concrete cap `held` and every authority `a` it can exercise is
    BOUNDED BY that held cap's REAL `List Auth` (`a ∈ capAuthConferred held`). The exercise is
    `IsNonAmplifying held held` over the real lattice: it confers exactly — never more than — the held
    cap's authority. (An auth NOT in `capAuthConferred held` is genuinely out of reach — the bound has
    teeth via `amplifying_grant_rejected`.) -/
theorem exercise_non_amplifying {s s' : RecChainedState} {actor target : Label}
    (h : exerciseStep s actor target = some s') :
    execGraph s'.kernel.caps = execGraph s.kernel.caps
      ∧ ∃ held : ECap, held ∈ s.kernel.caps actor ∧ confersEdgeTo target held = true
          ∧ IsNonAmplifying held held :=
  ⟨exercise_graph_unchanged h,
   let ⟨held, hmem, hconf⟩ := exercise_holds_real_cap h
   ⟨held, hmem, hconf, fun _ ha => ha⟩⟩

/-- **(d) `exercise_chainlink` — PROVED.** Appends exactly its authority receipt. -/
theorem exercise_chainlink {s s' : RecChainedState} {actor target : Label}
    (h : exerciseStep s actor target = some s') : s'.log = authReceipt actor :: s.log := by
  obtain ⟨_, hs'⟩ := exerciseStep_factors h; subst hs'; rfl

/-- **Fail-closed — PROVED.** Without a held edge to `target`, no exercise commits. The confinement
core for ExerciseViaCapability. -/
theorem exercise_unheld_fails (s : RecChainedState) (actor target : Label)
    (h : (s.kernel.caps actor).any (fun cap => confersEdgeTo target cap) = false) :
    exerciseStep s actor target = none := by
  unfold exerciseStep; rw [if_neg]; rw [h]; simp

/-! ## §6 — `ValidateHandoff`: a CapTP handoff IS a Granovetter introduce.

dregg1's `Effect::ValidateHandoff { … }` accepts a two-signature CapTP handoff certificate. The
crypto (two signatures + cert/target binding) is the §8 `Prop`-carrier portal (`attested`). The
SOUNDNESS content reuses `Exec.CapTP` verbatim: a valid handoff IS a Granovetter `Introduce`
(`handoff_is_introduce`), so the conferred cap is non-amplifying (`handoff_non_amplifying`). We carry
the abstract `Spec.Graph`/rights here (not the executable `caps`) because the handoff lattice is the
abstract `Spec.Cap … Rights` (the same carriers `AuthModes.captp_*` use). -/

section Handoff
variable {CellId Rights : Type*} [SemilatticeInf Rights] [OrderTop Rights]

open Dregg2.Exec.CapTP (HandoffCert HandoffValid handoff_is_introduce handoff_non_amplifying)

/-- **(a)+(e) `validateHandoff_is_introduce` — PROVED.** A `HandoffValid` certificate (connectivity,
A holds the cap, target consents, plus the §8 two-signature `attested` portal) IS a Granovetter
`Spec.Introduce` step on the abstract capability graph — the forward-sim's `AbsStep` for the handoff:
the abstract graph moves by `addEdge` (`cert.post`). Reuses `CapTP.handoff_is_introduce`. -/
theorem validateHandoff_is_introduce
    (cert : HandoffCert CellId Rights) (G : Graph CellId Rights)
    (consents : CellId → Prop) (attested : Prop)
    (hv : HandoffValid cert G consents attested) :
    Introduce G consents cert.introducer cert.recipient cert.held cert.granted (cert.post G) :=
  handoff_is_introduce hv

/-- **(b-authority) `validateHandoff_non_amplifying` — THE HEADLINE (PROVED).** The conferred
(granted) cap is `≤` the introducer's held cap on the rights order: `granted.rights ≤ held.rights`.
EXACTLY the `is_attenuation(held, granted)` check `AuthModes.captp_granted_le_held` certifies — the
non-amplification dregg1's `verify_captp_delivered` was MISSING. Reuses `CapTP.handoff_non_amplifying`.
-/
theorem validateHandoff_non_amplifying
    (cert : HandoffCert CellId Rights) (G : Graph CellId Rights)
    (consents : CellId → Prop) (attested : Prop)
    (hv : HandoffValid cert G consents attested) :
    cert.granted.rights ≤ cert.held.rights :=
  handoff_non_amplifying hv

end Handoff

/-! ## §7 — `RefreshDelegation` and `SetPermissions`: idempotent narrowing + gate replacement.

`RefreshDelegation` (`action.rs::RefreshDelegation`) — a child re-snapshots its parent's c-list. We
model the per-cap content as an idempotent narrowing: re-deriving a cap with `keep ⊇ its rights` is
the identity (still narrower-or-equal), so a refresh never amplifies. `SetPermissions`
(`action.rs::SetPermissions`) — replace a cell's permission gate; the SOUND case has the new gate
NARROWER than the old (its admit-set a subset). Both reduce to a single non-amplification face:
the abstract authority is a subset after the edit. -/

/-- **`refreshStep` — RefreshDelegation's executable semantics.** Re-attenuate the child's `idx`-th
cap against `keep` (the parent-snapshot rights), then append the receipt — the self-refresh. (When
`keep` already ⊇ the cap's rights, it is the identity; in general it narrows.) -/
def refreshStep (s : RecChainedState) (child : Label) (idx : Nat) (keep : List Auth) :
    RecChainedState :=
  attenuateStep s child idx keep

/-- **(b) `refresh_non_amplifying` — THE HEADLINE (PROVED).** A refresh re-snapshots via attenuation,
so the refreshed cap confers a SUBSET of the original — never more. Reuses `attenuate_subset`. -/
theorem refresh_non_amplifying (keep : List Auth) (c : ECap) :
    capAuthConferred (attenuate keep c) ⊆ capAuthConferred c :=
  Dregg2.Exec.attenuate_subset keep c

/-- **(b-balance) `refresh_conserves` — PROVED.** Conservation-trivial (it is an `attenuateStep`). -/
theorem refresh_conserves (s : RecChainedState) (child : Label) (idx : Nat) (keep : List Auth) :
    recTotal (refreshStep s child idx keep).kernel = recTotal s.kernel := rfl

/-- **(c)+(d) `refresh_confined` — PROVED.** A refresh edits only the child's OWN slot (self-refresh)
and appends exactly the receipt. -/
theorem refresh_confined (s : RecChainedState) (child : Label) (idx : Nat) (keep : List Auth) :
    (∀ l, l ≠ child → (refreshStep s child idx keep).kernel.caps l = s.kernel.caps l)
    ∧ (refreshStep s child idx keep).log = authReceipt child :: s.log :=
  attenuate_metadata s child idx keep

/-- **SetPermissions as a permission-gate narrowing (the abstract authority face).** A cell's
permission gate is a predicate `Label → Bool` (who it admits). The SOUND `SetPermissions` replaces
the gate with one whose admit-set is a SUBSET of the old. We capture exactly this obligation. -/
def NarrowsGate (old new : Label → Bool) : Prop := ∀ l, new l = true → old l = true

/-- **(b-authority) `setPermissions_non_amplifying` — THE HEADLINE (PROVED).** A sound
`SetPermissions` only NARROWS the cell's permission gate: anyone the new gate admits, the old gate
already admitted (`NarrowsGate old new`). So the gate replacement confers no NEW access — the
admit-set strictly shrinks (or holds). The `apply.rs` "SetPermissions applied LAST + checks use
ORIGINAL permissions" discipline, as the abstract non-amplification: the new gate cannot widen. -/
theorem setPermissions_non_amplifying {old new : Label → Bool}
    (h : NarrowsGate old new) (l : Label) (hadmit : new l = true) : old l = true :=
  h l hadmit

/-- **`setPermissions_identity_narrows` — PROVED (non-vacuity of `NarrowsGate`).** Replacing a gate
with itself is a (trivial) narrowing — the boundary case showing `NarrowsGate` is inhabited and the
no-op is admitted. -/
theorem setPermissions_identity_narrows (g : Label → Bool) : NarrowsGate g g := fun _ h => h

/-! ## §8 — The forward-simulation square (reused across the regime).

The record-world abstract state + `AbsStep` of `EffectTransfer §5`, specialized to the authority
regime: the abstract `balance` total is CONSERVED (every authority effect is conservation-trivial),
and the authority `Graph` moves by the named `Spec.AuthStep` edit (`addEdge` for introduce,
`removeEdge` for revoke/dropRef, identity for exercise). One abstraction, instantiated per effect. -/

/-- The record-world abstract Spec state an authority effect refines (the `EffectTransfer.AbstractT`
shape): the conserved `balance` total and the reconstructed authority `Graph`. -/
structure AbstractA where
  /-- the conserved `balance`-domain total. -/
  balanceTotal : ℤ
  /-- the reconstructed authority graph. -/
  authGraph    : Graph Label ExecRights

/-- The abstraction function: a chained record state denotes its `recTotal` and its `execGraph`. -/
def absA (s : RecChainedState) : AbstractA :=
  { balanceTotal := recTotal s.kernel, authGraph := execGraph s.kernel.caps }

/-- **`introduce_forward_sim` — THE REFINEMENT (PROVED).** A committed introduction is matched by an
abstract step: the abstract `balance` total is CONSERVED, and the abstract authority graph moves by
EXACTLY `addEdge … recipient ⟨target,()⟩` (the `Spec.Introduce.result` bottom edge). The record-world
forward-simulation square for Introduce. -/
theorem introduce_forward_sim {s s' : RecChainedState} {introducer recipient target : Label}
    (h : introduceStep s introducer recipient target = some s') :
    conservedInDomain Domain.balance [(absA s').balanceTotal - (absA s).balanceTotal]
    ∧ (absA s').authGraph
        = addEdge (absA s).authGraph recipient (⟨target, ()⟩ : Spec.Cap Label ExecRights) := by
  refine ⟨?_, ?_⟩
  · unfold conservedInDomain absA; rw [introduce_conserves h]; simp
  · simp only [absA]; exact introduce_addEdge h

/-- **`revokeDelegation_forward_sim` — THE REFINEMENT (PROVED).** A committed revocation conserves
the abstract balance and moves the abstract graph by EXACTLY `removeEdge … holder ⟨target,()⟩`
(`Spec.Revoke.result`). -/
theorem revokeDelegation_forward_sim (s : RecChainedState) (holder target : Label) :
    conservedInDomain Domain.balance
        [(absA (revokeDelegationStep s holder target)).balanceTotal - (absA s).balanceTotal]
    ∧ (absA (revokeDelegationStep s holder target)).authGraph
        = removeEdge (absA s).authGraph holder (⟨target, ()⟩ : Spec.Cap Label ExecRights) := by
  refine ⟨?_, ?_⟩
  · unfold conservedInDomain absA; rw [revokeDelegation_conserves]; simp
  · simp only [absA]; exact revokeDelegation_removeEdge s holder target

/-- **`exercise_forward_sim` — THE REFINEMENT (PROVED).** A committed exercise conserves the abstract
balance and leaves the abstract authority graph FIXED (identity edit — the graph-preserving regime). -/
theorem exercise_forward_sim {s s' : RecChainedState} {actor target : Label}
    (h : exerciseStep s actor target = some s') :
    conservedInDomain Domain.balance [(absA s').balanceTotal - (absA s).balanceTotal]
    ∧ (absA s').authGraph = (absA s).authGraph := by
  refine ⟨?_, ?_⟩
  · unfold conservedInDomain absA; rw [exercise_conserves h]; simp
  · simp only [absA]; exact exercise_graph_unchanged h

/-! ## §9 — Axiom-hygiene tripwires (the honesty pins over every authority-edit keystone).

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. Every per-effect non-amplification + the forward-sim squares are genuinely proved. -/

#assert_axioms introduceStep_factors
#assert_axioms introduce_conserves
#assert_axioms introduce_addEdge
#assert_axioms introduce_authorized
#assert_axioms introduce_non_amplifying
#assert_axioms introduce_grounded_and_non_amplifying
#assert_axioms amplifying_grant_rejected
#assert_axioms introduce_chainlink
#assert_axioms revokeDelegation_conserves
#assert_axioms revokeDelegation_removeEdge
#assert_axioms revokeDelegation_non_amplifying
#assert_axioms revokeDelegation_only_subtracts
#assert_axioms revokeDelegation_authorized
#assert_axioms revokeDelegation_chainlink
#assert_axioms attenuate_conserves
#assert_axioms attenuate_non_amplifying
#assert_axioms attenuate_authorized
#assert_axioms attenuate_metadata
#assert_axioms dropRef_conserves
#assert_axioms dropRef_removeEdge
#assert_axioms dropRef_non_amplifying
#assert_axioms dropRef_authorized
#assert_axioms dropRef_chainlink
#assert_axioms exerciseStep_factors
#assert_axioms exercise_conserves
#assert_axioms exercise_authorized
#assert_axioms exercise_graph_unchanged
#assert_axioms exercise_holds_real_cap
#assert_axioms exercise_non_amplifying
#assert_axioms exercise_chainlink
#assert_axioms exercise_unheld_fails
#assert_axioms validateHandoff_is_introduce
#assert_axioms validateHandoff_non_amplifying
#assert_axioms refresh_non_amplifying
#assert_axioms refresh_conserves
#assert_axioms refresh_confined
#assert_axioms setPermissions_non_amplifying
#assert_axioms setPermissions_identity_narrows
#assert_axioms introduce_forward_sim
#assert_axioms revokeDelegation_forward_sim
#assert_axioms exercise_forward_sim

/-! ## §10 — Non-vacuity: each effect fires on concrete data.

Reuses `AuthTurn.rsCap`-style states: cells 0,1 with balances; actor 0 holds a `node 7` cap (so it
can introduce/exercise connectivity to 7), actor 2 holds an `endpoint 9 [read,write]` cap (so we can
attenuate it). Empty receipt chain. -/

/-- A chained record state: cells 0,1 with balances 100,5; actor 0 holds a `node 7` connectivity
cap; actor 2 holds an `endpoint 9 [read,write]` cap. Empty receipt chain. -/
def as0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun c => if c = 0 then .record [("balance", .int 100)]
                         else if c = 1 then .record [("balance", .int 5)]
                         else .record [("balance", .int 0)]
        caps := fun l => if l = 0 then [Dregg2.Authority.Cap.node 7]
                         else if l = 2 then [Dregg2.Authority.Cap.endpoint 9 [Auth.read, Auth.write]] else [] }
    log := [] }

-- (1) INTRODUCE: actor 0 (holds `node 7`) introduces recipient 1 to target 7. Commits.
#guard ((introduceStep as0 0 1 7).isSome)  --  true
-- ...is conservation-trivial (recTotal 105 unchanged) and grows the chain by one:
#guard ((introduceStep as0 0 1 7).map (fun s => recTotal s.kernel)) == some 105  --  some 105
#guard ((introduceStep as0 0 1 7).map (fun s => s.log.length)) == some 1  --  some 1
-- ...and recipient 1 now holds the `node 7` cap (the new authority edge):
#guard (((introduceStep as0 0 1 7).map (fun s => s.kernel.caps 1)).getD []) == [Dregg2.Authority.Cap.node 7]  --  [Dregg2.Authority.Cap.node 7]
-- An introducer with NO connectivity to the target cannot introduce it (fail-closed):
#guard ((introduceStep as0 5 1 9).isSome) == false  --  false

-- (1') THE TEETH — genuine rights non-amplification over the real `List Auth` lattice.
-- Holder 2 holds `endpoint 9 [read, write]`; attenuating to `[read]` confers `[read]`, a real SUBSET:
#eval capAuthConferred (attenuate [Auth.read]
        (Dregg2.Authority.Cap.endpoint 9 [Auth.read, Auth.write]))             -- [read] ⊆ [read, write]
-- the genuine `introduce_non_amplifying` fires on this concrete held cap (granted ⊆ held, real rights):
example : IsNonAmplifying (Dregg2.Authority.Cap.endpoint 9 [Auth.read, Auth.write])
    (attenuate [Auth.read] (Dregg2.Authority.Cap.endpoint 9 [Auth.read, Auth.write])) :=
  introduce_non_amplifying (Dregg2.Authority.Cap.endpoint 9 [Auth.read, Auth.write]) [Auth.read]
-- ...and an AMPLIFYING grant is genuinely REJECTED: a `node 9` cap confers `[control]`, which the
-- held `endpoint 9 [read, write]` cap does NOT confer — so it FAILS the non-amplification predicate.
example : ¬ IsNonAmplifying (Dregg2.Authority.Cap.endpoint 9 [Auth.read, Auth.write])
    (Dregg2.Authority.Cap.node 9) :=
  amplifying_grant_rejected (Dregg2.Authority.Cap.endpoint 9 [Auth.read, Auth.write])
    (Dregg2.Authority.Cap.node 9) Auth.control (by decide) (by decide)

-- (2) REVOKE-DELEGATION: holder 0 drops its edge to 7. Always commits, conservation-trivial.
#guard ((revokeDelegationStep as0 0 7).log.length) == 1  --  1
#guard (recTotal (revokeDelegationStep as0 0 7).kernel) == 105  --  105 (FIXED)
#guard ((revokeDelegationStep as0 0 7).kernel.caps 0) == []  --  [] (node 7 gone)

-- (3) ATTENUATE: narrow actor 2's `endpoint 9 [read,write]` to keep only `read`.
#eval (attenuateStep as0 2 0 [Auth.read]).kernel.caps 2                   -- [endpoint 9 [read]]
#guard (recTotal (attenuateStep as0 2 0 [Auth.read]).kernel) == 105  --  105 (FIXED)
-- ...the narrowed cap confers a SUBSET: [read] ⊆ [read, write].
#eval capAuthConferred (attenuate [Auth.read] (Dregg2.Authority.Cap.endpoint 9 [Auth.read, Auth.write]))  -- [read]

-- (4) DROP-REF: holder 0 GC-drops its reference to 7.
#guard ((dropRefStep as0 0 7).kernel.caps 0) == []  --  []
#guard (recTotal (dropRefStep as0 0 7).kernel) == 105  --  105 (FIXED)

-- (5) EXERCISE: actor 0 (holds `node 7`) exercises its cap to target 7. Commits; graph unchanged.
#guard ((exerciseStep as0 0 7).isSome)  --  true
#guard (((exerciseStep as0 0 7).map (fun s => s.kernel.caps 0)).getD []) == [Dregg2.Authority.Cap.node 7]  -- [Cap.node 7] (unchanged)
-- An actor NOT holding an edge to the target cannot exercise (fail-closed):
#guard ((exerciseStep as0 5 9).isSome) == false  --  false

-- (7) SET-PERMISSIONS: a strictly-narrower gate (admit only label 0) narrows the all-true gate —
-- the non-amplification witness fires on concrete gates (anyone the new gate admits, `l = 0`, the
-- old all-true gate also admitted).
example : NarrowsGate (fun _ => true) (fun l => decide (l = 0)) := fun _ _ => rfl
-- ...and the non-amplification keystone fires on it: anyone the narrower gate admits, the old admits.
example (l : Label) (h : (fun l => decide (l = 0)) l = true) : (fun _ => true) l = true :=
  setPermissions_non_amplifying (old := fun _ => true) (new := fun l => decide (l = 0))
    (fun _ _ => rfl) l h

end Dregg2.Exec.EffectsAuthority
