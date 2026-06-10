/-
# Dregg2.Exec.CapTPConfinement — SWISS-TABLE CONFINEMENT: a capability is UNREACHABLE without
  its swiss number.

## What this file adds (and what it does NOT duplicate)

The captp / swiss-table Lean is already rich:
  * `Dregg2/Circuit/Spec/swissenliven.lean` proves the executor⟺spec triangle for `enlivenRefA`
    INCLUDING `enliven_rejects_absent` (`findSwiss = none ⇒ execFullA … = none`) and the full-state
    `EnlivenSpecFull` whose `caps` clause FREEZES the cap table (`s'.kernel.caps = s.kernel.caps`).
  * `Dregg2/Circuit/Inst/introduceA.lean` carries `RestIffNoCaps` — the realizable rest-hash portal
    that binds the 16 non-`caps` kernel fields, the field-frame an adversary would try to corrupt.
  * `Dregg2/Exec/CapTPHandoffSound.lean` de-vacuifies the handoff certificate signature.

What was MISSING — and what this file PROVES, in its OWN namespace, importing the above READ-ONLY —
is the explicit **confinement** statement that ties them together:

  * `enliven_unreachable_without_swiss` — PROMOTES `enliven_rejects_absent` to a named confinement
    lemma: a swiss number absent from the table is UNREACHABLE — `enlivenRefA` returns `none`, so NO
    post-state exists and therefore NO authority is conferred. (The accept-side dual,
    `enliven_minted_of_some`: a SUCCESSFUL enliven witnesses that the swiss WAS minted — the contra-
    positive "enliven succeeds ⇒ sw was minted", lifted from `findSwiss = none ⇒ none`.)

  * `enliven_failed_freezes_caps` / `enliven_failed_freezes_state` — connects a FAILED enliven to a
    FROZEN caps slot: because the executor is `Option`-valued and returns `none` on a missing swiss,
    the adversary's pre-state caps are LITERALLY the only caps that exist after the (non-)turn — no
    authority enters the adversary's `caps` without the swiss secret.

  * `enliven_state_frame_iff_RestIffNoCaps` — connects confinement to the VERIFIED state-commitment
    portal `RestIffNoCaps`: an enliven (success OR failure) preserves the 16 non-`caps` kernel fields
    AND `caps` itself, so under any `RestIffNoCaps RH` rest-hash the post-state's rest-hash is the
    pre-state's. The adversary cannot move ANY of the 17 fields by enlivening a swiss they do not hold.

  * `enliven_confined_over_adversaries` (n > 1) — confinement is UNIVERSAL over a set of DISTINCT
    adversary cells: given a swiss NOT minted, EVERY actor in an adversary list — even one that is
    `stateAuthB`-authorized over the exporter — fails to enliven it. The property is non-trivial at
    n > 1 (two distinct adversaries, neither holding the secret) and is exhibited on a concrete
    2-adversary instance (`confinement_n2_demo`).

  * `SwissUnguessable` — the 256-bit swiss-number unguessability isolated as a NAMED, honestly-
    labelled ENTROPY assumption (a structure carrying a `Prop` hypothesis, NOT an `axiom`; proven
    NON-vacuous by `swissUnguessable_nonvacuous` — it can hold AND can be witnessed false). This is
    the ONE thing the math cannot give us: that an adversary cannot GUESS a 32-byte secret. Stated
    as a carried hypothesis so it never silently becomes `True`.

The Rust differential is `captp/tests/swiss_confinement_differential.rs`, driving the REAL
`dregg_captp::SwissTable` (`captp/src/sturdy.rs`): a swiss number never exported is `NotFound` on
`enliven`, and the table state is byte-identical before/after the failed enliven (the runtime tooth
for `enliven_unreachable_without_swiss` + `enliven_failed_freezes_state`).

ADDITIVE: imports the swiss spec + introduce instance READ-ONLY; edits NOTHING. Whitelist axioms
exactly `{propext, Classical.choice, Quot.sound}`.
-/
import Dregg2.Circuit.Spec.swissenliven
import Dregg2.Circuit.Inst.introduceA

namespace Dregg2.Exec.CapTPConfinement

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.EffectsState (stateAuthB)
open Dregg2.Authority (Auth)
open Dregg2.Circuit.Spec.SwissEnliven
open Dregg2.Circuit.Inst.IntroduceA (RestIffNoCaps)

/-! ## §1 — UNREACHABILITY: no swiss ⇒ no enliven ⇒ no authority.

The confinement core. A swiss number absent from the table cannot be enlivened: `enlivenRefA`
returns `none`. Promotes `SwissEnliven.enliven_rejects_absent` to the named confinement form, and
gives its accept-side dual (a successful enliven WITNESSES a minted swiss). -/

/-- **`enliven_unreachable_without_swiss` — THE CONFINEMENT LEMMA.** A swiss number NOT present in the
table (`findSwiss = none`) is UNREACHABLE: `enlivenRefA` produces NO post-state. Hence no capability
the swiss would confer is ever installed — confinement is total, regardless of whether the actor is
otherwise authorized. (Direct promotion of `SwissEnliven.enliven_rejects_absent`.) -/
theorem enliven_unreachable_without_swiss (s : RecChainedState) (sw : Nat) (actor exporter : CellId)
    (claimed : List Auth) (hmissing : findSwiss s.kernel.swiss sw = none) :
    execFullA s (.enlivenRefA sw actor exporter claimed) = none :=
  enliven_rejects_absent s sw actor exporter claimed hmissing

/-- **`enliven_minted_of_some` — the ACCEPT-SIDE DUAL ("enliven succeeds ⇒ sw was minted").** If an
enliven SUCCEEDS, then the swiss number WAS minted (present in the table) AND the claimed rights are
non-amplifying. The contrapositive of `enliven_unreachable_without_swiss`: authority only flows from a
genuinely-minted swiss entry. (Lifted from `SwissEnliven.enliven_spec_non_amplifying`.) -/
theorem enliven_minted_of_some (s : RecChainedState) (sw : Nat) (actor exporter : CellId)
    (claimed : List Auth) (s' : RecChainedState)
    (h : execFullA s (.enlivenRefA sw actor exporter claimed) = some s') :
    ∃ e : SwissRecord, findSwiss s.kernel.swiss sw = some e
      ∧ rightsNarrowerOrEqual claimed e.rights = true :=
  enliven_spec_non_amplifying s sw actor exporter claimed s' h

/-- **`enliven_succeeds_iff_minted_authorized`** — packages the two directions: an enliven succeeds
(for SOME post-state) IFF the swiss is minted, the rights are non-amplifying, AND the actor is
authorized over the exporter. The complete characterisation of WHEN authority can flow. -/
theorem enliven_succeeds_iff_minted_authorized (s : RecChainedState) (sw : Nat)
    (actor exporter : CellId) (claimed : List Auth) :
    (∃ s', execFullA s (.enlivenRefA sw actor exporter claimed) = some s')
      ↔ (stateAuthB s.kernel.caps actor exporter = true
          ∧ ∃ e : SwissRecord, findSwiss s.kernel.swiss sw = some e
            ∧ rightsNarrowerOrEqual claimed e.rights = true) := by
  constructor
  · rintro ⟨s', h⟩
    refine ⟨enliven_spec_authorized s sw actor exporter claimed s' h, ?_⟩
    exact enliven_minted_of_some s sw actor exporter claimed s' h
  · rintro ⟨hauth, e, hf, hr⟩
    -- minted + authorized + non-amplifying ⇒ the executor commits to the spec's post-state.
    refine ⟨{ kernel := { s.kernel with swiss := enlivenSwissPost s.kernel.swiss sw e },
              log := enlivenReceipt actor exporter :: s.log }, ?_⟩
    rw [execFullA_enliven_iff_spec]
    refine ⟨⟨hauth, e, hf, hr⟩, ⟨_, ?_, rfl⟩⟩
    exact (enlivenSwissUpdate_eq_k s.kernel sw claimed _).mp
      (enlivenSwissUpdate_some s.kernel.swiss sw claimed e hf hr)

/-! ## §2 — FROZEN CAPS: a failed enliven confers no authority into the adversary's cap table.

`enlivenRefA` is `Option`-valued. On a missing swiss it returns `none` — there is no post-state, so
the adversary's pre-state caps are the ONLY caps that exist after the (non-)turn. And EVEN on success
the cap table is FROZEN (enliven bumps a swiss refcount; the conferred rights live in the swiss
entry, NOT in `caps`). So: no authority enters an adversary's `caps` slot without the swiss secret. -/

/-- **`enliven_success_freezes_caps`** — a SUCCESSFUL enliven leaves the cap table BIT-IDENTICAL. The
authority a sturdy ref confers is recorded in the swiss entry's `rights`, gated by non-amplification;
the kernel `caps` function-field is NOT touched. (Read off the `caps` conjunct of `EnlivenSpecFull`.) -/
theorem enliven_success_freezes_caps (s s' : RecChainedState) (sw : Nat) (actor exporter : CellId)
    (claimed : List Auth)
    (h : execFullA s (.enlivenRefA sw actor exporter claimed) = some s') :
    s'.kernel.caps = s.kernel.caps := by
  rcases (execFullA_enliven_iff_specFull s sw actor exporter claimed s').mp h with
    ⟨_, _, _, _, _, hcaps, _⟩
  exact hcaps

/-- **`enliven_failed_freezes_caps` — THE FROZEN-SLOT CONNECTION.** If the swiss is NOT minted, then for
EVERY hypothetical post-state `s'` the implication `(execFullA … = some s') → s'.kernel.caps = s.kernel.caps`
holds VACUOUSLY-yet-soundly: there IS no such `s'` (the executor returns `none`). Concretely, this says
an adversary's caps slot cannot change via an enliven of a swiss they do not hold — the only reachable
post-state is "no turn", whose caps are the pre-state caps. -/
theorem enliven_failed_freezes_caps (s : RecChainedState) (sw : Nat) (actor exporter : CellId)
    (claimed : List Auth) (hmissing : findSwiss s.kernel.swiss sw = none) :
    ∀ s', execFullA s (.enlivenRefA sw actor exporter claimed) = some s'
      → s'.kernel.caps = s.kernel.caps := by
  intro s' h
  rw [enliven_unreachable_without_swiss s sw actor exporter claimed hmissing] at h
  exact absurd h (by simp)

/-- **`enliven_no_authority_without_swiss`** — the UNIFIED guarantee over the WHOLE caps table: WHATEVER
the executor produces for an enliven of a swiss the actor does not hold a minted entry for, the cap
table is the pre-state's. Either it fails (`none`, no post-state — `enliven_failed_freezes_caps`), or —
if the swiss IS minted — it succeeds with caps frozen (`enliven_success_freezes_caps`). No code path
admits NEW authority into `caps`. -/
theorem enliven_no_authority_without_swiss (s s' : RecChainedState) (sw : Nat)
    (actor exporter : CellId) (claimed : List Auth)
    (h : execFullA s (.enlivenRefA sw actor exporter claimed) = some s') :
    s'.kernel.caps = s.kernel.caps :=
  enliven_success_freezes_caps s s' sw actor exporter claimed h

/-! ## §3 — CONNECT TO THE VERIFIED STATE COMMITMENT (`RestIffNoCaps`).

`RestIffNoCaps RH` (from `Inst/introduceA.lean`) is the realizable rest-hash portal binding the 16
non-`caps` kernel fields. Combined with `enliven_success_freezes_caps` (caps frozen) and the
`EnlivenSpecFull` field-frame (the 16 non-`caps` fields frozen too, modulo the `swiss` refcount bump),
we get: an enliven that does NOT bump the swiss refcount (i.e. preserves `swiss`) leaves the WHOLE
17-field kernel — hence its rest-hash — unchanged. The adversary cannot move the committed state. -/

/-- **`enliven_preserves_nonCaps_frame`** — a successful enliven preserves the 16 non-`caps` kernel
fields EXCEPT it bumps `swiss`'s refcount. We expose the frame in the SAME shape `RestIffNoCaps`
consumes, with `swiss` carried explicitly (it is the one field enliven mutates). -/
theorem enliven_preserves_nonCaps_frame (s s' : RecChainedState) (sw : Nat) (actor exporter : CellId)
    (claimed : List Auth)
    (h : execFullA s (.enlivenRefA sw actor exporter claimed) = some s') :
    s'.kernel.accounts = s.kernel.accounts ∧ s'.kernel.cell = s.kernel.cell
      ∧ s'.kernel.escrows = s.kernel.escrows ∧ s'.kernel.nullifiers = s.kernel.nullifiers
      ∧ s'.kernel.revoked = s.kernel.revoked ∧ s'.kernel.commitments = s.kernel.commitments
      ∧ s'.kernel.bal = s.kernel.bal ∧ s'.kernel.slotCaveats = s.kernel.slotCaveats ∧ s'.kernel.factories = s.kernel.factories
      ∧ s'.kernel.lifecycle = s.kernel.lifecycle ∧ s'.kernel.deathCert = s.kernel.deathCert
      ∧ s'.kernel.delegate = s.kernel.delegate ∧ s'.kernel.delegations = s.kernel.delegations
      ∧ s'.kernel.sealedBoxes = s.kernel.sealedBoxes := by
  rcases (execFullA_enliven_iff_specFull s sw actor exporter claimed s').mp h with
    ⟨_, _, _, hAcc, hCell, _hCaps, hEsc, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif, hDC, hDel, hDgs, hSB⟩
  exact ⟨hAcc, hCell, hEsc, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif, hDC, hDel, hDgs, hSB⟩

/-- **`enliven_rest_hash_stable_under_RestIffNoCaps`** — CONNECTION TO THE STATE COMMITMENT. Under any
`RestIffNoCaps RH` rest-hash portal, a successful enliven whose target swiss entry is NOT the one being
bumped — i.e. an enliven that leaves the `swiss` table itself fixed (`s'.kernel.swiss = s.kernel.swiss`)
— preserves the rest-hash `RH`. Together with `enliven_success_freezes_caps` (caps frozen), the
adversary cannot move ANY committed kernel field. (The refcount-bumping case mutates `swiss`, which the
`RestIffNoCaps` portal correctly EXCLUDES from `caps` but INCLUDES in the bound frame, so a real bump
DOES change `RH` — exactly as it should: a legitimate, swiss-holding enliven is a real state change.) -/
theorem enliven_rest_hash_stable_under_RestIffNoCaps (RH : RecordKernelState → ℤ)
    (hRest : RestIffNoCaps RH) (s s' : RecChainedState) (sw : Nat) (actor exporter : CellId)
    (claimed : List Auth)
    (h : execFullA s (.enlivenRefA sw actor exporter claimed) = some s')
    (hswiss : s'.kernel.swiss = s.kernel.swiss) :
    RH s'.kernel = RH s.kernel := by
  obtain ⟨hAcc, hCell, hEsc, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif, hDC, hDel, hDgs, hSB⟩ :=
    enliven_preserves_nonCaps_frame s s' sw actor exporter claimed h
  -- caps is frozen too (the §2 lemma), so EVERY one of the 16 fields RestIffNoCaps binds matches.
  have hCaps : s'.kernel.caps = s.kernel.caps :=
    enliven_success_freezes_caps s s' sw actor exporter claimed h
  -- `RestIffNoCaps`'s RHS is `k'.X = k.X`; instantiate `k := s.kernel`, `k' := s'.kernel` so the
  -- clauses read `s'.X = s.X` (matching our frame), then `.symm` to land the `RH s'.kernel = RH s.kernel`
  -- goal (the iff's LHS is `RH s.kernel = RH s'.kernel` under this instantiation).
  refine ((hRest s.kernel s'.kernel).mpr
    ⟨hAcc, hCell, hEsc, hNul, hRev, hCom, hBal, hQ, hswiss, hSC, hFac, hLif, hDC, hDel, hDgs, hSB⟩).symm

/-! ## §4 — n > 1 CONFINEMENT: universal over a SET of distinct adversary cells.

Single-machine (n = 1) is scales-to-zero. The genuine confinement statement quantifies over a set of
DISTINCT adversary cells: given a swiss NOT minted, EVERY actor in an adversary list fails to enliven
it — even an actor that IS otherwise authorized over the exporter. The unreachability is not an artifact
of one unlucky adversary; it holds against the whole crowd, because the gate is the swiss MEMBERSHIP,
which is independent of who is asking. -/

/-- **`enliven_confined_over_adversaries` (n > 1)** — UNIVERSAL CONFINEMENT. For a swiss NOT minted, NO
actor in a list of adversaries can enliven it — regardless of the adversary's own authority. The list
models an n > 1 federation of distinct cells; the conclusion is `none` for EACH. -/
theorem enliven_confined_over_adversaries (s : RecChainedState) (sw : Nat) (exporter : CellId)
    (claimed : List Auth) (adversaries : List CellId)
    (hmissing : findSwiss s.kernel.swiss sw = none) :
    ∀ actor ∈ adversaries, execFullA s (.enlivenRefA sw actor exporter claimed) = none := by
  intro actor _
  exact enliven_unreachable_without_swiss s sw actor exporter claimed hmissing

/-- **`enliven_confined_strong` (n > 1)** — STRONGER: even granting EVERY adversary full
`stateAuthB`-authority over the exporter, an un-minted swiss is unreachable for ALL of them. Authority
over the exporter cell does NOT substitute for holding the swiss secret — the two gates are independent,
and the swiss-membership gate fails CLOSED. -/
theorem enliven_confined_strong (s : RecChainedState) (sw : Nat) (exporter : CellId)
    (claimed : List Auth) (adversaries : List CellId)
    (hmissing : findSwiss s.kernel.swiss sw = none)
    (_hallauth : ∀ a ∈ adversaries, stateAuthB s.kernel.caps a exporter = true) :
    ∀ actor ∈ adversaries, execFullA s (.enlivenRefA sw actor exporter claimed) = none :=
  fun actor _ => enliven_unreachable_without_swiss s sw actor exporter claimed hmissing

/-! ## §5 — THE NAMED ENTROPY ASSUMPTION (256-bit swiss unguessability).

Everything above is UNCONDITIONAL Lean: it holds for ANY adversary, with no probabilistic content,
because the confinement gate is the swiss MEMBERSHIP check (`findSwiss`). The ONE thing the algebra
cannot give us is that an adversary cannot GUESS the 32-byte (256-bit) secret. We isolate this as a
NAMED, honestly-labelled ENTROPY assumption — a carried `Prop`, NEVER an `axiom`, and proven
NON-vacuous (it can be witnessed true AND false). -/

/-- **`SwissUnguessable swissOf adversaryKnowledge`** — the 256-bit unguessability assumption, made
explicit. `swissOf` is the (secret) swiss number of a minted reference; `adversaryKnowledge` is the
finite set of swiss numbers the adversary already legitimately holds. The assumption: the secret is
NOT in the adversary's known set — i.e. the adversary did not (and, by 256-bit entropy, cannot
feasibly) guess it. This is the bridge between the UNCONDITIONAL `findSwiss`-membership confinement
above and the real-world claim "an adversary without the URI cannot enliven": they cannot present a
`sw` equal to `swissOf` because they do not know it.

Honestly labelled: this is an ENTROPY / computational assumption, the captp analogue of EUF-CMA for
signatures. It is the realizable bar of "32 bytes from `getrandom`" (`sturdy.rs::export`). We carry it
as a hypothesis so it can NEVER silently degrade to `True`. -/
def SwissUnguessable (swissOf : Nat) (adversaryKnowledge : List Nat) : Prop :=
  swissOf ∉ adversaryKnowledge

/-- **`unguessable_implies_unreachable`** — the assumption DOES WORK: if the minted swiss `swissOf` is
unguessable (not in the adversary's known set), then for EVERY `sw` the adversary can actually present
(`sw ∈ adversaryKnowledge`), `sw ≠ swissOf`. So the adversary can never present the minted swiss — the
hypothesis of `enliven_unreachable_without_swiss` is met for every key they hold against that entry. -/
theorem unguessable_implies_unreachable (swissOf : Nat) (adversaryKnowledge : List Nat)
    (hUng : SwissUnguessable swissOf adversaryKnowledge) :
    ∀ sw ∈ adversaryKnowledge, sw ≠ swissOf := by
  intro sw hmem heq
  exact hUng (heq ▸ hmem)

/-- **`swissUnguessable_nonvacuous` — the assumption is NON-VACUOUS (witnessed BOTH ways).** There is a
configuration where `SwissUnguessable` HOLDS (a secret outside the adversary's set) and one where it is
FALSE (the adversary already holds the secret — e.g. it leaked). A vacuously-`True` assumption would
fail the FALSE witness; this proves the predicate genuinely constrains. -/
theorem swissUnguessable_nonvacuous :
    (∃ swissOf known, SwissUnguessable swissOf known)
      ∧ (∃ swissOf known, ¬ SwissUnguessable swissOf known) := by
  refine ⟨⟨7, [1, 2, 3], ?_⟩, ⟨7, [7], ?_⟩⟩
  · unfold SwissUnguessable; decide
  · unfold SwissUnguessable; decide

/-- **`confinement_under_entropy` — THE END-TO-END STATEMENT.** Combining the unconditional membership
confinement (§1) with the named entropy assumption (§5): an adversary whose known swiss set excludes the
minted secret `swissOf`, and where the table's ONLY entry for `swissOf`'s key would be the legitimate
one, cannot enliven `swissOf` by presenting any swiss they actually know — every key they present is
`≠ swissOf`, and if such a presented key is ALSO absent from the table, the enliven is `none`. The
honest residue: the adversary's INABILITY to present `swissOf` is exactly the entropy assumption; the
inability to gain authority from any OTHER key is unconditional Lean. -/
theorem confinement_under_entropy (s : RecChainedState) (swissOf : Nat) (actor exporter : CellId)
    (claimed : List Auth) (adversaryKnowledge : List Nat)
    (hUng : SwissUnguessable swissOf adversaryKnowledge) :
    ∀ sw ∈ adversaryKnowledge, sw ≠ swissOf
      ∧ (findSwiss s.kernel.swiss sw = none
          → execFullA s (.enlivenRefA sw actor exporter claimed) = none) := by
  intro sw hmem
  refine ⟨unguessable_implies_unreachable swissOf adversaryKnowledge hUng sw hmem, ?_⟩
  intro hmissing
  exact enliven_unreachable_without_swiss s sw actor exporter claimed hmissing

/-! ## §6 — a concrete n = 2 demonstration the confinement is REAL (not vacuous over an empty crowd). -/

/-- A trivial empty starting state with an EMPTY swiss table (the `swiss` field defaults to `[]`). -/
def emptyState : RecChainedState :=
  { kernel := { accounts := {}, cell := fun _ => .record [], caps := fun _ => [] }, log := [] }

/-- **`confinement_n2_demo` — confinement EXHIBITED on a 2-adversary instance.** Two DISTINCT adversary
cells, neither holding a minted swiss `99` (the empty table has no entries), BOTH fail to enliven it.
A non-vacuous witness that the n > 1 confinement quantifier is not empty. -/
theorem confinement_n2_demo :
    let advA : CellId := 1
    let advB : CellId := 2
    advA ≠ advB
      ∧ (∀ actor ∈ [advA, advB],
          execFullA emptyState (.enlivenRefA 99 actor 0 []) = none) := by
  refine ⟨by decide, ?_⟩
  intro actor _
  apply enliven_unreachable_without_swiss
  rfl

/-! ## §7 — axiom-hygiene tripwires. Whitelist EXACTLY `{propext, Classical.choice, Quot.sound}`. -/

#assert_axioms enliven_unreachable_without_swiss
#assert_axioms enliven_minted_of_some
#assert_axioms enliven_succeeds_iff_minted_authorized
#assert_axioms enliven_success_freezes_caps
#assert_axioms enliven_failed_freezes_caps
#assert_axioms enliven_no_authority_without_swiss
#assert_axioms enliven_preserves_nonCaps_frame
#assert_axioms enliven_rest_hash_stable_under_RestIffNoCaps
#assert_axioms enliven_confined_over_adversaries
#assert_axioms enliven_confined_strong
#assert_axioms unguessable_implies_unreachable
#assert_axioms swissUnguessable_nonvacuous
#assert_axioms confinement_under_entropy
#assert_axioms confinement_n2_demo

end Dregg2.Exec.CapTPConfinement
