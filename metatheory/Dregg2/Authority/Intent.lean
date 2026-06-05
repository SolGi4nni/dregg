/-
# Dregg2.Authority.Intent — the intent face: the ∃-resolver / inverse vat boundary.

An **intent** gates an *incoming filler*: a predicate `want : P` fires when any filler
`w : W` with `Verify want w = true` arrives. This is the inverse of the vat boundary,
which gates an *outgoing* settled turn.

The asymmetry between the two sides is carried in the types:
- **VERIFY is tractable and in-TCB**: `Verifiable.Verify : P → W → Bool` is a total
  decidable function; the cell can always decide acceptance.
- **FIND is undecidable and untrusted**: `Searchable.find : P → Option W` is an opaque
  plugin with no completeness, termination, or `Decidable` promise. It may return `none`,
  loop (modelled by `Option`), or return a wrong fill. Its only contract is
  soundness-by-verification (`Laws.search_sound`).

The keystone (`intent_fill_verifies`): whatever an untrusted matcher returns, if the
cell's VERIFY accepts it, the fill genuinely satisfies the predicate. Soundness rests on
VERIFY alone; FIND is never trusted.

Reuses `Verifiable`/`Discharged`/`Searchable`/`find`/`search_sound`/`Await` unchanged.
Pure, `#eval`-able.
-/
import Dregg2.Laws
import Dregg2.Await
import Dregg2.Authority.Positional

namespace Dregg2.Authority

open Dregg2.Laws
open Dregg2.Await (intent)

universe u

/-! ## 1. The intent — an existentially-quantified hole over the verify side. -/

/-- **`Intent P W` — an existentially-quantified hole.** It carries only its *shape*:
the predicate `want : P` that any filler must discharge. It is *not* a named promise to a
specified party (that is `zkpromise`/`discharge`, `Await.lean` Faces 1–2) — it fires for
*any* `w : W` with `Verify want w = true`. This is the structural minimum of the intent
face; the captured one-shot continuation lives on `Await.intent` (Face 3), to which this
connects via `ofAwait`/`toAwait` below. -/
structure Intent (P : Type u) (W : Type u) where
  /-- The hole's shape: the predicate any incoming filler must satisfy. -/
  want : P

/-- **`Intent.Fires i`** — the existential firing condition: the intent resolves exactly
when *there exists* a filler discharging its predicate. This is the `∃`-resolver
semantics ("a hole that fires when filled") stated over the `Laws.Discharged` verify
side — deliberately a `Prop` (it asserts existence), NOT a `Bool` (deciding it is the
undecidable FIND problem, not the tractable VERIFY problem). -/
def Intent.Fires [Verifiable P W] (i : Intent P W) : Prop :=
  ∃ w : W, Discharged i.want w

/-- **`Intent.Accepts i w`** — the *decidable* acceptance check the owning cell runs on a
**claimed** fill `w`. Unlike `Fires` (an existential `Prop`), this is grounded at a
specific `w` and is therefore exactly `Discharged i.want w`, which is decidable. This is
the VERIFY side made local to the intent. -/
def Intent.Accepts [Verifiable P W] (i : Intent P W) (w : W) : Prop :=
  Discharged i.want w

/-- **VERIFY is decidable (the in-TCB half of the seam).** The owning cell can *always*
decide whether to accept a claimed fill. This instance is the type-level witness that
`Verify`/`Accepts` is tractable; the matcher `find` below carries NO analogous instance,
which is the asymmetry made precise. -/
instance [Verifiable P W] (i : Intent P W) (w : W) : Decidable (Intent.Accepts i w) := by
  unfold Intent.Accepts; infer_instance

/-! ## 2. The fill / resolve mechanism — untrusted matcher proposes, cell verifies. -/

/-- **`Intent.propose i` — the matcher proposes a fill.** The matcher plugin is the
`Searchable.find` of `Laws.lean`, applied to the intent's predicate. It returns
`Option W`: `some w` is a *proposed* fill (NOT yet trusted — the cell must still VERIFY
it), `none` is "I found nothing / I gave up" (the plugin may be partial or
nonterminating; `Option` models that). Crucially there is no `Decidable`/completeness
guarantee on this: `find` is opaque. -/
def Intent.propose [Searchable P W] (i : Intent P W) : Option W :=
  Searchable.find i.want

/-- **`Intent.resolve i` — the cell resolves the intent.** The two-step protocol made
one function: (1) the untrusted matcher *proposes* a fill via `propose`; (2) the cell
*verifies* it with the decidable `Verify`, keeping it only if it actually discharges the
predicate. The result is `some w` ONLY for a fill that both the matcher returned *and*
the cell accepted. A matcher that returns a non-satisfying (or adversarial) fill is
filtered out here — soundness is enforced by VERIFY, never by trusting FIND. -/
def Intent.resolve [Verifiable P W] [Searchable P W] (i : Intent P W) : Option W :=
  match Searchable.find i.want with
  | none   => none
  | some w => if Verifiable.Verify i.want w then some w else none

/-! ## 3. The keystone — soundness-by-verification at the intent. -/

/-- **`intent_fill_verifies` (keystone, part (a))** — if `resolve` yields `some w`, then
`w` discharges the intent's predicate. The matcher may be buggy or adversarial; the
accepted fill is sound because acceptance gates on the decidable `Verify`. (`resolve`
re-checks `Verify` itself, so no appeal to `search_sound` is needed.) -/
theorem intent_fill_verifies
    [Verifiable P W] [Searchable P W] (i : Intent P W) (w : W)
    (h : i.resolve = some w) :
    Discharged i.want w := by
  unfold Intent.resolve at h
  cases hf : (Searchable.find i.want : Option W) with
  | none => rw [hf] at h; exact absurd h (by simp)
  | some v =>
    rw [hf] at h
    simp only at h  -- reduce the `match some v with …` to its `some` arm
    by_cases hv : Verifiable.Verify i.want v = true
    · -- accepted: `h : some v = some w` ⇒ `v = w`; `Verify want v = true` is `Discharged`.
      simp only [hv, if_pos] at h
      have : v = w := by injection h
      subst this
      exact hv
    · -- rejected by VERIFY: the if-branch is `none`, contradicting `… = some w`.
      rw [Bool.not_eq_true] at hv
      rw [hv] at h
      simp only [Bool.false_eq_true, if_false] at h
      exact absurd h (by simp)

/-- **`intent_accepts_discharged_def`** — a definitional unfold, NOT a theorem with
content. `Intent.Accepts` is *defined* as `Discharged i.want w` (see §1), so this `Iff` is
`Iff.rfl`: it records, for callers, that `Accepts` is a transparent alias adding nothing
beyond the verify-side `Discharged` — the intent trusts only the verifier. Named `_def` to
be honest that it discharges by unfolding a definition, not by a proof step. -/
theorem intent_accepts_discharged_def
    [Verifiable P W] (i : Intent P W) (w : W) :
    i.Accepts w ↔ Discharged i.want w := Iff.rfl

/-- **`intent_resolve_fires` — a resolved intent has fired.** If the cell accepted a fill,
then the existential firing condition holds (a witness exists). The converse does NOT
hold and is deliberately left open below: `Fires` asserting *some* filler exists does not
let the cell *produce* one — that is the undecidable FIND direction. -/
theorem intent_resolve_fires
    [Verifiable P W] [Searchable P W] (i : Intent P W) (w : W)
    (h : i.resolve = some w) :
    i.Fires :=
  ⟨w, intent_fill_verifies i w h⟩

/-- **`intent_sound_against_adversary`** — for any `Searchable P W` instance (including
one engineered to return wrong fills), every fill the cell accepts still discharges the
predicate. VERIFY is in the TCB; FIND is not. -/
theorem intent_sound_against_adversary
    [Verifiable P W] [Searchable P W] (i : Intent P W) :
    ∀ w : W, i.resolve = some w → Discharged i.want w :=
  fun w h => intent_fill_verifies i w h

/-! ## Keystone part (b) — the asymmetry is in the types.

VERIFY is decidable: the `Decidable (Intent.Accepts i w)` instance in §1 witnesses this.
FIND carries no such guarantee: `Searchable.find : P → Option W` is an opaque typeclass
method with no completeness or termination law.

  -- OPEN: `Decidable (Intent.Fires i)` is NOT provided and MUST NOT be — `Fires` is
  -- `∃ w, Discharged want w`, whose decision is general fill-finding (higher-order
  -- unification), undecidable. The matcher is an untrusted plugin (`Intent.propose`);
  -- we never claim to decide `Fires`.
-/

/-! ## 4. The duality — an intent is the inverse of the vat-boundary cross case. -/

/-- **`ofAwait` / `toAwait`** — the intent developed here is *the same object* as
`Await.intent` (Face 3 of the await family), forgetting/restoring the continuation and
witness-typing decoration. This connects the authority-grade `Intent` to the await
family without redefining it: the existential hole is one primitive, viewed two ways.
`ofAwait` reads the predicate off an `Await.intent`; `toAwait` re-attaches a
continuation. -/
def ofAwait {P W Reply S : Type u} [Verifiable P W]
    (a : intent P W Reply S) : Intent P W :=
  { want := a.want }

/-- Re-attach a continuation, recovering the await-family Face-3 view. -/
def toAwait {P W Reply S : Type u} [Verifiable P W]
    (i : Intent P W) (k : Dregg2.Await.OneShot Reply S) : intent P W Reply S :=
  { want := i.want, kont := k }

/-- **`intent_face_agrees_def`** — a definitional unfold, NOT a theorem with content.
`ofAwait` is defined to copy `want` on the nose (`(ofAwait a).want = a.want` by `rfl`), and
both `Fires` predicates are `∃ w, Discharged ·.want w`; so the two firing conditions are the
*same* `Prop` up to unfolding, and this `Iff` is `Iff.rfl`. It records, for callers, that the
forgetful map `ofAwait` preserves the `∃`-resolver semantics definitionally — the agreement
is by construction, not a proved correspondence. Named `_def` to be honest about that. -/
theorem intent_face_agrees_def {P W Reply S : Type u} [Verifiable P W]
    (a : intent P W Reply S) :
    Dregg2.Await.intent.Fires a ↔ (ofAwait a).Fires := Iff.rfl

/-- **The outgoing-boundary predicate of an intent.** To state the duality against the
*actual* vat-boundary object (`Authority.Integrity`, the lift of l4v `integrity_obj_atomic`,
`Positional.lean`) rather than against a copy of `Discharged`, we view an intent `i` as a
boundary whose admissibility predicate is, on every cell-object change, exactly `i.want`. The
boundary then admits a **cross** change iff some witness discharges `i.want` — the same hole
the intent gates, but presented as an *outgoing* membrane over abstract object-states `KO`. -/
def Intent.boundaryPred (i : Intent P W) : KO → KO → P := fun _ _ => i.want

/-- **`intent_inverts_boundary`** — an outgoing cross-vat change is admissible (via
`Integrity.cross`) exactly when the intent fires. The duality goes through the inductive
`Integrity.cross` introduction (not `Iff.rfl`): the forward direction destructs the
`Integrity` proof — `intra` is unavailable because `owner ∉ subjects = []` — so
admissibility can only come from a discharged witness, which is precisely a firing of the
intent. The companion `intent_accepts_witnesses_boundary` shows an accepted incoming filler
is exactly a witness producing the outgoing admissibility. Together: the intent is the vat
boundary with the morphism direction reversed. -/
theorem intent_inverts_boundary [Verifiable P W] (i : Intent P W)
    (owner : Label) (ko ko' : KO) :
    Integrity W owner ([] : List Label) (i.boundaryPred) ko ko' ↔ i.Fires := by
  constructor
  · intro hcross
    cases hcross with
    | intra hmem => exact absurd hmem (by simp)   -- no `intra`: owner ∉ [] (genuinely cross)
    | cross w hw => exact ⟨w, hw⟩                  -- the cross witness IS a firing of the intent
  · rintro ⟨w, hw⟩
    exact Integrity.cross w hw                     -- a firing builds the outgoing `cross` admission

/-- **`intent_accepts_witnesses_boundary` — the incoming filler IS the outgoing admission
witness (PROVED).** A specific filler `w` that the intent *accepts* on the incoming side
(`i.Accepts w`, the decidable local VERIFY) is exactly a witness that admits the *outgoing*
cross-vat change via `Integrity.cross`. The two faces share their witness, in opposite
directions across the membrane — the concrete content of "intent is the inverse boundary." -/
theorem intent_accepts_witnesses_boundary [Verifiable P W] (i : Intent P W)
    (owner : Label) (ko ko' : KO) (w : W) (hacc : i.Accepts w) :
    Integrity W owner ([] : List Label) (i.boundaryPred) ko ko' :=
  Integrity.cross w hacc

/-! ## 5. `#eval` demos — soundness against a correct and an adversarial matcher.

Intent predicate: "a multiple of 3" (`w % 3 == 0`). Three matchers: correct (returns 6,
accepted), adversarial (returns 7, rejected by VERIFY), give-up (returns `none`). -/

/-- Demo predicate space: a single predicate "is a multiple of 3". -/
inductive DivBy3 where
  | mult3
  deriving Repr, DecidableEq

/-- Demo witness space: a natural number (the proposed fill). -/
abbrev Fill := Nat

/-- VERIFY (in TCB): a fill discharges `mult3` iff it is divisible by 3. Decidable,
total, cheap — exactly the verify side. -/
instance demoVerifiable : Verifiable DivBy3 Fill where
  Verify := fun _ w => w % 3 == 0

/-- The concrete intent: a hole wanting a multiple of 3. -/
def demoIntent : Intent DivBy3 Fill := { want := DivBy3.mult3 }

/-- A CORRECT matcher: proposes `6` (a genuine fill). UNTRUSTED, but happens to be right. -/
@[reducible] def goodMatcher : Searchable DivBy3 Fill where
  find := fun _ => some 6

/-- An ADVERSARIAL matcher: proposes `7` (NOT a multiple of 3). The cell must reject it. -/
@[reducible] def evilMatcher : Searchable DivBy3 Fill where
  find := fun _ => some 7

/-- A GIVE-UP matcher: finds nothing (models partiality/nontermination). -/
@[reducible] def emptyMatcher : Searchable DivBy3 Fill where
  find := fun _ => none

/-! ### `goodMatcher` lifts to `SoundSearchable`; `evilMatcher` does not — the contract has teeth. -/

/-- **`goodMatcher`** is a contracted `SoundSearchable` plugin: its only return `6` verifies
(`6 % 3 == 0`), witnessing that the `find_sound` assumption is satisfiable (non-vacuous). -/
instance goodSoundMatcher : SoundSearchable DivBy3 Fill where
  find := goodMatcher.find
  find_sound := fun p w h => by
    -- `goodMatcher.find p` reduces to `some 6`, so `h : some 6 = some w` gives `w = 6`;
    -- `Discharged mult3 6` unfolds to `Verify mult3 6 = true`, i.e. `(6 % 3 == 0) = true`.
    have hw : (6 : Fill) = w := Option.some.inj h
    rw [← hw]
    unfold Discharged
    rfl

/-- **`evilMatcher_not_sound`** — no `SoundSearchable` instance agreeing with
`evilMatcher.find` can exist: it returns `7`, which does not verify (`7 % 3 ≠ 0`), so any
`find_sound` for it would prove the false `Discharged mult3 7`. The soundness contract is a
genuine, non-trivial constraint. -/
theorem evilMatcher_not_sound
    (s : SoundSearchable DivBy3 Fill) (hagree : s.find = evilMatcher.find) :
    False := by
  have hfound : s.find DivBy3.mult3 = some 7 := by rw [hagree]; rfl
  have hd : Discharged DivBy3.mult3 7 := s.find_sound DivBy3.mult3 7 hfound
  -- `Discharged mult3 7` IS (defeq) `Verify mult3 7 = true`; but `Verify mult3 7` computes to
  -- `false` (`7 % 3 = 1 ≠ 0`), so `hd : false = true` — absurd.
  have hd2 : Verifiable.Verify DivBy3.mult3 (7 : Fill) = true := hd
  have hfalse : Verifiable.Verify DivBy3.mult3 (7 : Fill) = false := rfl
  rw [hfalse] at hd2
  exact Bool.false_ne_true hd2

-- The good matcher proposes 6, a genuine fill: ACCEPTED → `some 6`.
#guard (@Intent.resolve DivBy3 Fill demoVerifiable goodMatcher demoIntent) == some 6
-- The adversarial matcher proposes 7, NOT a multiple of 3: REJECTED by VERIFY → `none`.
-- Soundness holds against a buggy/adversarial matcher: the bad fill never escapes.
#guard (@Intent.resolve DivBy3 Fill demoVerifiable evilMatcher demoIntent) == none
-- The give-up matcher finds nothing: `none`.
#guard (@Intent.resolve DivBy3 Fill demoVerifiable emptyMatcher demoIntent) == none
-- The untrusted PROPOSE step (pre-verification) does surface the adversarial 7 …
#guard (@Intent.propose DivBy3 Fill evilMatcher demoIntent) == some 7
-- … but the cell's own VERIFY rejects it (decidable, in-TCB):
#guard (@Intent.Accepts DivBy3 Fill demoVerifiable demoIntent 7 : Bool) == false
#guard (@Intent.Accepts DivBy3 Fill demoVerifiable demoIntent 6 : Bool)

end Dregg2.Authority
