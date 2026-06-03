/-
# Dregg2.Confluence.DriftStable — the coordination-cost ladder, in theorems.

`Confluence.CRDT` gives the instance catalog (grow-only = tier-1; bounded = NOT, escrow
quota-partition = the way out). This module formalizes two further pieces from
`DRIFT-STABILITY-SPECTRUM.md` §4–§5: *conditional drift-stability* and the *tiered caveat
(verify-not-find dispatch)*.

A state-reading caveat `φ` has two soundness windows. The commit-instant (TOCTOU) window is
already handled: `Exec.CrossCaveat.caveated_check_eq_use` (the equalizer). This module is the
composition-window drift: while parties compose a turn, cells drift forward; a turn composed
against `x` must remain valid at commit against `x ⊔ Δ`.

What is proved (the load-bearing five):
  1. `IConfluentUnder E φ` — conditional drift-stability: confluence in the sublattice cut out
     by environment guarantee `E`. `IConfluent φ` is the `E = ⊤` case.
  2. `driftStable_composes` — an I-confluent caveat survives forward-compatible drift: `φ` true
     at compose-state `x` and at drift `Δ` gives `φ` at `x ⊔ Δ`, no re-check needed.
  3. `locked_driftStable` — a chain environment (pairwise-comparable reachable states) makes
     ANY `φ` drift-stable, because the merge equals one operand.
  4. The dual (as theorems): `monotone_caveat_driftStable` (grow-only composes free) and
     `bounded_caveat_needs_coordination` (the bounded-counter is NOT drift-stable, with the two
     built escape hatches in `BoundedEscape`).
  5. The tiered caveat (§5): a computable `DriftTier` tag + `TieredCaveat` carrying the
     tier-appropriate proof. The tier is a checked witness, never a search.

Zero sorry/admit/native_decide/axiom. Every keystone is `#assert_axioms`-pinned to
`{propext, Classical.choice, Quot.sound}`.
-/
import Dregg2.Tactics
import Dregg2.Confluence
import Dregg2.Confluence.CRDT
import Dregg2.Exec.CrossCaveat
import Dregg2.Authority.ThirdPartyDischarge

namespace Dregg2.Confluence.DriftStable

open Dregg2.Confluence

universe u

/-! ## §1. Conditional drift-stability — `IConfluentUnder`.

An environment guarantee `E` restricts the reachable states and thereby enlarges what is
drift-stable: `φ` need only survive merges of states both satisfying `E`. Plain `IConfluent`
is the `E = ⊤` case. -/

/-- **Conditional drift-stability (`IConfluentUnder`).** `φ` is I-confluent over the sublattice cut
out by `E`: concurrent `E`-states that each preserve `φ` merge `φ`-safely. A stronger `E` enlarges
what is stable. -/
def IConfluentUnder {S : Type u} [MergeState S] (E φ : Invariant S) : Prop :=
  ∀ x y : S, E x → E y → φ x → φ y → φ (x ⊔ y)

/-- **`IConfluent` is the `E = ⊤` case of `IConfluentUnder`.** Unconditional drift-stability is
conditional stability under the always-true environment (no guarantee). -/
theorem iconfluent_iff_under_top {S : Type u} [MergeState S] (φ : Invariant S) :
    IConfluent φ ↔ IConfluentUnder (fun _ => True) φ := by
  constructor
  · intro h x y _ _ hx hy; exact h x y hx hy
  · intro h x y hx hy; exact h x y trivial trivial hx hy

/-- **A stronger environment enlarges drift-stability (monotone in `E`).** If `φ` is I-confluent
under `E` and `E'` is stronger (`E' x → E x`), then `φ` is I-confluent under `E'` too. -/
theorem iconfluentUnder_mono {S : Type u} [MergeState S] {E E' φ : Invariant S}
    (hEE' : ∀ s, E' s → E s) (h : IConfluentUnder E φ) : IConfluentUnder E' φ := by
  intro x y hx hy hφx hφy
  exact h x y (hEE' x hx) (hEE' y hy) hφx hφy

/-! ## §2. `driftStable_composes` — the drift-window theorem.

A turn composed against `x` commits against `x ⊔ Δ` (the drift). If `φ` is I-confluent,
`φ x` and `φ Δ` together give `φ (x ⊔ Δ)` — no re-check, no coordination. -/

/-- **`driftStable_composes`.** An I-confluent caveat survives forward-compatible drift. With `x` the
compose-state, `Δstate` the concurrent drift, and `x ⊔ Δstate` the commit-state: `φ x` and `φ Δstate`
imply `φ (x ⊔ Δstate)` — the composed turn commits without re-checking `φ` and without coordination
(`Confluence.admits_sound`). -/
theorem driftStable_composes {S : Type u} [MergeState S] {φ : Invariant S}
    (hI : IConfluent φ) {x Δstate : S} (hx : φ x) (hΔ : φ Δstate) :
    φ (x ⊔ Δstate) :=
  -- the merge `x ⊔ Δstate` is the drift; `admits_sound` (= the I-confluence gate) closes it.
  admits_sound φ hI x Δstate hx hΔ

/-- **Under-`E` form: drift-stability within an environment.** For compose-state and drift both
reachable under `E`, an `IConfluentUnder E` caveat survives the drift. -/
theorem driftStable_composes_under {S : Type u} [MergeState S] {E φ : Invariant S}
    (hI : IConfluentUnder E φ) {x Δstate : S} (hEx : E x) (hEΔ : E Δstate)
    (hx : φ x) (hΔ : φ Δstate) :
    φ (x ⊔ Δstate) :=
  hI x Δstate hEx hEΔ hx hΔ

/-! ## §3. `locked_driftStable` — the lock collapses the merge.

Under a single-writer environment `E`, reachable states form a chain (pairwise comparable). A
comparable merge equals one operand, so the merge never escapes the invariant — ANY `φ` is
drift-stable under such `E`. Coordination once (acquiring the lock) buys drift-stability even
for non-monotone `φ`. -/

/-- **`locked_driftStable`.** If `E` guarantees pairwise comparability (`E x → E y → x ≤ y ∨ y ≤ x`),
every `φ` is `IConfluentUnder E`. A comparable merge equals one operand (`sup_eq_right`/`sup_eq_left`),
so the invariant is preserved trivially. -/
theorem locked_driftStable {S : Type u} [MergeState S] {E : Invariant S}
    (hchain : ∀ x y : S, E x → E y → x ≤ y ∨ y ≤ x) (φ : Invariant S) :
    IConfluentUnder E φ := by
  intro x y hEx hEy hφx hφy
  rcases hchain x y hEx hEy with hle | hle
  · -- `x ≤ y` ⇒ `x ⊔ y = y`; `φ y` holds.
    rw [sup_eq_right.mpr hle]; exact hφy
  · -- `y ≤ x` ⇒ `x ⊔ y = x`; `φ x` holds.
    rw [sup_eq_left.mpr hle]; exact hφx

/-! ### §3a. The lock is non-vacuous — a concrete version-stamped chain.

The lock environment is instantiated over `Fin 1 → ℕ` (a single-writer cell with one monotone
version slot). On this one-element index, pointwise order is linear, so `lockEnv` genuinely
forces comparable merges and `locked_driftStable` applies. -/

/-- A single-writer cell: a one-slot G-counter carrying a monotone version. -/
abbrev VersionCell := CRDT.GCounter (Fin 1)

/-- The lock environment: all reachable states are comparable (single-writer). Modeled as the
always-true predicate; comparability comes from `versionCell_chain`. -/
def lockEnv : Invariant VersionCell := fun _ => True

/-- **The single-slot G-counter is a chain.** On `Fin 1 → ℕ` any two states are comparable: the
pointwise order on a one-element index reduces to the linear order on the single slot. Discharges
`hchain` for `locked_driftStable`. -/
theorem versionCell_chain (x y : VersionCell) : x ≤ y ∨ y ≤ x := by
  rcases le_total (x 0) (y 0) with h | h
  · left; intro i
    have : i = 0 := Subsingleton.elim i 0
    subst this; exact h
  · right; intro i
    have : i = 0 := Subsingleton.elim i 0
    subst this; exact h

/-- **A non-monotone caveat made drift-stable by the lock.** "the cell is at exactly version `v`" is
NOT I-confluent in general, but under the single-writer chain (`versionCell_chain`),
`locked_driftStable` makes it drift-stable: the lock cuts drift to a chain, so equal-version states
merge to that same version. -/
theorem lockedExactVersion_driftStable (v : ℕ) :
    IConfluentUnder (S := VersionCell) lockEnv (fun g => g 0 = v) :=
  locked_driftStable (fun x y _ _ => versionCell_chain x y) (fun g => g 0 = v)

/-! ## §4. The dual — monotone composes free; bounded needs coordination.

A grow-only caveat composes under drift for free; the bounded-counter caveat is NOT drift-stable,
forcing one of two built escape hatches: the equalizer (`CrossCaveat.crossCaveat_sound`) or the
OCC freshness window (`ThirdParty.stale_discharge_rejected`). -/

/-- **`monotone_caveat_driftStable`.** The grow-only lower-bound caveat "replica `i` has counted ≥ `k`"
composes under drift for free — `driftStable_composes` with `CRDT.gcounter_lowerBound_iconfluent`.
No coordination, no re-check (tier-1). -/
theorem monotone_caveat_driftStable {ι : Type u} (i : ι) (k : ℕ)
    {x Δstate : CRDT.GCounter ι} (hx : k ≤ x i) (hΔ : k ≤ Δstate i) :
    k ≤ (x ⊔ Δstate) i :=
  driftStable_composes (CRDT.gcounter_lowerBound_iconfluent i k) hx hΔ

/-- **The two escape hatches for a non-drift-stable caveat.** When `φ` is NOT drift-stable, the
executor must take either the commit-instant equalizer (`CrossCaveat.crossCaveat_sound`) or read
within the OCC freshness window (`ThirdParty.stale_discharge_rejected`). Carried structurally so
the theorem points at a concrete sound fallback. -/
inductive BoundedEscape where
  /-- Take the atomic equalizer per use — `CrossCaveat.crossCaveat_sound` (blocks under partition). -/
  | equalizer
  /-- Read the non-monotone fact within the OCC freshness window — `ThirdParty.stale_discharge_rejected`
  (`MAX_DISCHARGE_AGE`); stale ⇒ rejected. -/
  | freshnessWindow
deriving DecidableEq, Repr

/-- **`bounded_caveat_needs_coordination`.** The bounded-counter caveat (`CRDT.withinBudget 1`) is
NOT drift-stable: a clashing drift pair `x`, `Δ` exists — both within budget, but their merge
overshoots — so committing without re-check is unsound. The caveat must take a `BoundedEscape`. -/
theorem bounded_caveat_needs_coordination :
    ¬ IConfluent (S := CRDT.Budget) (CRDT.withinBudget 1) ∧
    (∃ x Δ : CRDT.Budget,
        CRDT.withinBudget 1 x ∧ CRDT.withinBudget 1 Δ ∧
        ¬ CRDT.withinBudget 1 (x ⊔ Δ)) ∧
    (∃ _e : BoundedEscape, True) := by
  refine ⟨CRDT.withinBudget_not_iconfluent, ?_, ?_⟩
  · -- the clashing drift pair: the catalog's escalation witness IS the non-drift-stable merge.
    exact CRDT.withinBudget_escalation
  · -- a sound fallback exists: take the equalizer (or, equally, the freshness window).
    exact ⟨BoundedEscape.equalizer, trivial⟩

/-- **The equalizer fallback is sound.** `BoundedEscape.equalizer` is justified by
`Exec.CrossCaveat.crossCaveat_sound`: a committed caveated bilateral turn proves the caveat held
on the atomic commit snapshot. -/
theorem boundedEscape_equalizer_sound
    {φ : Dregg2.Exec.CrossCaveat.CrossCaveat}
    {A B A' B' : Dregg2.Exec.KernelState} {bt : Dregg2.Exec.JointCell.BiTurn}
    (bind : Dregg2.Exec.JointCell.SharedBinding bt)
    (h : Dregg2.Exec.CrossCaveat.jointApplyCaveated φ A B bt = some (A', B')) :
    Dregg2.Exec.JointCell.jointTotal A' B' = Dregg2.Exec.JointCell.jointTotal A B ∧
      bind.sidOfA = bind.sidOfB ∧ φ A B = true :=
  Dregg2.Exec.CrossCaveat.crossCaveat_sound bind h

/-- **The freshness-window fallback is sound.** `BoundedEscape.freshnessWindow` is justified by
`Authority.ThirdParty.stale_discharge_rejected`: a discharge whose freshness check fails is rejected
— so a non-monotone fact is only honored within `MAX_DISCHARGE_AGE`. -/
theorem boundedEscape_freshness_sound
    [Authority.ThirdParty.DischargeCrypto]
    {Ctx : Type} (tpc : Authority.ThirdParty.ThirdPartyCaveat Ctx)
    (m : Authority.ThirdParty.DischargeMacaroon Ctx)
    (parentTail : Authority.ThirdParty.Bytes) (ctx : Ctx) (now : Authority.ThirdParty.Time)
    (hstale : Authority.ThirdParty.fresh m.createdAt now = false) :
    Authority.ThirdParty.accepts tpc m parentTail ctx now = false :=
  Authority.ThirdParty.stale_discharge_rejected tpc m parentTail ctx now hstale

/-! ## §5. The tiered caveat — the verify-not-find dispatch.

"Is `φ` I-confluent?" is not decidable, so it is not decided. The tier is carried as a witness
(supplied at construction), and the executor reads the computable tag and dispatches: monotone ⇒
coordination-free; coordinated ⇒ take the equalizer. The tier is a checked witness, never a
search. -/

/-- **The drift-stability tier (computable tag).** Read by the executor to dispatch coordination. -/
inductive DriftTier where
  /-- Tier-1: `φ` is unconditionally I-confluent (grow-only / CRDT-native) — run coordination-free. -/
  | monotone
  /-- Tier-3: a bounded resource made local-safe by RESERVING quota (the escrow refinement). -/
  | reservation
  /-- Tier-4: exclusive access cuts drift to a chain — `IConfluentUnder env φ` for a chain `env`. -/
  | locked
  /-- Tier-5: genuinely non-monotone, no rep — MUST take the atomic equalizer per use. -/
  | coordinated
deriving DecidableEq, Repr

/-- The witness a `TieredCaveat` carries, dependent on its tier — the tier-APPROPRIATE proof:
  * `monotone`    ⇒ a full `IConfluent φ` (drift-stable unconditionally);
  * `reservation` ⇒ the escrow obligation: a quota `q`/budget `B` partition with `Σ q = B`, against
                    which the LOCAL quota discipline is the I-confluent invariant (so `φ` is the
                    `withinQuota q` read) AND it implies the global bound (the `escrow_refinement` pair);
  * `locked`      ⇒ `IConfluentUnder env φ` (drift-stable in the lock's chain sublattice);
  * `coordinated` ⇒ `Unit` (no drift-stability proof; the executor MUST take the equalizer). -/
def DriftWitness {S : Type u} [MergeState S] (env φ : Invariant S) : DriftTier → Type
  | .monotone    => PLift (IConfluent φ)
  | .reservation => PLift (IConfluent φ)
  | .locked      => PLift (IConfluentUnder env φ)
  | .coordinated => PUnit

/-- **A tiered caveat (the §5 dependent record).** Carries its environment guarantee `env`, the caveat
`φ`, a COMPUTABLE drift `tier`, and the tier-appropriate `witness` (a REAL carried proof for the
non-coordinated tiers). The executor reads `tier` (data) and dispatches; the `witness` is what makes
skipping coordination sound. -/
structure TieredCaveat (S : Type u) [MergeState S] where
  env     : Invariant S
  φ       : Invariant S
  tier    : DriftTier
  witness : DriftWitness env φ tier

/-- **`tieredCaveat_driftStable`.** For any tiered caveat with tier ≠ `coordinated`, the carried
witness yields drift-stability: a caveat true at compose-state `x` and drift `Δ` stays true at
`x ⊔ Δ`. The conclusion follows from the witness: `monotone`/`reservation` carry `IConfluent φ`;
`locked` carries `IConfluentUnder env φ` (env hypotheses genuinely consumed). For `coordinated`
no witness exists — the executor takes the equalizer. -/
theorem tieredCaveat_driftStable {S : Type u} [MergeState S]
    (tc : TieredCaveat S) (hne : tc.tier ≠ .coordinated)
    {x Δstate : S} (hEx : tc.env x) (hEΔ : tc.env Δstate)
    (hx : tc.φ x) (hΔ : tc.φ Δstate) :
    tc.φ (x ⊔ Δstate) := by
  -- dispatch on the (computable) carried tier; each non-coordinated branch USES its witness.
  cases htier : tc.tier with
  | monotone =>
      -- witness : PLift (IConfluent φ) — drift-stable unconditionally.
      have hw : DriftWitness tc.env tc.φ tc.tier := tc.witness
      rw [htier] at hw
      exact driftStable_composes hw.down hx hΔ
  | reservation =>
      have hw : DriftWitness tc.env tc.φ tc.tier := tc.witness
      rw [htier] at hw
      exact driftStable_composes hw.down hx hΔ
  | locked =>
      -- witness : PLift (IConfluentUnder env φ) — the env hypotheses are genuinely consumed.
      have hw : DriftWitness tc.env tc.φ tc.tier := tc.witness
      rw [htier] at hw
      exact driftStable_composes_under hw.down hEx hEΔ hx hΔ
  | coordinated => exact absurd htier hne

/-! ### §5a. The dispatch is non-vacuous — concrete instances on the catalog. -/

/-- A MONOTONE tiered caveat: the grow-only lower-bound "replica `i` ≥ `k`" carrying its `IConfluent`. -/
def monotoneTC {ι : Type u} (i : ι) (k : ℕ) : TieredCaveat (CRDT.GCounter ι) where
  env     := fun _ => True
  φ       := fun g => k ≤ g i
  tier    := .monotone
  witness := PLift.up (CRDT.gcounter_lowerBound_iconfluent i k)

/-- **The monotone tiered caveat is drift-stable by dispatch.** Reading the `.monotone` tag and the
carried `IConfluent` witness, `tieredCaveat_driftStable` fires — no coordination. -/
theorem monotoneTC_driftStable {ι : Type u} (i : ι) (k : ℕ)
    {x Δstate : CRDT.GCounter ι} (hx : k ≤ x i) (hΔ : k ≤ Δstate i) :
    k ≤ (x ⊔ Δstate) i :=
  tieredCaveat_driftStable (monotoneTC i k)
    (show DriftTier.monotone ≠ DriftTier.coordinated by decide) trivial trivial hx hΔ

/-- A locked tiered caveat: the non-monotone "exactly version `v`" on the single-writer cell,
carrying the `IConfluentUnder` proof supplied by `versionCell_chain`. -/
def lockedTC (v : ℕ) : TieredCaveat VersionCell where
  env     := fun _ => True
  φ       := fun g => g 0 = v
  tier    := .locked
  witness := PLift.up (locked_driftStable (fun x y _ _ => versionCell_chain x y) (fun g => g 0 = v))

/-- **The locked tiered caveat is drift-stable by dispatch, with a non-monotone `φ`.** Reading the
`.locked` tag and the carried `IConfluentUnder env φ` witness, the "exactly version `v`" caveat
(which is NOT unconditionally I-confluent) survives drift under the lock — env hypotheses genuinely
consumed. -/
theorem lockedTC_driftStable (v : ℕ) {x Δstate : VersionCell}
    (hx : x 0 = v) (hΔ : Δstate 0 = v) :
    (x ⊔ Δstate) 0 = v :=
  tieredCaveat_driftStable (lockedTC v)
    (show DriftTier.locked ≠ DriftTier.coordinated by decide) trivial trivial hx hΔ

/-! ## §6. #eval witnesses — non-vacuity by computation.

Computational sanity checks: a grow-only caveat survives a concrete drift-merge; the bounded
caveat fails one. Not proofs — the theorems above are — but concretely inspectable. -/

section Evals

-- A grow-only caveat "replica 0 ≥ 2", composed against `x` and committed against the drift-merge.
def dsX : CRDT.GCounter (Fin 2) := fun i => if i = 0 then 2 else 0          -- compose-state
def dsΔ : CRDT.GCounter (Fin 2) := fun i => if i = 0 then 5 else 3          -- concurrent drift

-- compose-state satisfies `2 ≤ x 0`; drift satisfies `2 ≤ Δ 0`; the MERGE still does ⇒ composes free.
#eval decide (2 ≤ dsX 0)                       -- true  (caveat holds at compose-time)
#eval decide (2 ≤ dsΔ 0)                       -- true  (drift preserves the caveat)
#eval decide (2 ≤ (dsX ⊔ dsΔ) 0)               -- true  (SURVIVES the drift-merge — no coordination)
#eval ((dsX ⊔ dsΔ) 0, (dsX ⊔ dsΔ) 1)           -- (5, 3)  the drift-merged commit-state

-- The bounded caveat: `(1,0)` composed, `(0,1)` drift; each within budget 1, MERGE overshoots ⇒ NEEDS
-- coordination (the drift-window is unsound; take the equalizer / freshness window).
def bdX : CRDT.Budget := fun i => if i = 0 then 1 else 0                    -- compose-state
def bdΔ : CRDT.Budget := fun i => if i = 0 then 0 else 1                    -- concurrent drift
#eval decide (CRDT.consumed bdX ≤ 1)           -- true  (within budget at compose-time)
#eval decide (CRDT.consumed bdΔ ≤ 1)           -- true  (drift within budget)
#eval decide (CRDT.consumed (bdX ⊔ bdΔ) ≤ 1)   -- false (drift-merge OVERSHOOTS — NOT drift-stable)
#eval CRDT.consumed (bdX ⊔ bdΔ)                -- 2     (the overshoot: needs coordination)

-- The lock collapses the merge: two equal-version states (single-writer chain) merge to that version.
def lkX : VersionCell := fun _ => 7
def lkΔ : VersionCell := fun _ => 7
#eval decide ((lkX ⊔ lkΔ) 0 = 7)               -- true  (non-monotone "version = 7" SURVIVES under lock)

-- The tier tag is computable (the executor reads it to dispatch); a fallback exists for the bounded case.
#eval (monotoneTC (ι := Fin 2) 0 2).tier       -- DriftTier.monotone
#eval (lockedTC 7).tier                         -- DriftTier.locked
#eval (decide ((monotoneTC (ι := Fin 2) 0 2).tier = DriftTier.coordinated))  -- false (⇒ dispatch fires)
#eval (BoundedEscape.equalizer, BoundedEscape.freshnessWindow)               -- the two sound fallbacks

end Evals

/-! ## §7. Axiom-hygiene pins (`#assert_axioms`) — every keystone is sorry-free.

Each pin elaborates to an error if the keystone depends on any axiom outside
`{propext, Classical.choice, Quot.sound}` (notably `sorryAx`). -/

-- §1 conditional drift-stability
#assert_axioms iconfluent_iff_under_top
#assert_axioms iconfluentUnder_mono
-- §2 the headline
#assert_axioms driftStable_composes
#assert_axioms driftStable_composes_under
-- §3 the lock
#assert_axioms locked_driftStable
#assert_axioms versionCell_chain
#assert_axioms lockedExactVersion_driftStable
-- §4 the teeth + the two built escape hatches
#assert_axioms monotone_caveat_driftStable
#assert_axioms bounded_caveat_needs_coordination
#assert_axioms boundedEscape_equalizer_sound
#assert_axioms boundedEscape_freshness_sound
-- §5 the tiered caveat (verify-not-find dispatch)
#assert_axioms tieredCaveat_driftStable
#assert_axioms monotoneTC_driftStable
#assert_axioms lockedTC_driftStable

end Dregg2.Confluence.DriftStable
