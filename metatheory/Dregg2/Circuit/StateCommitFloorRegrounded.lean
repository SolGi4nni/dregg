/-
# `Dregg2.Circuit.StateCommitFloorRegrounded` — the `StateCommit` leaf/log injective floors proved
FALSE at deployed parameters, and their consumers RE-GROUNDED onto a REAL collision-game reduction
carrying an explicit `Eff`.

## The bug this closes (`VACUITY-SWEEP.md` FINDING 2, cluster 2)

`HashFloorHonesty` (2026-07) proved FOUR injectivity floors FALSE for any range-bounded hash and
doc-marked them BROKEN. **It did not sweep the class.** `VACUITY-SWEEP.md` FINDING 2 found ~20 more
carriers with the identical predicate shape, still doc-marked "REALIZABLE", none pointing at the teeth,
**none re-grounded**. Two of them live in `StateCommit.lean` itself — *the same file as two already-flagged
siblings*:

  * `StateCommit.cellLeafInjective CH := ∀ c v w, CH c v = CH c w → v = w`   (`StateCommit.lean:230`)
  * `StateCommit.logHashInjective LH := ∀ xs ys, LH xs = LH ys → xs = ys`    (`StateCommit.lean:238`)

Both are **FALSE at deployed parameters** and §1 proves it: `Value` is infinite (`Value.int` injects `ℤ`),
`List Turn` is infinite, and a real leaf/log hash lands in a BOUNDED BabyBear field — so pigeonhole forces
collisions and the injective floor is unsatisfiable (`cellLeafInjective_false_babyBear`,
`logHashInjective_false_babyBear`). Their consumers — `MovedDigestBindsCells`, `FrameDigestBindsCells`,
`cellDigest_binds_cells`, `recStateCommit_binds_kernel`, `transfer_circuit_full_sound`, and the
`EffectInstances2` / `EffectRefinement` log-growing effects — are therefore **VACUOUSLY TRUE at real
parameters**. `#assert_axioms` is blind to it: the proofs are clean; the *hypothesis* is the flaw.

## ⚑ The `*Realization` bundles are NON-INHABITABLE, which is worse than a hypothesis

`Poseidon2Binding.LeafRealization CH` / `LogRealization LH` carry `spongeCR : Poseidon2SpongeCR sponge`
as a **structure FIELD**, and `HashFloorHonesty.poseidon2SpongeCR_false_babyBear` had **already proved
that field's type FALSE** at BabyBear. So §1's `leafRealization_uninhabitable_babyBear` /
`logRealization_uninhabitable_babyBear` prove a deployed `LeafRealization`/`LogRealization` **value cannot
exist** — this is the `Compress8CR`-in-`Cap8Scheme` shape the sweep flagged as the priority. Every
discharge routed through them (`cellLeafInjective_of_realization`, `logHashInjective_of_realization`, and
`Verify/KeystoneAuditArgusReceipt.LH₀_inj`) is satisfied only by the TOY injective sponge
(`Reference.refLogRealization`, `Encodable.encode`) — verbatim the **FALSE COMFORT**
`HashFloorHonesty`'s own header named: *"toy witness satisfiable; real instantiation false."*

## ⚑ The re-grounding does NOT go through `CollisionResistant` — that floor is false too

`FloorGames.collisionResistant_false_of_compressing` proves `HashFloorHonesty.CollisionResistant F` is
ITSELF FALSE at deployed parameters (`CollisionResistant F ↔ HashCRHardQuant F ⊤`, and the
`Classical.choice` finder wins with probability `1` on a compressing family). At the **unrestricted**
adversary class every floor is false-at-deployed or vacuous — `hard_top_iff_solvableFrac_negl` is an `↔`,
so no restatement of the win relation escapes. **The only honest escape is the `Eff` parameter**
(`FloorGames` §8), and this file takes it, exactly as `HermineHashCRRegrounded` does.

So the re-grounded consumers below condition on `HashCRHardQuant F Eff` — the collision floor at a
NAMED, EXPLICIT adversary class — and carry the `Eff`-membership obligation for the finder the reduction
builds, in the open, at the use site.

## The re-grounding, per consumer (§3–§5)

The deployed consumer is `StateCommit.cellDigest_binds_cells` / `recStateCommit_binds_kernel`: "equal
cell-digests force equal cell maps". Its BREAK is a **state-commitment equivocator** — two kernels with
the SAME accounts, both `AccountsWF`, whose cell maps DIFFER yet whose `cellDigest`s agree. §3 makes that
a first-class `Game` (`scEquivGame`) read directly off the deployed `cellDigest`; nothing here is a
docstring.

§4 is the reduction, as four maps of adversaries into three collision games over the SAME sampled
instance space:

  * **`scToOuterNodeAdv`** — the equivocator's two `(frameDigest, movedDigest)` children: a collision of
    the 2-to-1 node hash at the cell-digest root.
  * **`scToMovedNodeAdv`** — its two `(CH src, CH dst)` children: a node collision inside `movedDigest`.
  * **`scToSpongeAdv`** — its two sorted leaf lists: a collision of the frame sponge.
  * **`scToLeafAdv`** — the two `Value`s at the cell where the maps differ (`diffCell`): a collision of
    the LEAF hash — the horn `cellLeafInjective` was carrying for free.

`sc_wins_imp` is the dichotomy: every instance the equivocator wins, one of the four derived finders wins
a genuine collision game — proved by the exhaustive `{src} ∪ {dst} ∪ (accounts \ {src,dst}) ∪ dead`
partition, with the dead-cell case closed by `AccountsWF` on both states (the SAME partition
`cellDigest_binds_cells` runs, contraposed into an extractor). `sc_adv_le` is the union bound over the
shared instance space; `stateCommit_equivocation_advantage_bound` is the keystone: under the collision
floor at the three families the reduction attacks, an equivocator has NEGLIGIBLE advantage.

**This statement is FALSE if you delete the reduction** — the conclusion is about the equivocation game,
the hypotheses about the collision games, and `sc_adv_le` is the only bridge. §6's canary compiles that
fact; it was unwritable under the free `cellLeafInjective` hypothesis.

## Non-fake

The floors are SATISFIABLE (`hard_bot_vacuous`, recorded honestly and worth nothing on its own — the
value of a satisfiability witness is nothing without the refutation beside it) and the derived collision
floors are priced exactly by §7: `Eff := ⊤` makes them FALSE at compressing parameters,
`Eff := ⊥` vacuous. `valueDecEq` is COMPUTABLE, derived from the proven-injective `Poseidon2Binding.Reference.encV`
— no `Classical.decEq` smuggled into the counting. Old injective-floor consumers KEPT untouched; siblings
ADDED. `#assert_all_clean`; no `sorry`, no fresh `axiom`.

## Coordination

This is the COMMIT-STATE lane of the FINDING-2 sweep (`cellLeafInjective`/`logHashInjective`). The factory
content-hash, the 2-to-1 `Compress1CR` and the macaroon binding hash are
`Crypto.FactoryBindingFloorRegrounded` (sibling file, same cluster); `compress4Injective` /
`Poseidon2WideCR` / `Compress8CR` are other lanes'. The commit-reveal side is
`Crypto.HermineHashCRRegrounded`, whose `winProb_le_add_of_imp` union bound this file REUSES rather than
duplicates.
-/
import Dregg2.Crypto.HermineHashCRRegrounded
import Dregg2.Crypto.FloorGames
import Dregg2.Crypto.CostAdversary
import Dregg2.Crypto.CostTactics
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.StateCommit

namespace Dregg2.Circuit.StateCommitFloorRegrounded

open Dregg2.Crypto.ConcreteSecurity (Negl Ensemble negl_add negl_zero)
open Dregg2.Crypto.ProbCrypto (winProb negl_of_le)
open Dregg2.Circuit.HashFloorHonesty
  (KeyedHashFamily CollisionFinder CollisionResistant collisionAdv
   not_injective_of_finite_range injective_family_CR)
open Dregg2.Crypto.FloorGames
  (Game Adversary gameAdv gameAdv_mem_unit Hard hard_bot_vacuous hashGame HashCRHardQuant
   not_hard_top_of_always_solvable)
open Dregg2.Crypto.HermineHashCRRegrounded (winProb_le_add_of_imp)
open Dregg2.Circuit.StateCommit
  (cellLeafInjective logHashInjective AccountsWF cellDigest frameDigest movedDigest)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR LeafRealization LogRealization)
open Dregg2.Exec
open Dregg2.Crypto.CostAdversary (AnsSize IsPolyTime isPolyTime_inhabited idAdv)

set_option autoImplicit false

/-! ## §1 — FALSIFIABILITY TEETH: the two `StateCommit` floors are FALSE at deployed parameters.

The counting core is `HashFloorHonesty.not_injective_of_finite_range` — an injective function from an
INFINITE domain has an INFINITE range, and a real hash's range is a bounded field. Nobody had tried to
prove THESE two false, which is why the sweep found them still doc-marked "REALIZABLE". -/

/-- A function into a bounded integer window has finite range (`⊆ Ico 0 q`). The general form of
`HashFloorHonesty.finite_range_of_field_bound`, which is specialized to `List ℤ → ℤ`; both leaf
(`Value → ℤ`) and log (`List Turn → ℤ`) hashes need it. -/
theorem finite_range_of_field_window {α : Type*} (f : α → ℤ) (q : ℤ)
    (hb : ∀ x, 0 ≤ f x ∧ f x < q) : (Set.range f).Finite := by
  refine (Set.finite_Ico (0 : ℤ) q).subset ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨(hb x).1, (hb x).2⟩

/-- `Value` is INFINITE — `Value.int` injects all of `ℤ`. This is what makes the leaf floor false: a
cell's `Value` is unbounded data, and a leaf hash pins it into ONE field element. -/
instance : Infinite Value :=
  Infinite.of_injective Value.int (fun _ _ h => by injection h)

/-- `List Turn` is INFINITE (the length-`n` constant lists are distinct). This is what makes the log
floor false: the receipt chain GROWS without bound, and the log hash pins it into ONE field element. -/
instance : Infinite (List Turn) :=
  Infinite.of_injective (fun n : ℕ => List.replicate n (⟨0, 0, 0, 0⟩ : Turn))
    (fun n m h => by have := congrArg List.length h; simpa using this)

/-- **TOOTH 1 — `cellLeafInjective` is FALSE for a range-bounded leaf hash.** At any FIXED cell `c`, the
leaf map `CH c : Value → ℤ` runs the infinite `Value` into a finite set of field elements, so pigeonhole
forces two distinct `Value`s to one leaf — and the floor claims there are none. -/
theorem cellLeafInjective_false_of_finite_range (CH : CellId → Value → ℤ) (c : CellId)
    (hfin : (Set.range (CH c)).Finite) : ¬ cellLeafInjective CH := fun hinj =>
  not_injective_of_finite_range (CH c) hfin (fun v w h => hinj c v w h)

/-- **TOOTH 1 (deployed form) — `cellLeafInjective` is FALSE at the REAL BabyBear parameters.** A leaf
hash whose output is a BabyBear field element (`0 ≤ · < p`, `p = 2³¹ − 2²⁷ + 1`) — i.e. every real
Poseidon2 leaf hash the deployed `recStateCommit` runs — refutes the floor. The floor is not merely
un-proven for the real hash; it is provably FALSE there, exactly as
`HashFloorHonesty.poseidon2SpongeCR_false_babyBear` is for its already-flagged sibling in the same
file. -/
theorem cellLeafInjective_false_babyBear (CH : CellId → Value → ℤ) (c : CellId)
    (hb : ∀ v, 0 ≤ CH c v ∧ CH c v < (2013265921 : ℤ)) : ¬ cellLeafInjective CH :=
  cellLeafInjective_false_of_finite_range CH c (finite_range_of_field_window (CH c) _ hb)

/-- **TOOTH 2 — `logHashInjective` is FALSE for a range-bounded log hash.** The receipt chain
`List Turn` is infinite; a bounded-range accumulator cannot inject it. -/
theorem logHashInjective_false_of_finite_range (LH : List Turn → ℤ)
    (hfin : (Set.range LH).Finite) : ¬ logHashInjective LH := fun hinj =>
  not_injective_of_finite_range LH hfin (fun xs ys h => hinj xs ys h)

/-- **TOOTH 2 (deployed form) — `logHashInjective` is FALSE at the REAL BabyBear parameters.** Every real
Poseidon2 receipt-chain accumulator lands in a BabyBear field element, so the growing-log effects
(`EffectInstances2`, `EffectRefinement`) carry an unsatisfiable hypothesis. -/
theorem logHashInjective_false_babyBear (LH : List Turn → ℤ)
    (hb : ∀ xs, 0 ≤ LH xs ∧ LH xs < (2013265921 : ℤ)) : ¬ logHashInjective LH :=
  logHashInjective_false_of_finite_range LH (finite_range_of_field_window LH _ hb)

/-! ### ⚑ The `*Realization` bundles are NON-INHABITABLE at deployed parameters.

Worse than a false hypothesis on a theorem: `Poseidon2Binding.LeafRealization` / `LogRealization` carry
`spongeCR : Poseidon2SpongeCR sponge` as a structure FIELD, whose type `HashFloorHonesty` had ALREADY
proved false at BabyBear. So a deployed realization VALUE cannot exist, and every discharge routed
through one is satisfied only by the toy injective `Encodable.encode` sponge. This is the
`Compress8CR`-in-`Cap8Scheme` shape the sweep named the priority — here, twice, in the leaf/log tree. -/

/-- **(TOOTH — a deployed `LeafRealization` CANNOT EXIST.)** If the sponge a `LeafRealization` factors
through is BabyBear-range-bounded — which every real Poseidon2 `hash_many` is — the bundle is
uninhabitable: its `spongeCR` field's type is FALSE. So
`Poseidon2Binding.cellLeafInjective_of_realization` discharges `cellLeafInjective` only at a sponge no
deployment runs. -/
theorem leafRealization_uninhabitable_babyBear {CH : CellId → Value → ℤ} (R : LeafRealization CH)
    (hb : ∀ xs, 0 ≤ R.sponge xs ∧ R.sponge xs < (2013265921 : ℤ)) : False :=
  Dregg2.Circuit.HashFloorHonesty.poseidon2SpongeCR_false_babyBear R.sponge hb R.spongeCR

/-- **(TOOTH — a deployed `LogRealization` CANNOT EXIST.)** Same for the log side. In particular
`Verify/KeystoneAuditArgusReceipt.LH₀_inj` — which discharges `logHashInjective` via
`logHashInjective_of_realization refLogRealization` — stands on `Reference.refLogRealization`, whose
sponge IS `Encodable.encode` (injective into ALL of `ℤ`, range NOT bounded). The receipt's carrier is
discharged, and at BabyBear it could not be. -/
theorem logRealization_uninhabitable_babyBear {LH : List Turn → ℤ} (R : LogRealization LH)
    (hb : ∀ xs, 0 ≤ R.sponge xs ∧ R.sponge xs < (2013265921 : ℤ)) : False :=
  Dregg2.Circuit.HashFloorHonesty.poseidon2SpongeCR_false_babyBear R.sponge hb R.spongeCR

/-! ## §2 — the honest floor's carriers: decidable equality, and the union bound.

`KeyedHashFamily` needs `DecidableEq` on its input (the game checks `x ≠ x'`). The tree deliberately has
NO `DecidableEq Value` (`FinKernelStep`, `EffectsAsDataProto`, `FlowRefine` each note the absence). We do
NOT reach for `Classical.decEq`: `Poseidon2Binding.Reference.encV_inj` already proves `encV : Value → ℕ` injective,
so decidable equality on `Value` is COMPUTABLE, and the collision game's counting stays a real finite
count. Kept a plain `def` (NOT an instance) so the tree's deliberate absence is not disturbed. -/

/-- **Decidable equality on `Value`, COMPUTED** — via the proven-injective `Poseidon2Binding.Reference.encV`. Not
an instance (the tree deliberately has none); supplied explicitly to the leaf family below. -/
def valueDecEq : DecidableEq Value := fun v w =>
  decidable_of_iff (Dregg2.Circuit.Poseidon2Binding.Reference.encV v = Dregg2.Circuit.Poseidon2Binding.Reference.encV w)
    ⟨fun h => Dregg2.Circuit.Poseidon2Binding.Reference.encV_inj v w h, fun h => by rw [h]⟩

/-- **THE THREE-HORN UNION BOUND.** `HermineHashCRRegrounded.winProb_le_add_of_imp` peeled once: if every
winning outcome of `f` wins one of `g`, `h`, `k`, then `winProb f ≤ winProb g + (winProb h + winProb k)`.
Reused, not re-proved — the two-horn lemma is the general fact. -/
theorem winProb_le_add3_of_imp {Ω : Type*} [Fintype Ω] {f g h k : Ω → Bool}
    (himp : ∀ o, f o = true → g o = true ∨ h o = true ∨ k o = true) :
    winProb f ≤ winProb g + (winProb h + winProb k) := by
  refine le_trans (winProb_le_add_of_imp (f := f) (g := g) (h := fun o => h o || k o) ?_) ?_
  · intro o ho
    rcases himp o ho with h1 | h2 | h3
    · exact Or.inl h1
    · exact Or.inr (by simp [h2])
    · exact Or.inr (by simp [h3])
  · gcongr
    exact winProb_le_add_of_imp (f := fun o => h o || k o) (g := h) (h := k) (fun o ho => by
      simpa using ho)

/-- **THE FOUR-HORN UNION BOUND.** The same peel once more — the equivocation reduction below has four
horns (two node-hash sites, the frame sponge, and the leaf hash). -/
theorem winProb_le_add4_of_imp {Ω : Type*} [Fintype Ω] {f g h k m : Ω → Bool}
    (himp : ∀ o, f o = true → g o = true ∨ h o = true ∨ k o = true ∨ m o = true) :
    winProb f ≤ winProb g + (winProb h + (winProb k + winProb m)) := by
  refine le_trans (winProb_le_add_of_imp (f := f) (g := g)
    (h := fun o => h o || (k o || m o)) ?_) ?_
  · intro o ho
    rcases himp o ho with h1 | h2 | h3 | h4
    · exact Or.inl h1
    · exact Or.inr (by simp [h2])
    · exact Or.inr (by simp [h3])
    · exact Or.inr (by simp [h4])
  · gcongr
    exact winProb_le_add3_of_imp (f := fun o => h o || (k o || m o)) (g := h) (h := k) (k := m)
      (fun o ho => by
        simp only [Bool.or_eq_true] at ho
        rcases ho with h1 | h2 | h3
        · exact Or.inl h1
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr h3))

/-! ## §3 — the state-commitment equivocator, as a first-class λ-indexed game.

The deployed consumer is `StateCommit.cellDigest_binds_cells`: equal `cellDigest`s force equal cell maps,
GIVEN `compressInjective compress`, `compressNInjective compressN` and `cellLeafInjective CH` — all three
false at deployed parameters (§1 and `HashFloorHonesty`). Its BREAK is an equivocator: two kernels over
the same accounts, both `AccountsWF`, with DIFFERENT cell maps and EQUAL cell-digests. This section makes
that adversary a `Game` played over a SAMPLED instance, exactly as `HermineHashCRRegrounded`'s
`concurrentForgeryGame` makes a rushing forger one. -/

/-- **THE STATE-COMMITMENT FAMILY.** At each security parameter `l`: a FINITE space of sampled instances,
and per instance the deployed commitment surface — the leaf hash `CH`, the 2-to-1 node hash `compress`,
the frame sponge `compressN`, and the `turn` the commitment is taken at. This carries the deployed data of
`StateCommit.cellDigest` and nothing else. (The instance is the honest home of the domain-separation the
deployed unkeyed Poseidon2 uses as its effective key — `HashFloorHonesty` §2.) -/
structure StateCommitFamily where
  /-- The instance space (domain-separation / commitment-surface sampling). -/
  Inst : ℕ → Type
  /-- The instance space is finite (the game samples a uniform instance). -/
  instFin : ∀ l, Fintype (Inst l)
  /-- The instance space is inhabited (a non-empty outcome space). -/
  instNe : ∀ l, Nonempty (Inst l)
  /-- The per-cell leaf hash at parameter `l`, instance `i`. -/
  CH : ∀ l, Inst l → CellId → Value → ℤ
  /-- The 2-to-1 Merkle node hash at parameter `l`, instance `i`. -/
  compress : ∀ l, Inst l → ℤ → ℤ → ℤ
  /-- The frame sponge over a list of leaves at parameter `l`, instance `i`. -/
  compressN : ∀ l, Inst l → List ℤ → ℤ
  /-- The turn the commitment is taken at (it pins the moved/frame partition). -/
  turn : ∀ l, Inst l → Turn

/-- **THE LEAF-HASH KEYED FAMILY.** Inputs are `(cell, value)` pairs, outputs field elements, and the
keyed hash is the deployed `CH`. A `cellLeafInjective` break at cell `c` — two distinct `Value`s with
equal leaves — IS a collision of this family (the pair `((c,v),(c,w))`). Keys are the SAME sampled
instances as the equivocation game, so the union bound below is over ONE `Ω`. -/
def scLeafFamily (F : StateCommitFamily) : KeyedHashFamily where
  Key := F.Inst
  Input := CellId × Value
  Out := ℤ
  H := fun l i p => F.CH l i p.1 p.2
  keyFintype := F.instFin
  keyNonempty := F.instNe
  inputDecEq := letI := valueDecEq; inferInstance
  outDecEq := inferInstance

/-- **THE NODE-HASH KEYED FAMILY.** Inputs are the 2-to-1 hash's input pairs; the keyed hash is the
deployed `compress`. Both node sites the reduction attacks (the cell-digest root and the `movedDigest`
node) collide in THIS family. -/
def scNodeFamily (F : StateCommitFamily) : KeyedHashFamily where
  Key := F.Inst
  Input := ℤ × ℤ
  Out := ℤ
  H := fun l i p => F.compress l i p.1 p.2
  keyFintype := F.instFin
  keyNonempty := F.instNe
  inputDecEq := inferInstance
  outDecEq := inferInstance

/-- **THE FRAME-SPONGE KEYED FAMILY.** Inputs are sorted leaf lists; the keyed hash is the deployed
`compressN`. The frame horn of the reduction collides here. -/
def scSpongeFamily (F : StateCommitFamily) : KeyedHashFamily where
  Key := F.Inst
  Input := List ℤ
  Out := ℤ
  H := fun l i xs => F.compressN l i xs
  keyFintype := F.instFin
  keyNonempty := F.instNe
  inputDecEq := inferInstance
  outDecEq := inferInstance

/-- The frame carrier at an instance: the live accounts MINUS the two moved cells — the carrier
`StateCommit.cellDigest` partitions over. -/
def scCarrier (F : StateCommitFamily) (l : ℕ) (i : F.Inst l) (k : RecordKernelState) : Finset CellId :=
  k.accounts \ {(F.turn l i).src, (F.turn l i).dst}

/-- The two children of the cell-digest ROOT node: `(frameDigest, movedDigest)`. `scCellDigest_eq` pins
that `cellDigest` IS `compress` of this pair — so an equivocation is a collision at THIS node whenever the
pairs differ. -/
def scOuterPair (F : StateCommitFamily) (l : ℕ) (i : F.Inst l) (k : RecordKernelState) : ℤ × ℤ :=
  (frameDigest (F.CH l i) (F.compressN l i) k (scCarrier F l i k),
   movedDigest (F.CH l i) (F.compress l i) k.cell (F.turn l i).src (F.turn l i).dst)

/-- The two children of the `movedDigest` node: the `src`/`dst` LEAVES. -/
def scMovedPair (F : StateCommitFamily) (l : ℕ) (i : F.Inst l) (f : CellId → Value) : ℤ × ℤ :=
  (F.CH l i (F.turn l i).src (f (F.turn l i).src),
   F.CH l i (F.turn l i).dst (f (F.turn l i).dst))

/-- The frame sponge's INPUT: the untouched cells' leaves in CANONICAL (sorted) order. -/
def scFrameList (F : StateCommitFamily) (l : ℕ) (i : F.Inst l) (k : RecordKernelState) : List ℤ :=
  ((scCarrier F l i k).sort (· ≤ ·)).map (fun c => F.CH l i c (k.cell c))

/-- **THE DEPLOYED `cellDigest` IS `compress` OF THE OUTER PAIR** — by `rfl`, straight off
`StateCommit.cellDigest`. The reduction's node horn attacks this equation, not a paraphrase of it. -/
theorem scCellDigest_eq (F : StateCommitFamily) (l : ℕ) (i : F.Inst l) (k : RecordKernelState) :
    cellDigest (F.CH l i) (F.compress l i) (F.compressN l i) k (F.turn l i)
      = F.compress l i (scOuterPair F l i k).1 (scOuterPair F l i k).2 := rfl

/-- **THE DEPLOYED `movedDigest` IS `compress` OF THE MOVED PAIR** — by `rfl`. -/
theorem scMovedDigest_eq (F : StateCommitFamily) (l : ℕ) (i : F.Inst l) (f : CellId → Value) :
    movedDigest (F.CH l i) (F.compress l i) f (F.turn l i).src (F.turn l i).dst
      = F.compress l i (scMovedPair F l i f).1 (scMovedPair F l i f).2 := rfl

/-- **THE DEPLOYED `frameDigest` IS `compressN` OF THE FRAME LIST** — by `rfl`. -/
theorem scFrameDigest_eq (F : StateCommitFamily) (l : ℕ) (i : F.Inst l) (k : RecordKernelState) :
    frameDigest (F.CH l i) (F.compressN l i) k (scCarrier F l i k)
      = F.compressN l i (scFrameList F l i k) := rfl

/-- **THE STATE-COMMITMENT EQUIVOCATION GAME.** The adversary is handed a sampled commitment surface and
WINS iff it outputs two kernels that are `AccountsWF`, agree on `accounts`, DIFFER on the cell map, and
yet have EQUAL `cellDigest`s. Winning this game is exactly breaking the deployed binding
`StateCommit.cellDigest_binds_cells` claims — the break is IN the win predicate, read off the real
`cellDigest`. (`winsDec` is classical: `AccountsWF` and cell-map inequality quantify over the infinite
`CellId`, so they are genuine propositions with no computable decider. The counting is unaffected — the
instance space is what is finite and sampled.) -/
noncomputable def scEquivGame (F : StateCommitFamily) : Game where
  Inst := F.Inst
  Ans := fun _ => RecordKernelState × RecordKernelState
  instFin := F.instFin
  instNe := F.instNe
  wins := fun l i p =>
    AccountsWF p.1 ∧ AccountsWF p.2 ∧ p.1.accounts = p.2.accounts ∧ p.1.cell ≠ p.2.cell ∧
      cellDigest (F.CH l i) (F.compress l i) (F.compressN l i) p.1 (F.turn l i)
        = cellDigest (F.CH l i) (F.compress l i) (F.compressN l i) p.2 (F.turn l i)
  winsDec := fun _ _ _ => Classical.propDecidable _

/-- **THE PROBLEM IS IN THE STATEMENT** — the equivocation game's win relation is a genuine break of the
deployed cell-digest binding. -/
theorem scEquivGame_wins_iff (F : StateCommitFamily) (l : ℕ) (i : F.Inst l)
    (p : RecordKernelState × RecordKernelState) :
    (scEquivGame F).wins l i p ↔
      (AccountsWF p.1 ∧ AccountsWF p.2 ∧ p.1.accounts = p.2.accounts ∧ p.1.cell ≠ p.2.cell ∧
        cellDigest (F.CH l i) (F.compress l i) (F.compressN l i) p.1 (F.turn l i)
          = cellDigest (F.CH l i) (F.compress l i) (F.compressN l i) p.2 (F.turn l i)) :=
  Iff.rfl

/-! ## §4 — the reduction: four maps of adversaries, and the dichotomy.

`StateCommit.cellDigest_binds_cells` walks the exhaustive partition `{src} ∪ {dst} ∪ (accounts\{src,dst})
∪ dead` and uses the three injectivity floors to force equality at each. CONTRAPOSED, that walk is an
EXTRACTOR: wherever the cell maps differ, the equal digests hand back a collision at one of three real
hash sites. These are the maps. -/

/-- A cell where two cell maps DIFFER. `Classical.epsilon` on the `∃` that `funext` contraposes to — the
adversary must be TOTAL, so on agreeing maps this is junk, which is real and harmless (the reduction only
ever reads it under a winning `p.1.cell ≠ p.2.cell`). -/
noncomputable def diffCell (f g : CellId → Value) : CellId :=
  Classical.epsilon (fun c => f c ≠ g c)

/-- `diffCell` really does find a difference when there is one — `funext`, contraposed. -/
theorem diffCell_spec {f g : CellId → Value} (hne : f ≠ g) :
    f (diffCell f g) ≠ g (diffCell f g) := by
  have hex : ∃ c, f c ≠ g c := by
    by_contra hc
    push_neg at hc
    exact hne (funext hc)
  exact Classical.epsilon_spec hex

/-- **HORN 1 — the ROOT node collision, as a map of adversaries.** The equivocator's two
`(frameDigest, movedDigest)` children. Equal cell-digests mean `compress` agrees on them; if the pairs
differ, that IS a node-hash collision. -/
noncomputable def scToOuterNodeAdv (F : StateCommitFamily) (A : Adversary (scEquivGame F)) :
    Adversary (hashGame (scNodeFamily F)) where
  run := fun l i => let p := A.run l i; (scOuterPair F l i p.1, scOuterPair F l i p.2)

/-- **HORN 2 — the `movedDigest` node collision, as a map of adversaries.** The two `(CH src, CH dst)`
leaf pairs of the moved node. -/
noncomputable def scToMovedNodeAdv (F : StateCommitFamily) (A : Adversary (scEquivGame F)) :
    Adversary (hashGame (scNodeFamily F)) where
  run := fun l i => let p := A.run l i; (scMovedPair F l i p.1.cell, scMovedPair F l i p.2.cell)

/-- **HORN 3 — the frame-sponge collision, as a map of adversaries.** The two sorted leaf lists over the
untouched carrier. -/
noncomputable def scToSpongeAdv (F : StateCommitFamily) (A : Adversary (scEquivGame F)) :
    Adversary (hashGame (scSpongeFamily F)) where
  run := fun l i => let p := A.run l i; (scFrameList F l i p.1, scFrameList F l i p.2)

/-- **HORN 4 — the LEAF collision, as a map of adversaries — the horn `cellLeafInjective` was carrying
for free.** At the cell where the two maps differ, the two `Value`s. When the node/sponge horns close,
these two DISTINCT values have EQUAL leaves: precisely a `cellLeafInjective` counterexample, now a
collision the floor must pay for. -/
noncomputable def scToLeafAdv (F : StateCommitFamily) (A : Adversary (scEquivGame F)) :
    Adversary (hashGame (scLeafFamily F)) where
  run := fun l i =>
    let p := A.run l i
    let c := diffCell p.1.cell p.2.cell
    ((c, p.1.cell c), (c, p.2.cell c))

/-- **⚑ THE DICHOTOMY, ON A CLAIM — and this is `cellDigest_binds_cells`, contraposed.** Wherever an
equivocator wins, the equal cell-digests force a collision at ONE of the four real hash sites: the root
node, the moved node, the frame sponge, or the LEAF. Proved by the SAME exhaustive partition
`StateCommit.cellDigest_binds_cells` runs — `{src}`, `{dst}`, the untouched carrier, and the dead cells
(closed by `AccountsWF` on BOTH states, so a dead cell cannot be the difference). The hash content lives
in proof terms, not in a sentence about them. -/
theorem sc_claim_wins_imp (F : StateCommitFamily) (l : ℕ) (i : F.Inst l)
    (p : RecordKernelState × RecordKernelState) (hwin : (scEquivGame F).wins l i p) :
    (scOuterPair F l i p.1 ≠ scOuterPair F l i p.2 ∧
        F.compress l i (scOuterPair F l i p.1).1 (scOuterPair F l i p.1).2
          = F.compress l i (scOuterPair F l i p.2).1 (scOuterPair F l i p.2).2)
      ∨ (scMovedPair F l i p.1.cell ≠ scMovedPair F l i p.2.cell ∧
        F.compress l i (scMovedPair F l i p.1.cell).1 (scMovedPair F l i p.1.cell).2
          = F.compress l i (scMovedPair F l i p.2.cell).1 (scMovedPair F l i p.2.cell).2)
      ∨ (scFrameList F l i p.1 ≠ scFrameList F l i p.2 ∧
        F.compressN l i (scFrameList F l i p.1) = F.compressN l i (scFrameList F l i p.2))
      ∨ (let c := diffCell p.1.cell p.2.cell
         ((c, p.1.cell c) ≠ (c, p.2.cell c) ∧ F.CH l i c (p.1.cell c) = F.CH l i c (p.2.cell c))) := by
  obtain ⟨hwf, hwf', hAcc, hcellne, hcd⟩ := hwin
  set c := diffCell p.1.cell p.2.cell with hcdef
  have hc : p.1.cell c ≠ p.2.cell c := diffCell_spec hcellne
  -- the cell-digest equality, read at the root node.
  have hroot : F.compress l i (scOuterPair F l i p.1).1 (scOuterPair F l i p.1).2
      = F.compress l i (scOuterPair F l i p.2).1 (scOuterPair F l i p.2).2 := by
    rw [← scCellDigest_eq, ← scCellDigest_eq]; exact hcd
  by_cases houter : scOuterPair F l i p.1 = scOuterPair F l i p.2
  · -- ROOT node children AGREE: the frame digests agree AND the moved digests agree.
    have hframeD : (scOuterPair F l i p.1).1 = (scOuterPair F l i p.2).1 := by rw [houter]
    have hmovedD : (scOuterPair F l i p.1).2 = (scOuterPair F l i p.2).2 := by rw [houter]
    have hmovedNode : F.compress l i (scMovedPair F l i p.1.cell).1 (scMovedPair F l i p.1.cell).2
        = F.compress l i (scMovedPair F l i p.2.cell).1 (scMovedPair F l i p.2.cell).2 := by
      rw [← scMovedDigest_eq, ← scMovedDigest_eq]; exact hmovedD
    have hspongeEq : F.compressN l i (scFrameList F l i p.1) = F.compressN l i (scFrameList F l i p.2) := by
      rw [← scFrameDigest_eq, ← scFrameDigest_eq]; exact hframeD
    -- the exhaustive partition on where the difference `c` lives.
    by_cases hcsrc : c = (F.turn l i).src
    · -- MOVED cell (src): either the moved node collides, or its `src` leaf does.
      by_cases hmp : scMovedPair F l i p.1.cell = scMovedPair F l i p.2.cell
      · refine Or.inr (Or.inr (Or.inr ?_))
        have hleaf : F.CH l i (F.turn l i).src (p.1.cell (F.turn l i).src)
            = F.CH l i (F.turn l i).src (p.2.cell (F.turn l i).src) := congrArg Prod.fst hmp
        exact ⟨by simp only [ne_eq, Prod.mk.injEq, true_and]; exact hc, by rw [hcsrc]; exact hleaf⟩
      · exact Or.inr (Or.inl ⟨hmp, hmovedNode⟩)
    · by_cases hcdst : c = (F.turn l i).dst
      · -- MOVED cell (dst): symmetric.
        by_cases hmp : scMovedPair F l i p.1.cell = scMovedPair F l i p.2.cell
        · refine Or.inr (Or.inr (Or.inr ?_))
          have hleaf : F.CH l i (F.turn l i).dst (p.1.cell (F.turn l i).dst)
              = F.CH l i (F.turn l i).dst (p.2.cell (F.turn l i).dst) := congrArg Prod.snd hmp
          exact ⟨by simp only [ne_eq, Prod.mk.injEq, true_and]; exact hc, by rw [hcdst]; exact hleaf⟩
        · exact Or.inr (Or.inl ⟨hmp, hmovedNode⟩)
      · by_cases hcacc : c ∈ p.1.accounts
        · -- UNTOUCHED live cell: either the frame sponge collides, or the leaf at `c` does.
          by_cases hfl : scFrameList F l i p.1 = scFrameList F l i p.2
          · refine Or.inr (Or.inr (Or.inr ?_))
            -- equal sorted-leaf lists over the SAME carrier ⇒ per-position leaves agree.
            have hcarr : scCarrier F l i p.2 = scCarrier F l i p.1 := by
              unfold scCarrier; rw [hAcc]
            have hmap : ((scCarrier F l i p.1).sort (· ≤ ·)).map (fun x => F.CH l i x (p.1.cell x))
                = ((scCarrier F l i p.1).sort (· ≤ ·)).map (fun x => F.CH l i x (p.2.cell x)) := by
              unfold scFrameList at hfl; rw [hcarr] at hfl; exact hfl
            have hpt : ∀ x ∈ (scCarrier F l i p.1).sort (· ≤ ·),
                F.CH l i x (p.1.cell x) = F.CH l i x (p.2.cell x) := List.map_inj_left.mp hmap
            have hmem : c ∈ scCarrier F l i p.1 := by
              unfold scCarrier
              simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨hcacc, hcsrc, hcdst⟩
            exact ⟨by simp only [ne_eq, Prod.mk.injEq, true_and]; exact hc,
              hpt c ((Finset.mem_sort (· ≤ ·)).mpr hmem)⟩
          · exact Or.inr (Or.inr (Or.inl ⟨hfl, hspongeEq⟩))
        · -- DEAD cell: `AccountsWF` on BOTH states makes both default — it cannot be the difference.
          exact absurd (by rw [hwf c hcacc, hwf' c (by rw [← hAcc]; exact hcacc)]) hc
  · -- ROOT node children DIFFER: a genuine node-hash collision at the cell-digest root.
    exact Or.inl ⟨houter, hroot⟩

/-- **⚑ THE DICHOTOMY AT THE GAME LEVEL.** `sc_claim_wins_imp` at the equivocator's actual output: every
instance it wins, one of the four derived finders wins its collision game. The derived runs are
DEFINITIONALLY the four extractors, so this is `sc_claim_wins_imp` transported by `rfl`. -/
theorem sc_wins_imp (F : StateCommitFamily) (A : Adversary (scEquivGame F)) (l : ℕ) (i : F.Inst l)
    (hwin : (scEquivGame F).wins l i (A.run l i)) :
    (hashGame (scNodeFamily F)).wins l i ((scToOuterNodeAdv F A).run l i) ∨
      (hashGame (scNodeFamily F)).wins l i ((scToMovedNodeAdv F A).run l i) ∨
      (hashGame (scSpongeFamily F)).wins l i ((scToSpongeAdv F A).run l i) ∨
      (hashGame (scLeafFamily F)).wins l i ((scToLeafAdv F A).run l i) :=
  sc_claim_wins_imp F l i (A.run l i) hwin

/-- **THE ADVANTAGE INEQUALITY.** The equivocator's advantage is at most the SUM of the four extracted
finders' advantages, at every parameter — all five play over the SAME sampled instance space, and every
instance the equivocator wins one of the four derived finders wins. A genuine union-bound reduction
inequality over real game advantages. -/
theorem sc_adv_le (F : StateCommitFamily) (A : Adversary (scEquivGame F)) (l : ℕ) :
    gameAdv (scEquivGame F) A l ≤
      gameAdv (hashGame (scNodeFamily F)) (scToOuterNodeAdv F A) l +
        (gameAdv (hashGame (scNodeFamily F)) (scToMovedNodeAdv F A) l +
          (gameAdv (hashGame (scSpongeFamily F)) (scToSpongeAdv F A) l +
            gameAdv (hashGame (scLeafFamily F)) (scToLeafAdv F A) l)) := by
  refine @winProb_le_add4_of_imp _ (F.instFin l) _ _ _ _ _ (fun i hi => ?_)
  rw [Adversary.hit_eq_true] at hi
  rcases sc_wins_imp F A l i hi with h1 | h2 | h3 | h4
  · exact Or.inl ((Adversary.hit_eq_true (scToOuterNodeAdv F A) l i).mpr h1)
  · exact Or.inr (Or.inl ((Adversary.hit_eq_true (scToMovedNodeAdv F A) l i).mpr h2))
  · exact Or.inr (Or.inr (Or.inl ((Adversary.hit_eq_true (scToSpongeAdv F A) l i).mpr h3)))
  · exact Or.inr (Or.inr (Or.inr ((Adversary.hit_eq_true (scToLeafAdv F A) l i).mpr h4)))

/-! ## §5 — the RE-GROUNDED keystone. -/

/-- **⚑ RE-GROUNDED `StateCommit.cellDigest_binds_cells` / `recStateCommit_binds_kernel` — from
COLLISION HARDNESS at the three families the reduction attacks, VIA the reduction.**

Under the collision floor at the node hash, the frame sponge and the LEAF hash — each at a NAMED adversary
class `Eff` — a state-commitment equivocator whose four extracted finders lie in those classes has
NEGLIGIBLE advantage: the published cell-digest pins the whole cell map EXCEPT with negligible
probability. The Boolean "equal digests ⇒ equal cell maps", which needed the FALSE `cellLeafInjective`
(§1) and its two already-flagged siblings, becomes an honest advantage bound.

⚑ **THE `hEff*` OBLIGATIONS ARE UNDISCHARGED AND THAT IS THE HONEST STATE.** They say the extracted
finders are in the classes the floors quantify over — the standard "the reduction is efficient". They are
PARAMETERS here, in the open, at the use site, because this tree has no cost model (`FloorGames` §8). The
floors are priced exactly by §7: `Eff := ⊤` makes them FALSE at compressing parameters (which is why this
file does NOT route through `HashFloorHonesty.CollisionResistant`, itself
`HashCRHardQuant _ ⊤` and itself false — `FloorGames.collisionResistant_false_of_compressing`),
`Eff := ⊥` vacuous. -/
theorem stateCommit_equivocation_advantage_bound (F : StateCommitFamily)
    (EffNode : Adversary (hashGame (scNodeFamily F)) → Prop)
    (EffSponge : Adversary (hashGame (scSpongeFamily F)) → Prop)
    (EffLeaf : Adversary (hashGame (scLeafFamily F)) → Prop)
    (A : Adversary (scEquivGame F))
    (hEffOuter : EffNode (scToOuterNodeAdv F A))
    (hEffMoved : EffNode (scToMovedNodeAdv F A))
    (hEffSponge : EffSponge (scToSpongeAdv F A))
    (hEffLeaf : EffLeaf (scToLeafAdv F A))
    (hNode : HashCRHardQuant (scNodeFamily F) EffNode)
    (hSponge : HashCRHardQuant (scSpongeFamily F) EffSponge)
    (hLeaf : HashCRHardQuant (scLeafFamily F) EffLeaf) :
    Negl (gameAdv (scEquivGame F) A) :=
  negl_of_le (fun l => (gameAdv_mem_unit (scEquivGame F) A l).1)
    (sc_adv_le F A)
    (negl_add (hNode _ hEffOuter)
      (negl_add (hNode _ hEffMoved)
        (negl_add (hSponge _ hEffSponge) (hLeaf _ hEffLeaf))))

/-! ## §5b — the LOG-HASH consumer, re-grounded (`logHashInjective`).

⚑ **The honest scope of this one is smaller than §3–§5, and saying so is the point.** The leaf floor
needed a four-horn reduction because `cellDigest` is a TREE: an equivocation there could be paid for at any
of four hash sites, and only the walk of the partition says which. The log floor is not a tree.
`logHashInjective LH := ∀ xs ys, LH xs = LH ys → xs = ys` is consumed by `EffectInstances2` /
`EffectRefinement` (`effect2_circuit_full_sound`, `effect_refines_*`) for exactly one thing: recovering the
receipt chain from its digest. Its BREAK — two distinct turn lists with one log hash — **IS definitionally
a collision of the log hash**, so there is no multi-horn dichotomy to build and inventing one would be
theatre.

What the re-grounding buys here is therefore precise and it is not nothing: the consumer moves off a
hypothesis that is FALSE at deployed parameters (`logHashInjective_false_babyBear`, and
`logRealization_uninhabitable_babyBear` for the bundle that discharges it) onto a floor about an
adversary FINDING a collision, at a NAMED `Eff` class. Existence → advantage. That is the entire content,
and `scLogFamily_CR_of_logHashInjective` + `logHashInjective_false_babyBear` together are the finding:
the old carrier was STRICTLY STRONGER than needed AND unsatisfiable. -/

/-- **THE LOG-HASH FAMILY.** Inputs are receipt chains, outputs field elements, the keyed hash the deployed
`LH`. A `logHashInjective` break IS a collision of this family. -/
structure LogCommitFamily where
  /-- The instance space (domain-separation sampling). -/
  Inst : ℕ → Type
  /-- The instance space is finite. -/
  instFin : ∀ l, Fintype (Inst l)
  /-- The instance space is inhabited. -/
  instNe : ∀ l, Nonempty (Inst l)
  /-- The receipt-chain hash at parameter `l`, instance `i`. -/
  LH : ∀ l, Inst l → List Turn → ℤ

/-- The log hash as a `KeyedHashFamily` — the collision game the honest floor lives over. -/
def scLogFamily (F : LogCommitFamily) : KeyedHashFamily where
  Key := F.Inst
  Input := List Turn
  Out := ℤ
  H := F.LH
  keyFintype := F.instFin
  keyNonempty := F.instNe
  inputDecEq := inferInstance
  outDecEq := inferInstance

/-- **THE PROBLEM IS IN THE STATEMENT** — the log game's win relation is a genuine collision of the real
receipt-chain hash: two DISTINCT turn lists, one digest. This is exactly the event `logHashInjective`
declared impossible and §1 proves pigeonhole FORCES. -/
theorem scLogGame_wins_iff (F : LogCommitFamily) (l : ℕ) (i : F.Inst l) (p : List Turn × List Turn) :
    (hashGame (scLogFamily F)).wins l i p ↔ (p.1 ≠ p.2 ∧ F.LH l i p.1 = F.LH l i p.2) :=
  Iff.rfl

/-- **⚑ RE-GROUNDED `logHashInjective` CONSUMER (`EffectInstances2.effect2_circuit_full_sound`,
`EffectRefinement.effect_refines_*`).** Under the collision floor at the log family, at a NAMED `Eff`
class, a receipt-chain equivocator has NEGLIGIBLE advantage: the published log digest pins the chain
EXCEPT with negligible probability. The Boolean "equal log hashes ⇒ equal chains", which needed the FALSE
`logHashInjective`, becomes an honest advantage bound.

⚑ `hEff` is UNDISCHARGED and that is the honest state (`FloorGames` §8) — priced by
`sc_log_floor_top_false_of_compressing` / `sc_log_floor_satisfiable_vacuously`. -/
theorem log_equivocation_advantage_bound (F : LogCommitFamily)
    (Eff : Adversary (hashGame (scLogFamily F)) → Prop)
    (A : Adversary (hashGame (scLogFamily F))) (hEff : Eff A)
    (hLog : HashCRHardQuant (scLogFamily F) Eff) :
    Negl (gameAdv (hashGame (scLogFamily F)) A) :=
  hLog A hEff

/-- **`logHashInjective` ⟹ the log collision floor at the UNRESTRICTED class.** Unlike the leaf carrier
(§8 — per-cell injectivity does not cover its family's cross-cell collisions), this bridge is VALID:
`logHashInjective` is full injectivity of `LH`, so it forbids every collision and every finder's advantage
is `0`. Together with `logHashInjective_false_babyBear` that is the whole finding: the old carrier was
STRICTLY STRONGER than the honest floor needs AND unsatisfiable at deployed parameters — an empty
hypothesis, which is why its consumers were vacuously true. -/
theorem scLogFamily_CR_of_logHashInjective (F : LogCommitFamily)
    (hinj : ∀ l (i : F.Inst l), logHashInjective (F.LH l i)) :
    CollisionResistant (scLogFamily F) :=
  injective_family_CR (scLogFamily F) (fun l i xs ys h => hinj l i xs ys h)

/-- **(TOOTH — the log floor is SATISFIABLE, vacuously.)** At the empty class it holds for any log hash,
including a constant one. Recorded honestly; worth nothing without the refutation beside it. -/
theorem sc_log_floor_satisfiable_vacuously (F : LogCommitFamily) :
    HashCRHardQuant (scLogFamily F) (fun _ => False) :=
  hard_bot_vacuous _

/-- **(TOOTH — the log floor is FALSE at the unrestricted class, when the log hash is compressing.)** The
price of `hEff`, as a theorem: §1 proves pigeonhole forces such a collision at BabyBear, so at `Eff := ⊤`
the floor is FALSE and `log_equivocation_advantage_bound` is vacuous there. This is why the consumer must
NOT be re-grounded onto `HashFloorHonesty.CollisionResistant` (= this floor at `⊤`). -/
theorem sc_log_floor_top_false_of_compressing (F : LogCommitFamily)
    (hcol : ∀ l (i : F.Inst l), ∃ xs ys : List Turn, xs ≠ ys ∧ F.LH l i xs = F.LH l i ys) :
    ¬ HashCRHardQuant (scLogFamily F) (fun _ => True) := by
  refine not_hard_top_of_always_solvable (hashGame (scLogFamily F)) (fun _ => ⟨([], [])⟩) ?_
  intro l i
  obtain ⟨xs, ys, hne, heq⟩ := hcol l i
  exact ⟨(xs, ys), hne, heq⟩

/-! ## §6 — the CANARY: break the reduction and the keystone goes RED.

The sweep's lesson is that a floor consumer must be checked by asking whether it survives the WRONG
hypothesis. Under the OLD statement — `cellDigest_binds_cells (hLeaf : cellLeafInjective CH) …` — the
hypothesis was a FREE `Prop` that the conclusion never mentions, so no such canary was writable: the
floor and the conclusion did not share an object to disconnect. Here they cannot avoid it. -/

/-- **(CANARY — the keystone does NOT follow from the floors applied at OTHER adversaries.)** Strip the
reduction — try to conclude the equivocator's negligibility from the collision floors applied at some
OTHER finders `B`, `C`, `D`, `E`, NOT the ones extracted from it — and the proof does not go through: the
floors bound `B`/`C`/`D`/`E`, and only `sc_adv_le` connects the EXTRACTED four to the equivocation game.
The `negl_add` chain proves `Negl` of the WRONG advantage sum, so it cannot close
`Negl (gameAdv (scEquivGame F) A)`. This tooth was impossible to write under the old free
`cellLeafInjective` hypothesis; it compiles now, and REDS if a future edit reconnects the games. -/
example (F : StateCommitFamily)
    (EffNode : Adversary (hashGame (scNodeFamily F)) → Prop)
    (EffSponge : Adversary (hashGame (scSpongeFamily F)) → Prop)
    (EffLeaf : Adversary (hashGame (scLeafFamily F)) → Prop)
    (A : Adversary (scEquivGame F))
    (B C : Adversary (hashGame (scNodeFamily F))) (hB : EffNode B) (hC : EffNode C)
    (D : Adversary (hashGame (scSpongeFamily F))) (hD : EffSponge D)
    (E : Adversary (hashGame (scLeafFamily F))) (hE : EffLeaf E)
    (hNode : HashCRHardQuant (scNodeFamily F) EffNode)
    (hSponge : HashCRHardQuant (scSpongeFamily F) EffSponge)
    (hLeaf : HashCRHardQuant (scLeafFamily F) EffLeaf) : True := by
  fail_if_success
    (have : Negl (gameAdv (scEquivGame F) A) :=
      negl_add (hNode B hB) (negl_add (hNode C hC) (negl_add (hSponge D hD) (hLeaf E hE))))
  trivial

/-- **THE POSITIVE POLE — the RIGHT floors DO discharge it.** A gate that refuses everything is a broken
keystone, not a fixed one. With the collision floors at the EXTRACTED finders the keystone fires. Refusal
is discrimination only if acceptance still happens. -/
theorem the_repaired_bound_fires_on_the_right_floors (F : StateCommitFamily)
    (EffNode : Adversary (hashGame (scNodeFamily F)) → Prop)
    (EffSponge : Adversary (hashGame (scSpongeFamily F)) → Prop)
    (EffLeaf : Adversary (hashGame (scLeafFamily F)) → Prop)
    (A : Adversary (scEquivGame F))
    (hEffOuter : EffNode (scToOuterNodeAdv F A)) (hEffMoved : EffNode (scToMovedNodeAdv F A))
    (hEffSponge : EffSponge (scToSpongeAdv F A)) (hEffLeaf : EffLeaf (scToLeafAdv F A))
    (hNode : HashCRHardQuant (scNodeFamily F) EffNode)
    (hSponge : HashCRHardQuant (scSpongeFamily F) EffSponge)
    (hLeaf : HashCRHardQuant (scLeafFamily F) EffLeaf) :
    Negl (gameAdv (scEquivGame F) A) :=
  stateCommit_equivocation_advantage_bound F EffNode EffSponge EffLeaf A
    hEffOuter hEffMoved hEffSponge hEffLeaf hNode hSponge hLeaf

/-! ## §7 — the derived floors, priced honestly (both poles PROVED).

`FloorGames` §8's residual is that the tree has no cost model, so `Eff` cannot be given honest content
here. What CAN be proved is the price of both extremes — and that is what makes the `hEff*` parameters an
honest name for "the reduction is efficient" rather than a decoration. -/

/-- **(TOOTH — the leaf floor is SATISFIABLE, vacuously.)** At the empty adversary class it holds for any
leaf hash, including a completely broken one. Recorded HONESTLY, and it is not evidence of anything:
`hard_bot_vacuous` is exactly the statement that this satisfiability is vacuous. -/
theorem sc_leaf_floor_satisfiable_vacuously (F : StateCommitFamily) :
    HashCRHardQuant (scLeafFamily F) (fun _ => False) :=
  hard_bot_vacuous _

/-- **(TOOTH — the node floor is SATISFIABLE, vacuously.)** Likewise. -/
theorem sc_node_floor_satisfiable_vacuously (F : StateCommitFamily) :
    HashCRHardQuant (scNodeFamily F) (fun _ => False) :=
  hard_bot_vacuous _

/-- **(TOOTH — the sponge floor is SATISFIABLE, vacuously.)** Likewise. -/
theorem sc_sponge_floor_satisfiable_vacuously (F : StateCommitFamily) :
    HashCRHardQuant (scSpongeFamily F) (fun _ => False) :=
  hard_bot_vacuous _

/-- **(TOOTH — the LEAF floor is FALSE at the unrestricted class, when the leaf hash is compressing.)**
The real content, and the reason `Eff` is not decoration: if at every sampled instance two distinct
`Value`s share a leaf — which §1 proves pigeonhole FORCES at BabyBear — then the floor at `Eff := ⊤` is
FALSE, and the keystone is vacuous there. This is the price of `hEffLeaf`, stated as a theorem instead of
a promise. -/
theorem sc_leaf_floor_top_false_of_compressing (F : StateCommitFamily)
    (hcol : ∀ l (i : F.Inst l), ∃ (c : CellId) (v : Value) (w : Value),
      v ≠ w ∧ F.CH l i c v = F.CH l i c w) :
    ¬ HashCRHardQuant (scLeafFamily F) (fun _ => True) := by
  refine not_hard_top_of_always_solvable (hashGame (scLeafFamily F))
    (fun _ => ⟨((0, default), (0, default))⟩) ?_
  intro l i
  obtain ⟨c, v, w, hne, heq⟩ := hcol l i
  exact ⟨((c, v), (c, w)), fun h => hne (congrArg Prod.snd h), heq⟩

/-- **(TOOTH — the NODE floor is FALSE at the unrestricted class, when the node hash is compressing.)**
Same price for the 2-to-1 horn: two field elements do not fit in one
(`HashFloorHonesty.compressInjective_false_of_finite_range` is the injective-shape sibling of this). -/
theorem sc_node_floor_top_false_of_compressing (F : StateCommitFamily)
    (hcol : ∀ l (i : F.Inst l), ∃ a b : ℤ × ℤ, a ≠ b ∧ F.compress l i a.1 a.2 = F.compress l i b.1 b.2) :
    ¬ HashCRHardQuant (scNodeFamily F) (fun _ => True) := by
  refine not_hard_top_of_always_solvable (hashGame (scNodeFamily F))
    (fun _ => ⟨((0, 0), (0, 0))⟩) ?_
  intro l i
  obtain ⟨a, b, hne, heq⟩ := hcol l i
  exact ⟨(a, b), hne, heq⟩

/-- **(TOOTH — the SPONGE floor is FALSE at the unrestricted class, when the sponge is compressing.)**
The third horn's price — `List ℤ` is infinite and the squeeze is one field element. -/
theorem sc_sponge_floor_top_false_of_compressing (F : StateCommitFamily)
    (hcol : ∀ l (i : F.Inst l), ∃ xs ys : List ℤ, xs ≠ ys ∧ F.compressN l i xs = F.compressN l i ys) :
    ¬ HashCRHardQuant (scSpongeFamily F) (fun _ => True) := by
  refine not_hard_top_of_always_solvable (hashGame (scSpongeFamily F)) (fun _ => ⟨([], [])⟩) ?_
  intro l i
  obtain ⟨xs, ys, hne, heq⟩ := hcol l i
  exact ⟨(xs, ys), hne, heq⟩

/-! ## §8 — ⚑ the OLD floor is WEAKER than its family, and the reduction stays on the DIAGONAL.

The usual re-grounding note is "the old injective floor implies the new one, so it was strictly stronger
and, being false, empty" (`HashFloorHonesty.commitRevealFamily_CR_of_hashcr` for the flagged siblings).
**That note is FALSE here, and saying so is the point.** `cellLeafInjective CH` is injectivity in the
`Value` at a FIXED cell — it says NOTHING about `CH c v = CH c' w` for `c ≠ c'`. So it does NOT discharge
`CollisionResistant (scLeafFamily F)`, whose game admits cross-cell collisions: the old carrier is not
merely false, it is not even the right shape for its own family.

What saves the reduction is that it never needs the cross-cell case: `scToLeafAdv` outputs a DIAGONAL
pair by construction (`scToLeafAdv_diagonal`), because the cell where two maps differ is ONE cell. So the
leaf floor is consumed exactly on the diagonal — precisely the property `cellLeafInjective` was claiming
for free, now paid for as a collision advantage. The `EffLeaf` class the keystone quantifies over may
therefore be taken to contain only diagonal finders without weakening the bound. -/

/-- **The extracted leaf finder is DIAGONAL** — it always outputs two `(cell, value)` pairs at the SAME
cell. So `stateCommit_equivocation_advantage_bound` consumes the leaf collision floor only on the
diagonal, which is exactly the surface `cellLeafInjective` claimed to cover — no cross-cell strength is
smuggled in, and the floor may be restricted to diagonal finders without weakening the keystone. -/
theorem scToLeafAdv_diagonal (F : StateCommitFamily) (A : Adversary (scEquivGame F)) (l : ℕ)
    (i : F.Inst l) : ((scToLeafAdv F A).run l i).1.1 = ((scToLeafAdv F A).run l i).2.1 := rfl

/-! ## §9 — `hEff*` DISCHARGED: the four legs' efficiency is a THEOREM at `Eff := IsPolyTime`.

§5's keystone carried FOUR bare `hEff*` parameters, one per extracted finder — the honest name for "the
reduction is efficient", undischarged because `FloorGames` §8 had no cost model.
`Dregg2.Crypto.CostAdversary` supplies one at COST-VECTOR resolution (intrinsic instructions +
per-oracle call counts, DERIVED from a deep-embedded program's syntax), and every one of the four horns
is a pure output reshaping of the equivocator's answer with the sampled instance passed through — i.e.
an `Adversary.postMap` — so `isPolyTime_postMap` turns all four parameters into CONSEQUENCES of ONE
hypothesis: that the equivocator itself is efficient.

The only per-site inputs left are the reshapers' DECLARED work `(cw, bw)` (a Lean `fun` has no runtime;
that number is CHARGED in the program's syntax) and each horn's OUTPUT SIZE, PROVED here:

  * the two NODE horns and the LEAF horn write a FIXED-WIDTH answer (two `ℤ×ℤ` pairs / two
    `(cell, value)` pairs), so their growth constants are `(0, 4)`;
  * the SPONGE horn writes the two frame lists, whose length is the untouched carrier's cardinality —
    bounded by the kernel's own `accounts` (`scFrameList_length_le`, `scCarrier` is a SUBSET), so its
    growth constants are `(1, 0)` against the game's own answer measure. Nothing here is asserted: the
    frame horn is the one horn that could have blown up, and it provably does not. -/

/-- **THE EQUIVOCATION GAME'S ANSWER ENCODING.** A forged pair of kernels costs, to write down, its two
account sets. Concrete on purpose: the size measure belongs to the GAME (`CostAdversary` design
commitment 4), and leaving it open would let a degenerate `sz := 0` make the frame horn's output free. -/
def scAnsSize (F : StateCommitFamily) : AnsSize (scEquivGame F) :=
  fun _ (p : RecordKernelState × RecordKernelState) => p.1.accounts.card + p.2.accounts.card

/-- **THE NODE COLLISION GAME'S ANSWER ENCODING** — the two claimed 2-to-1 input pairs. -/
def scNodeAnsSize (F : StateCommitFamily) : AnsSize (hashGame (scNodeFamily F)) :=
  fun _ (_ : (ℤ × ℤ) × (ℤ × ℤ)) => 4

/-- **THE SPONGE COLLISION GAME'S ANSWER ENCODING** — the two claimed absorbed leaf lists. -/
def scSpongeAnsSize (F : StateCommitFamily) : AnsSize (hashGame (scSpongeFamily F)) :=
  fun _ (p : List ℤ × List ℤ) => p.1.length + p.2.length

/-- **THE LEAF COLLISION GAME'S ANSWER ENCODING** — the two claimed `(cell, value)` pairs. -/
def scLeafAnsSize (F : StateCommitFamily) : AnsSize (hashGame (scLeafFamily F)) :=
  fun _ (_ : (CellId × Value) × (CellId × Value)) => 4

/-- **⚑ THE FRAME HORN DOES NOT BLOW UP ITS INPUT.** The sponge's absorbed list is one leaf per
UNTOUCHED cell, and the untouched carrier is `accounts \ {src, dst}` — a SUBSET of the kernel's own
account set. So the frame horn's output is bounded by the game's own answer measure, linearly with
slope `1`: the one horn whose output is not fixed-width is still size-linear, PROVED off `scCarrier`. -/
theorem scFrameList_length_le (F : StateCommitFamily) (l : ℕ) (i : F.Inst l)
    (k : RecordKernelState) : (scFrameList F l i k).length ≤ k.accounts.card := by
  simp only [scFrameList, List.length_map, Finset.length_sort]
  exact Finset.card_le_card (Finset.sdiff_subset)

/-- **⚑ ALL FOUR `hEff*` DISCHARGED — the re-grounded `StateCommit.cellDigest_binds_cells` with NO
floating efficiency parameter.** A state-commitment equivocator that is EFFICIENT at the game's own
answer encoding, put through the four horns of the partition walk, yields four collision finders that
are STILL efficient — so the node, sponge and leaf collision floors at `Eff := IsPolyTime` apply to
THEM, and the published cell-digest pins the whole cell map except with negligible probability.

The four `hEff*` parameters of §5 are PROVED here, not assumed. What remains supplied is each
reshaper's declared work `(cw, bw)`; no `PolyBoundedNat` overhead hypothesis is taken, because the
composed overhead's poly-ness is derived from the equivocator's own bound. -/
theorem stateCommit_equivocation_from_polyTime (F : StateCommitFamily)
    (A : Adversary (scEquivGame F)) (hA : IsPolyTime (scAnsSize F) A) (cw bw : ℕ)
    (hNode : HashCRHardQuant (scNodeFamily F) (IsPolyTime (scNodeAnsSize F)))
    (hSponge : HashCRHardQuant (scSpongeFamily F) (IsPolyTime (scSpongeAnsSize F)))
    (hLeaf : HashCRHardQuant (scLeafFamily F) (IsPolyTime (scLeafAnsSize F))) :
    Negl (gameAdv (scEquivGame F) A) := by
  have hOuter : IsPolyTime (scNodeAnsSize F) (scToOuterNodeAdv F A) := by
    poly_time (scAnsSize F) (scNodeAnsSize F)
      (fun l i (p : RecordKernelState × RecordKernelState) =>
        (scOuterPair F l i p.1, scOuterPair F l i p.2))
      cw bw 0 4 hA
    intro l i p
    show (4 : ℕ) ≤ 0 * (scAnsSize F l p) + 4
    omega
  have hMoved : IsPolyTime (scNodeAnsSize F) (scToMovedNodeAdv F A) := by
    poly_time (scAnsSize F) (scNodeAnsSize F)
      (fun l i (p : RecordKernelState × RecordKernelState) =>
        (scMovedPair F l i p.1.cell, scMovedPair F l i p.2.cell))
      cw bw 0 4 hA
    intro l i p
    show (4 : ℕ) ≤ 0 * (scAnsSize F l p) + 4
    omega
  have hSp : IsPolyTime (scSpongeAnsSize F) (scToSpongeAdv F A) := by
    poly_time (scAnsSize F) (scSpongeAnsSize F)
      (fun l i (p : RecordKernelState × RecordKernelState) =>
        (scFrameList F l i p.1, scFrameList F l i p.2))
      cw bw 1 0 hA
    intro l i p
    have h1 := scFrameList_length_le F l i p.1
    have h2 := scFrameList_length_le F l i p.2
    show (scFrameList F l i p.1).length + (scFrameList F l i p.2).length
      ≤ 1 * (p.1.accounts.card + p.2.accounts.card) + 0
    omega
  have hLf : IsPolyTime (scLeafAnsSize F) (scToLeafAdv F A) := by
    poly_time (scAnsSize F) (scLeafAnsSize F)
      (fun _ _ (p : RecordKernelState × RecordKernelState) =>
        ((diffCell p.1.cell p.2.cell, p.1.cell (diffCell p.1.cell p.2.cell)),
         (diffCell p.1.cell p.2.cell, p.2.cell (diffCell p.1.cell p.2.cell))))
      cw bw 0 4 hA
    intro l i p
    show (4 : ℕ) ≤ 0 * (scAnsSize F l p) + 4
    omega
  exact stateCommit_equivocation_advantage_bound F
    (IsPolyTime (scNodeAnsSize F)) (IsPolyTime (scSpongeAnsSize F)) (IsPolyTime (scLeafAnsSize F))
    A hOuter hMoved hSp hLf hNode hSponge hLeaf

/-- **THE LOG GAME'S ANSWER ENCODING** — the two claimed receipt chains. -/
def scLogAnsSize (F : LogCommitFamily) : AnsSize (hashGame (scLogFamily F)) :=
  fun _ (p : List Turn × List Turn) => p.1.length + p.2.length

/-- **⚑ THE LOG CONSUMER'S `hEff` DISCHARGED — and its honest shape stated plainly.** §5b's bound is the
floor applied to the equivocator ITSELF, because a receipt-chain equivocation IS definitionally a
collision of the log hash: there is no tree, hence no extractor and no reduction hop, and inventing one
would be theatre. What §9 changes is therefore exactly one thing, and it is the thing that was open: the
adversary class is no longer a floating `Eff` but the CONCRETE `IsPolyTime` at the game's own answer
encoding — a class proved non-empty (`scLogFloor_isPolyTime_inhabited`) and proved not to be `⊤`
(`CostAdversary.bruteForce_not_polyTime`), so the floor sits strictly between the two poles §5b prices. -/
theorem log_equivocation_from_polyTime (F : LogCommitFamily)
    (A : Adversary (hashGame (scLogFamily F))) (hA : IsPolyTime (scLogAnsSize F) A)
    (hLog : HashCRHardQuant (scLogFamily F) (IsPolyTime (scLogAnsSize F))) :
    Negl (gameAdv (hashGame (scLogFamily F)) A) :=
  log_equivocation_advantage_bound F (IsPolyTime (scLogAnsSize F)) A hA hLog

/-- **(TOOTH — the node floor's class is NOT EMPTY.)** -/
theorem scNodeFloor_isPolyTime_inhabited (F : StateCommitFamily) :
    IsPolyTime (scNodeAnsSize F)
      (idAdv (O := Unit) (Q := fun _ => Unit) (R := fun _ => Unit)
        (fun _ _ => (((0 : ℤ), (0 : ℤ)), ((0 : ℤ), (0 : ℤ))))).toAdversary :=
  isPolyTime_inhabited _ _ ⟨4, 0, fun _ _ => by simp [scNodeAnsSize]⟩

/-- **(TOOTH — the sponge floor's class is NOT EMPTY.)** -/
theorem scSpongeFloor_isPolyTime_inhabited (F : StateCommitFamily) :
    IsPolyTime (scSpongeAnsSize F)
      (idAdv (O := Unit) (Q := fun _ => Unit) (R := fun _ => Unit)
        (fun _ _ => (([] : List ℤ), ([] : List ℤ)))).toAdversary :=
  isPolyTime_inhabited _ _ ⟨0, 0, fun _ _ => by simp [scSpongeAnsSize]⟩

/-- **(TOOTH — the leaf floor's class is NOT EMPTY.)** -/
theorem scLeafFloor_isPolyTime_inhabited (F : StateCommitFamily) :
    IsPolyTime (scLeafAnsSize F)
      (idAdv (O := Unit) (Q := fun _ => Unit) (R := fun _ => Unit)
        (fun _ _ => (((0 : CellId), (default : Value)),
                     ((0 : CellId), (default : Value))))).toAdversary :=
  isPolyTime_inhabited _ _ ⟨4, 0, fun _ _ => by simp [scLeafAnsSize]⟩

/-- **(TOOTH — the log floor's class is NOT EMPTY.)** -/
theorem scLogFloor_isPolyTime_inhabited (F : LogCommitFamily) :
    IsPolyTime (scLogAnsSize F)
      (idAdv (O := Unit) (Q := fun _ => Unit) (R := fun _ => Unit)
        (fun _ _ => (([] : List Turn), ([] : List Turn)))).toAdversary :=
  isPolyTime_inhabited _ _ ⟨0, 0, fun _ _ => by simp [scLogAnsSize]⟩

#assert_all_clean [
  scFrameList_length_le,
  stateCommit_equivocation_from_polyTime,
  log_equivocation_from_polyTime,
  scNodeFloor_isPolyTime_inhabited,
  scSpongeFloor_isPolyTime_inhabited,
  scLeafFloor_isPolyTime_inhabited,
  scLogFloor_isPolyTime_inhabited
]

#assert_all_clean [
  finite_range_of_field_window,
  cellLeafInjective_false_of_finite_range,
  cellLeafInjective_false_babyBear,
  logHashInjective_false_of_finite_range,
  logHashInjective_false_babyBear,
  leafRealization_uninhabitable_babyBear,
  logRealization_uninhabitable_babyBear,
  winProb_le_add3_of_imp,
  winProb_le_add4_of_imp,
  scCellDigest_eq,
  scMovedDigest_eq,
  scFrameDigest_eq,
  scEquivGame_wins_iff,
  diffCell_spec,
  sc_claim_wins_imp,
  sc_wins_imp,
  sc_adv_le,
  stateCommit_equivocation_advantage_bound,
  the_repaired_bound_fires_on_the_right_floors,
  sc_leaf_floor_satisfiable_vacuously,
  sc_node_floor_satisfiable_vacuously,
  sc_sponge_floor_satisfiable_vacuously,
  sc_leaf_floor_top_false_of_compressing,
  sc_node_floor_top_false_of_compressing,
  sc_sponge_floor_top_false_of_compressing,
  scToLeafAdv_diagonal,
  scLogGame_wins_iff,
  log_equivocation_advantage_bound,
  scLogFamily_CR_of_logHashInjective,
  sc_log_floor_satisfiable_vacuously,
  sc_log_floor_top_false_of_compressing
]

end Dregg2.Circuit.StateCommitFloorRegrounded
