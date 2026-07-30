/-
# Dregg2.Circuit.Emit.PastaMsmSliced — the **FOUR-WAY CUT** of the terminal `⟨s, srs.g⟩` MSM,
emitted as AIR instances that each NAME THEIR OWN SLICE.

## Substrate, said out loud

**Lean-authored AIR.** Every constraint here is produced by a `def` returning
`List VmConstraint2`, and every theorem is about that ACTUALLY EMITTED list. Rust hand-writes no
constraint, no builder gadget and no `air_accepts` predicate: it parses the emitted descriptor,
fills trace CELLS, and runs the deployed prover. The row template is **not re-authored** — it is
`PastaMsmWindowed.rowGates ++ threadGates` verbatim, and `slicedRowDesc_extends_windowed` proves
the emitted list still has it as a PREFIX.

## Why the cut, and why four

`PastaIpaDeferral` §4b measured it. The discharge of `sg == ⟨s, srs.g⟩` is `4,227,200` RCB adds —
`2.016×` the deployed two-adicity ceiling `2^21` at every `N`, because amortisation moves the
per-block AVERAGE and does not shrink the single indivisible object. Cut in TWO it misses by
`16,512` rows; cut in THREE it clears but `3 ∤ 32768`, so the slices are ragged and
`PastaIpaFold.chunk_length` does not apply. **FOUR divides and clears**: `8,192` generators,
`1,056,896` rows — `50.4%` of the RAW rows and, once the trace is padded to a power of two,
**100% of the committed `2^21` domain** (§6, §7.4). The cut that leaves real headroom is EIGHT.

The deployed prover carries several AIR instances per proof and derives each one's `degree_bits`
from its own trace HEIGHT (`p3_batch_stark`'s `ProverData::from_instances`), so four instances
ride in one proof and heterogeneous heights are the ordinary case, not an extension.

## ⚑ The hole this file closes, and the correction it makes to how that hole was stated

A prior lane caught the shape of it on the 32-chunk kernel version: a re-sum of partials is a
GROUP SUM, so it forgets its order, and "every instance passed and they re-sum correctly" could be
green with the instances paired to the wrong slices.

**Read at the right resolution that framing is half right, and the half it gets wrong is the half
a guard would have been built against.** §3 settles it by exhibiting all three cases:

  * `permutation_is_harmless` — re-ORDERING correct partials really is harmless; `P 0 := ⟨slice 1⟩,
    P 1 := ⟨slice 0⟩` sums to the same total. So ORDER is *not* what must be pinned, and a guard
    sold as pinning it would be pinning the wrong thing.
  * `cross_pairing_breaks_the_sum` — the actual hazard is the PAIRING: slice `k`'s scalars against
    slice `j`'s generators. That is a genuinely different total (`21,430` against `43,210` on the
    exhibited witness) and is what a per-instance statement saying only "this is SOME partial"
    would admit.
  * `duplicated_slice_breaks_the_sum` — and so is covering one slice twice while another is never
    covered (`420` against `43,210`).

So what must be pinned is the PAIRING and the COVERAGE. `slicePartial` takes ONE index and uses it
for BOTH lists, so a cross-paired claim is not merely refused, it is **unstateable**; and
`slices_compose` consumes `∀ k < n, P k = slicePartial w k as ps`, so a doubled or uncovered slice
has no proof. §4 then puts the same bounds in the EMITTED OBJECT: the descriptor pins `lo` as a
literal and publishes `[lo, hi)` and the partial as public inputs.

## ⚑ The 29 emitted `piBinding`s, and what they force — §5c, §5d, §7.6

Until §5c existed this file emitted 29 `piBinding`s and proved only SHAPE facts about them
(`sMaxPi ≤ piCount`, in-bounds), while §5's two "publishes" theorems were stated on HAND-WRITTEN
constraints that nothing said were in the emitted list. `acceptB` is `List.all gateBodyEvalZero`
and returns `true` on every constructor that is not `.base (.gate _)`, so the row-local denotation
**cannot see a `piBinding` at all** — which is exactly how 29 gates sat un-forcing with every
theorem green.

§5c states the forcing over the ACTUALLY EMITTED list, and the answer is worth reading before
citing any of it: `pi_pins_refuse_no_trace` proves **not one of the 29 refuses a trace.** They are
publication, not checking. What they buy is `wire_is_the_declared_interval` (the declared interval
is on the wire, so the four-way tiling is checkable off the proofs) and
`published_partial_is_the_fold` (the 27 published limbs ARE the fold the emitted row template and
thread force) — the theorem that makes `slices_compose`'s `P k` a value rather than a name. §5d
exhibits both polarities on a whole trace, including the forgery no other gate here can see: an
untouched, row-locally accepted trace with a mis-published partial.

## Axiom hygiene

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/
`native_decide`. `#guard`s reduce in the kernel. Imports read-only. Import line:
`import Dregg2.Circuit.Emit.PastaMsmSliced`
-/
import Dregg2.Circuit.Emit.PastaMsmWindowed
import Dregg2.Circuit.Emit.PastaIpaFold

namespace Dregg2.Circuit.Emit.PastaMsmSliced

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2 (VmConstraint2 EffectVmDescriptor2 WindowExpr WindowConstraint)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.Emit.AirBuilder
open Dregg2.Circuit.Emit.PastaField (acceptB gateBodyEvalZero bumpAt)
open Dregg2.Circuit.Emit.PastaScalarMul (acceptB_prefix gateBodyEvalZero_cgH)
open Dregg2.Circuit.Emit.PastaIpaFold (msmN msmN_nil_left flatMap_chunks chunk_length)
open Dregg2.Circuit.Emit.PastaMsmWindowed (WTrace envOf cw ACCX)

set_option autoImplicit false

/-! ## §1 — THE SLICE, index-pinned on BOTH lists.

`sliceAt w k` cuts at `w · k` — the SAME `k` for the scalars and for the generators. That is the
anti-mispairing discipline, and it is structural rather than stated: there is no second index to
get wrong. `sliceLo`/`sliceHi` are the declared bounds the emitted descriptor carries (§4) and the
numbers a verifier reads off the proofs' public inputs. -/

/-- Slice `k` of width `w`: list indices `[w·k, w·k + w)`. -/
def sliceAt {α : Type} (w k : Nat) (l : List α) : List α := (l.drop (w * k)).take w

/-- The declared INCLUSIVE lower bound of slice `k`. -/
def sliceLo (w k : Nat) : Nat := w * k
/-- The declared EXCLUSIVE upper bound of slice `k`. -/
def sliceHi (w k : Nat) : Nat := w * k + w

/-- The declared bounds of every slice, in order — the list a verifier checks the proofs' public
inputs against. -/
def sliceBounds (w n : Nat) : List (Nat × Nat) :=
  (List.range n).map (fun k => (sliceLo w k, sliceHi w k))

/-- **`slices_partition`** — the `n` declared slices reassemble the list IN ORDER: nothing skipped,
nothing counted twice, no slice at the wrong offset. Via `PastaIpaFold.flatMap_chunks`, so no
`2^15`-element list equality is ever `decide`d. -/
theorem slices_partition {α : Type} (w n : Nat) (l : List α) (hl : l.length = w * n) :
    ((List.range n).flatMap (fun k => sliceAt w k l)) = l :=
  flatMap_chunks w n l hl

/-- **`slice_is_full`** — every slice below the end really has `w` entries, so a ragged tail cannot
hide inside a green partition. -/
theorem slice_is_full {α : Type} (w n k : Nat) (l : List α) (hl : l.length = w * n) (hk : k < n) :
    (sliceAt w k l).length = w := chunk_length w n k l hl hk

/-- **`slice_bounds_abut`** — slice `k` ends exactly where slice `k+1` begins. With
`slice_bounds_start` this is the interval-level tiling a verifier checks on the declared public
inputs. -/
theorem slice_bounds_abut (w k : Nat) : sliceHi w k = sliceLo w (k + 1) := by
  simp only [sliceHi, sliceLo, Nat.mul_succ]

/-- The first slice starts at 0. -/
theorem slice_bounds_start (w : Nat) : sliceLo w 0 = 0 := by simp [sliceLo]

/-- The last slice ends at the full length. -/
theorem slice_bounds_last (w m : Nat) : sliceHi w m = w * (m + 1) := by
  simp only [sliceHi, Nat.mul_succ]

/-- Slice `k` is exactly the elements at indices `[sliceLo w k, sliceHi w k)` — so the DECLARED
bounds and the CUT are visibly the same numbers, rather than two conventions that agree today. -/
theorem slice_is_its_declared_interval {α : Type} (w k : Nat) (l : List α) :
    sliceAt w k l = (l.drop (sliceLo w k)).take (sliceHi w k - sliceLo w k) := by
  simp [sliceAt, sliceLo, sliceHi]

#assert_axioms slices_partition
#assert_axioms slice_is_full
#assert_axioms slice_bounds_abut
#assert_axioms slice_bounds_start
#assert_axioms slice_bounds_last
#assert_axioms slice_is_its_declared_interval

/-! ## §2 — THE COMPOSITION, slice-count-independent.

`n` is universally quantified and occurs in the proofs only as an induction variable: the statement
at `n = 4` is the same theorem as at `n = 2` or `n = 32`. Over an arbitrary `AddCommGroup`, so
nothing here is about Pallas. -/

section Compose
variable {M : Type} [AddCommGroup M]

/-- **`slicePartial`** — the partial MSM instance `k` is responsible for. ⚑ `k` is the ONLY index
and it is used for BOTH lists, so "instance `k`'s partial against slice `j`" cannot be written
down. §3 shows that is the property doing the work, not the order of the re-sum. -/
def slicePartial (w k : Nat) (as : List Nat) (ps : List M) : M :=
  msmN (sliceAt w k as) (sliceAt w k ps)

/-- `⟨a ++ b, p ++ q⟩ = ⟨a, p⟩ + ⟨b, q⟩` when the first blocks line up — the `ℕ`-scalar twin of
`PastaIpaFold.msm_append`. -/
theorem msmN_append : ∀ (as : List Nat) (ps : List M) (bs : List Nat) (qs : List M),
    as.length = ps.length → msmN (as ++ bs) (ps ++ qs) = msmN as ps + msmN bs qs := by
  intro as
  induction as with
  | nil =>
    intro ps bs qs h
    have hp : ps = [] := List.eq_nil_of_length_eq_zero (by simpa using h.symm)
    subst hp
    simp [msmN_nil_left]
  | cons a rest ih =>
    intro ps bs qs h
    match ps with
    | [] => simp at h
    | P :: pr =>
      have hl : rest.length = pr.length := by simpa using h
      have hstep : msmN (a :: (rest ++ bs)) (P :: (pr ++ qs))
          = a • P + msmN (rest ++ bs) (pr ++ qs) := rfl
      have hhd : msmN (a :: rest) (P :: pr) = a • P + msmN rest pr := rfl
      simp only [List.cons_append, hstep, hhd, ih pr bs qs hl]
      abel

/-- Slice 0 is the head block. -/
theorem sliceAt_zero {α : Type} (w : Nat) (l : List α) : sliceAt w 0 l = l.take w := by
  simp [sliceAt]

/-- Slice `k+1` of a list is slice `k` of its tail past the first block. -/
theorem sliceAt_succ {α : Type} (w k : Nat) (l : List α) :
    sliceAt w (k + 1) l = sliceAt w k (l.drop w) := by
  have h : w * k + w = w + w * k := Nat.add_comm _ _
  simp only [sliceAt, List.drop_drop, Nat.mul_succ, h]

/-- **`msmN_slices`** — the whole MSM IS the sum of its `n` slice partials. By induction on `n`;
`w` and the lists are arbitrary. -/
theorem msmN_slices (w : Nat) : ∀ (n : Nat) (as : List Nat) (ps : List M),
    as.length = w * n → ps.length = w * n →
    msmN as ps = ((List.range n).map (fun k => slicePartial w k as ps)).sum := by
  intro n
  induction n with
  | zero =>
    intro as ps ha _
    have ha0 : as = [] := List.eq_nil_of_length_eq_zero (by simpa using ha)
    subst ha0
    simp [msmN_nil_left]
  | succ m ih =>
    intro as ps ha hp
    have haw : (as.take w).length = w := by rw [List.length_take, ha, Nat.mul_succ]; omega
    have hpw : (ps.take w).length = w := by rw [List.length_take, hp, Nat.mul_succ]; omega
    have had : (as.drop w).length = w * m := by rw [List.length_drop, ha, Nat.mul_succ]; omega
    have hpd : (ps.drop w).length = w * m := by rw [List.length_drop, hp, Nat.mul_succ]; omega
    have hmap : ((List.range m).map (fun k => slicePartial w k (as.drop w) (ps.drop w)))
        = ((List.range m).map (fun k => slicePartial w (k + 1) as ps)) := by
      apply List.map_congr_left
      intro k _
      simp only [slicePartial, sliceAt_succ]
    calc msmN as ps
        = msmN (as.take w ++ as.drop w) (ps.take w ++ ps.drop w) := by
            rw [List.take_append_drop, List.take_append_drop]
      _ = msmN (as.take w) (ps.take w) + msmN (as.drop w) (ps.drop w) :=
            msmN_append _ _ _ _ (by rw [haw, hpw])
      _ = slicePartial w 0 as ps
            + ((List.range m).map (fun k => slicePartial w (k + 1) as ps)).sum := by
            rw [ih (as.drop w) (ps.drop w) had hpd, hmap]
            simp only [slicePartial, sliceAt_zero]
      _ = ((List.range (m + 1)).map (fun k => slicePartial w k as ps)).sum := by
            rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
            simp [Function.comp_def]

/-- ⚑⚑ **`slices_compose`** — **the deliverable.** If each of `n` claimed partials IS its own
slice's partial — the SAME `k` on the scalars and on the generators — then their sum is the whole
MSM.

The hypothesis is what forbids a mispairing: `P k` must equal `slicePartial w k as ps`, and there
is no way to satisfy that with slice `j`'s partial (§3 exhibits a witness where the totals
genuinely differ). A slice covered twice or never covered has no proof of the hypothesis either,
because `k` ranges over `range n` exactly once each.

`n` occurs in no bound: this is the same theorem at `n = 4` and at `n = 32`. -/
theorem slices_compose (w n : Nat) (as : List Nat) (ps : List M) (P : Nat → M)
    (ha : as.length = w * n) (hp : ps.length = w * n)
    (hP : ∀ k, k < n → P k = slicePartial w k as ps) :
    ((List.range n).map P).sum = msmN as ps := by
  rw [msmN_slices w n as ps ha hp]
  congr 1
  apply List.map_congr_left
  intro k hk
  exact hP k (List.mem_range.mp hk)

end Compose

#assert_axioms msmN_append
#assert_axioms sliceAt_zero
#assert_axioms sliceAt_succ
#assert_axioms msmN_slices
#assert_axioms slices_compose

/-! ## §3 — ⚑ THE MISPAIRING TEETH: what actually has to be pinned, exhibited rather than asserted.

Three concrete witnesses over `ℤ`, all reducing in the kernel. `as = [1,2,3,4]`,
`ps = [10,100,1000,10000]`, `w = 2`, `n = 2`, so the honest total is `43,210` and the two slice
partials are `210` and `43,000`. -/

section Teeth

/-- The exhibited scalars. -/
def katA : List Nat := [1, 2, 3, 4]
/-- The exhibited "generators" — `ℤ` as an `AddCommGroup`, because the hazard is group-theoretic
and has nothing to do with Pallas. -/
def katG : List ℤ := [10, 100, 1000, 10000]

/-- The honest total. -/
theorem kat_total : msmN katA katG = 43210 := by decide

/-- The two honest slice partials. -/
theorem kat_partials :
    slicePartial 2 0 katA katG = 210 ∧ slicePartial 2 1 katA katG = 43000 := by
  constructor <;> decide

/-- The honest re-sum is the total — `slices_compose` at this instance, kernel-checked. -/
theorem kat_resum : slicePartial 2 0 katA katG + slicePartial 2 1 katA katG = msmN katA katG := by
  decide

/-- ⚑ **`permutation_is_harmless`** — re-ORDERING correct partials changes nothing. So "the re-sum
is order-insensitive" is TRUE, and it is therefore NOT the property a guard should be sold as
pinning. Stated so the next reader does not build the wrong guard. -/
theorem permutation_is_harmless :
    slicePartial 2 1 katA katG + slicePartial 2 0 katA katG = msmN katA katG := by decide

/-- ⚑⚑ **`cross_pairing_breaks_the_sum`** — THE hazard, and it is not order. Pairing slice 0's
scalars with slice 1's generators (and vice versa) gives `21,430`, not `43,210`. A per-instance
statement saying only "this accumulator is SOME partial" would accept exactly this. -/
theorem cross_pairing_breaks_the_sum :
    msmN (sliceAt 2 0 katA) (sliceAt 2 1 katG) + msmN (sliceAt 2 1 katA) (sliceAt 2 0 katG)
      ≠ msmN katA katG := by decide

/-- The cross-paired total, named so the gap is a number rather than an inequality. -/
theorem cross_pairing_total :
    msmN (sliceAt 2 0 katA) (sliceAt 2 1 katG) + msmN (sliceAt 2 1 katA) (sliceAt 2 0 katG)
      = 21430 := by decide

/-- ⚑ **`duplicated_slice_breaks_the_sum`** — covering slice 0 twice while slice 1 is never covered
gives `420`. This is what `∀ k < n` in `slices_compose` forbids. -/
theorem duplicated_slice_breaks_the_sum :
    slicePartial 2 0 katA katG + slicePartial 2 0 katA katG ≠ msmN katA katG := by decide

#guard msmN katA katG == 43210
#guard slicePartial 2 0 katA katG == 210
#guard slicePartial 2 1 katA katG == 43000
#guard decide (msmN (sliceAt 2 0 katA) (sliceAt 2 1 katG)
                 + msmN (sliceAt 2 1 katA) (sliceAt 2 0 katG) ≠ msmN katA katG)

#assert_axioms kat_total
#assert_axioms kat_partials
#assert_axioms kat_resum
#assert_axioms permutation_is_harmless
#assert_axioms cross_pairing_breaks_the_sum
#assert_axioms cross_pairing_total
#assert_axioms duplicated_slice_breaks_the_sum

end Teeth

/-! ## §4 — THE EMITTED OBJECT: one instance per slice, each NAMING ITS OWN SLICE.

The row template is `PastaMsmWindowed`'s, unchanged and not re-authored. What this file adds is two
columns and the constraints that make the emitted descriptor say WHICH slice it is:

  * `LO` (col 525) and `HI` (col 526), held CONSTANT down the trace by two `windowGate`s, so a
    trace cannot change its declared slice halfway through;
  * `LO = lo` as a LITERAL in the emitted gate — instance `k`'s descriptor is textually a different
    object from instance `j`'s, so running slice 3's descriptor and calling it slice 0 is not a
    witness question at all;
  * `HI − LO = w` as a literal, so the declared interval has the declared WIDTH;
  * `LO`/`HI` bound to public inputs 0 and 1 at the FIRST row, so the bounds are on the wire and a
    verifier reads them off the proof rather than off the prover's word;
  * the final accumulator's 27 limb columns bound to public inputs 2..28 at the LAST row, so
    instance `k` DECLARES its partial. Without that the partials are not even named and
    `slices_compose`'s `P` has nothing to be instantiated at. -/

/-- The slice's declared inclusive lower bound (column). -/
def LO : Nat := 525
/-- The slice's declared exclusive upper bound (column). -/
def HI : Nat := 526
/-- The sliced row template's width: `PastaMsmWindowed.W = 525` plus the two declaration columns. -/
def WS : Nat := 527

/-- Public-input index of the declared lower bound. -/
def PI_LO : Nat := 0
/-- Public-input index of the declared upper bound. -/
def PI_HI : Nat := 1
/-- First public-input index of the declared final accumulator (27 limb columns follow). -/
def PI_OUT : Nat := 2
/-- Public inputs an instance carries: `lo`, `hi`, and 27 accumulator limbs. -/
def PI_COUNT : Nat := 29

/-- `LO − lo` — the LITERAL slice pin. The offset is baked into the emitted constraint, so the
descriptor itself names the slice. -/
def sliceLoGate (lo : Nat) : VmConstraint2 := cgH ((Head.lin 1 LO).addConst (-(lo : ℤ)))

/-- `HI − LO − w` — the declared interval has the declared width. -/
def sliceWidthGate (w : Nat) : VmConstraint2 :=
  cgH (((Head.lin 1 HI).append ((Head.lin 1 LO).scale (-1))).addConst (-(w : ℤ)))

/-- `nxt LO − loc LO` — the declared slice cannot change down the trace.

⚠ **What this gate buys is ONE ROW, and it is not the row an earlier revision of this comment
claimed.** That revision said "without this a prover could declare slice 0 at the first row, where
the PI binding looks, and compute slice 3 on every row after it." `sliceLoGate` is a per-row
`LO − lo = 0` LITERAL, which under the deployed `when_transition()` semantics fires on rows
`0 … H−2` — so that forgery was never available. `declConst_of_literal` (§5c.4) proves the
constancy is already implied wherever the literal fires on both rows of the window; what these two
gates actually force is the LAST row's `LO`/`HI`, which no gate and no public input reads. §7.7. -/
def loConstGate : VmConstraint2 := cw (.add (.nxt LO) (.mul (.const (-1)) (.loc LO)))
/-- `nxt HI − loc HI`. -/
def hiConstGate : VmConstraint2 := cw (.add (.nxt HI) (.mul (.const (-1)) (.loc HI)))

/-- The declared bounds, on the wire: the first row's `LO`/`HI` ARE public inputs 0 and 1. -/
def sliceBoundPiGates : List VmConstraint2 :=
  [ .base (.piBinding .first LO PI_LO), .base (.piBinding .first HI PI_HI) ]

/-- The declared PARTIAL, on the wire: the last row's 27 accumulator limb columns are public
inputs 2..28. `PastaMsmWindowed`'s thread constraint fires on the window ENDING at the last row,
so that row's accumulator is the forced final value rather than a free cell. -/
def outPiGates : List VmConstraint2 :=
  (List.range 27).map (fun i => .base (.piBinding .last (ACCX + i) (PI_OUT + i)))

/-- ⚑ **The slice declaration** — four gates plus 2 + 27 public-input bindings. -/
def sliceDeclGates (lo w : Nat) : List VmConstraint2 :=
  [ sliceLoGate lo, sliceWidthGate w, loConstGate, hiConstGate ]
    ++ sliceBoundPiGates ++ outPiGates

/-- ⚑ **The sliced descriptor for slice `k` of `n`, at width `w`.** The row template is
`PastaMsmWindowed`'s two lists, unchanged; `sliceDeclGates` is appended. -/
def slicedRowDesc (n k w : Nat) : EffectVmDescriptor2 :=
  { name        := "dregg-pasta-rcb-sg-slice-" ++ toString k ++ "-of-" ++ toString n ++ "::v1"
  , traceWidth  := WS
  , piCount     := PI_COUNT
  , tables      := []
  , constraints := Dregg2.Circuit.Emit.PastaMsmWindowed.rowGates
                     ++ Dregg2.Circuit.Emit.PastaMsmWindowed.threadGates
                     ++ sliceDeclGates (sliceLo w k) w
  , hashSites   := []
  , ranges      := [] }

/-- ⚑ **`slicedRowDesc_extends_windowed`** — the emitted list still has the WINDOWED row template
as a PREFIX. This is the theorem that says the layout was REUSED, not re-authored:
`PastaMsmWindowed`'s 45 constraints are present, in order, unmodified. -/
theorem slicedRowDesc_extends_windowed (n k w : Nat) :
    Dregg2.Circuit.Emit.PastaMsmWindowed.windowedRowDesc.constraints
      <+: (slicedRowDesc n k w).constraints :=
  ⟨sliceDeclGates (sliceLo w k) w, by
    simp [slicedRowDesc, Dregg2.Circuit.Emit.PastaMsmWindowed.windowedRowDesc,
      List.append_assoc]⟩

/-- The emitted constraint count: 45 from the windowed template, 4 declaration gates, 2 bound
bindings, 27 accumulator bindings. Still a CONSTANT — independent of the slice width and of the
row count. -/
theorem slicedRowDesc_constraints_length (n k w : Nat) :
    (slicedRowDesc n k w).constraints.length = 78 := rfl

/-! ### §4b — the deployed checker's OWN predicates, discharged in the kernel.

`circuit/src/descriptor_ir2.rs` refuses a descriptor whose constraint addresses a column
`>= trace_width` (the `chk` closure) or whose `pi_binding` names a `pi_index >= public_input_count`
(`:1581`). `PastaMsmWindowed.cMaxVar` returns `0` on the `piBinding` arm — correct for a file that
emits none, and a SILENT HOLE for one that does — so both predicates are re-decided here over a
`maxVar` that covers the arms this file actually emits. -/

/-- The largest column index a constraint addresses, over the arms THIS file emits — including the
`piBinding` arm `PastaMsmWindowed.cMaxVar` does not reach. -/
def sMaxVar : VmConstraint2 → Nat
  | .base (.gate e)            => Dregg2.Circuit.Emit.PastaMsmWindowed.eMaxVar e
  | .base (.boundary _ e)      => Dregg2.Circuit.Emit.PastaMsmWindowed.eMaxVar e
  | .base (.piBinding _ col _) => col + 1
  | .windowGate w              => Dregg2.Circuit.Emit.PastaMsmWindowed.wMaxVar w.body
  | _                          => 0

/-- The public-input index a constraint addresses (0 when it names none). -/
def sMaxPi : VmConstraint2 → Nat
  | .base (.piBinding _ _ k) => k + 1
  | _                        => 0

set_option maxRecDepth 40000 in
/-- ⚑ **`slicedRowDesc_columns_in_bounds`** — EVERY column EVERY emitted constraint addresses is
`≤ traceWidth`, decided in the kernel over the emitted list. This is `descriptor_ir2.rs`'s `chk`
closure, and it covers the `piBinding` columns the windowed file's own bound check cannot see. -/
theorem slicedRowDesc_columns_in_bounds :
    (slicedRowDesc 4 0 8192).constraints.all
        (fun c => decide (sMaxVar c ≤ (slicedRowDesc 4 0 8192).traceWidth)) = true := by decide

set_option maxRecDepth 40000 in
/-- ⚑ **`slicedRowDesc_pi_indices_in_bounds`** — every `pi_binding` names a public input the
descriptor declares. This is `descriptor_ir2.rs:1581`. -/
theorem slicedRowDesc_pi_indices_in_bounds :
    (slicedRowDesc 4 0 8192).constraints.all
        (fun c => decide (sMaxPi c ≤ (slicedRowDesc 4 0 8192).piCount)) = true := by decide

#guard (slicedRowDesc 4 0 8192).traceWidth == 527
#guard (slicedRowDesc 4 0 8192).piCount == 29
#guard (slicedRowDesc 4 0 8192).constraints.length == 78
#guard (slicedRowDesc 4 2 8192).name == "dregg-pasta-rcb-sg-slice-2-of-4::v1"

#assert_axioms slicedRowDesc_extends_windowed
#assert_axioms slicedRowDesc_constraints_length
#assert_axioms slicedRowDesc_columns_in_bounds
#assert_axioms slicedRowDesc_pi_indices_in_bounds

/-! ## §5 — THE FORCING: the emitted declaration constraints BITE.

Two separate denotations, because the deployed AIR treats the families differently and one
predicate would blur them. The literal pins are `.gate`s and land in `acceptB` (the ℤ model every
`Pasta*` rung uses); the constancy windows and the PI bindings are not `.gate`s, so they are stated
against `WindowExpr.eval` and `VmConstraint.holdsVm` directly. -/

/-- ⚑ **`sliceDecl_forces_bounds`** — a row satisfying the emitted LITERAL pins carries exactly the
declared interval: `LO = lo` and `HI = lo + w`. The offset and the width are in the emitted
constraint, so this holds for every accepted row of instance `k` and for no row of instance `j`. -/
theorem sliceDecl_forces_bounds (lo w : Nat) (a : Assignment)
    (h : acceptB (sliceDeclGates lo w) a = true) :
    a LO = (lo : ℤ) ∧ a HI = (lo : ℤ) + (w : ℤ) := by
  have hpref : acceptB [sliceLoGate lo, sliceWidthGate w, loConstGate, hiConstGate] a = true :=
    acceptB_prefix _ _ a (by simpa [sliceDeclGates, List.append_assoc] using h)
  simp only [acceptB, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    sliceLoGate, sliceWidthGate, gateBodyEvalZero_cgH] at hpref
  obtain ⟨g1, g2, _, _⟩ := hpref
  have e1 : a LO = (lo : ℤ) := by
    have hd := of_decide_eq_true g1
    simp only [evalH_lin, evalH_addConst] at hd
    linarith
  refine ⟨e1, ?_⟩
  have hd := of_decide_eq_true g2
  simp only [evalH_lin, evalH_append, evalH_scale, evalH_addConst] at hd
  linarith

/-- The content of the two emitted constancy windows. -/
def DeclConstant (T : WTrace) (i : Nat) : Prop :=
  T (i + 1) LO = T i LO ∧ T (i + 1) HI = T i HI

/-- Every emitted declaration `windowGate` body vanishes on the window at row `i`. -/
def DeclWindowAccepted (lo w : Nat) (T : WTrace) (i : Nat) : Prop :=
  ∀ wc : WindowConstraint, VmConstraint2.windowGate wc ∈ sliceDeclGates lo w →
    wc.body.eval (envOf T i) = 0

/-- ⚑ **`sliceDecl_forces_constant`** — the declared slice cannot change down the trace.

⚠ Read `loConstGate`'s own doc and §7.7 before citing this as a defence: `sliceLoGate`'s literal
already pins `LO` on every row the deployed `when_transition()` arm fires on, so what this theorem
adds over the row-local pins is the LAST row. `declConst_of_literal` (§5c.4) is the statement of
exactly that. -/
theorem sliceDecl_forces_constant (lo w : Nat) (T : WTrace) (i : Nat)
    (h : DeclWindowAccepted lo w T i) : DeclConstant T i := by
  constructor
  · have hw := h ⟨.add (.nxt LO) (.mul (.const (-1)) (.loc LO)), true⟩
      (by simp [sliceDeclGates, loConstGate, cw])
    simp only [WindowExpr.eval, envOf] at hw
    linarith
  · have hw := h ⟨.add (.nxt HI) (.mul (.const (-1)) (.loc HI)), true⟩
      (by simp [sliceDeclGates, hiConstGate, cw])
    simp only [WindowExpr.eval, envOf] at hw
    linarith

/-- ⚑ **`sliceBoundPi_publishes`** — the emitted `piBinding`s put the declared bounds ON THE WIRE:
at the first row the `LO`/`HI` columns ARE public inputs 0 and 1, in the deployed denotation
(`holdsVm`, mod BabyBear). This is what lets a verifier check the four declared intervals tile
`[0, w·n)` — `slice_bounds_abut` — from the proof rather than from the prover's word. -/
theorem sliceBoundPi_publishes (env : VmRowEnv) (isLast : Bool)
    (hlo : VmConstraint.holdsVm env true isLast (.piBinding .first LO PI_LO))
    (hhi : VmConstraint.holdsVm env true isLast (.piBinding .first HI PI_HI)) :
    env.loc LO ≡ env.pub PI_LO [ZMOD 2013265921]
      ∧ env.loc HI ≡ env.pub PI_HI [ZMOD 2013265921] := ⟨hlo rfl, hhi rfl⟩

/-- ⚑ **`outPi_publishes`** — likewise for the declared PARTIAL: at the LAST row every accumulator
limb column IS its public input. This is the binding that makes `slices_compose`'s `P k` a value on
the wire instead of a claim in prose. -/
theorem outPi_publishes (env : VmRowEnv) (isFirst : Bool) (i : Nat)
    (h : VmConstraint.holdsVm env isFirst true (.piBinding .last (ACCX + i) (PI_OUT + i))) :
    env.loc (ACCX + i) ≡ env.pub (PI_OUT + i) [ZMOD 2013265921] := h rfl

#assert_axioms sliceDecl_forces_bounds
#assert_axioms sliceDecl_forces_constant
#assert_axioms sliceBoundPi_publishes
#assert_axioms outPi_publishes

/-! ### §5b — ⚑ the declaration constraints are SATISFIABLE and REFUTABLE.

A forcing theorem whose hypothesis nothing satisfies is TRUE AND EMPTY. Exhibited here in the
kernel, over the actually-emitted `sliceDeclGates`. -/

/-- A row carrying the declared bounds. -/
def declAsg (lo w : Nat) : Assignment :=
  fun col => if col = LO then (lo : ℤ) else if col = HI then (lo : ℤ) + (w : ℤ) else 0

-- SATISFIABLE — the honest declaration of slice 0 of 4 at width 8,192.
#guard acceptB (sliceDeclGates 0 8192) (declAsg 0 8192) == true
-- SATISFIABLE — slice 2 of 4.
#guard acceptB (sliceDeclGates 16384 8192) (declAsg 16384 8192) == true
-- ⚑ REFUTABLE — slice 2's declaration under slice 0's emitted gates is REFUSED. The literal pin
-- biting: the descriptor names its slice, so instance 0 cannot carry slice 2's bounds.
#guard acceptB (sliceDeclGates 0 8192) (declAsg 16384 8192) == false
-- ⚑ REFUTABLE — the right offset with the WRONG width is REFUSED.
#guard acceptB (sliceDeclGates 0 8192) (declAsg 0 4096) == false
-- REFUTABLE — a bumped bound column is REFUSED, either one.
#guard acceptB (sliceDeclGates 0 8192) (bumpAt (declAsg 0 8192) LO) == false
#guard acceptB (sliceDeclGates 0 8192) (bumpAt (declAsg 0 8192) HI) == false

/-! ## §5c — ⚑⚑ THE 29 EMITTED `piBinding`s, AND WHAT THEY FORCE.

**Everything §5 says about the pins is said about a HAND-WRITTEN constraint.**
`sliceBoundPi_publishes` and `outPi_publishes` take a `.piBinding` as a HYPOTHESIS and unfold
`holdsVm` on it; neither says the EMITTED list contains that constraint, and both would still be
true if `sliceDeclGates` emitted no `piBinding` at all. Everything else this file said about the
29 was SHAPE — `sMaxPi ≤ piCount`, a bound check that is satisfied by a pin binding nothing.

⚑ **And the row-local denotation cannot repair that, structurally.** `acceptB` is
`List.all gateBodyEvalZero`, and `gateBodyEvalZero` returns `true` on every constructor that is not
`.base (.gate _)` — so it **cannot see a `.piBinding` at all**. Proving over `acceptB` can never
reach one. That is precisely why 29 gates could sit emitted, with nothing saying what they force,
while every theorem in this file stayed green.

This section is `PastaMsmScalarDerive` §4e's shape one rung down, and no technique is invented: a
denotation over the ACTUALLY EMITTED list, an INVERSION saying which pins that list contains and
which it does not, the forcing, and a decidable twin §5d exhibits both polarities of.

⚑ **Read §5c.4 for the answer to "what do the 29 force".** `pi_pins_refuse_no_trace` proves they
refuse NO TRACE — every trace has a satisfying public-input vector — so none of the 29 constrains
the prover's trace at all. Their whole content is on the WIRE, and that is what a publication gate
is for; the file now says which of its gates are which, rather than leaving a reader to assume a
`piBinding` is a check. -/

section WirePins

open Dregg2.Circuit.Emit.PastaMsmWindowed
  (ACCY ACCZ SRCX SRCY SRCZ BIT rowGates ThreadAccepted threadGates_force
   windowedRef windowedRows_forces fpVal_as_sum)
open Dregg2.Circuit.Emit.PastaScalarMul (PtP PointIsZ)
open Dregg2.Circuit.Emit.PastaField (fpVal numLimbs bumpAt)
open Dregg2.Circuit.Emit.PastaMsmLayouts (bitAt)

/-! ### §5c.1 — the pins the emitted list ACTUALLY contains. -/

/-- The `(row, column, public-input index)` triples the declaration binds, EXTRACTED from the
emitted list rather than restated beside it. -/
def declPins (lo w : Nat) : List (Dregg2.Circuit.Emit.EffectVmEmit.VmRow × Nat × Nat) :=
  (sliceDeclGates lo w).filterMap (fun c => match c with
    | .base (.piBinding r col k) => some (r, col, k)
    | _                          => none)

/-- ⚑ **`declPins_eq`** — the emitted pins, in emission order and at EVERY `(lo, w)`: the two
declared bounds on the FIRST row, then the 27 accumulator limbs on the LAST. The declaration gates
contribute none, whatever the slice offset and width are. -/
theorem declPins_eq (lo w : Nat) :
    declPins lo w
      = (.first, LO, PI_LO) :: (.first, HI, PI_HI)
          :: (List.range 27).map (fun i => (Dregg2.Circuit.Emit.EffectVmEmit.VmRow.last,
                ACCX + i, PI_OUT + i)) := by
  simp [declPins, sliceDeclGates, sliceBoundPiGates, outPiGates, sliceLoGate, sliceWidthGate,
    loConstGate, hiConstGate, cgH, cg, cw, List.filterMap_map]

/-- A pin in the emitted list is a pin in `declPins` — the bridge that makes every inversion below
a statement about the EMITTED object. -/
theorem mem_declPins (lo w : Nat) (r : Dregg2.Circuit.Emit.EffectVmEmit.VmRow) (col k : Nat)
    (h : VmConstraint2.base (.piBinding r col k) ∈ sliceDeclGates lo w) :
    (r, col, k) ∈ declPins lo w :=
  List.mem_filterMap.mpr ⟨_, h, rfl⟩

/-- ⚑ **`piFirst_is_a_bound`** — a `.piBinding .first` in the emitted list is one of the two
DECLARED BOUNDS and nothing else. There is no third first-row pin, at any `(lo, w)`. -/
theorem piFirst_is_a_bound (lo w col k : Nat)
    (h : VmConstraint2.base (.piBinding .first col k) ∈ sliceDeclGates lo w) :
    (col = LO ∧ k = PI_LO) ∨ (col = HI ∧ k = PI_HI) := by
  have hm := mem_declPins lo w .first col k h
  rw [declPins_eq] at hm
  simp only [List.mem_cons, List.mem_map, List.mem_range, Prod.mk.injEq] at hm
  rcases hm with ⟨-, hc, hk⟩ | ⟨-, hc, hk⟩ | ⟨i, -, hi⟩
  · exact Or.inl ⟨hc, hk⟩
  · exact Or.inr ⟨hc, hk⟩
  · exact absurd hi.1 (by simp)

/-- ⚑ **`piLast_is_an_acc_limb`** — a `.piBinding .last` in the emitted list is one of the 27
ACCUMULATOR LIMBS, at its own public input. No last-row pin names anything else. -/
theorem piLast_is_an_acc_limb (lo w col k : Nat)
    (h : VmConstraint2.base (.piBinding .last col k) ∈ sliceDeclGates lo w) :
    ∃ i, i < 27 ∧ col = ACCX + i ∧ k = PI_OUT + i := by
  have hm := mem_declPins lo w .last col k h
  rw [declPins_eq] at hm
  simp only [List.mem_cons, List.mem_map, List.mem_range, Prod.mk.injEq] at hm
  rcases hm with ⟨hr, -, -⟩ | ⟨hr, -, -⟩ | ⟨i, hi, hr, hc, hk⟩
  · exact absurd hr (by simp)
  · exact absurd hr (by simp)
  · exact ⟨i, hi, hc.symm, hk.symm⟩

/-- The declared bound pins are IN the emitted list. -/
theorem mem_loPi (lo w : Nat) :
    VmConstraint2.base (.piBinding .first LO PI_LO) ∈ sliceDeclGates lo w := by
  simp [sliceDeclGates, sliceBoundPiGates]

theorem mem_hiPi (lo w : Nat) :
    VmConstraint2.base (.piBinding .first HI PI_HI) ∈ sliceDeclGates lo w := by
  simp [sliceDeclGates, sliceBoundPiGates]

/-- …and so is accumulator limb `i`'s pin, for each of the 27. -/
theorem mem_outPi (lo w i : Nat) (hi : i < 27) :
    VmConstraint2.base (.piBinding .last (ACCX + i) (PI_OUT + i)) ∈ sliceDeclGates lo w :=
  List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)

/-- ⚑ **`declPins_indices`** — the emitted pins name public inputs `0, 1, …, 28`: EVERY declared
public input is bound, and no two pins name the same one. A declared-but-unbound public input is a
free wire a verifier reads as meaningful; a double-bound one silently equates two columns.
`slicedRowDesc_pi_indices_in_bounds` checks neither — it only checks no index is too large. -/
theorem declPins_indices (lo w : Nat) :
    (declPins lo w).map (fun p => p.2.2) = List.range PI_COUNT := by
  rw [declPins_eq]; rfl

theorem declPins_length (lo w : Nat) : (declPins lo w).length = PI_COUNT := by
  rw [declPins_eq]; rfl

theorem declPins_indices_nodup (lo w : Nat) :
    ((declPins lo w).map (fun p => p.2.2)).Nodup := by
  rw [declPins_indices]; exact List.nodup_range

/-- …and the COLUMNS the pins name are distinct too, so no two public inputs are two names for one
cell. -/
theorem declPins_cols_nodup (lo w : Nat) :
    ((declPins lo w).map (fun p => p.2.1)).Nodup := by
  rw [declPins_eq]; decide

/-! ### §5c.2 — the denotation, over the emitted list, at the DEPLOYED row tags. -/

/-- The content of the emitted `.piBinding .first` pins against the DECLARED public-input vector
`pv`, read at row 0 — where `descriptor_ir2.rs`'s `builder.is_first_row()` selector puts them.

⚠ `pv` is a SEPARATE argument and NOT `envOf`'s `pub` field: `PastaMsmWindowed.envOf` sets
`pub := T 0`, the trace's first row, while the deployed `envAt` sets `pub := t.pub`. No
`WindowExpr` reads `pub` at all so the discrepancy is inert for the window gates, but a PI pin is
exactly the constraint that WOULD read it, so it is given the deployed reading. -/
def SliceFirstPiAccepted (lo w : Nat) (T : WTrace) (pv : Nat → ℤ) : Prop :=
  ∀ col k : Nat, VmConstraint2.base (.piBinding .first col k) ∈ sliceDeclGates lo w →
    T 0 col = pv k

/-- …and of the emitted `.piBinding .last` pins, read at the trace's LAST ROW `L`
(`builder.is_last_row()`). `L` is an argument rather than a derived `H − 1`, so no theorem below
carries a row count in a bound. -/
def SliceLastPiAccepted (lo w L : Nat) (T : WTrace) (pv : Nat → ℤ) : Prop :=
  ∀ col k : Nat, VmConstraint2.base (.piBinding .last col k) ∈ sliceDeclGates lo w →
    T L col = pv k

/-- ⚑ **The DECIDABLE twin of the whole declaration** — the literal pins, the constancy windows and
BOTH families of PI pin, over the same emitted list. This is `acceptB`'s counterpart for the three
constructors `acceptB` cannot see, and §5d decides it in the kernel, which is what makes the
tampers there MEASUREMENTS rather than assertions.

⚠ The `match` ends in `_ => true`. That is correct for the three constructors `sliceDeclGates`
emits today and it is FAIL-OPEN by construction — §7.8. -/
def sliceDeclAcceptB (lo w L i : Nat) (T : WTrace) (pv : Nat → ℤ) : Bool :=
  (sliceDeclGates lo w).all (fun c => match c with
    | .base (.gate e)                 => decide (e.eval (T i) = 0)
    | .base (.piBinding .first col k) => decide (T 0 col = pv k)
    | .base (.piBinding .last col k)  => decide (T L col = pv k)
    | .windowGate wc                  => decide (wc.body.eval (envOf T i) = 0)
    | _                               => true)

/-- ⚑ **`sliceDeclAccept_forces`** — the decidable twin IMPLIES the row-local denotation, both PI
predicates and the window predicate, so a kernel `#guard` on it is evidence about the theorems
below and not about a separate object. -/
theorem sliceDeclAccept_forces (lo w L i : Nat) (T : WTrace) (pv : Nat → ℤ)
    (h : sliceDeclAcceptB lo w L i T pv = true) :
    acceptB (sliceDeclGates lo w) (T i) = true
      ∧ SliceFirstPiAccepted lo w T pv
      ∧ SliceLastPiAccepted lo w L T pv
      ∧ DeclWindowAccepted lo w T i := by
  rw [sliceDeclAcceptB, List.all_eq_true] at h
  refine ⟨?_, fun col k hk => of_decide_eq_true (h _ hk),
             fun col k hk => of_decide_eq_true (h _ hk),
             fun wc hw => of_decide_eq_true (h _ hw)⟩
  rw [acceptB, List.all_eq_true]
  intro c hc
  have hcc := h c hc
  cases c with
  | base b =>
    cases b with
    | gate e => simpa [gateBodyEvalZero] using hcc
    | transition _ _ => rfl
    | boundary _ _ => rfl
    | piBinding _ _ _ => rfl
  | lookup _ => rfl
  | memOp _ => rfl
  | mapOp _ => rfl
  | umemOp _ => rfl
  | proofBind _ => rfl
  | windowGate _ => rfl

/-! ### §5c.3 — the forcing: what the 29 put ON THE WIRE. -/

theorem loPi_forces (lo w : Nat) (T : WTrace) (pv : Nat → ℤ)
    (h : SliceFirstPiAccepted lo w T pv) : T 0 LO = pv PI_LO := h _ _ (mem_loPi lo w)

theorem hiPi_forces (lo w : Nat) (T : WTrace) (pv : Nat → ℤ)
    (h : SliceFirstPiAccepted lo w T pv) : T 0 HI = pv PI_HI := h _ _ (mem_hiPi lo w)

theorem outPi_forces (lo w L : Nat) (T : WTrace) (pv : Nat → ℤ) (i : Nat) (hi : i < 27)
    (h : SliceLastPiAccepted lo w L T pv) : T L (ACCX + i) = pv (PI_OUT + i) :=
  h _ _ (mem_outPi lo w i hi)

/-- ⚑⚑ **`wire_is_the_declared_interval`** — the two emitted bound pins put the DECLARED INTERVAL
on the wire: public inputs 0 and 1 ARE `lo` and `lo + w`, the literals baked into the emitted gate.
This is what lets a verifier check `slice_bounds_abut` — that the four declared intervals tile
`[0, w·n)` — from the PROOF rather than from the prover's word.

⚑ Read the conclusion: it is entirely about `pv`. The TRACE side (`T 0 LO = lo`) comes from
`sliceLoGate`, a row-local literal that `acceptB` already sees; the pins add nothing to it. §7.6. -/
theorem wire_is_the_declared_interval (lo w : Nat) (T : WTrace) (pv : Nat → ℤ)
    (hrow : acceptB (sliceDeclGates lo w) (T 0) = true)
    (hpi : SliceFirstPiAccepted lo w T pv) :
    pv PI_LO = (lo : ℤ) ∧ pv PI_HI = (lo : ℤ) + (w : ℤ) := by
  obtain ⟨hl, hh⟩ := sliceDecl_forces_bounds lo w (T 0) hrow
  exact ⟨by rw [← loPi_forces lo w T pv hpi, hl], by rw [← hiPi_forces lo w T pv hpi, hh]⟩

/-- The DECLARED PARTIAL as a row-addressed assignment: limb column `ACCX + i` carries public input
`PI_OUT + i`. Reading the wire through the row's own layout is what lets the three `fpVal` value
heads be stated on it without re-authoring them. -/
def piRow (pv : Nat → ℤ) : Assignment := fun c => pv (PI_OUT + (c - ACCX))

/-- ⚑ **`published_partial_is_the_last_row`** — the 27 emitted `.last` pins make the three declared
value heads on the WIRE equal the LAST ROW's three accumulator value heads. Nothing here is a row
count: `L` is an argument. -/
theorem published_partial_is_the_last_row (lo w L : Nat) (T : WTrace) (pv : Nat → ℤ)
    (h : SliceLastPiAccepted lo w L T pv) :
    fpVal (piRow pv) ACCX = fpVal (T L) ACCX
      ∧ fpVal (piRow pv) ACCY = fpVal (T L) ACCY
      ∧ fpVal (piRow pv) ACCZ = fpVal (T L) ACCZ := by
  have key : ∀ b : Nat, b + 9 ≤ 27 →
      fpVal (piRow pv) (ACCX + b) = fpVal (T L) (ACCX + b) := by
    intro b hb
    rw [fpVal_as_sum, fpVal_as_sum]
    refine congrArg List.sum (List.map_congr_left (fun i hi => ?_))
    rw [List.mem_range] at hi
    have hlt : b + i < 27 := by simp only [numLimbs] at hi; omega
    have hcol : ACCX + b + i = ACCX + (b + i) := by omega
    rw [hcol, outPi_forces lo w L T pv (b + i) hlt h]
    simp [piRow]
  refine ⟨key 0 (by norm_num), ?_, ?_⟩
  · have e : ACCY = ACCX + 9 := by decide
    rw [e]; exact key 9 (by norm_num)
  · have e : ACCZ = ACCX + 18 := by decide
    rw [e]; exact key 18 (by norm_num)

/-- ⚑⚑ **`published_partial_is_the_fold` — THE DELIVERABLE.** The 27 numbers a verifier reads off
the proof ARE the fold the emitted row template and the emitted thread force. Until this theorem
existed, `slices_compose`'s `P k` was a value a caller NAMED; here it is the value the emitted
object puts on the wire.

`L` is universally quantified and occurs only as `windowedRows_forces`' induction bound: the
statement at `L = 8` is the statement at `L = 1,056,896`.

⚠ What is still carried is `PastaMsmWindowed`'s own — `hsrc`, that a row's `SRC` columns carry the
point they are supposed to. §7.1 is unchanged by this section: the slice CONTENTS are bound one
rung up, in `PastaMsmBound`, and not here. -/
theorem published_partial_is_the_fold (lo w L : Nat) (T : WTrace) (pv : Nat → ℤ)
    (Sv : Nat → PtP) (acc0 : PtP)
    (h0 : PointIsZ (T 0) ACCX ACCY ACCZ acc0)
    (hrows : ∀ i, i < L → acceptB rowGates (T i) = true)
    (hthr : ∀ i, i < L → ThreadAccepted T i)
    (hsrc : ∀ i, i < L → PointIsZ (T i) SRCX SRCY SRCZ (Sv i))
    (hpi : SliceLastPiAccepted lo w L T pv) :
    PointIsZ (piRow pv) ACCX ACCY ACCZ (windowedRef Sv (fun i => bitAt (T i) BIT) acc0 L) := by
  obtain ⟨ex, ey, ez⟩ := published_partial_is_the_last_row lo w L T pv hpi
  obtain ⟨px, py, pz⟩ := windowedRows_forces T Sv acc0 h0 L (fun i hi => hrows i hi)
    (fun i hi => threadGates_force T i (hthr i hi)) (fun i hi => hsrc i hi)
  exact ⟨by rw [ex]; exact px, by rw [ey]; exact py, by rw [ez]; exact pz⟩

/-! ### §5c.4 — ⚑⚑ WHAT THE 29 DO NOT DO, PROVED RATHER THAN INSPECTED. -/

/-- The public-input vector a trace's OWN CELLS determine — what an honest prover publishes, and
what `circuit/tests/pasta_sliced_sg_prove.rs`'s `public_inputs_of` computes. -/
def piOf (T : WTrace) (L : Nat) : Nat → ℤ := fun k =>
  if k = PI_LO then T 0 LO
  else if k = PI_HI then T 0 HI
  else T L (ACCX + (k - PI_OUT))

/-- ⚑⚑ **`pi_pins_refuse_no_trace` — THE ANSWER TO "WHAT DO THE 29 FORCE".** EVERY trace, honest or
not, has a public-input vector satisfying all 29 emitted pins — namely the one read off its own
cells. So the 29 add NOTHING to the trace's solution set: **not one of them refuses a trace.**

That is not a defect and it is not a decoration; it is what a PUBLICATION gate is. The 29 are the
only reason the values `slices_compose` composes exist on the wire at all, and `wire_is_the_declared
_interval` / `published_partial_is_the_fold` are what they buy. But a reader who assumes a
`piBinding` is a CHECK on the prover is wrong, at every one of the 29, and this file said nothing
either way until now. Contrast `sliceLoGate`, which does refuse traces — §5b's `#guard`s. -/
theorem pi_pins_refuse_no_trace (lo w L : Nat) (T : WTrace) :
    SliceFirstPiAccepted lo w T (piOf T L) ∧ SliceLastPiAccepted lo w L T (piOf T L) := by
  constructor
  · intro col k hmem
    rcases piFirst_is_a_bound lo w col k hmem with ⟨hc, hk⟩ | ⟨hc, hk⟩ <;> subst hc <;> subst hk <;>
      simp [piOf, PI_LO, PI_HI]
  · intro col k hmem
    obtain ⟨i, -, hc, hk⟩ := piLast_is_an_acc_limb lo w col k hmem
    subst hc; subst hk
    have h1 : ¬ (PI_OUT + i = PI_LO) := by simp only [PI_OUT, PI_LO]; omega
    have h2 : ¬ (PI_OUT + i = PI_HI) := by simp only [PI_OUT, PI_HI]; omega
    simp only [piOf, if_neg h1, if_neg h2, Nat.add_sub_cancel_left]

/-- ⚑ **`declConst_of_literal`** — and the two CONSTANCY windows are redundant wherever the
row-local LITERAL pin fires on both rows of the window. `sliceLoGate` is a per-row `LO − lo = 0`,
so "a prover could declare slice 0 at the first row and compute slice 3 after it" was never a
thing the constancy gates were needed for. Under the deployed `when_transition()` semantics the
literal fires on rows `0 … H−2`, so what `loConstGate`/`hiConstGate` buy is exactly the LAST row's
`LO`/`HI` — two cells no gate and no public input reads. §7.7. -/
theorem declConst_of_literal (lo w : Nat) (T : WTrace) (i : Nat)
    (h0 : acceptB (sliceDeclGates lo w) (T i) = true)
    (h1 : acceptB (sliceDeclGates lo w) (T (i + 1)) = true) :
    DeclConstant T i := by
  obtain ⟨a0, b0⟩ := sliceDecl_forces_bounds lo w (T i) h0
  obtain ⟨a1, b1⟩ := sliceDecl_forces_bounds lo w (T (i + 1)) h1
  exact ⟨by rw [a0, a1], by rw [b0, b1]⟩

#assert_axioms declPins_eq
#assert_axioms mem_declPins
#assert_axioms piFirst_is_a_bound
#assert_axioms piLast_is_an_acc_limb
#assert_axioms mem_loPi
#assert_axioms mem_hiPi
#assert_axioms mem_outPi
#assert_axioms declPins_indices
#assert_axioms declPins_length
#assert_axioms declPins_indices_nodup
#assert_axioms declPins_cols_nodup
#assert_axioms sliceDeclAccept_forces
#assert_axioms loPi_forces
#assert_axioms hiPi_forces
#assert_axioms outPi_forces
#assert_axioms wire_is_the_declared_interval
#assert_axioms published_partial_is_the_last_row
#assert_axioms published_partial_is_the_fold
#assert_axioms pi_pins_refuse_no_trace
#assert_axioms declConst_of_literal

/-! ## §5d — ⚑⚑ THE PINS BITE, ON A WHOLE TRACE, IN BOTH POLARITIES.

§5b exercises the declaration on ONE assignment. The pins are not row-local and `acceptB` cannot
see them, so they need their own exhibit or §5c is a page of theorems about an object nothing
satisfies. Both polarities below are decided in the kernel over the ACTUALLY EMITTED
`sliceDeclGates`, on a FOUR-ROW trace of slice 0 of 4 at the real width `8,192`.

⚑ **The forgery the 27 pins kill is the one no other gate in this descriptor can see:** a prover
whose trace is entirely honest — every row satisfies the row template, every window satisfies the
thread, every row carries the declared bounds — and whose PUBLISHED PARTIAL is a different number.
`slices_compose` composes what is on the wire, so four honest slices publishing four chosen
partials re-sum to whatever the prover picked. The guard below MEASURES that the row-local
denotation accepts that trace rather than asserting it. -/

/-- A DECLARATION trace: every row carries the declared bounds, and the accumulator's bottom limb
carries `v`. Nothing here is an RCB add — §5d is about the DECLARATION and the WIRE, and the row
template's own satisfiability is `PastaMsmWindowed` §4c's exhibit, not re-authored here. -/
def declTrace (lo w v : Nat) : WTrace := fun _ => fun c =>
  if c = LO then (lo : ℤ)
  else if c = HI then (lo : ℤ) + (w : ℤ)
  else if c = ACCX then (v : ℤ)
  else 0

/-- A one-cell perturbation of ONE ROW of a trace. -/
def bumpTraceAt (T : WTrace) (r c : Nat) : WTrace :=
  fun i => if i = r then bumpAt (T i) c else T i

-- ⚑ SATISFIABLE, JOINTLY — §5c's hypotheses are INHABITED, which is the thing a forcing theorem is
-- worthless without. Every window of the honest four-row trace satisfies the literal pins, the
-- constancy windows AND both PI families, against the public inputs the trace itself determines.
#guard (List.range 4).all (fun i =>
  sliceDeclAcceptB 0 8192 3 i (declTrace 0 8192 7) (piOf (declTrace 0 8192 7) 3))
-- …and at slice 2 of 4, whose emitted descriptor is a textually different object.
#guard (List.range 4).all (fun i =>
  sliceDeclAcceptB 16384 8192 3 i (declTrace 16384 8192 7) (piOf (declTrace 16384 8192 7) 3))

-- ⚑⚑ THE MEASUREMENT — **THE MIS-PUBLISHED PARTIAL.** The trace is UNTOUCHED and every row of it
-- is accepted by the row-local denotation, which is where every theorem in this file lived before
-- §5c…
#guard (List.range 4).all (fun i => acceptB (sliceDeclGates 0 8192) (declTrace 0 8192 7 i))
-- …and the emitted `.last` pins REFUSE the wire that claims a different partial. This is the whole
-- content of the 27, and nothing else in this descriptor can see the forgery.
#guard ! sliceDeclAcceptB 0 8192 3 0 (declTrace 0 8192 7) (piOf (declTrace 0 8192 9) 3)
-- ⚑ …AND THE FORGED WIRE IS NOT MALFORMED: the same public inputs, against the trace that really
-- computes them, are ACCEPTED. So what refuses above is the BINDING to this trace, not a
-- malformity — the polarity `PastaMsmScalarDerive` §5d establishes for the challenge pins.
#guard (List.range 4).all (fun i =>
  sliceDeclAcceptB 0 8192 3 i (declTrace 0 8192 9) (piOf (declTrace 0 8192 9) 3))

-- ⚑ REFUTABLE — the MOVED partial: the last row's published limb bumped. Row-locally accepted on
-- every row (the declaration gates read `LO`/`HI` and nothing else), refused by the pin.
#guard (List.range 4).all (fun i =>
  acceptB (sliceDeclGates 0 8192) (bumpTraceAt (declTrace 0 8192 7) 3 ACCX i))
#guard ! sliceDeclAcceptB 0 8192 3 0 (bumpTraceAt (declTrace 0 8192 7) 3 ACCX)
          (piOf (declTrace 0 8192 7) 3)

-- ⚑ REFUTABLE — the MIS-PUBLISHED BOUND: slice 0's trace with slice 2's interval on the wire.
-- This is the pin that makes the four-way tiling check readable off the proofs.
#guard ! sliceDeclAcceptB 0 8192 3 0 (declTrace 0 8192 7) (piOf (declTrace 16384 8192 7) 3)

-- ⚑ THE REACH, measured rather than asserted. The 29 pins reach exactly TWO rows — the first and
-- the last. A NON-last row's accumulator is pinned by none of them: bumping row 1's `ACCX` leaves
-- the whole declaration ACCEPTING. That cell is the accumulator THREAD's to force, and saying so
-- is the difference between the pins being understood and being assumed.
#guard sliceDeclAcceptB 0 8192 3 0 (bumpTraceAt (declTrace 0 8192 7) 1 ACCX)
         (piOf (declTrace 0 8192 7) 3)

-- ⚑ …and the same measurement from the other side: every trace has a satisfying wire
-- (`pi_pins_refuse_no_trace`), so a trace with an arbitrary cell moved is still accepted once the
-- wire follows it. The 29 refuse no trace; they pin what the verifier reads.
#guard (List.range 4).all (fun i =>
  sliceDeclAcceptB 0 8192 3 i (bumpTraceAt (declTrace 0 8192 7) 3 ACCX)
    (piOf (bumpTraceAt (declTrace 0 8192 7) 3 ACCX) 3))

-- ⚑ The emitted pin INVENTORY, in the kernel: 29 pins, naming public inputs `0..28` exactly once
-- each, on the two declaration columns and the 27 accumulator limbs `442..468`.
#guard (declPins 0 8192).length == 29
#guard (declPins 0 8192).map (fun p => p.2.2) == List.range 29
#guard (declPins 0 8192).map (fun p => p.2.1) == 525 :: 526 :: (List.range 27).map (442 + ·)
#guard ((declPins 0 8192).filter (fun p => p.1 == .first)).length == 2
#guard ((declPins 0 8192).filter (fun p => p.1 == .last)).length == 27
-- …and the whole emitted descriptor carries no OTHER pin: 78 constraints, 29 of them `piBinding`s.
#guard ((slicedRowDesc 4 0 8192).constraints.filterMap (fun c => match c with
          | .base (.piBinding _ _ k) => some k
          | _                        => none)) == List.range 29

end WirePins

/-! ## §6 — THE FOUR-WAY CUT AT THE REAL NUMBERS.

`PastaIpaDeferral` §4b's row vocabulary, re-pinned against the DECLARED bounds so the arithmetic
and the emitted object are checked in one place. Cheap: no group operations. -/

/-- `|srs.g|` on the Wrap/Tock side — the leg every dregg→Mina gap bottoms out in. -/
def WRAP_SRS : Nat := 32768
/-- The cut. -/
def SLICES : Nat := 4
/-- Generators per slice. -/
def SLICE_W : Nat := 8192
/-- Bit planes at the GLV layout (`PastaMsmLayouts` §6's measured best). -/
def PLANES : Nat := 128
/-- The deployed single-instance trace ceiling: BabyBear two-adicity at `log_blowup = 6`. -/
def MAX_ROWS : Nat := 2097152

/-- Rows one slice costs — `PastaIpaDeferral.chunkRows`. -/
def sliceRows (w : Nat) : Nat := PLANES * (w + 1) + w

-- The cut divides.
#guard SLICES * SLICE_W == WRAP_SRS
-- ⚑ …and it clears the ceiling IN RAW ROWS, at 50.4% — which is NOT headroom; see the padded
-- guards below, where the same 1,056,896 fills the committed 2^21 domain exactly.
#guard sliceRows SLICE_W == 1056896
#guard sliceRows SLICE_W < MAX_ROWS
#guard 100 * sliceRows SLICE_W < 51 * MAX_ROWS
#guard 100 * sliceRows SLICE_W > 50 * MAX_ROWS
-- TWO misses by 16,512 rows; THREE clears the ceiling but does not divide 32,768.
#guard sliceRows 16384 - MAX_ROWS == 16512
#guard 3 * 10923 ≠ WRAP_SRS
-- ⚑ AND HERE IS THE PART THE ROW COUNT ALONE HIDES: a STARK trace height is a POWER OF TWO, so the
-- honest per-instance height is the PADDED one — and 1,056,896 pads to 2^21, i.e. exactly the
-- ceiling. "50.4% of the ceiling" is 50.4% of the RAW rows and 100% of the COMMITTED domain.
-- Clearing the ceiling in raw rows is therefore NOT headroom; §7.4.
#guard 1048576 < sliceRows SLICE_W && sliceRows SLICE_W <= MAX_ROWS
#guard 2 * 1048576 == MAX_ROWS
-- ⚑ …and the cut that DOES leave headroom once padding is priced is EIGHT, not four: 4,096
-- generators, 528,512 rows, which pads to 2^20 — half the ceiling rather than all of it. Eight
-- divides 32,768 as cleanly as four does. Recorded because "four-way clears at 50.4%" is a
-- statement about RAW rows and reads as headroom it does not have.
#guard WRAP_SRS / 8 == 4096
#guard 8 * 4096 == WRAP_SRS
#guard sliceRows 4096 == 528512
#guard 524288 < sliceRows 4096 && sliceRows 4096 <= 1048576
#guard 2 * 1048576 == MAX_ROWS

/-- The four declared intervals, as a verifier reads them off the proofs' public inputs. -/
theorem real_cut_bounds :
    sliceBounds SLICE_W SLICES = [(0, 8192), (8192, 16384), (16384, 24576), (24576, 32768)] := by
  decide

/-- ⚑⚑ **`real_cut_composes`** — **the four partials compose to the whole `2^15`-term MSM, each
naming its own slice.** `slices_compose` at `n = 4`, `w = 8192`; the general theorem holds at every
`(n, w)`, so nothing here is a special case that could be true by accident. -/
theorem real_cut_composes {M : Type} [AddCommGroup M] (as : List Nat) (ps : List M)
    (ha : as.length = WRAP_SRS) (hp : ps.length = WRAP_SRS) (P : Nat → M)
    (hP : ∀ k, k < SLICES → P k = slicePartial SLICE_W k as ps) :
    P 0 + P 1 + P 2 + P 3 = msmN as ps := by
  have h := slices_compose SLICE_W SLICES as ps P
    (by rw [ha]; rfl) (by rw [hp]; rfl) hP
  have e : ((List.range SLICES).map P).sum = P 0 + (P 1 + (P 2 + (P 3 + 0))) := rfl
  rw [← h, e]
  abel

#assert_axioms real_cut_bounds
#assert_axioms real_cut_composes

/-! ## §7 — WHAT THIS DOES NOT DO. At the CURRENT resolution.

1. ⚑ **The slice DECLARATION is bound; the slice CONTENTS are not.** `sliceDecl_forces_bounds` pins
   `[lo, hi)` into the emitted gates, `sliceBoundPi_publishes` puts it on the wire, and
   `outPi_publishes` publishes the partial. NOTHING in the emitted constraints says the row's `SRC`
   columns carry `srs.g[lo + t]`, or that its `BIT` column carries the right bit of `sVec[lo + t]`.
   Those are trace-level hypotheses, exactly as `PastaMsmWindowed` §6.1 leaves the `DBL` pattern.
   An adversary may declare `[0, 8192)` and fill the rows with any 8,192 points.

   What would close it is nameable and unbuilt: an exact-public table (`TableSem.ExactPublicRows`,
   which this IR already carries and `Ir2Air::ExactPublicRow` already proves) holding
   `(absolute index, generator limbs)` for the slice, plus a threaded term-index column, with each
   conditional-add row doing a lookup into it. Then a row could not carry a generator from another
   slice. That is the next rung; it is not this one.

2. **The kernel `decide` of rung 5h and this AIR are DIFFERENT OBJECTS, and neither subsumes the
   other.** `MinaWrapSgCore`/`MinaWrapSgChunk*` check `sg == ⟨s, srs.g⟩` on Mina devnet block
   539508 by evaluating it in the Lean kernel over the REAL `srs.g` — that binds the contents and
   produces no proof object. This file produces a proof object and does not bind the contents.
   Saying "rung 5h is proved" without saying which one is meant is the confusion to avoid.

3. **The ℤ ↔ felt gap is inherited, unchanged.** `acceptB` reads a gate body as an INTEGER zero;
   the deployed prover reads it as zero in BabyBear. `PastaMsmWindowed` §6.2 states this residual
   and this file neither widens nor narrows it.

4. ⚑ **Clearing `2^21` is not the same as being provable, and the padding says so before memory
   does.** `2^21` is a two-adicity limit on the COMMITTED domain, and 1,056,896 raw rows pad to
   `2^21` exactly — so the four-way cut lands each instance AT the ceiling, with the headroom
   spent on padding. On top of that the binding practical constraint at `traceWidth 527` is
   MEMORY, and it binds far below `2^21`. The four-way cut is the right cut for the ceiling and
   does not by itself make a slice provable on any box. The measured wall is reported by
   `circuit/tests/pasta_sliced_sg_prove.rs`; it is not asserted here.

5. **P10 is untouched.** Cutting an opening check into four does not make it sound; that a prover
   passing it must KNOW an opening is the IPA extraction argument, and no rung here moves it.

6. ⚑⚑ **THE 29 `piBinding`s REFUSE NO TRACE, and that is a theorem** (`pi_pins_refuse_no_trace`,
   §5c.4) rather than an inspection. Every trace has a public-input vector satisfying all 29 — the
   one read off its own cells — so not one of the 29 constrains the prover's trace. They are
   PUBLICATION, not checking: `wire_is_the_declared_interval` and `published_partial_is_the_fold`
   are what they buy, and they are the only reason `slices_compose`'s `P k` denotes a value a
   verifier can read. A reader who takes a `piBinding` for a check on the prover is wrong at every
   one of the 29, and until §5c this file said nothing either way — it proved only `sMaxPi ≤
   piCount`, a bound check a pin binding nothing satisfies.

   The 29 split 2 / 27 and the halves are not alike:

   * the **2 bound pins** publish what the descriptor's own literal ALREADY says. A verifier
     holding the descriptor knows `lo` before it reads a public input; what the pins buy is that
     the PI vector agrees with the literal, so the four-way tiling check (`slice_bounds_abut`) can
     be run on the PI vectors alone. Their trace side is `sliceLoGate`'s, entirely.
   * the **27 accumulator pins** are the only gates in this descriptor that read the accumulator's
     final value at all. Delete them and four honest slices publish four chosen partials, and
     `slices_compose` composes the chosen ones. §5d exhibits exactly that forgery: an untouched,
     row-locally accepted trace with a mis-published partial.

7. ⚑ **`loConstGate` / `hiConstGate` force two cells nothing reads.** `sliceLoGate` is a per-row
   LITERAL, so under the deployed `when_transition()` arm `LO = lo` already holds on rows
   `0 … H−2`; `declConst_of_literal` proves the constancy windows are implied wherever the literal
   fires on both rows of a window. What the two windows add is the LAST row's `LO`/`HI` — and the
   `.first` pins read row 0, no gate in `PastaMsmSliced` reads `LO` again, and `PastaMsmBound`
   builds its manifest from the Nat literal `sliceLo w k`, never from the column. So the two gates
   are emitted weight.

   **They are not deleted here and the reason is scope, not doubt.** Dropping them re-emits four
   descriptors, moves the constraint count `78 → 76`, and breaks the pinned sha256s and the `78`
   assertions in `PastaMsmBound` / `PastaMsmOnCurve` / `PastaMsmScalarDerive` and in four Rust
   test files, while two sibling lanes are live in that tree. Named as debt, with the theorem that
   makes the claim checkable rather than a reading.

8. ⚠ **`sliceDeclAcceptB`'s `match` ends in `_ => true`, which is FAIL-OPEN by construction.** It
   is correct for the three constructors `sliceDeclGates` emits today, and a fourth added to that
   list would be silently accepted by every `#guard` in §5d while `sliceDeclAccept_forces` kept
   proving four predicates that no longer cover the emitted object. **Any addition to
   `sliceDeclGates` must extend `sliceDeclAcceptB`'s match and the predicates in the same commit.**

   The same shape is live in `sMaxVar` and `sMaxPi`, whose `_ => 0` arms report a bound of zero for
   any constructor they do not name — and that is not hypothetical: `PastaMsmWindowed.cMaxVar` had
   exactly this hole for `.piBinding` (§4b), and `PastaMsmBound` had to add `bMaxVar` for
   `.lookup`. Three instances of one class, in one tower.

9. ⚑ **The published partial is a PROJECTIVE REPRESENTATIVE, not a point.** The 27 pins publish
   `(X : Y : Z)` limbs; `(λ²X : λ³Y : λZ)` is the same partial and a different public-input vector,
   and no emitted gate normalises `Z` or pins it to 1. So two honest provers of the same slice
   publish different PI vectors, and EQUALITY of published partials is not equality of partials.
   A consumer must compare projectively — `circuit/tests/pasta_sliced_sg_prove.rs` does (`proj_eq`)
   — and `slices_compose`'s `P k` is the point the representative denotes, which
   `published_partial_is_the_fold` states in `ZMod p` via `PointIsZ` rather than on limbs.
-/

end Dregg2.Circuit.Emit.PastaMsmSliced
