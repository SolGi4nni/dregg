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
`1,056,896` rows, `50.4%` of the ceiling (§6).

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

/-- `nxt LO − loc LO` — the declared slice cannot change down the trace. -/
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

/-- ⚑ **`sliceDecl_forces_constant`** — the declared slice cannot change down the trace. Without
this a prover could declare slice 0 at the first row, where the PI binding looks, and compute
slice 3 on every row after it. -/
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
-- ⚑ …and it CLEARS the ceiling, at 50.4%.
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
-/

end Dregg2.Circuit.Emit.PastaMsmSliced
