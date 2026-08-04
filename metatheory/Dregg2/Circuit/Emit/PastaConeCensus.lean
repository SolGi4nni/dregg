/-
# Dregg2.Circuit.Emit.PastaConeCensus — WHICH GATES OF A DESCRIPTOR HAVE A FORCED ℤ MEANING, as a
count computed from the emitted object.

## The gap this closes

`circuit/tests/ir2_oversized_constant_refusal.rs` makes the Pasta cone legible along ONE axis: a
gate COEFFICIENT wider than a felt. That is a real refusal and it bites on all fifteen. But it is
not the defect. The defect is that a gate BODY can exceed `P`, so the prover's
`body ≡ 0 (mod P)` does not imply `body = 0` over ℤ — and a descriptor can carry that with every
coefficient comfortably inside a felt. Coefficient width is a proxy; body REACH is the thing.

⚠ And once a descriptor is PARSED the proxy is gone: `lean_descriptor_air.rs::LeanExpr::Const` is
an `i64`, and `parse_vm_descriptor2_unsound_oversized` reaches it by folding the 495-bit constant
to its residue mod `P`. So the parsed object no longer carries the evidence of its own defect.
The census therefore has to live HERE, on the Lean-authored descriptor whose coefficients are ℤ.

## What is counted

`reach bnd e` is the largest `|e.eval a|` admits when every column `i` satisfies `|a i| ≤ bnd i`
(`reach_bounds`). `declaredBnd d` is the bound the descriptor's OWN declared range lookups supply:
`2^bits − 1` for a column some `rangeLimb bits` lookup pins, `P − 1` (any canonical felt) for every
other. `unforcedGates d` counts the row gates whose reach touches `P`.

`forced_of_reach_lt_P` is why the count means something: below `P`, the deployed mod-`P` reading
IS the ℤ reading. It is the general form of `PastaFieldSound.coefBody_abs_lt_P` and
`PastaAddSubSound.adBody_abs_lt_P` — those two prove a tight bound by hand for the argument's sake;
this one is crude, decidable, and runs over any descriptor.

## The measurement (all `decide`, kernel-reduced)

    dregg-pasta-rcb-windowed::v1     42 row gates,  42 UNFORCED   ← the whole cone's root
    dregg-pasta-fpmul-sound::v1      63 row gates,   0 unforced
    dregg-pasta-fqmul-sound::v1      63 row gates,   0 unforced
    dregg-pasta-fpadd-sound::v1      32 row gates,   0 unforced
    dregg-pasta-fpsub-sound::v1      32 row gates,   0 unforced
    dregg-pasta-fqadd-sound::v1      32 row gates,   0 unforced
    dregg-pasta-fqsub-sound::v1      32 row gates,   0 unforced

⚑ `42 of 42`. Not "the multiply is unsound and the rest is fine" — the windowed descriptor declares
**no tables and no ranges at all**, so every column in it is an arbitrary canonical felt and NOT ONE
of its row gates has a forced integer meaning. Measured the same way on the rest of the cone (by
`scripts/`-free arithmetic over the checked-in JSON, not proved here because the objects are large):
`pasta-rcb-sg-slice-0-of-4` 43/44, `pasta-rcb-sg-bound-0-of-4` 43/44, `pasta-rcb-sg-oncurve-0-of-4`
59/60, `pasta-rcb-sg-derive-0-of-10922` 998/999. The one forced gate in each is the same
`binGate` — a booleanity `c·(c−1)`.

⚠ **Booleanity is the one place this metric asks the wrong question.** A `binGate`'s intended
meaning IS the field statement, and `c(c−1) ≡ 0 (mod P)` with `P` prime and `c` canonical does force
`c ∈ {0,1}`. So of the windowed descriptor's 42, three are booleanity gates that are fine, and
**39 are limb-recomposition gates with no forced ℤ meaning whatsoever** — the twelve multiplies, the
nineteen add/subs, the two constant-scalar multiplies, and the six point selections. The count
below is the honest mechanical one; this paragraph is the reading of it.

⚠ **The three `on_transition` window gates are NOT in the count.** `gateBodies` takes
`.base (.gate _)` only; a `windowGate`'s body reads two rows and needs a two-row bound. They are
limb recompositions too (`Σ 2^(30 i)·loc − Σ 2^(30 i)·nxt`), so the true unforced total for the
windowed descriptor is 45, not 42. Named rather than quietly dropped.

## Why a count and not a caption

A caption cannot go red. This one does: re-emit any of these descriptors and the theorem either
still holds or fails to compile. When the RCB/MSM cone is migrated (or retired), the
`windowedRowDesc` line is what has to be restated.

## Axiom hygiene

`#assert_axioms`-clean; no `sorry`/`native_decide`; zero `#guard`s.
-/
import Dregg2.Circuit.Emit.PastaAddSubSound
import Dregg2.Circuit.Emit.PastaMsmWindowed

namespace Dregg2.Circuit.Emit.PastaConeCensus

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 VmConstraint2 TableId)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint)
open Dregg2.Circuit.Emit.EffectLower (P)

set_option autoImplicit false
set_option maxRecDepth 40000
-- the 63-gate multiply census reduces ~800k `List.find?` steps in the kernel; the default 200 000
-- heartbeats stops halfway through it.
set_option maxHeartbeats 2000000

/-! ## §1 — REACH, and the theorem that makes it mean something. -/

/-- The largest `|e.eval a|` can be when every column `i` satisfies `|a i| ≤ bnd i`. Crude by
design: it is the term-by-term triangle bound, which is decidable and needs no structure. -/
def reach (bnd : Nat → ℤ) : EmittedExpr → ℤ
  | .const c => |c|
  | .var i   => bnd i
  | .add a b => reach bnd a + reach bnd b
  | .mul a b => reach bnd a * reach bnd b

theorem reach_nonneg (bnd : Nat → ℤ) (hb : ∀ i, 0 ≤ bnd i) (e : EmittedExpr) :
    0 ≤ reach bnd e := by
  induction e with
  | const c => exact abs_nonneg c
  | var i => exact hb i
  | add a b ha hb' => exact add_nonneg ha hb'
  | mul a b ha hb' => exact mul_nonneg ha hb'

/-- **`reach` is a bound.** Without this the count below would be about a function nobody had
connected to the evaluation. -/
theorem reach_bounds (bnd : Nat → ℤ) (hb : ∀ i, 0 ≤ bnd i) (a : Assignment)
    (h : ∀ i, |a i| ≤ bnd i) (e : EmittedExpr) : |e.eval a| ≤ reach bnd e := by
  induction e with
  | const c => simp [EmittedExpr.eval, reach]
  | var i => simpa [EmittedExpr.eval, reach] using h i
  | add x y hx hy =>
    calc |(EmittedExpr.add x y).eval a| = |x.eval a + y.eval a| := by simp [EmittedExpr.eval]
      _ ≤ |x.eval a| + |y.eval a| := Dregg2.Circuit.Emit.PastaFieldSound.abs_add_le' _ _
      _ ≤ reach bnd x + reach bnd y := by linarith
      _ = reach bnd (.add x y) := rfl
  | mul x y hx hy =>
    calc |(EmittedExpr.mul x y).eval a| = |x.eval a| * |y.eval a| := by
          simp [EmittedExpr.eval, abs_mul]
      _ ≤ reach bnd x * reach bnd y :=
          mul_le_mul hx hy (abs_nonneg _) (reach_nonneg bnd hb x)
      _ = reach bnd (.mul x y) := rfl

/-- ⚑ **THE GENERAL FORM OF THE WHOLE REPAIR.** When a gate body cannot reach `P`, the reading the
deployed prover performs (`body ≡ 0 mod P`) and the reading every forcing lemma in this tree assumes
(`body = 0` over ℤ) COINCIDE. `PastaFieldSound.coefBody_abs_lt_P` and
`PastaAddSubSound.adBody_abs_lt_P` are the tight hand-proved instances; this is the statement they
are instances of, and it is what the census counts. -/
theorem forced_of_reach_lt_P (bnd : Nat → ℤ) (hb : ∀ i, 0 ≤ bnd i) (a : Assignment)
    (h : ∀ i, |a i| ≤ bnd i) (e : EmittedExpr)
    (hr : reach bnd e < P) (hd : P ∣ e.eval a) : e.eval a = 0 := by
  have hle := reach_bounds bnd hb a h e
  rcases hd with ⟨t, ht⟩
  by_contra hne
  have ht0 : t ≠ 0 := by rintro rfl; rw [mul_zero] at ht; exact hne ht
  have hP0 : (0 : ℤ) < P := by norm_num [Dregg2.Circuit.Emit.EffectLower.P]
  have h1 : (1 : ℤ) ≤ |t| := by rcases abs_cases t with ⟨hh, _⟩ | ⟨hh, _⟩ <;> omega
  have : P ≤ |e.eval a| := by
    rw [ht, abs_mul, abs_of_nonneg (le_of_lt hP0)]
    nlinarith
  linarith

/-! ## §2 — the per-column bound a descriptor's OWN lookups supply, and the count. -/

/-- The declared range width of a table id, if it is a `rangeLimb` table. -/
def rangeBitsOf (d : EffectVmDescriptor2) (tid : TableId) : Option Nat :=
  (d.tables.find? (fun t => t.id == tid)).bind (fun t =>
    match t.sem with
    | .rangeLimb b => some b
    | _            => none)

/-- Every `(column, width)` pair the descriptor's own single-`var` range lookups pin. -/
def pinnedCols (d : EffectVmDescriptor2) : List (Nat × Nat) :=
  d.constraints.filterMap (fun c =>
    match c with
    | .lookup l =>
      match l.tuple with
      | [.var col] => (rangeBitsOf d l.table).map (fun b => (col, b))
      | _          => none
    | _ => none)

/-- ⚑ **The bound a PIN LIST supplies.** A pinned column holds `< 2^bits`; every other column is an
arbitrary canonical felt, so `P − 1`. Taking the list as a PARAMETER rather than recomputing
`pinnedCols d` per column occurrence is not style: the kernel then shares one reduced list across
the ~800k lookups the multiply census performs. -/
def boundOf (pins : List (Nat × Nat)) (col : Nat) : ℤ :=
  match pins.find? (fun p => p.1 == col) with
  | some (_, b) => (2 : ℤ) ^ b - 1
  | none        => P - 1

/-- The bound the descriptor ITSELF supplies. A descriptor that declares no tables gets `P − 1`
everywhere, which is exactly why `pasta-rcb-windowed` scores what it scores. -/
def declaredBnd (d : EffectVmDescriptor2) : Nat → ℤ := boundOf (pinnedCols d)

theorem boundOf_nonneg (pins : List (Nat × Nat)) (col : Nat) : 0 ≤ boundOf pins col := by
  unfold boundOf
  cases pins.find? (fun p => p.1 == col) with
  | none => norm_num [Dregg2.Circuit.Emit.EffectLower.P]
  | some p =>
    show (0 : ℤ) ≤ 2 ^ p.2 - 1
    have h : (0 : ℤ) < 2 ^ p.2 := by positivity
    omega

theorem declaredBnd_nonneg (d : EffectVmDescriptor2) (col : Nat) : 0 ≤ declaredBnd d col :=
  boundOf_nonneg _ col

/-- The ROW gate bodies. ⚠ `.windowGate` is deliberately excluded — a two-row body needs a two-row
bound — and the docblock names the three that costs on `windowedRowDesc`. -/
def gateBodies (d : EffectVmDescriptor2) : List EmittedExpr :=
  d.constraints.filterMap (fun c =>
    match c with
    | .base (.gate b) => some b
    | _               => none)

/-- A row gate is FORCED under a pin list when its body cannot reach `P`. -/
def gateForced (pins : List (Nat × Nat)) (e : EmittedExpr) : Bool :=
  decide (reach (boundOf pins) e < P)

/-- ⚑ **THE CENSUS.** How many row gates of `d` the deployed prover does NOT force to zero over ℤ.
`0` means every gate's mod-`P` check IS its integer check. -/
def unforcedGates (d : EffectVmDescriptor2) : Nat :=
  ((gateBodies d).filter (fun e => !gateForced (pinnedCols d) e)).length

/-- …stated against `declaredBnd`, so the count and the bound theorem are visibly the same object. -/
theorem unforcedGates_eq (d : EffectVmDescriptor2) : unforcedGates d
    = ((gateBodies d).filter (fun e => !decide (reach (declaredBnd d) e < P))).length := rfl

/-- …and the denominator, so a count is never read without its base. -/
def rowGates (d : EffectVmDescriptor2) : Nat := (gateBodies d).length

/-! ## §3 — THE MEASUREMENT. -/

open Dregg2.Circuit.Emit.PastaFieldSound (fpMulSoundDesc fqMulSoundDesc)
open Dregg2.Circuit.Emit.PastaAddSubSound
  (fpAddSoundDesc fpSubSoundDesc fqAddSoundDesc fqSubSoundDesc)
open Dregg2.Circuit.Emit.PastaMsmWindowed (windowedRowDesc)

/-- ⚑ **THE CONE'S ROOT: 42 ROW GATES, 42 UNFORCED.** `dregg-pasta-rcb-windowed::v1` declares no
tables and no ranges, so every one of its columns is an arbitrary canonical felt and not a single
row gate has a forced integer meaning. This is the descriptor
`circuit/tests/pasta_{field,addsub}_felt_soundness.rs` proves two live forgeries against. -/
theorem windowedRowDesc_row_gates : rowGates windowedRowDesc = 42 := by decide

theorem windowedRowDesc_unforced : unforcedGates windowedRowDesc = 42 := by decide

/-- ⚑ **AND THE SOUND ENCODINGS SCORE ZERO** — each from its OWN declared lookups, computed off the
emitted object rather than read out of the soundness proof. Two independent sources agreeing is what
makes this a gate; the hand proof alone would be one source pinned against itself. -/
theorem fpMulSoundDesc_all_forced : unforcedGates fpMulSoundDesc = 0 := by decide
theorem fqMulSoundDesc_all_forced : unforcedGates fqMulSoundDesc = 0 := by decide
theorem fpAddSoundDesc_all_forced : unforcedGates fpAddSoundDesc = 0 := by decide
theorem fpSubSoundDesc_all_forced : unforcedGates fpSubSoundDesc = 0 := by decide
theorem fqAddSoundDesc_all_forced : unforcedGates fqAddSoundDesc = 0 := by decide
theorem fqSubSoundDesc_all_forced : unforcedGates fqSubSoundDesc = 0 := by decide

theorem fpMulSoundDesc_row_gates : rowGates fpMulSoundDesc = 63 := by decide
theorem fpAddSoundDesc_row_gates : rowGates fpAddSoundDesc = 32 := by decide
theorem fpSubSoundDesc_row_gates : rowGates fpSubSoundDesc = 32 := by decide

/-- ⚑ **AND THE CENSUS ITSELF IS REFUTABLE.** Strip the range lookups off the sound add descriptor
— keep every gate, drop every `.lookup` — and the count goes from `0` to all 32. A metric that
scored zero whatever the descriptor said would be decoration; this is the proof it is not. -/
def stripLookups (d : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  { d with tables := [], constraints := d.constraints.filter (fun c =>
      match c with | .lookup _ => false | _ => true) }

theorem census_is_refutable : unforcedGates (stripLookups fpAddSoundDesc) = 32 := by decide

#assert_axioms reach_bounds
#assert_axioms forced_of_reach_lt_P
#assert_axioms windowedRowDesc_unforced
#assert_axioms fpMulSoundDesc_all_forced
#assert_axioms fpAddSoundDesc_all_forced
#assert_axioms fpSubSoundDesc_all_forced
#assert_axioms census_is_refutable

end Dregg2.Circuit.Emit.PastaConeCensus
