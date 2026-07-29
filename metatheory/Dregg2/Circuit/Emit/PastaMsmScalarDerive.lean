/-
# Dregg2.Circuit.Emit.PastaMsmScalarDerive — the s-vector RECOMPUTED by emitted constraints.

## Substrate, said out loud

**Lean-authored AIR.** Every constraint here is produced by a `def` returning `VmConstraint2`, and
every theorem is about that ACTUALLY EMITTED list. Rust hand-writes no constraint, no builder
gadget and no `air_accepts` predicate: it parses the emitted descriptor, fills trace CELLS and runs
the deployed prover. `deriveRowDesc_extends_onCurve` proves `PastaMsmOnCurve.onCurveRowDesc`'s 98
constraints are still a PREFIX, so every forcing theorem of the tower below applies unchanged.

## The hole this file closes, and the sentence it retires

`PastaMsmScalarBound` §7.1 said the tensor `s_i = ∏_j c_j^{bit_j(i)}` is *bound at the descriptor's
manifest, not recomputed by an emitted constraint*, and named the blocker:

> A row carries ONE BIT of its scalar; the other 254 live at the same term index in the other 254
> bit planes. `WindowExpr` has exactly `loc` and `nxt`, and the Horner schedule is plane-outer, so
> rows sharing a term index are `w + 1` apart. **Recomposing a scalar from its per-plane digits**
> therefore cannot be written as a window constraint at all.

⚑ **The direction was backwards, and that is the whole content of this rung.** RE-composing a
scalar from digits spread across planes is cross-row. DE-composing a scalar into its digits is
ROW-LOCAL. Put the scalar itself on the row — derived, in `nb` modular multiplications from the
challenges on the wire — and the row carries its own `s_{lo+t}`, all `planes` of its binary digits,
and a selector that reads off the one its own plane index names. Nothing crosses a row boundary,
so nothing needs a stride-`k` window arm or a column-major schedule. **The IR was never the
blocker; the SHARING was.**

## What it costs, and why sharing was never worth an IR change

The derivation is repeated once per ROW rather than once per TERM — `planes`-fold redundant work.
That redundancy is nearly free, and the reason is structural: **an AIR's columns are global.** A
stride-`k` arm would let the chain's gates fire only on plane-0 rows, but its columns would still
be committed on all `planes·(w+1)` rows, and a guarded gate is a HIGHER-degree gate, not a cheaper
one. The committed area — which is what FRI pays for — is identical either way. §6 prices both
against the deployed four-way cut.

The one shape that IS cheaper is a SEPARATE, SHORTER instance (`w` rows, not `planes·(w+1)`) tied
to the MSM rows by a bus. That needs a `provide` dual of `Lookup`, which this IR does not have
(`descriptor_ir2.rs`'s main arm calls `LookupBus::lookup_key` with multiplicity `ONE` and never
`table_entry`). §6.2 names it as the cost rung, with its price.

## The chain, and what it is anchored to

`PastaMsmScalarBound.sAt` reads the `i`-th s-vector entry in `|cs|` multiplications, and
`sVec_getElem?_eq_sAt` proves it IS `(PastaIPA.sVec cs)[i]`, which `sVec_eq_bPoly` proves is the
coefficient vector of `b(X) = ∏_j (1 + c_j X^{2^j})`. This file emits that product as a gate chain:
`PR 0 = 1`, `PR (j+1) ≡ PR j · MU j (mod q)`, with `MU j` the SELECTED multiplier — `c_j` when the
`(nb−1−j)`-th binary digit of the row's own `GIDX` is set, `1` otherwise. `GIDX` is the ABSOLUTE
generator index `PastaMsmBound.bound_forces_gidx` already forces onto the row, so the chain is
evaluated at the index the row actually consumes.

## Axiom hygiene

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/
`native_decide`. `#guard`s reduce in the kernel. Imports read-only. Import line:
`import Dregg2.Circuit.Emit.PastaMsmScalarDerive`
-/
import Dregg2.Circuit.Emit.PastaMsmOnCurve
import Dregg2.Circuit.Emit.PastaMsmScalarBound

namespace Dregg2.Circuit.Emit.PastaMsmScalarDerive

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2 (VmConstraint2 EffectVmDescriptor2 WindowExpr WindowConstraint
  TableId TableDef VmTrace)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.AirBuilder
open Dregg2.Circuit.Emit.PastaField (pN qN numLimbs limbBits fpValue fpVal acceptB)
open Dregg2.Circuit.Emit.PastaMsmWindowed (WTrace envOf cw BIT DBL fpVal_as_sum)
open Dregg2.Circuit.Emit.PastaMsmSliced (sliceLo PI_COUNT sMaxPi)
open Dregg2.Circuit.Emit.PastaMsmBound (Pt TIDX GIDX bMaxVar termAt planeAt scalarDigit)
open Dregg2.Circuit.Emit.PastaMsmOnCurve (WOC onCurveRowDesc)
open Dregg2.Circuit.Emit.PastaMsmScalarBound (sAt sFactors sNat)

set_option autoImplicit false

/-! ## §1 — THE LAYOUT.

Everything is appended above `PastaMsmOnCurve.WOC = 799`; not one existing column moves. `nb` is
the challenge count (15 for the deployed block), `planes` the bit-plane count. The four 9-limb
families are addressed by a FLAT limb index `m`, so `CHc nb (numLimbs*j + l)` is challenge `j`'s
limb `l` — which keeps every length lemma a `List.length_map` and keeps the kernel `decide`s small.

  * `PIDX`   — the row's BIT PLANE, threaded from the `DBL` column (§2.1). The plane-outer schedule
               already says which plane a row is in; this puts that fact in a column so a row-local
               gate can use it.
  * `GBc j`  — the `j`-th binary digit of `GIDX`, the ABSOLUTE generator index the row consumes.
  * `CHc m`  — the challenge limbs, PI-bound on row 0 and threaded down (§2.3). ⚑ This is what
               "the challenges are on the wire" means, concretely.
  * `MUc m`  — the SELECTED multiplier limbs: challenge `j` if `GBc (nb−1−j) = 1`, else the field 1.
  * `PRc m`  — the running product, `nb + 1` blocks. `PRc` block 0 is pinned to 1; block `nb` IS
               `s_GIDX`.
  * `QUc m`  — the modular-reduction quotients (the `fqMulCore` witnesses).
  * `SBc p`  — the `p`-th binary digit of the derived scalar, MSB-first over `planes` planes — the
               same indexing `PastaMsmBound.scalarDigit` uses.
  * `SEc p`  — the plane selector: boolean, sums to 1, and `Σ p·SEc p = PIDX`. -/

/-- The base of everything this file adds. -/
def DB : Nat := WOC

/-- The row's bit-plane index. -/
def PIDX : Nat := DB
/-- The `j`-th binary digit of `GIDX`. -/
def GBc (j : Nat) : Nat := DB + 1 + j
/-- Challenge limb `m` (flat: `numLimbs*j + l`). -/
def CHc (nb m : Nat) : Nat := DB + 1 + nb + m
/-- Selected-multiplier limb `m`. -/
def MUc (nb m : Nat) : Nat := DB + 1 + nb + numLimbs * nb + m
/-- Running-product limb `m` (`nb + 1` blocks). -/
def PRc (nb m : Nat) : Nat := DB + 1 + nb + 2 * numLimbs * nb + m
/-- Reduction-quotient limb `m`. -/
def QUc (nb m : Nat) : Nat := DB + 1 + nb + 2 * numLimbs * nb + numLimbs * (nb + 1) + m
/-- The `p`-th binary digit of the derived scalar. -/
def SBc (nb p : Nat) : Nat := DB + 1 + nb + 4 * numLimbs * nb + numLimbs + p
/-- The `p`-th plane selector. -/
def SEc (nb planes p : Nat) : Nat := DB + 1 + nb + 4 * numLimbs * nb + numLimbs + planes + p
/-- The derived row template's width. -/
def WD (nb planes : Nat) : Nat :=
  DB + 1 + nb + 4 * numLimbs * nb + numLimbs + 2 * planes

/-- The columns this file adds, as a closed form: `10 + 37·nb + 2·planes`. -/
theorem WD_eq (nb planes : Nat) : WD nb planes = WOC + (10 + 37 * nb + 2 * planes) := by
  simp only [WD, DB, numLimbs]; omega

/-! ## §2 — THE EMITTED GATES. -/

/-! ### §2.1 — the plane thread.

`DBL` is 1 exactly on a plane-boundary row (`PastaMsmBound.bound_forces_doubling` /
`bound_forces_dbl_off`), so counting the doubling rows at or before row `i` counts the planes. The
thread reads the NEXT row's `DBL`, which is what makes `PIDX` agree with `planeAt` on the boundary
row itself rather than one row late. -/

/-- `PIDX = 0` on the FIRST row. -/
def pidxStartGate : VmConstraint2 := .base (.boundary .first (.var PIDX))

/-- `nxt PIDX − (loc PIDX + nxt DBL)` — the plane index advances exactly at a doubling row. -/
def pidxThreadGate : VmConstraint2 :=
  cw (.add (.nxt PIDX) (.mul (.const (-1)) (.add (.loc PIDX) (.nxt DBL))))

/-! ### §2.2 — the index digits. -/

/-- `GIDX − Σ_j 2^j · GBc j` — the index recomposition. -/
def gidxBitsGate (nb : Nat) : VmConstraint2 :=
  cgH ((List.range nb).foldl (fun h j => h.addLin (-(2 ^ j : ℤ)) (GBc j)) (Head.lin 1 GIDX))

/-- The index digits' booleanity plus their recomposition. -/
def gidxBitGates (nb : Nat) : List VmConstraint2 :=
  (List.range nb).map (fun j => binGate (GBc j)) ++ [gidxBitsGate nb]

/-! ### §2.3 — the challenges, ON THE WIRE.

`nb` field elements at 9 limbs each are `9·nb` public-input slots, pinned on the first row and
threaded down the trace so every row reads the same challenge vector. -/

/-- The PI count a derived descriptor declares: the sliced 29 plus `9·nb` challenge limbs. -/
def PID (nb : Nat) : Nat := PI_COUNT + numLimbs * nb

/-- Challenge limb pins on the first row. -/
def chalPinGates (nb : Nat) : List VmConstraint2 :=
  (List.range (numLimbs * nb)).map (fun m => pinPi (CHc nb m) (PI_COUNT + m))

/-- …and the threads that carry them to every other row. A first-row pin ALONE would leave the
challenge columns FREE on rows 1.., which is exactly the shape that makes a derivation look
verified while a prover picks a fresh challenge vector per row. -/
def chalThreadGates (nb : Nat) : List VmConstraint2 :=
  (List.range (numLimbs * nb)).map (fun m =>
    cw (.add (.nxt (CHc nb m)) (.mul (.const (-1)) (.loc (CHc nb m)))))

/-! ### §2.4 — the tensor chain.

`sAt (c :: rest) i = (if testBit i rest.length then c else 1) * sAt rest i`, so the HEAD challenge
pairs with the HIGH index bit. Step `j` therefore selects on `GBc (nb − 1 − j)`. -/

/-- Limb `m`'s selection head: `MU − b·CH − δ·(1 − b)`, with `b = GBc (nb−1−m/numLimbs)` and
`δ = [m % numLimbs = 0]`. Zero forces the selected multiplier to be `c_j` at `b = 1` and the field
ONE at `b = 0`. -/
def mulSelHead (nb m : Nat) : Head :=
  let b := GBc (nb - 1 - m / numLimbs)
  let d : ℤ := if m % numLimbs = 0 then 1 else 0
  (((Head.lin 1 (MUc nb m)).addProd (-1) [b, CHc nb m]).addLin d b).addConst (-d)

/-- The `9·nb` selection gates. -/
def mulSelGates (nb : Nat) : List VmConstraint2 :=
  (List.range (numLimbs * nb)).map (fun m => cgH (mulSelHead nb m))

/-- `PRc 0 − 1` — the chain starts at the field ONE. -/
def prdOneGate (nb : Nat) : VmConstraint2 := cgH ((fpValue (PRc nb 0)).addConst (-1))

/-- `PR j · MU j ≡ PR (j+1) (mod q)` — the deployed `PastaField.fqMulCore`, `nb` times. Nothing new
is authored: this is the same modular-multiplication gate the RCB block already uses, at the Pallas
SCALAR modulus, which is the field the s-vector lives in. -/
def chainGates (nb : Nat) : List VmConstraint2 :=
  (List.range nb).map (fun j =>
    Dregg2.Circuit.Emit.PastaField.fqMulCore
      (PRc nb (numLimbs * j)) (MUc nb (numLimbs * j))
      (PRc nb (numLimbs * (j + 1))) (QUc nb (numLimbs * j)))

/-! ### §2.5 — the DECOMPOSITION, and the plane read.

This is the half `PastaMsmScalarBound` §7.1 believed inexpressible, and it is inexpressible only in
the RE-composing direction. The row holds `s = PRc nb`; it witnesses all `planes` of its binary
digits MSB-first and pins their weighted sum to `s`. Booleanity plus that one equation is a
complete, ROW-LOCAL bit decomposition — and because the digits are boolean the sum lies in
`[0, 2^planes)`, which is what makes the reconstructed value CANONICAL rather than merely
congruent mod `q`. -/

/-- `Σ_p 2^(planes−1−p) · SBc p − s` — the MSB-first decomposition of the derived scalar. -/
def sBitsGate (nb planes : Nat) : VmConstraint2 :=
  cgH ((List.range planes).foldl
        (fun h p => h.addLin ((2 : ℤ) ^ (planes - 1 - p)) (SBc nb p))
        ((fpValue (PRc nb (numLimbs * nb))).scale (-1)))

/-- Booleanity for every digit, plus that decomposition. -/
def sBitGates (nb planes : Nat) : List VmConstraint2 :=
  (List.range planes).map (fun p => binGate (SBc nb p)) ++ [sBitsGate nb planes]

/-- `Σ_p SEc p − 1` — exactly one plane is selected. -/
def selOneGate (nb planes : Nat) : VmConstraint2 :=
  cgH ((List.range planes).foldl (fun h p => h.addLin 1 (SEc nb planes p)) (Head.c (-1)))

/-- `Σ_p p · SEc p − PIDX` — and it is the row's OWN plane. -/
def selIdxGate (nb planes : Nat) : VmConstraint2 :=
  cgH ((List.range planes).foldl
        (fun (h : Head) (p : Nat) => h.addLin ((p : ℤ)) (SEc nb planes p))
        (Head.lin (-1) PIDX))

/-- `(1 − DBL) · (BIT − Σ_p SEc p · SBc p)` — ⚑ **the join.** On a conditional-add row the emitted
conditional bit IS the selected digit of the DERIVED scalar.

⚠ The guard is load-bearing and is not decoration: a doubling row has `BIT = 1` forced by
`PastaMsmWindowed.dblPinGates`, so demanding `Σ SE·SB = 1` there would be a gate no honest trace
can satisfy — the exact shape of a constraint that is "true because nothing satisfies it". §5
exhibits an accepting doubling row, so the guard is known to bite rather than merely to be written. -/
def bitJoinHead (nb planes : Nat) : Head :=
  let core : Head :=
    (List.range planes).foldl (fun h p => h.addProd (-1) [SEc nb planes p, SBc nb p])
      (Head.lin 1 BIT)
  (core.mulByCol (-1) DBL).append core

/-- The selector's booleanity, its two pins, and the join. -/
def selGates (nb planes : Nat) : List VmConstraint2 :=
  (List.range planes).map (fun p => binGate (SEc nb planes p))
    ++ [selOneGate nb planes, selIdxGate nb planes, cgH (bitJoinHead nb planes)]

/-! ### §2.6 — the whole added block. -/

/-- The ROW-LOCAL derivation gates (every one a `.base (.gate _)`), in emission order. §5 decides
this list in the kernel at concrete rows, which is what makes the tampers measurements. -/
def deriveRowGates (nb planes : Nat) : List VmConstraint2 :=
  gidxBitGates nb ++ mulSelGates nb ++ (prdOneGate nb :: chainGates nb)
    ++ sBitGates nb planes ++ selGates nb planes

/-- The NON-row-local additions: the plane thread's origin pin and step, the challenge PI pins and
the challenge threads. -/
def deriveWireGates (nb : Nat) : List VmConstraint2 :=
  pidxStartGate :: pidxThreadGate :: (chalPinGates nb ++ chalThreadGates nb)

/-- Everything this file emits. -/
def deriveGates (nb planes : Nat) : List VmConstraint2 :=
  deriveWireGates nb ++ deriveRowGates nb planes

/-! ## §3 — THE DESCRIPTOR. -/

/-- ⚑⚑ **The SCALAR-DERIVED curve-gated contents-bound descriptor.**
`PastaMsmOnCurve.onCurveRowDesc`'s 98 constraints and its exact-public manifest verbatim, plus the
derivation block. Same table, same wire id, same manifest arity, same row count; `9·nb` more public
inputs and `10 + 37·nb + 2·planes` more columns.

⚑ **The manifest is retained deliberately, and it is now REDUNDANT.** Retaining it keeps the whole
tower's prefix property and keeps the generator / wrong-block-scalar / absorbing-state tampers live
on this same instance. What changed is that the digit column no longer DEPENDS on it: §4's forcing
never mentions `PublicLookupBalanced`. A manifest and a challenge vector that disagree now have NO
satisfying trace, which is a strictly stronger object than either half alone. -/
def deriveRowDesc (nb n k w planes : Nat) (gens : List Pt) (scal : List Nat) :
    EffectVmDescriptor2 :=
  { name        := "dregg-pasta-rcb-sg-derive-" ++ toString k ++ "-of-" ++ toString n ++ "::v1"
  , traceWidth  := WD nb planes
  , piCount     := PID nb
  , tables      := (onCurveRowDesc n k w planes gens scal).tables
  , constraints := (onCurveRowDesc n k w planes gens scal).constraints ++ deriveGates nb planes
  , hashSites   := []
  , ranges      := [] }

/-- ⚑ **`deriveRowDesc_extends_onCurve`** — the emitted list still has the CURVE-GATED descriptor's
98 constraints as a PREFIX, hence (transitively) `PastaMsmBound`'s 82, `PastaMsmSliced`'s 78 and
`PastaMsmWindowed`'s 45. Nothing was re-authored. -/
theorem deriveRowDesc_extends_onCurve (nb n k w planes : Nat) (gens : List Pt) (scal : List Nat) :
    (onCurveRowDesc n k w planes gens scal).constraints <+:
      (deriveRowDesc nb n k w planes gens scal).constraints :=
  ⟨deriveGates nb planes, rfl⟩

/-- …and the table is the same object, so the CONTENTS forcing is inherited, not restated. -/
theorem deriveRowDesc_tables (nb n k w planes : Nat) (gens : List Pt) (scal : List Nat) :
    (deriveRowDesc nb n k w planes gens scal).tables
      = (onCurveRowDesc n k w planes gens scal).tables := rfl

/-- The emitted constraint count: `8 + 29·nb + 2·planes` added. Still independent of the ROW
count — it moves with the challenge count and the plane count, and with nothing else. -/
theorem deriveGates_length (nb planes : Nat) :
    (deriveGates nb planes).length = 8 + 29 * nb + 2 * planes := by
  simp only [deriveGates, deriveWireGates, deriveRowGates, gidxBitGates, chalPinGates,
    chalThreadGates, mulSelGates, chainGates, sBitGates, selGates, List.length_append,
    List.length_cons, List.length_nil, List.length_map, List.length_range, numLimbs]
  omega

theorem deriveRowDesc_constraints_length (nb n k w planes : Nat) (gens : List Pt)
    (scal : List Nat) :
    (deriveRowDesc nb n k w planes gens scal).constraints.length
      = 98 + (8 + 29 * nb + 2 * planes) := by
  simp [deriveRowDesc, deriveGates_length,
    Dregg2.Circuit.Emit.PastaMsmOnCurve.onCurveRowDesc_constraints_length]

set_option maxRecDepth 1000000 in
/-- ⚑ **`deriveRowDesc_columns_in_bounds`** — every column every emitted constraint addresses,
including the chain's degree-2 cross products and the selector's degree-3 join, is `≤ traceWidth`.
This is `descriptor_ir2.rs`'s `chk` closure, decided in the kernel before the prover sees it. -/
theorem deriveRowDesc_columns_in_bounds :
    (deriveRowDesc 2 4 0 2 4 [] []).constraints.all
        (fun c => decide (bMaxVar c ≤ (deriveRowDesc 2 4 0 2 4 [] []).traceWidth)) = true := by
  decide

set_option maxRecDepth 1000000 in
/-- ⚑ **`deriveRowDesc_pi_indices_in_bounds`** — every `pi_binding` names a DECLARED public input.
This is the reason `PID` exists: the `9·nb` challenge pins name slots 29.., and against the sliced
descriptor's `piCount = 29` `descriptor_ir2.rs:1597-1607` refuses exactly that. -/
theorem deriveRowDesc_pi_indices_in_bounds :
    (deriveRowDesc 2 4 0 2 4 [] []).constraints.all
        (fun c => decide (sMaxPi c ≤ (deriveRowDesc 2 4 0 2 4 [] []).piCount)) = true := by decide

#guard (deriveRowDesc 2 4 0 2 4 [] []).traceWidth == 891
#guard (deriveRowDesc 2 4 0 2 4 [] []).piCount == 47
#guard (deriveRowDesc 2 4 0 2 4 [] []).constraints.length == 172
#guard (deriveRowDesc 2 4 2 2 4 [] []).name == "dregg-pasta-rcb-sg-derive-2-of-4::v1"
-- ⚑ THE PRICE AT THE DEPLOYED SHAPE, as an object: 15 challenges, 255 bit planes.
#guard WD 15 255 - WOC == 1075
#guard 8 + 29 * 15 + 2 * 255 == 953

#assert_axioms WD_eq
#assert_axioms deriveRowDesc_extends_onCurve
#assert_axioms deriveGates_length
#assert_axioms deriveRowDesc_constraints_length
#assert_axioms deriveRowDesc_columns_in_bounds
#assert_axioms deriveRowDesc_pi_indices_in_bounds

/-! ## §4 — THE FORCING, ROW-COUNT-INDEPENDENT.

Every statement below is about ONE row and quantifies `nb`, `planes`, `j` and `p` universally, with
none of them occurring in a bound. There is no induction over the trace and no row count anywhere:
the whole derivation is row-local, which is exactly the property that made it expressible without
an IR change. The statement at `planes·(w+1) = 128` is the statement at `1,056,896`. -/

open Dregg2.Circuit.Emit.PastaScalarMul (acceptB_append acceptB_cons acceptB_prefix acceptB_suffix
  gateBodyEvalZero_cgH)

/-- The row's challenge `j`: the field element its 9 PI-bound limbs reconstruct. -/
def chalOf (a : Assignment) (nb j : Nat) : ℤ := fpVal a (CHc nb (numLimbs * j))
/-- The row's selected multiplier `j`. -/
def mulOf (a : Assignment) (nb j : Nat) : ℤ := fpVal a (MUc nb (numLimbs * j))
/-- The row's running product after `j` steps. `prdOf a nb nb` IS the derived scalar. -/
def prdOf (a : Assignment) (nb j : Nat) : ℤ := fpVal a (PRc nb (numLimbs * j))
/-- The index digit challenge `j` is selected by. -/
def gbOf (a : Assignment) (nb j : Nat) : ℤ := a (GBc (nb - 1 - j))

/-- A gate of a `map`ped family holds, in head form. -/
theorem head_of_map {α : Type} (a : Assignment) (L : List α) (g : α → Head)
    (h : acceptB (L.map (fun x => cgH (g x))) a = true) {x : α} (hx : x ∈ L) :
    evalH (g x) a = 0 := by
  rw [acceptB, List.all_eq_true] at h
  have hm : cgH (g x) ∈ L.map (fun x => cgH (g x)) := List.mem_map.mpr ⟨x, hx, rfl⟩
  have := h _ hm
  rw [gateBodyEvalZero_cgH] at this
  exact of_decide_eq_true this

/-- ⚑ **The nine-limb split**: if every limb of the block at `bM` is `g·(the limb at `bC`) + δ·(1−g)`
with `δ` the units indicator, then the block's VALUE is `g·(the value at `bC`) + (1−g)`. This is
what turns nine per-limb gates into one field-element statement. -/
theorem limb_split (a : Assignment) (bM bC : Nat) (g : ℤ)
    (h0 : a (bM + 0) = g * a (bC + 0) + (1 - g))
    (hr : ∀ i, i < numLimbs → i ≠ 0 → a (bM + i) = g * a (bC + i)) :
    fpVal a bM = g * fpVal a bC + (1 - g) := by
  have h1 := hr 1 (by decide) (by decide); have h2 := hr 2 (by decide) (by decide)
  have h3 := hr 3 (by decide) (by decide); have h4 := hr 4 (by decide) (by decide)
  have h5 := hr 5 (by decide) (by decide); have h6 := hr 6 (by decide) (by decide)
  have h7 := hr 7 (by decide) (by decide); have h8 := hr 8 (by decide) (by decide)
  rw [fpVal_as_sum, fpVal_as_sum]
  simp only [numLimbs, limbBits, List.range_succ, List.range_zero, List.map_append, List.map_cons,
    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, List.nil_append]
  linear_combination h0 + (2:ℤ)^30 * h1 + (2:ℤ)^60 * h2 + (2:ℤ)^90 * h3 + (2:ℤ)^120 * h4
    + (2:ℤ)^150 * h5 + (2:ℤ)^180 * h6 + (2:ℤ)^210 * h7 + (2:ℤ)^240 * h8

/-- ⚑ **`mulSel_forces`** — the emitted selection gates force the multiplier to be challenge `j`
when the index digit is 1 and the field ONE when it is 0. Nothing here is a hypothesis about the
prover: the digit's booleanity is forced separately (`gidxBitGates`), and either value of `gbOf`
gives a determinate multiplier. -/
theorem mulSel_forces (a : Assignment) (nb : Nat)
    (h : acceptB (mulSelGates nb) a = true) (j : Nat) (hj : j < nb) :
    mulOf a nb j = gbOf a nb j * chalOf a nb j + (1 - gbOf a nb j) := by
  -- The gate at flat limb index `numLimbs*j + i`, in evaluated form.
  have gate : ∀ i, i < numLimbs →
      a (MUc nb (numLimbs * j) + i)
        - gbOf a nb j * a (CHc nb (numLimbs * j) + i)
        + (if i = 0 then (1 : ℤ) else 0) * gbOf a nb j
        - (if i = 0 then (1 : ℤ) else 0) = 0 := by
    intro i hi
    have hlt : numLimbs * j + i < numLimbs * nb := by
      simp only [numLimbs] at hi ⊢
      have : j + 1 ≤ nb := hj
      nlinarith
    have hm : numLimbs * j + i ∈ List.range (numLimbs * nb) := List.mem_range.mpr hlt
    have hg := head_of_map a (List.range (numLimbs * nb)) (mulSelHead nb) h hm
    have hdiv : (numLimbs * j + i) / numLimbs = j := by
      simp only [numLimbs] at hi ⊢; omega
    have hmod : (numLimbs * j + i) % numLimbs = i := by
      simp only [numLimbs] at hi ⊢; omega
    simp only [mulSelHead, hdiv, hmod, evalH_addConst, evalH_addLin, evalH_addProd, evalH_lin,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil] at hg
    simp only [MUc, CHc, gbOf] at hg ⊢
    have hMU : DB + 1 + nb + numLimbs * nb + (numLimbs * j + i)
        = DB + 1 + nb + numLimbs * nb + numLimbs * j + i := by omega
    have hCH : DB + 1 + nb + (numLimbs * j + i) = DB + 1 + nb + numLimbs * j + i := by omega
    rw [hMU, hCH] at hg
    linarith
  refine limb_split a _ _ (gbOf a nb j) ?_ (fun i hi hi0 => ?_)
  · have := gate 0 (by decide); norm_num at this ⊢; linarith
  · have := gate i hi; simp only [if_neg hi0] at this; linarith

/-- ⚑ **`chain_forces`** — the emitted `fqMulCore` chain forces the running product to be the
TENSOR of the wire challenges, selected by the row's own index digits, in `ZMod q`. The induction is
over the CHALLENGE count, not the row count. -/
theorem chain_forces (a : Assignment) (nb : Nat)
    (h1 : evalH ((fpValue (PRc nb 0)).addConst (-1)) a = 0)
    (hc : acceptB (chainGates nb) a = true) (hm : acceptB (mulSelGates nb) a = true) :
    ∀ j, j ≤ nb →
      ((prdOf a nb j : ℤ) : ZMod qN)
        = ((List.range j).map (fun j' =>
            ((gbOf a nb j' * chalOf a nb j' + (1 - gbOf a nb j') : ℤ) : ZMod qN))).prod := by
  intro j
  induction j with
  | zero =>
    intro _
    simp only [List.range_zero, List.map_nil, List.prod_nil]
    have : prdOf a nb 0 = 1 := by
      simp only [prdOf, Nat.mul_zero]
      simp only [evalH_addConst, Dregg2.Circuit.Emit.PastaField.fpVal_eq] at h1
      omega
    rw [this]; norm_num
  | succ m ih =>
    intro hm1
    have hmn : m < nb := by omega
    have hmem : m ∈ List.range nb := List.mem_range.mpr hmn
    rw [acceptB, List.all_eq_true] at hc
    have hgate := hc _ (List.mem_map.mpr ⟨m, hmem, rfl⟩)
    rw [Dregg2.Circuit.Emit.PastaField.fqMulCore, gateBodyEvalZero_cgH] at hgate
    have hdvd := Dregg2.Circuit.Emit.PastaField.fqMulCore_forces a
      (PRc nb (numLimbs * m)) (MUc nb (numLimbs * m)) (PRc nb (numLimbs * (m + 1)))
      (QUc nb (numLimbs * m)) (of_decide_eq_true hgate)
    haveI : NeZero qN := ⟨by decide⟩
    have hstep : ((prdOf a nb (m + 1) : ℤ) : ZMod qN)
        = ((prdOf a nb m : ℤ) : ZMod qN) * ((mulOf a nb m : ℤ) : ZMod qN) := by
      have hz : ((fpVal a (PRc nb (numLimbs * m)) * fpVal a (MUc nb (numLimbs * m))
          - fpVal a (PRc nb (numLimbs * (m + 1))) : ℤ) : ZMod qN) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ qN).mpr
          (by simpa [Dregg2.Circuit.Emit.PastaField.q] using hdvd)
      simp only [prdOf, mulOf]
      push_cast at hz
      linear_combination -hz
    rw [hstep, ih (by omega), List.range_succ, List.map_append, List.prod_append]
    rw [mulSel_forces a nb hm m hmn]
    simp

/-! ### §4b — the plane read.

The selector's three gates make `BIT` the digit of the row's OWN plane, and the guard makes the
whole join silent on a doubling row (where `BIT` is pinned to 1 by the row template and no digit
statement could hold). -/

/-- An indicator-weighted sum over `List.range` reads the one entry it selects. -/
theorem sum_indicator (f : Nat → ℤ) (n pl : Nat) (hpl : pl < n) :
    ((List.range n).map (fun p => if p = pl then f p else 0)).sum = f pl := by
  induction n with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    by_cases hm : pl = m
    · subst hm
      have hz : ((List.range pl).map (fun p => if p = pl then f p else 0)).sum = 0 := by
        have hmap : (List.range pl).map (fun p => if p = pl then f p else 0)
            = (List.range pl).map (fun _ => (0 : ℤ)) :=
          List.map_congr_left (fun p hp => by
            rw [List.mem_range] at hp; simp [Nat.ne_of_lt hp])
        rw [hmap]; simp
      simp [hz]
    · have hpn : pl < m := by omega
      simp [ih hpn, Ne.symm hm]

/-- ⚑ **`sel_forces`** — on a CONDITIONAL-ADD row, the emitted (guarded) join makes `BIT` the
`pl`-th digit of the derived scalar's witnessed decomposition. `nb`, `planes` and `pl` are
universally quantified and occur in no bound.

⚠ **Named residual, not smuggled:** the selector's SHAPE (`SEc` is the indicator at `pl`) is a
HYPOTHESIS here. The emitted `selOneGate`/`selIdxGate` plus the selector booleanity DO force it —
boolean columns summing to 1 have exactly one 1, and `Σ p·SEc p = PIDX` says which — but that
"exactly one" argument is not discharged in this file. §5 exhibits the tamper (`SEc` bumped, `PIDX`
bumped) being refused over the emitted gates, so the gates are known live; the missing piece is the
proof, not the constraint. -/
theorem sel_forces (a : Assignment) (nb planes pl : Nat)
    (h : acceptB (selGates nb planes) a = true)
    (hdbl : a DBL = 0) (hpl : pl < planes)
    (hsel : ∀ p, p < planes → a (SEc nb planes p) = if p = pl then 1 else 0) :
    a BIT = a (SBc nb pl) := by
  have hj : evalH (bitJoinHead nb planes) a = 0 := by
    have hs : acceptB [selOneGate nb planes, selIdxGate nb planes, cgH (bitJoinHead nb planes)]
        a = true := acceptB_suffix _ _ a h
    rw [acceptB, List.all_eq_true] at hs
    have hmem := hs (cgH (bitJoinHead nb planes)) (by simp)
    rw [gateBodyEvalZero_cgH] at hmem
    exact of_decide_eq_true hmem
  simp only [bitJoinHead, evalH_append, evalH_mulByCol, hdbl, evalH_foldl_addProdF, evalH_lin,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil] at hj
  have hcong : (List.range planes).map (fun x => a (SEc nb planes x) * (a (SBc nb x) * 1))
      = (List.range planes).map (fun p => if p = pl then a (SBc nb p) else 0) :=
    List.map_congr_left (fun p hp => by
      rw [List.mem_range] at hp
      rw [hsel p hp]
      by_cases hpp : p = pl <;> simp [hpp])
  rw [hcong, sum_indicator (fun p => a (SBc nb p)) planes pl hpl] at hj
  linarith

#assert_axioms head_of_map
#assert_axioms limb_split
#assert_axioms mulSel_forces
#assert_axioms chain_forces
#assert_axioms sum_indicator
#assert_axioms sel_forces

/-! ## §5 — ⚑⚑ THE GATES BITE: SATISFIABLE, and a CHALLENGE-INCONSISTENT DIGIT IS REFUSED.

A forcing theorem whose hypothesis nothing satisfies is TRUE AND EMPTY, and a tamper the
denotation cannot see is not a tooth. Both polarities are decided in the kernel over the ACTUALLY
EMITTED `deriveRowGates`, at `nb = 2, planes = 4` — two challenges, so a whole s-vector is four
entries and every one of them fits four bit planes.

⚠ The two challenge lists are chosen so their s-vectors DIFFER at an index the row reads and both
stay inside `2^planes`: `[3,5] ↦ [1,5,3,15]`, `[3,4] ↦ [1,4,3,12]`. -/

/-- Challenge `j`'s SELECTED multiplier at index `idx`, at `nb = 2`. Mirrors `mulSelHead`'s pairing:
challenge `j` is selected by index bit `nb − 1 − j`. -/
def katMul (ds : List Nat) (idx j : Nat) : Nat :=
  if Nat.testBit idx (2 - 1 - j) then ds.getD j 1 else 1

/-- The derived scalar at `idx`: the tensor, two factors. -/
def katS (ds : List Nat) (idx : Nat) : Nat := katMul ds idx 0 * katMul ds idx 1

/-- Its `p`-th binary digit, MSB-first over 4 planes — `PastaMsmBound.scalarDigit`'s indexing. -/
def katBit (ds : List Nat) (idx p : Nat) : Nat := katS ds idx / 2 ^ (4 - 1 - p) % 2

/-- ⚑ **The exhibited row, with the WIRE challenges and the DIGIT challenges kept SEPARATE.**
`cs` fills the `CHc` columns — the PI-bound, threaded challenge vector, i.e. what the verifier sees.
`ds` fills the multiplier, product and digit columns — i.e. what the prover claims the scalar is.
An honest row is `cs = ds`; the forgery is `cs ≠ ds`, and it is the whole tamper. -/
def katAsg (cs ds : List Nat) (idx pl : Nat) : Assignment := fun c =>
  if c = GIDX then (idx : ℤ)
  else if c = BIT then ((katBit ds idx pl : Nat) : ℤ)
  else if c = PIDX then (pl : ℤ)
  else if c = GBc 0 then ((idx % 2 : Nat) : ℤ)
  else if c = GBc 1 then ((idx / 2 % 2 : Nat) : ℤ)
  else if c = CHc 2 0 then ((cs.getD 0 1 : Nat) : ℤ)
  else if c = CHc 2 numLimbs then ((cs.getD 1 1 : Nat) : ℤ)
  else if c = MUc 2 0 then ((katMul ds idx 0 : Nat) : ℤ)
  else if c = MUc 2 numLimbs then ((katMul ds idx 1 : Nat) : ℤ)
  else if c = PRc 2 0 then 1
  else if c = PRc 2 numLimbs then ((katMul ds idx 0 : Nat) : ℤ)
  else if c = PRc 2 (2 * numLimbs) then ((katS ds idx : Nat) : ℤ)
  else if SBc 2 0 ≤ c ∧ c < SBc 2 0 + 4 then ((katBit ds idx (c - SBc 2 0) : Nat) : ℤ)
  else if SEc 2 4 0 ≤ c ∧ c < SEc 2 4 0 + 4 then (if c - SEc 2 4 0 = pl then 1 else 0)
  else 0

/-- A one-cell perturbation. -/
def bump (a : Assignment) (c : Nat) : Assignment := fun x => if x = c then a x + 1 else a x

/-- THIS block's challenges. -/
def katC : List Nat := [3, 5]
/-- ⚑ A DIFFERENT block's challenges: one round's challenge differs. -/
def katC' : List Nat := [3, 4]

-- The two s-vectors, in the kernel, and they DISAGREE at the index the exhibited row reads.
#guard ((List.range 4).map (katS katC)) == [1, 5, 3, 15]
#guard ((List.range 4).map (katS katC')) == [1, 4, 3, 12]
#guard katS katC 1 != katS katC' 1
-- …and the derived scalar IS the tensor `PastaMsmScalarBound.sAt` reads out of `PastaIPA.sVec`:
-- the `#guard` is against THAT file's own `katC` (`[(3 : Fq), (5 : Fq)]`), not a retranscription,
-- and `sVec_getElem?_eq_sAt` proves `sAt` is the s-vector's entry.
#guard ((List.range 4).map (katS katC))
         == ((List.range 4).map
               (fun i => (sAt Dregg2.Circuit.Emit.PastaMsmScalarBound.katC i).val))

-- ⚑ SATISFIABLE — an honest conditional-add row: the wire challenges and the digits agree, the
-- 2-step chain reproduces the tensor, the decomposition holds, and the plane selector reads the
-- row's own plane. The forcing below is therefore not true-because-empty.
#guard acceptB (deriveRowGates 2 4) (katAsg katC katC 1 2)
#guard acceptB (deriveRowGates 2 4) (katAsg katC katC 3 0)
#guard acceptB (deriveRowGates 2 4) (katAsg katC katC 0 3)

-- ⚑⚑ REFUTABLE — **THE CHALLENGE-INCONSISTENT DIGIT.** Every column of this row is internally
-- consistent with the OTHER block's challenges — its multipliers, its product, its 4 digits and its
-- `BIT` all agree with each other — and the only thing that disagrees is the challenge vector ON
-- THE WIRE. REFUSED by the emitted gates. This is the rung's defining test.
#guard ! acceptB (deriveRowGates 2 4) (katAsg katC katC' 1 2)
#guard ! acceptB (deriveRowGates 2 4) (katAsg katC katC' 1 0)

-- ⚑ …AND THE FORGERY IS INTERNALLY CONSISTENT: the same digit column, with the OTHER block's
-- challenges on the wire, is ACCEPTED. So what refuses it above is the binding to this block's
-- challenges, not a malformity — the polarity `PastaMsmScalarBound` §6b establishes for the
-- manifest half, established here for the DERIVED half.
#guard acceptB (deriveRowGates 2 4) (katAsg katC' katC' 1 2)
-- …and symmetrically.
#guard ! acceptB (deriveRowGates 2 4) (katAsg katC' katC 1 2)

-- ⚑ REFUTABLE — the CONDITIONAL BIT alone. Everything else honest; only `BIT` moves.
#guard ! acceptB (deriveRowGates 2 4) (bump (katAsg katC katC 1 2) BIT)
-- ⚑ REFUTABLE — a CHALLENGE LIMB alone. The wire moves; the derivation does not follow.
#guard ! acceptB (deriveRowGates 2 4) (bump (katAsg katC katC 1 2) (CHc 2 numLimbs))
-- ⚑ REFUTABLE — the PRODUCT alone: a prover who writes the scalar it wants rather than the one the
-- chain computes.
#guard ! acceptB (deriveRowGates 2 4) (bump (katAsg katC katC 1 2) (PRc 2 (2 * numLimbs)))
-- ⚑ REFUTABLE — the PLANE INDEX alone: reading the right scalar's digit at the WRONG plane. This is
-- the tooth that makes `PIDX` load-bearing rather than decorative.
#guard ! acceptB (deriveRowGates 2 4) (bump (katAsg katC katC 1 2) PIDX)
-- ⚑ REFUTABLE — the SELECTOR alone: selecting a plane the row is not in.
#guard ! acceptB (deriveRowGates 2 4) (bump (katAsg katC katC 1 2) (SEc 2 4 0))

/-! ### §5b — the guard on the join BITES, and is not decoration.

A doubling row has `BIT = 1` pinned by `PastaMsmWindowed.dblPinGates`. An UNGUARDED join would
demand `Σ SE·SB = 1` there — a gate no honest trace can satisfy, i.e. a gadget that is true only
because nothing satisfies it. The guarded join accepts the honest doubling row; the same row with
`DBL` taken to 0 is refused, which is what shows the guard is doing work rather than hiding a hole. -/

/-- The honest DOUBLING row: `DBL = 1`, `BIT = 1` pinned, plane 0, scalar `s_0 = 1` (digits 0001),
selector on plane 0 — whose digit is 0, so the join would fail were it not guarded. -/
def katDbl : Assignment := fun c =>
  if c = DBL then 1 else if c = BIT then 1 else katAsg katC katC 0 0 c

#guard acceptB (deriveRowGates 2 4) katDbl
-- ⚑ …and with the guard OFF (the same cells, `DBL = 0`) the very same row is REFUSED — so the
-- guard is the reason the doubling row passes, and the join is live everywhere else.
#guard ! acceptB (deriveRowGates 2 4) (fun c => if c = BIT then 1 else katAsg katC katC 0 0 c)

end Dregg2.Circuit.Emit.PastaMsmScalarDerive
