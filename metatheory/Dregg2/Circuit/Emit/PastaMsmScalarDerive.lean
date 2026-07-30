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
one. The committed area — which is what FRI pays for — is identical either way. §6.3 prices both
against the deployed four-way cut, in the kernel.

The one shape that IS cheaper is a SEPARATE, SHORTER instance (`w + 1` rows, not `planes·(w+1)`)
tied to the MSM rows by a bus. That needs a `provide` dual of `Lookup`, which this IR does not have
(`descriptor_ir2.rs`'s main arm calls `LookupBus::lookup_key` with multiplicity `ONE` and never
`table_entry`). §6.3 names it as the cost rung, with its price.

## ⚑⚑ The third half: THE WIRE GATES FORCE, they are no longer ASSUMED

`deriveWireGates` emits four objects — the plane thread's origin pin and step, the challenge PI pins
and the challenge threads. Until §4e existed they appeared in exactly ONE theorem in this file, and
that theorem was `deriveGates_length`, a COUNTING lemma; `derived_is_sNat` took their content as raw
hypotheses (`hwire`, `hpidx`). The module emitted the gates and assumed what they were supposed to
force. §4e discharges both in `PastaMsmBound.tidxThread_forces` / `tidx_is_the_row_index`'s shape —
`wire_forces_challenges` for the challenges, `pidx_is_the_plane_index` for the plane — and §4f is
the trace-level capstone with neither hypothesis carried. §5d exhibits an accepting eight-row trace
and the forgery the thread kills (a prover using a FRESH CHALLENGE VECTOR PER ROW, which the
row-local denotation accepts and the wire gates refuse).

⚑ **This is what fixed the redundancy claim.** `derived_row_bit_is_manifest_digit` used to hold for
the manifest's INDEX argument and not for its PLANE argument, because `pl` was a parameter a caller
named while the manifest declares row `i`'s digit at `planeAt w i`. The row-local statement survives
as `derived_row_bit_is_manifest_digit_at_a_named_plane`, which says so; the unqualified name is now
§4f's, which reproduces BOTH arguments from the emitted object.

⚠ **§6 is the residual list** — the first one this module has had. Read it before citing anything
here, and §6.2 first: nothing in this descriptor says the declared public inputs ARE the block's
transcript challenges.

## The chain, and what it is anchored to

`PastaMsmScalarBound.sAt` reads the `i`-th s-vector entry in `|cs|` multiplications, and
`sVec_getElem?_eq_sAt` proves it IS `(PastaIPA.sVec cs)[i]`, which `sVec_eq_bPoly` proves is the
coefficient vector of `b(X) = ∏_j (1 + c_j X^{2^j})`. This file emits that product as a gate chain:
`PR 0 = 1`, `PR (j+1) ≡ PR j · MU j (mod q)`, with `MU j` the SELECTED multiplier — `c_j` when the
`(nb−1−j)`-th binary digit of the row's own `GIDX` is set, `1` otherwise. `GIDX` is the ABSOLUTE
generator index `PastaMsmBound.bound_forces_gidx` already forces onto the row, so the chain is
evaluated at the index the row actually consumes.

## ⚑⚑ The second half: the value is CANONICAL, so the digits are the S-VECTOR'S

A chain of `fqMulCore` steps forces a RESIDUE CLASS mod `q`, not a number, and `9b88bc06e` measured
what that costs at the deployed shape: five representatives fit the 256-plane digit budget, `s` and
`s+q` differ at 58 planes, and only the descriptor's MANIFEST refused an internally consistent
non-canonical row. §2.7 closes it with the standard less-than-the-modulus certificate,
`s + Σ_{p<255} 2^p·CBc p = q − 1` over `CBITS = 255` boolean columns, and §4d turns that into the
two bridges the previous rung could not write:

  * `canon_forces` — `0 ≤ s < q`, so the class has exactly one representative on the row;
  * `sBits_are_the_digits` / `gidxBits_are_testBits` — boolean decompositions are UNIQUE, so the
    witnessed digit columns are the binary expansions they claim to be;
  * `derived_is_sNat` — therefore the landing value IS `PastaMsmScalarBound.sNat cs GIDX`, and
    `derived_row_bit_is_block_svec_bit` ranges over the CANONICAL s-vector rather than over a
    witnessed decomposition.

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
  TableId TableDef VmTrace lookupLog PublicLookupBalanced)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.AirBuilder
open Dregg2.Circuit.Emit.PastaField (pN qN numLimbs limbBits fpValue fpVal acceptB)
open Dregg2.Circuit.Emit.PastaMsmWindowed (WTrace envOf cw BIT DBL fpVal_as_sum)
open Dregg2.Circuit.Emit.PastaMsmSliced (sliceLo PI_COUNT sMaxPi)
open Dregg2.Circuit.Emit.PastaMsmBound (Pt TIDX GIDX bMaxVar termAt planeAt scalarDigit rowAt
  tupleOf manifestRow boundRowDesc isNotLookup filterMap_of_noLookup)
open Dregg2.Circuit.Emit.PastaMsmOnCurve (WOC onCurveRowDesc onCurveRowGates)
open Dregg2.Circuit.Emit.PastaMsmScalarBound (sAt sFactors sNat sScalars)
open Dregg2.Circuit.Emit.MinaWrapOpeningGate (Fq)

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
  * `SEc p`  — the plane selector: boolean, sums to 1, and `Σ p·SEc p = PIDX`.
  * `CBc p`  — ⚑ the CANONICITY certificate: `CBITS = 255` boolean columns whose weighted sum is
               `q − 1 − s` (§2.7). This is the block that makes the derived value THE s-vector
               entry rather than one of its five representatives inside the digit budget. -/

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

/-- ⚑⚑ **The canonicity certificate's width — THE CONSTANT 255, NEVER `planes`.**

`q < 2^255`, so `q − 1 − s` needs exactly 255 boolean places and no more. Writing `planes` here
instead would be the classic gadget-that-nothing-satisfies: at `planes = 4` the certificate's
budget is `[0, 15]` while `q − 1 − s` is a 255-bit number, and the gate would refuse EVERY honest
trace at every small plane count — including the `nb = 2, planes = 4` kernel exhibits of §5, which
is where it would be caught, and the deployed `planes = 256` shape, which is where it would not.
The two counts are independent and only one of them is a property of the FIELD. -/
def CBITS : Nat := 255

/-- The `p`-th bit of the canonicity certificate `q − 1 − s`, LSB-first. -/
def CBc (nb planes p : Nat) : Nat :=
  DB + 1 + nb + 4 * numLimbs * nb + numLimbs + 2 * planes + p

/-- The derived row template's width. -/
def WD (nb planes : Nat) : Nat :=
  DB + 1 + nb + 4 * numLimbs * nb + numLimbs + 2 * planes + CBITS

/-- The columns this file adds, as a closed form: `265 + 37·nb + 2·planes` (the `10 + 37·nb +
2·planes` of the derivation proper, plus `CBITS = 255` for the canonicity certificate). -/
theorem WD_eq (nb planes : Nat) : WD nb planes = WOC + (265 + 37 * nb + 2 * planes) := by
  simp only [WD, DB, numLimbs, CBITS]; omega

/-! ## §2 — THE EMITTED GATES. -/

/-! ### §2.1 — the plane thread.

`DBL` is 1 exactly on a plane-boundary row (`PastaMsmBound.bound_forces_doubling` /
`bound_forces_dbl_off`), so counting the doubling rows at or before row `i` counts the planes. The
thread reads the NEXT row's `DBL`, which is what makes `PIDX` agree with `planeAt` on the boundary
row itself rather than one row late.

⚑ **§4e proves this paragraph rather than asserting it:** `pidx_counts_doublings` (the count, from
these two gates alone and no `DBL` hypothesis) and `pidx_is_the_plane_index` (`PIDX = planeAt w i`,
under the pattern the rung below forces). Until §4e existed, both gates appeared in exactly one
theorem in this file and that theorem was `deriveGates_length`. -/

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
verified while a prover picks a fresh challenge vector per row.

⚑ **That sentence is now a theorem and a measurement, not a warning.** `chal_is_the_wire` (§4e)
proves the pin plus these threads put the declared public inputs on EVERY row, and §5d's
`katSwapRow1` exhibits the forgery: a row deriving completely and consistently against a different
block's challenges, which `acceptB (deriveRowGates 2 4)` ACCEPTS and these threads REFUSE. -/
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
complete, ROW-LOCAL bit decomposition, and `sBits_unique` proves the digits are then FORCED — they
are the binary expansion of `s`, not merely *a* decomposition of it.

⚠ **RETRACTED, and the retraction is why §2.7 exists.** An earlier revision of this paragraph said
that booleanity alone makes the reconstructed value "CANONICAL rather than merely congruent mod
`q`". That is FALSE at the deployed shape and the commit that measured it says so: booleanity pins
`s` into `[0, 2^planes)`, `planes = 256` and `q < 2^255`, so `s, s+q, s+2q, s+3q, s+4q` ALL fit —
and because `fqMulCore` witnesses a QUOTIENT, shifting the landing block by `q` and the last
quotient block by `1` leaves the chain gate exactly zero over ℤ. Measured on the deployed instance:
`s` and `s+q` differ at 58 of the 256 planes. **The decomposition is canonical because of §2.7's
certificate, and for no other reason.** -/

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

/-! ### §2.7 — ⚑⚑ THE CANONICITY CERTIFICATE.

`chainGates` forces `s ≡ ∏_j c_j^{bit_j(GIDX)} (mod q)` and nothing more: a congruence class, not a
number. `sBitGates` forces `s ∈ [0, 2^planes)`, which at `planes = 256` admits five members of that
class. The gap is closed by the standard **less-than-the-modulus certificate**: witness `q − 1 − s`
in `CBITS = 255` boolean places.

    s + Σ_{p < 255} 2^p · CBc p = q − 1

Booleanity makes the certificate's value non-negative, so the gate forces `s ≤ q − 1`; `sBitGates`
makes `s` non-negative; together `0 ≤ s < q`, and a residue class has exactly one representative
there. `canon_forces` proves that over the emitted list, and `derived_is_sNat` is what it buys:
the chain's landing value IS `PastaMsmScalarBound.sNat`, the `Nat` the manifest carries.

⚑ **SATISFIABLE, and that is not a formality here.** The certificate is an upper bound the honest
prover can always meet — `s < q` for any real s-vector entry, so `q − 1 − s ≥ 0` and its 255 bits
exist. §5 exhibits an accepting row carrying them, and §5b an accepting DOUBLING row, so this is
not a gate that is true because nothing satisfies it. The witness generator writes exactly
`q − 1 − s`; there is no search.

⚠ **The residual this does NOT close is K1, inherited unchanged.** Everything above is the ℤ
reading of the emitted bodies (`PastaField.acceptB`), which is the model every forcing theorem in
this tower is stated in. The deployed prover reads the same bodies in BabyBear, where a weighted
boolean sum can wrap; `PastaMsmWindowed` §6.2 names that gap and this rung does not narrow it. What
this rung closes is the gap that was open IN THE ℤ MODEL ITSELF. -/

/-- `s + Σ_p 2^p · CBc p − (q − 1)` — the less-than-the-modulus certificate, LSB-first. -/
def canonHead (nb planes : Nat) : Head :=
  (List.range CBITS).foldl (fun h p => h.addLin ((2 : ℤ) ^ p) (CBc nb planes p))
    ((fpValue (PRc nb (numLimbs * nb))).addConst (1 - (qN : ℤ)))

/-- The certificate's booleanity plus the bound gate: `CBITS + 1 = 256` constraints. -/
def canonGates (nb planes : Nat) : List VmConstraint2 :=
  (List.range CBITS).map (fun p => binGate (CBc nb planes p)) ++ [cgH (canonHead nb planes)]

/-! ### §2.6 — the whole added block. -/

/-- The ROW-LOCAL derivation gates (every one a `.base (.gate _)`), in emission order. §5 decides
this list in the kernel at concrete rows, which is what makes the tampers measurements. -/
def deriveRowGates (nb planes : Nat) : List VmConstraint2 :=
  gidxBitGates nb ++ mulSelGates nb ++ (prdOneGate nb :: chainGates nb)
    ++ sBitGates nb planes ++ selGates nb planes ++ canonGates nb planes

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

⚑ **The manifest is retained, and exactly ONE of its four fields is now redundant.** The manifest
row is `(key, gidx, digit, x‖y‖z limbs)`. §4d proves the trace's `BIT` is the block s-vector's bit
with no reference to `PublicLookupBalanced` at all, so the **`digit` field** is now derived twice
and the second copy checks nothing a satisfying trace could violate. The other three fields are
load-bearing and nothing else in the emitted list touches them: **no gate relates a generator INDEX
to generator COORDINATES.** Delete the manifest and the substituted-generator forgery — the same
row key, the same digit, a DIFFERENT real SRS point — has a satisfying trace. So the manifest stays;
what changed is *which* forgery it is the only defence against, and that list is now one item long. -/
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

/-- The emitted constraint count: `264 + 29·nb + 2·planes` added (`8 + 29·nb + 2·planes` for the
derivation, `CBITS + 1 = 256` for the canonicity certificate). Still independent of the ROW count —
it moves with the challenge count and the plane count, and with nothing else. -/
theorem deriveGates_length (nb planes : Nat) :
    (deriveGates nb planes).length = 264 + 29 * nb + 2 * planes := by
  simp only [deriveGates, deriveWireGates, deriveRowGates, gidxBitGates, chalPinGates,
    chalThreadGates, mulSelGates, chainGates, sBitGates, selGates, canonGates, CBITS,
    List.length_append, List.length_cons, List.length_nil, List.length_map, List.length_range,
    numLimbs]
  omega

theorem deriveRowDesc_constraints_length (nb n k w planes : Nat) (gens : List Pt)
    (scal : List Nat) :
    (deriveRowDesc nb n k w planes gens scal).constraints.length
      = 98 + (264 + 29 * nb + 2 * planes) := by
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

#guard (deriveRowDesc 2 4 0 2 4 [] []).traceWidth == 1146
#guard (deriveRowDesc 2 4 0 2 4 [] []).piCount == 47
#guard (deriveRowDesc 2 4 0 2 4 [] []).constraints.length == 428
#guard (deriveRowDesc 2 4 2 2 4 [] []).name == "dregg-pasta-rcb-sg-derive-2-of-4::v1"
-- ⚑ THE PRICE AT THE DEPLOYED SHAPE, as an object: 15 challenges, 256 bit planes. The canonicity
-- certificate is `+255` columns and `+256` constraints, flat, at every shape.
#guard WD 15 256 == 2131
#guard 98 + (264 + 29 * 15 + 2 * 256) == 1309
#guard WD 15 256 - (WD 15 256 - CBITS) == 255

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

⚠ **The selector's SHAPE (`SEc` is the indicator at `pl`) is a HYPOTHESIS in THIS lemma, and it is
DISCHARGED in the next section** — `sel_shape_forced` proves it from the emitted `selOneGate`,
`selIdxGate` and the selector booleanity, and `sel_forces_closed` is this lemma with it gone. Use
`sel_forces_closed`. (An earlier revision of this paragraph said the "exactly one" argument "is not
discharged in this file"; §4c discharged it and the sentence outlived its referent.) §5 exhibits
the tamper (`SEc` bumped, `PIDX` bumped) being refused over the emitted gates. -/
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

/-! ### §4c — ⚑⚑ THE SELECTOR'S SHAPE IS FORCED, not assumed.

`sel_forces` above takes "`SEc` is the indicator at `pl`" as a hypothesis and says so. It is
DERIVABLE from the two emitted pins plus the selector's booleanity, and the derivation is here, so
`sel_forces_closed` below has no shape hypothesis at all — only "the row's plane is `pl`", which is
what `PIDX` means. -/

/-- Booleanity, read off a `map`ped `binGate` family at any member. -/
theorem bool_of_map (a : Assignment) (L : List Nat) (f : Nat → Nat)
    (h : acceptB (L.map (fun p => binGate (f p))) a = true) {p : Nat} (hp : p ∈ L) :
    a (f p) = 0 ∨ a (f p) = 1 := by
  rw [acceptB, List.all_eq_true] at h
  have hm : binGate (f p) ∈ L.map (fun p => binGate (f p)) := List.mem_map.mpr ⟨p, hp, rfl⟩
  have hz := h _ hm
  simp only [binGate, cg, Dregg2.Circuit.Emit.PastaField.gateBodyEvalZero] at hz
  exact (gBin_eval_zero_iff a (f p)).mp (of_decide_eq_true hz)

/-- A list of non-negative integers summing to zero is all zeros. -/
theorem all_zero_of_sum_zero (L : List ℤ) (hnn : ∀ x ∈ L, 0 ≤ x) (h : L.sum = 0) :
    ∀ x ∈ L, x = 0 := by
  induction L with
  | nil => intro x hx; simp at hx
  | cons y ys ih =>
    have hy : 0 ≤ y := hnn y (by simp)
    have hys : 0 ≤ ys.sum := List.sum_nonneg (fun x hx => hnn x (by simp [hx]))
    rw [List.sum_cons] at h
    have hy0 : y = 0 := by linarith
    have hs0 : ys.sum = 0 := by linarith
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hy0
    · exact ih (fun z hz => hnn z (by simp [hz])) hs0 x hx'

/-- ⚑ **Boolean columns summing to 1 have EXACTLY ONE 1.** This is the "exactly one" argument the
first revision of `sel_forces` named as missing. -/
theorem bool_sum_one_unique (n : Nat) (e : Nat → ℤ) (hb : ∀ p, p < n → e p = 0 ∨ e p = 1)
    (h1 : ((List.range n).map e).sum = 1) :
    ∃ p0, p0 < n ∧ e p0 = 1 ∧ ∀ p, p < n → p ≠ p0 → e p = 0 := by
  induction n with
  | zero => simp at h1
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append] at h1
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h1
    rcases hb m (by omega) with hm | hm
    · -- the last column is 0, so the prefix carries the 1
      rw [hm, add_zero] at h1
      obtain ⟨p0, hp0, he0, hz⟩ := ih (fun p hp => hb p (by omega)) h1
      refine ⟨p0, by omega, he0, fun p hp hne => ?_⟩
      rcases Nat.lt_or_ge p m with hpm | hpm
      · exact hz p hpm hne
      · have : p = m := by omega
        rw [this]; exact hm
    · -- the last column is 1, so every earlier column is 0
      rw [hm] at h1
      have hpre : ((List.range m).map e).sum = 0 := by linarith
      have hnn : ∀ x ∈ (List.range m).map e, 0 ≤ x := by
        intro x hx
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
        rw [List.mem_range] at hp
        rcases hb p (by omega) with h | h <;> simp [h]
      have hall := all_zero_of_sum_zero _ hnn hpre
      refine ⟨m, by omega, hm, fun p hp hne => ?_⟩
      have hpm : p < m := by omega
      exact hall (e p) (List.mem_map.mpr ⟨p, List.mem_range.mpr hpm, rfl⟩)

/-- ⚑⚑ **`sel_shape_forced`** — the emitted `selOneGate`, `selIdxGate` and selector booleanity
FORCE the selector to be the indicator at the row's own plane. Nothing is assumed about the
prover's choice; `pl` is just the value `PIDX` carries. -/
theorem sel_shape_forced (a : Assignment) (nb planes pl : Nat)
    (h : acceptB (selGates nb planes) a = true) (hpl : pl < planes)
    (hpidx : a PIDX = (pl : ℤ)) :
    ∀ p, p < planes → a (SEc nb planes p) = if p = pl then 1 else 0 := by
  -- booleanity
  have hb : ∀ p, p < planes → a (SEc nb planes p) = 0 ∨ a (SEc nb planes p) = 1 := fun p hp =>
    bool_of_map a _ (fun p => SEc nb planes p) (acceptB_prefix _ _ a h) (List.mem_range.mpr hp)
  -- the two pins, in head form
  have htail : acceptB [selOneGate nb planes, selIdxGate nb planes, cgH (bitJoinHead nb planes)]
      a = true := acceptB_suffix _ _ a h
  rw [acceptB, List.all_eq_true] at htail
  have hone : evalH ((List.range planes).foldl
      (fun h p => h.addLin 1 (SEc nb planes p)) (Head.c (-1))) a = 0 := by
    have := htail (selOneGate nb planes) (by simp)
    rw [selOneGate, gateBodyEvalZero_cgH] at this
    exact of_decide_eq_true this
  have hidx : evalH ((List.range planes).foldl
      (fun (h : Head) (p : Nat) => h.addLin ((p : ℤ)) (SEc nb planes p)) (Head.lin (-1) PIDX))
      a = 0 := by
    have := htail (selIdxGate nb planes) (by simp)
    rw [selIdxGate, gateBodyEvalZero_cgH] at this
    exact of_decide_eq_true this
  rw [evalH_foldl_addLinF] at hone
  rw [evalH_foldl_addLinG] at hidx
  simp only [evalH, Head.c, List.map_nil, List.sum_nil, zero_add, one_mul] at hone
  simp only [evalH_lin, hpidx] at hidx
  have h1 : ((List.range planes).map (fun p => a (SEc nb planes p))).sum = 1 := by linarith
  obtain ⟨p0, hp0, he0, hz⟩ := bool_sum_one_unique planes (fun p => a (SEc nb planes p)) hb h1
  -- the index pin reads that one entry, so it is `pl`
  have hcong : (List.range planes).map (fun (p : Nat) => (p : ℤ) * a (SEc nb planes p))
      = (List.range planes).map (fun (p : Nat) => if p = p0 then (p : ℤ) else 0) :=
    List.map_congr_left (fun p hp => by
      rw [List.mem_range] at hp
      by_cases hpp : p = p0
      · rw [hpp, he0]; simp
      · rw [hz p hp hpp]; simp [hpp])
  rw [hcong, sum_indicator (fun (p : Nat) => (p : ℤ)) planes p0 hp0] at hidx
  have hp0pl : p0 = pl := by
    have : ((p0 : ℤ)) = (pl : ℤ) := by linarith
    exact_mod_cast this
  subst hp0pl
  intro p hp
  by_cases hpp : p = p0
  · rw [hpp, he0]; simp
  · rw [hz p hp hpp]; simp [hpp]

/-- ⚑⚑ **`sel_forces_closed`** — `sel_forces` with its selector-shape hypothesis DISCHARGED. On a
conditional-add row, the emitted join makes `BIT` the digit of the derived scalar at the row's own
bit plane, from the emitted gates alone. -/
theorem sel_forces_closed (a : Assignment) (nb planes pl : Nat)
    (h : acceptB (selGates nb planes) a = true)
    (hdbl : a DBL = 0) (hpl : pl < planes) (hpidx : a PIDX = (pl : ℤ)) :
    a BIT = a (SBc nb pl) :=
  sel_forces a nb planes pl h hdbl hpl (sel_shape_forced a nb planes pl h hpl hpidx)

/-! ### §4d — ⚑⚑ THE CANONICITY CERTIFICATE, AND THE TWO UNIQUENESS BRIDGES.

This is the section that moves the conclusion from "the digits are consistent" to "the digits are
the s-vector's". Three facts, none of them a hypothesis about the prover:

  1. `canon_forces` — the certificate pins the chain's landing value into `[0, q)`.
  2. `sBits_are_the_digits` / `gidxBits_are_testBits` — boolean decompositions are UNIQUE, so the
     witnessed digit columns are the binary expansions they claim to be.
  3. `derived_is_sNat` — therefore the landing value IS `PastaMsmScalarBound.sNat cs GIDX`. -/

/-- Casting a `Nat`-valued mapped sum. -/
theorem cast_sum_map {α : Type} (L : List α) (g : α → Nat) :
    ((L.map g).sum : ℤ) = (L.map (fun x => (g x : ℤ))).sum := by
  induction L with
  | nil => simp
  | cons x xs ih => simp [ih]

/-- Negation distributes over a mapped sum. -/
theorem sum_map_neg {α : Type} (L : List α) (g : α → ℤ) :
    (L.map (fun x => -(g x))).sum = -(L.map g).sum := by
  induction L with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- `2` factors out of a mapped `Nat` sum. -/
theorem sum_map_two_mul (L : List Nat) (g : Nat → Nat) :
    (L.map (fun p => 2 * g p)).sum = 2 * (L.map g).sum := by
  induction L with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- A weighted sum of BOOLEAN columns with non-negative weights is non-negative. -/
theorem boolWeighted_nonneg (L : List Nat) (w g : Nat → ℤ)
    (hw : ∀ p ∈ L, 0 ≤ w p) (hg : ∀ p ∈ L, g p = 0 ∨ g p = 1) :
    0 ≤ (L.map (fun p => w p * g p)).sum := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    have hx : 0 ≤ w x * g x := by
      rcases hg x (by simp) with hv | hv
      · simp [hv]
      · rw [hv, mul_one]; exact hw x (by simp)
    have hrest := ih (fun p hp => hw p (by simp [hp])) (fun p hp => hg p (by simp [hp]))
    simp only [List.map_cons, List.sum_cons]
    linarith

/-- ⚑ **MSB-first boolean decompositions are UNIQUE** — the witnessed digits are forced to be the
binary expansion of the value they sum to. -/
theorem msbBits_unique : ∀ (n : Nat) (f : Nat → Nat), (∀ p, p < n → f p ≤ 1) →
    ∀ p, p < n →
      (((List.range n).map (fun p => 2 ^ (n - 1 - p) * f p)).sum) / 2 ^ (n - 1 - p) % 2 = f p := by
  intro n
  induction n with
  | zero => intro f _ p hp; omega
  | succ m ih =>
    intro f hf p hp
    have hfm : f m ≤ 1 := hf m (by omega)
    have hsplit : ((List.range (m + 1)).map (fun p => 2 ^ (m + 1 - 1 - p) * f p)).sum
        = 2 * ((List.range m).map (fun p => 2 ^ (m - 1 - p) * f p)).sum + f m := by
      rw [List.range_succ, List.map_append, List.sum_append]
      have hcong : (List.range m).map (fun p => 2 ^ (m + 1 - 1 - p) * f p)
          = (List.range m).map (fun p => 2 * (2 ^ (m - 1 - p) * f p)) :=
        List.map_congr_left (fun p hp' => by
          rw [List.mem_range] at hp'
          have he : m + 1 - 1 - p = (m - 1 - p) + 1 := by omega
          rw [he]; ring)
      rw [hcong, sum_map_two_mul]
      simp
    rcases Nat.lt_or_ge p m with hpm | hpm
    · have hpow : (2 : Nat) ^ (m + 1 - 1 - p) = 2 * 2 ^ (m - 1 - p) := by
        have he : m + 1 - 1 - p = (m - 1 - p) + 1 := by omega
        rw [he]; ring
      rw [hsplit, hpow, ← Nat.div_div_eq_div_mul]
      have hd : (2 * ((List.range m).map (fun p => 2 ^ (m - 1 - p) * f p)).sum + f m) / 2
          = ((List.range m).map (fun p => 2 ^ (m - 1 - p) * f p)).sum := by omega
      rw [hd]
      exact ih f (fun q hq => hf q (by omega)) p hpm
    · have hpe : p = m := by omega
      subst hpe
      have h0 : p + 1 - 1 - p = 0 := by omega
      rw [hsplit, h0, pow_zero, Nat.div_one]
      omega

/-- ⚑ **LSB-first boolean decompositions are UNIQUE** — same fact, the index digits' indexing. -/
theorem lsbBits_unique : ∀ (n : Nat) (f : Nat → Nat), (∀ j, j < n → f j ≤ 1) →
    ∀ j, j < n → (((List.range n).map (fun j => 2 ^ j * f j)).sum) / 2 ^ j % 2 = f j := by
  intro n
  induction n with
  | zero => intro f _ j hj; omega
  | succ m ih =>
    intro f hf j hj
    have hf0 : f 0 ≤ 1 := hf 0 (by omega)
    have hsplit : ((List.range (m + 1)).map (fun j => 2 ^ j * f j)).sum
        = f 0 + 2 * ((List.range m).map (fun j => 2 ^ j * f (j + 1))).sum := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons]
      have hcong : (List.range m).map ((fun j => 2 ^ j * f j) ∘ Nat.succ)
          = (List.range m).map (fun j => 2 * (2 ^ j * f (j + 1))) :=
        List.map_congr_left (fun j _ => by
          simp only [Function.comp_apply, Nat.succ_eq_add_one, pow_succ]; ring)
      rw [hcong, sum_map_two_mul]
      simp
    cases j with
    | zero => rw [hsplit]; simp; omega
    | succ j' =>
      have hpow : (2 : Nat) ^ (j' + 1) = 2 * 2 ^ j' := by ring
      rw [hsplit, hpow, ← Nat.div_div_eq_div_mul]
      have hd : (f 0 + 2 * ((List.range m).map (fun j => 2 ^ j * f (j + 1))).sum) / 2
          = ((List.range m).map (fun j => 2 ^ j * f (j + 1))).sum := by omega
      rw [hd]
      exact ih (fun j => f (j + 1)) (fun q hq => hf (q + 1) (by omega)) j' (by omega)

/-- The MSB-first decomposition gate, evaluated: the weighted digit sum IS the landing value. -/
theorem sBits_sum (a : Assignment) (nb planes : Nat)
    (h : acceptB (sBitGates nb planes) a = true) :
    ((List.range planes).map (fun p => (2 : ℤ) ^ (planes - 1 - p) * a (SBc nb p))).sum
      = prdOf a nb nb := by
  have hg : evalH ((List.range planes).foldl
      (fun h p => h.addLin ((2 : ℤ) ^ (planes - 1 - p)) (SBc nb p))
      ((fpValue (PRc nb (numLimbs * nb))).scale (-1))) a = 0 := by
    have hs : acceptB [sBitsGate nb planes] a = true := acceptB_suffix _ _ a h
    rw [acceptB, List.all_eq_true] at hs
    have hz := hs (sBitsGate nb planes) (by simp)
    rw [sBitsGate, gateBodyEvalZero_cgH] at hz
    exact of_decide_eq_true hz
  rw [evalH_foldl_addLinG, evalH_scale, Dregg2.Circuit.Emit.PastaField.fpVal_eq] at hg
  simp only [prdOf]
  linarith

/-- The canonicity gate, evaluated: `s + Σ_p 2^p·CBc p = q − 1`. -/
theorem canon_sum (a : Assignment) (nb planes : Nat)
    (h : acceptB (canonGates nb planes) a = true) :
    prdOf a nb nb + ((List.range CBITS).map
        (fun p => (2 : ℤ) ^ p * a (CBc nb planes p))).sum = (qN : ℤ) - 1 := by
  have hg : evalH (canonHead nb planes) a = 0 := by
    have hs : acceptB [cgH (canonHead nb planes)] a = true := acceptB_suffix _ _ a h
    rw [acceptB, List.all_eq_true] at hs
    have hz := hs (cgH (canonHead nb planes)) (by simp)
    rw [gateBodyEvalZero_cgH] at hz
    exact of_decide_eq_true hz
  rw [canonHead, evalH_foldl_addLinG, evalH_addConst,
    Dregg2.Circuit.Emit.PastaField.fpVal_eq] at hg
  simp only [prdOf]
  linarith

/-- ⚑⚑ **`canon_forces`** — the emitted certificate pins the chain's landing value into `[0, q)`.
`[0, q)` holds exactly ONE representative of a residue class, which is the whole content: after
this, "congruent to the tensor" and "equal to the tensor's canonical value" are the same statement.

The lower bound is the decomposition's own (a non-negative weighted sum of boolean digits); the
upper bound is the certificate's. Neither is a hypothesis about the prover. -/
theorem canon_forces (a : Assignment) (nb planes : Nat)
    (hs : acceptB (sBitGates nb planes) a = true)
    (hc : acceptB (canonGates nb planes) a = true) :
    0 ≤ prdOf a nb nb ∧ prdOf a nb nb < (qN : ℤ) := by
  have hbs : ∀ p ∈ List.range planes, a (SBc nb p) = 0 ∨ a (SBc nb p) = 1 := fun p hp =>
    bool_of_map a _ (fun p => SBc nb p) (acceptB_prefix _ _ a hs) hp
  have hlo : 0 ≤ prdOf a nb nb := by
    rw [← sBits_sum a nb planes hs]
    exact boolWeighted_nonneg _ (fun p => (2 : ℤ) ^ (planes - 1 - p)) (fun p => a (SBc nb p))
      (fun p _ => by positivity) hbs
  refine ⟨hlo, ?_⟩
  have hcb : ∀ p ∈ List.range CBITS, a (CBc nb planes p) = 0 ∨ a (CBc nb planes p) = 1 := fun p hp =>
    bool_of_map a _ (fun p => CBc nb planes p) (acceptB_prefix _ _ a hc) hp
  have hsum : 0 ≤ ((List.range CBITS).map (fun p => (2 : ℤ) ^ p * a (CBc nb planes p))).sum :=
    boolWeighted_nonneg _ (fun p => (2 : ℤ) ^ p) (fun p => a (CBc nb planes p))
      (fun p _ => by positivity) hcb
  have := canon_sum a nb planes hc
  linarith

/-- The row's derived scalar as the `Nat` it is once `canon_forces` has pinned it non-negative. -/
def sOf (a : Assignment) (nb : Nat) : Nat := (prdOf a nb nb).toNat

/-- ⚑ **`sBits_are_the_digits`** — the witnessed digit column is FORCED to be the binary expansion
of the landing value, MSB-first over `planes` planes: `PastaMsmBound.scalarDigit`'s own indexing. -/
theorem sBits_are_the_digits (a : Assignment) (nb planes : Nat)
    (hs : acceptB (sBitGates nb planes) a = true)
    (p : Nat) (hp : p < planes) :
    a (SBc nb p) = ((sOf a nb / 2 ^ (planes - 1 - p) % 2 : Nat) : ℤ) := by
  have hbs : ∀ q, q < planes → a (SBc nb q) = 0 ∨ a (SBc nb q) = 1 := fun q hq =>
    bool_of_map a _ (fun q => SBc nb q) (acceptB_prefix _ _ a hs) (List.mem_range.mpr hq)
  set f : Nat → Nat := fun q => (a (SBc nb q)).toNat with hfdef
  have hfv : ∀ q, q < planes → ((f q : Nat) : ℤ) = a (SBc nb q) := by
    intro q hq
    rcases hbs q hq with hv | hv <;> simp [hfdef, hv]
  have hfle : ∀ q, q < planes → f q ≤ 1 := by
    intro q hq
    rcases hbs q hq with hv | hv <;> simp [hfdef, hv]
  -- the ℤ decomposition, re-read as a `Nat` one
  have hz := sBits_sum a nb planes hs
  have hmap : (List.range planes).map (fun q => (2 : ℤ) ^ (planes - 1 - q) * a (SBc nb q))
      = (List.range planes).map (fun q => ((2 ^ (planes - 1 - q) * f q : Nat) : ℤ)) :=
    List.map_congr_left (fun q hq => by
      rw [List.mem_range] at hq
      push_cast
      rw [hfv q hq])
  rw [hmap, ← cast_sum_map] at hz
  have hnatsum : sOf a nb = ((List.range planes).map (fun q => 2 ^ (planes - 1 - q) * f q)).sum := by
    simp only [sOf, ← hz, Int.toNat_natCast]
  have := msbBits_unique planes f hfle p hp
  rw [hnatsum, this, ← hfv p hp]

/-- ⚑ **`gidxBits_are_testBits`** — the index digits are FORCED to be `GIDX`'s binary digits, from
the emitted booleanity and the one recomposition gate. This is what lets the chain's product be
identified with `PastaMsmScalarBound.sAt`, whose factors are selected by `Nat.testBit`. -/
theorem gidxBits_are_testBits (a : Assignment) (nb idx : Nat)
    (h : acceptB (gidxBitGates nb) a = true) (hg : a GIDX = (idx : ℤ)) :
    ∀ j, j < nb → a (GBc j) = (if Nat.testBit idx j then 1 else 0) := by
  have hbs : ∀ j, j < nb → a (GBc j) = 0 ∨ a (GBc j) = 1 := fun j hj =>
    bool_of_map a _ GBc (acceptB_prefix _ _ a h) (List.mem_range.mpr hj)
  set f : Nat → Nat := fun j => (a (GBc j)).toNat with hfdef
  have hfv : ∀ j, j < nb → ((f j : Nat) : ℤ) = a (GBc j) := by
    intro j hj; rcases hbs j hj with hv | hv <;> simp [hfdef, hv]
  have hfle : ∀ j, j < nb → f j ≤ 1 := by
    intro j hj; rcases hbs j hj with hv | hv <;> simp [hfdef, hv]
  -- the recomposition gate, evaluated
  have hgate : evalH ((List.range nb).foldl (fun h j => h.addLin (-(2 ^ j : ℤ)) (GBc j))
      (Head.lin 1 GIDX)) a = 0 := by
    have hs : acceptB [gidxBitsGate nb] a = true := acceptB_suffix _ _ a h
    rw [acceptB, List.all_eq_true] at hs
    have hz := hs (gidxBitsGate nb) (by simp)
    rw [gidxBitsGate, gateBodyEvalZero_cgH] at hz
    exact of_decide_eq_true hz
  rw [evalH_foldl_addLinG, evalH_lin, hg] at hgate
  have hneg : (List.range nb).map (fun j => -(2 ^ j : ℤ) * a (GBc j))
      = (List.range nb).map (fun j => -(((2 ^ j * f j : Nat) : ℤ))) :=
    List.map_congr_left (fun j hj => by
      rw [List.mem_range] at hj
      push_cast
      rw [hfv j hj]
      ring)
  rw [hneg, sum_map_neg, ← cast_sum_map] at hgate
  have hval : idx = ((List.range nb).map (fun j => 2 ^ j * f j)).sum := by
    have : ((idx : ℤ)) = (((List.range nb).map (fun j => 2 ^ j * f j)).sum : ℤ) := by linarith
    exact_mod_cast this
  intro j hj
  have hbit := lsbBits_unique nb f hfle j hj
  rw [← hval] at hbit
  rw [← hfv j hj]
  rcases (hfle j hj).lt_or_eq with hlt | heq
  · have hz0 : f j = 0 := by omega
    have htb : Nat.testBit idx j = false := by
      rw [Nat.testBit_eq_decide_div_mod_eq, hbit, hz0]; simp
    rw [htb, hz0]; simp
  · have htb : Nat.testBit idx j = true := by
      rw [Nat.testBit_eq_decide_div_mod_eq, hbit, heq]; simp
    rw [htb, heq]; simp

/-- `sAt` as the product over `List.range`, one factor per challenge — the exact shape
`chain_forces` lands the running product in, so the two can be identified. -/
theorem sAt_as_range_prod (cs : List Fq) (idx : Nat) :
    sAt cs idx = ((List.range cs.length).map
        (fun j => if Nat.testBit idx (cs.length - 1 - j) then cs.getD j 0 else 1)).prod := by
  induction cs with
  | nil => simp [sAt]
  | cons c rest ih =>
    rw [sAt, ih, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
      List.prod_cons]
    congr 1
    refine congrArg List.prod (List.map_congr_left (fun j _ => ?_))
    have he : rest.length - (j + 1) = rest.length - 1 - j := by omega
    simp [Function.comp_apply, he]

/-- ⚑⚑ **`derived_is_sNat` — THE BRIDGE, and the sentence it retires.**

`chain_forces` lands the running product in a RESIDUE CLASS mod `q`. `9b88bc06e` measured that the
class has five representatives inside the 256-plane digit budget, so up to that commit the
conclusion ranged over the WITNESSED decomposition rather than over `PastaMsmScalarBound.sNat`, and
the `SBc ↔ scalarDigit` bridge "cannot be written as stated". With §2.7's certificate it can be, and
this is it: the chain's landing value IS `sNat cs idx` — the `Nat` the manifest carries, the `.val`
of the block's own s-vector entry (`sNat_is_svec_entry`).

The index digits, the selected multipliers, the running product, the decomposition and its
canonicity are all FORCED from the emitted row-local gates. Two hypotheses remain and they are NOT
the same kind of thing:

  * `hgidx` names the absolute generator index the row consumes — a value
    `PastaMsmBound.bound_forces_gidx` forces onto the row one rung down, from ITS emitted lookup.
  * `hwire` says this row's challenge limbs reconstruct `cs`. ⚠ **An earlier revision of this
    paragraph called both "the two facts the VERIFIER supplies". That was wrong about `hwire`, and
    the error is exactly the one this file was emitting gates to prevent:** `chalPinGates` and
    `chalThreadGates` are EMITTED HERE and are supposed to force it, and until §4e nothing proved
    they did — so a prover could pick a fresh challenge vector per row and no theorem in this file
    could see it (§5d now exhibits precisely that forgery, accepted row-locally and refused by the
    thread). `wire_forces_challenges` discharges `hwire`; use §4f's capstone, which carries neither
    it nor `hpidx`. -/
theorem derived_is_sNat (a : Assignment) (nb planes idx : Nat) (cs : List Fq)
    (hcs : cs.length = nb)
    (h : acceptB (deriveRowGates nb planes) a = true)
    (hgidx : a GIDX = (idx : ℤ))
    (hwire : ∀ j, j < nb → ((chalOf a nb j : ℤ) : Fq) = cs.getD j 0) :
    sOf a nb = sNat cs idx := by
  haveI : NeZero qN := ⟨by decide⟩
  rw [deriveRowGates] at h
  have hcan : acceptB (canonGates nb planes) a = true := acceptB_suffix _ _ a h
  have h5 := acceptB_prefix _ _ a h
  have hsel : acceptB (selGates nb planes) a = true := acceptB_suffix _ _ a h5
  have h4 := acceptB_prefix _ _ a h5
  have hsb : acceptB (sBitGates nb planes) a = true := acceptB_suffix _ _ a h4
  have h3 := acceptB_prefix _ _ a h4
  have hch : acceptB (prdOneGate nb :: chainGates nb) a = true := acceptB_suffix _ _ a h3
  have h2 := acceptB_prefix _ _ a h3
  have hmul : acceptB (mulSelGates nb) a = true := acceptB_suffix _ _ a h2
  have hgb : acceptB (gidxBitGates nb) a = true := acceptB_prefix _ _ a h2
  rw [acceptB_cons, Bool.and_eq_true] at hch
  have hone : evalH ((fpValue (PRc nb 0)).addConst (-1)) a = 0 := by
    have hz := hch.1
    rw [prdOneGate, gateBodyEvalZero_cgH] at hz
    exact of_decide_eq_true hz
  have hprod := chain_forces a nb hone hch.2 hmul nb (le_refl nb)
  -- the index digits ARE `idx`'s bits, so the selected factors are `sAt`'s factors
  have hbits := gidxBits_are_testBits a nb idx hgb hgidx
  have hterms : (List.range nb).map (fun j =>
        ((gbOf a nb j * chalOf a nb j + (1 - gbOf a nb j) : ℤ) : Fq))
      = (List.range nb).map (fun j =>
        if Nat.testBit idx (nb - 1 - j) then cs.getD j 0 else 1) :=
    List.map_congr_left (fun j hj => by
      rw [List.mem_range] at hj
      have hgbj : gbOf a nb j = (if Nat.testBit idx (nb - 1 - j) then 1 else 0) := by
        simp only [gbOf]
        exact hbits (nb - 1 - j) (by omega)
      by_cases hb : Nat.testBit idx (nb - 1 - j)
      · rw [hgbj, if_pos hb, if_pos hb]
        push_cast
        rw [← hwire j hj]
        simp [chalOf]
      · rw [hgbj, if_neg hb, if_neg hb]
        push_cast
        simp)
  rw [hterms] at hprod
  have hsat : ((prdOf a nb nb : ℤ) : Fq) = sAt cs idx := by
    rw [hprod, sAt_as_range_prod cs idx, hcs]
  -- the certificate makes that congruence an EQUALITY of naturals
  obtain ⟨hlo, hhi⟩ := canon_forces a nb planes hsb hcan
  have hnat : ((sOf a nb : Nat) : ℤ) = prdOf a nb nb := Int.toNat_of_nonneg hlo
  have hlt : sOf a nb < qN := by
    have hc : ((sOf a nb : Nat) : ℤ) < (qN : ℤ) := by rw [hnat]; exact hhi
    exact_mod_cast hc
  have hcastn : ((sOf a nb : Nat) : Fq) = sAt cs idx := by
    have hz : (((sOf a nb : Nat) : ℤ) : Fq) = sAt cs idx := by rw [hnat]; exact hsat
    simpa using hz
  rw [sNat, ← hcastn, ZMod.val_natCast_of_lt hlt]

/-- ⚑⚑ **THE ROW'S CONDITIONAL BIT IS THE BLOCK'S S-VECTOR BIT.** The deliverable, stated over
`PastaMsmScalarBound.sNat` — the canonical value — rather than over a witnessed decomposition.
`nb`, `planes`, `idx` and `pl` are universally quantified and occur in no bound; there is no
induction over the trace and no row count anywhere. -/
theorem derived_row_bit_is_block_svec_bit (a : Assignment) (nb planes idx pl : Nat) (cs : List Fq)
    (hcs : cs.length = nb)
    (h : acceptB (deriveRowGates nb planes) a = true)
    (hgidx : a GIDX = (idx : ℤ))
    (hwire : ∀ j, j < nb → ((chalOf a nb j : ℤ) : Fq) = cs.getD j 0)
    (hdbl : a DBL = 0) (hpl : pl < planes) (hpidx : a PIDX = (pl : ℤ)) :
    a BIT = ((sNat cs idx / 2 ^ (planes - 1 - pl) % 2 : Nat) : ℤ) := by
  have h' := h
  rw [deriveRowGates] at h'
  have h5 := acceptB_prefix _ _ a h'
  have hsel : acceptB (selGates nb planes) a = true := acceptB_suffix _ _ a h5
  have hsb : acceptB (sBitGates nb planes) a = true :=
    acceptB_suffix _ _ a (acceptB_prefix _ _ a h5)
  rw [sel_forces_closed a nb planes pl hsel hdbl hpl hpidx,
    sBits_are_the_digits a nb planes hsb pl hpl,
    derived_is_sNat a nb planes idx cs hcs h hgidx hwire]

/-- ⚑ **…AND THAT IS THE MANIFEST'S OWN DIGIT FIELD — AT WHATEVER PLANE THE CALLER NAMES.**
`PastaMsmScalarBound.digit_is_block_svec_bit` says the emitted manifest's declared digit is `sNat`'s
bit at plane `pl`; this says the trace's `BIT` is too, with no reference to
`PublicLookupBalanced`.

⚠ **Read the quantifier before reading this as a redundancy claim.** `pl` here is a PARAMETER
carried in by `hpidx`, and the manifest's digit field for TRACE ROW `i` is not at an arbitrary
plane — it is at `PastaMsmBound.planeAt w i`, the row's own. Until `pl` is forced to be that, this
theorem closes the manifest's INDEX argument (`hgidx`, which `PastaMsmBound.bound_forces_gidx`
supplies) and leaves its PLANE argument open, which is a strictly weaker statement than "the digit
field is redundant". §4f is where `pl` is discharged from the emitted plane thread and the
redundancy claim is made at the trace level; `derived_row_bit_is_manifest_digit` is THERE, not
here. The manifest's other three fields are untouched by either: no emitted gate relates a
generator INDEX to generator COORDINATES. -/
theorem derived_row_bit_is_manifest_digit_at_a_named_plane
    (a : Assignment) (nb planes idx pl N : Nat) (cs : List Fq)
    (hcs : cs.length = nb) (hidx : idx < N)
    (h : acceptB (deriveRowGates nb planes) a = true)
    (hgidx : a GIDX = (idx : ℤ))
    (hwire : ∀ j, j < nb → ((chalOf a nb j : ℤ) : Fq) = cs.getD j 0)
    (hdbl : a DBL = 0) (hpl : pl < planes) (hpidx : a PIDX = (pl : ℤ)) :
    a BIT = ((scalarDigit (sScalars cs N) planes idx pl : Nat) : ℤ) := by
  rw [Dregg2.Circuit.Emit.PastaMsmScalarBound.digit_is_block_svec_bit cs N planes idx pl hidx]
  exact derived_row_bit_is_block_svec_bit a nb planes idx pl cs hcs h hgidx hwire hdbl hpl hpidx

/-! ### §4e — ⚑⚑ THE WIRE GATES AND THE PLANE THREAD, FORCED.

**Everything above this line is ROW-LOCAL** — it consumes `acceptB (deriveRowGates nb planes) a` on
ONE assignment, and `acceptB` is `List.all gateBodyEvalZero`, whose `gateBodyEvalZero` returns
`true` on every constructor that is not `.base (.gate _)`. So `acceptB` **cannot see** a
`.boundary`, a `.piBinding` or a `.windowGate`: the four objects `deriveWireGates` emits are
invisible to the denotation §4–§4d is stated in. That is not a defect of `acceptB`; it is why those
four need their own predicates, exactly as `PastaMsmBound` §4 gives its two index threads
`BoundWindowAccepted` / `BoundStartAccepted` rather than folding them into `acceptB`.

⚑ **THE DEFECT THIS SECTION REPAIRS, stated plainly.** Before this section `pidxStartGate`,
`pidxThreadGate`, `chalPinGates` and `chalThreadGates` appeared in exactly ONE theorem in this file
— `deriveGates_length`, a COUNTING lemma — while `derived_is_sNat` and
`derived_row_bit_is_block_svec_bit` took their CONTENT as raw hypotheses (`hwire`, `hpidx`). The
gates were emitted and their forcing was not proved, so the module was assuming what it emitted.
Both are discharged below, in the sibling's shape: three denotations over the ACTUALLY EMITTED
list, one per-row forcing lemma per gate, and row inductions whose bound `H` is universally
quantified and occurs nowhere but as the induction variable. `PastaMsmBound.tidxThread_forces` and
`tidx_is_the_row_index` are the template and no technique is invented here. -/

/-- The content of the emitted first-row `.boundary` gates of the wire block, in the ℤ model (§6.3:
the deployed prover reads them mod BabyBear — the inherited K1 residual). -/
def DeriveStartAccepted (nb : Nat) (T : WTrace) : Prop :=
  ∀ e : EmittedExpr, VmConstraint2.base (.boundary .first e) ∈ deriveWireGates nb →
    e.eval (T 0) = 0

/-- The content of the emitted first-row `.piBinding` pins, against the DECLARED public-input
vector `pv`. ⚑ **This is the only predicate in the Pasta MSM tower that reads a public input at
all** — it is where "the challenges are on the wire" stops being prose.

⚠ **And that is a finding about a SIBLING, recorded here because nothing else records it.**
`PastaMsmSliced` emits 29 `piBinding`s (`LO`/`HI` on the first row, the 27 accumulator limbs on the
last) and proves only SHAPE facts about them — `sMaxPi`, that each names a declared public input.
No theorem there says what those 29 pins FORCE, which is the same defect §4e repairs here, one rung
down and still open. It is not this rung's to fix; it is named so it is named somewhere. -/
def DerivePiAccepted (nb : Nat) (T : WTrace) (pv : Nat → ℤ) : Prop :=
  ∀ col k : Nat, VmConstraint2.base (.piBinding .first col k) ∈ deriveWireGates nb →
    T 0 col = pv k

/-- The content of the emitted `windowGate`s of the wire block on the two-row window at row `i`.

⚑ **Why every consumer below asks for this only at `i + 1 < H` and never at `i = H − 1`.** `cw` sets
`onTransition := true`, and `WindowConstraint.holdsAt env isLast` is then `isLast = false → body ≡
0` — the deployed `when_transition()` arm. The thread does NOT fire on the last row, where `nxt`
is the wrap/pad row. Requiring the predicate on `i + 1 < H` is exactly what an accepting trace of
height `H` supplies, and asking for it at `H − 1` would be asking for something the deployed AIR
does not check. -/
def DeriveWindowAccepted (nb : Nat) (T : WTrace) (i : Nat) : Prop :=
  ∀ wc : WindowConstraint, VmConstraint2.windowGate wc ∈ deriveWireGates nb →
    wc.body.eval (envOf T i) = 0

/-- ⚑ **The DECIDABLE twin of those three predicates**, over the same emitted list — `acceptB`'s
counterpart for the constructors `acceptB` cannot see. §5d decides it in the kernel, which is what
makes the wire tampers MEASUREMENTS rather than assertions.

⚠ `pv` is a SEPARATE argument and not `envOf`'s `pub` field. `PastaMsmWindowed.envOf` sets
`pub := T 0` — the trace's first row, not the public-input vector — and the deployed `envAt` sets
`pub := t.pub`. No `WindowExpr` constructor reads `pub` at all, so the discrepancy is inert for the
window gates; but a PI pin is exactly the constraint that WOULD read it, so it is given the
deployed reading here and not `envOf`'s. -/
def wireAcceptB (nb : Nat) (T : WTrace) (pv : Nat → ℤ) (i : Nat) : Bool :=
  (deriveWireGates nb).all (fun c => match c with
    | .base (.boundary .first e)      => decide (e.eval (T 0) = 0)
    | .base (.piBinding .first col k) => decide (T 0 col = pv k)
    | .windowGate wc                  => decide (wc.body.eval (envOf T i) = 0)
    | _                               => true)

/-- ⚑ **`wireAccept_forces`** — and the decidable twin IMPLIES the three predicates, so a kernel
`#guard` on it is evidence about the theorems above and not about a separate object. -/
theorem wireAccept_forces (nb : Nat) (T : WTrace) (pv : Nat → ℤ) (i : Nat)
    (h : wireAcceptB nb T pv i = true) :
    DeriveStartAccepted nb T ∧ DerivePiAccepted nb T pv ∧ DeriveWindowAccepted nb T i := by
  rw [wireAcceptB, List.all_eq_true] at h
  exact ⟨fun e he => of_decide_eq_true (h _ he),
         fun col k hk => of_decide_eq_true (h _ hk),
         fun wc hw => of_decide_eq_true (h _ hw)⟩

/-- The challenge PI pin for flat limb `m` is IN the emitted list. -/
theorem mem_chalPin (nb m : Nat) (hm : m < numLimbs * nb) :
    pinPi (CHc nb m) (PI_COUNT + m) ∈ deriveWireGates nb := by
  simp only [deriveWireGates, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inr (Or.inl (List.mem_map.mpr ⟨m, List.mem_range.mpr hm, rfl⟩)))

/-- …and so is its thread. -/
theorem mem_chalThread (nb m : Nat) (hm : m < numLimbs * nb) :
    cw (.add (.nxt (CHc nb m)) (.mul (.const (-1)) (.loc (CHc nb m)))) ∈ deriveWireGates nb := by
  simp only [deriveWireGates, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inr (Or.inr (List.mem_map.mpr ⟨m, List.mem_range.mpr hm, rfl⟩)))

/-- ⚑ **`pidxStart_forces`** — the emitted first-row boundary pins the plane thread's origin. -/
theorem pidxStart_forces (nb : Nat) (T : WTrace) (h : DeriveStartAccepted nb T) :
    T 0 PIDX = 0 := by
  have := h (.var PIDX) (by simp [deriveWireGates, pidxStartGate])
  simpa [Dregg2.Exec.CircuitEmit.EmittedExpr.eval] using this

/-- ⚑ **`pidxThread_forces`** — the emitted `windowGate` advances the plane index by the NEXT row's
doubling selector, and by nothing else. -/
theorem pidxThread_forces (nb : Nat) (T : WTrace) (i : Nat) (h : DeriveWindowAccepted nb T i) :
    T (i + 1) PIDX = T i PIDX + T (i + 1) DBL := by
  have hw := h ⟨.add (.nxt PIDX) (.mul (.const (-1)) (.add (.loc PIDX) (.nxt DBL))), true⟩
    (by simp [deriveWireGates, pidxThreadGate, cw])
  simp only [WindowExpr.eval, envOf] at hw
  linarith

/-- ⚑ **`chalPin_forces`** — the emitted `piBinding` pins the FIRST row's challenge limb to its
declared public input. -/
theorem chalPin_forces (nb : Nat) (T : WTrace) (pv : Nat → ℤ) (h : DerivePiAccepted nb T pv)
    (m : Nat) (hm : m < numLimbs * nb) : T 0 (CHc nb m) = pv (PI_COUNT + m) :=
  h _ _ (mem_chalPin nb m hm)

/-- ⚑ **`chalThread_forces`** — the emitted `windowGate` carries a challenge limb UNCHANGED to the
next row. This is the gate §2.3 exists for: a first-row pin alone leaves the challenge columns FREE
on rows 1.., which is the shape that makes a derivation look verified while the prover picks a
fresh challenge vector per row. -/
theorem chalThread_forces (nb : Nat) (T : WTrace) (i m : Nat) (hm : m < numLimbs * nb)
    (h : DeriveWindowAccepted nb T i) :
    T (i + 1) (CHc nb m) = T i (CHc nb m) := by
  have hw := h ⟨.add (.nxt (CHc nb m)) (.mul (.const (-1)) (.loc (CHc nb m))), true⟩
    (mem_chalThread nb m hm)
  simp only [WindowExpr.eval, envOf] at hw
  linarith

/-- ⚑⚑ **`chal_is_the_wire`** — the emitted pin plus the emitted threads make EVERY row's challenge
columns the DECLARED PUBLIC INPUTS', for every row. `H` is universally quantified and occurs only
as the induction bound: the statement at `planes·(w+1) = 128` is the statement at `1,056,896`. -/
theorem chal_is_the_wire (nb : Nat) (T : WTrace) (pv : Nat → ℤ) (H : Nat)
    (h0 : DerivePiAccepted nb T pv) (h : ∀ i, i + 1 < H → DeriveWindowAccepted nb T i) :
    ∀ i, i < H → ∀ m, m < numLimbs * nb → T i (CHc nb m) = pv (PI_COUNT + m) := by
  intro i
  induction i with
  | zero => intro _ m hm; exact chalPin_forces nb T pv h0 m hm
  | succ p ih =>
    intro hp m hm
    rw [chalThread_forces nb T p m hm (h p hp)]
    exact ih (by omega) m hm

/-- The field element challenge `j`'s NINE DECLARED PUBLIC INPUTS reconstruct. Read off `pv`; no
trace column occurs in it. -/
def piChal (pv : Nat → ℤ) (nb j : Nat) : ℤ :=
  ((List.range numLimbs).map
    (fun l => (2 : ℤ) ^ (limbBits * l) * pv (PI_COUNT + (numLimbs * j + l)))).sum

/-- ⚑ **`chalOf_is_piChal`** — a row's challenge VALUE is the public input's value, on every row. -/
theorem chalOf_is_piChal (nb : Nat) (T : WTrace) (pv : Nat → ℤ) (H : Nat)
    (h0 : DerivePiAccepted nb T pv) (h : ∀ i, i + 1 < H → DeriveWindowAccepted nb T i)
    (i : Nat) (hi : i < H) (j : Nat) (hj : j < nb) :
    chalOf (T i) nb j = piChal pv nb j := by
  have hw := chal_is_the_wire nb T pv H h0 h i hi
  rw [chalOf, fpVal_as_sum, piChal]
  refine congrArg List.sum (List.map_congr_left (fun l hl => ?_))
  rw [List.mem_range] at hl
  have hlt : numLimbs * j + l < numLimbs * nb := by
    simp only [numLimbs] at hl ⊢
    have : j + 1 ≤ nb := hj
    nlinarith
  have hcol : CHc nb (numLimbs * j) + l = CHc nb (numLimbs * j + l) := by
    simp only [CHc]; omega
  rw [hcol, hw (numLimbs * j + l) hlt]

/-- ⚑ **The challenge vector the VERIFIER supplies**, as a `List Fq` — `nb` field elements read off
the DECLARED public inputs, nine slots each starting at `PI_COUNT`. Nothing in the trace names it,
which is the whole point: it is what a light client HANDS the circuit. -/
def csOfPi (pv : Nat → ℤ) (nb : Nat) : List Fq :=
  (List.range nb).map (fun j => ((piChal pv nb j : ℤ) : Fq))

theorem csOfPi_length (pv : Nat → ℤ) (nb : Nat) : (csOfPi pv nb).length = nb := by
  simp [csOfPi]

theorem csOfPi_getD (pv : Nat → ℤ) (nb j : Nat) (hj : j < nb) :
    (csOfPi pv nb).getD j 0 = ((piChal pv nb j : ℤ) : Fq) := by
  have hlen : j < (csOfPi pv nb).length := by rw [csOfPi_length]; exact hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some]
  simp [csOfPi]

/-- ⚑⚑ **`wire_forces_challenges` — `hwire` DISCHARGED.** Exactly the hypothesis `derived_is_sNat`
and `derived_row_bit_is_block_svec_bit` used to CARRY, now a CONSEQUENCE of `chalPinGates` and
`chalThreadGates` — with the challenge list the one the DECLARED PUBLIC INPUTS carry, not one a
caller names. -/
theorem wire_forces_challenges (nb : Nat) (T : WTrace) (pv : Nat → ℤ) (H : Nat)
    (h0 : DerivePiAccepted nb T pv) (h : ∀ i, i + 1 < H → DeriveWindowAccepted nb T i)
    (i : Nat) (hi : i < H) :
    ∀ j, j < nb → ((chalOf (T i) nb j : ℤ) : Fq) = (csOfPi pv nb).getD j 0 := by
  intro j hj
  rw [chalOf_is_piChal nb T pv H h0 h i hi j hj, csOfPi_getD pv nb j hj]

/-- ⚑ **`pidx_counts_doublings`** — from the emitted origin pin and the emitted step ALONE, with no
hypothesis about the `DBL` column whatsoever: the plane index a row carries IS the number of
doubling rows at or below it and above row 0. -/
theorem pidx_counts_doublings (nb : Nat) (T : WTrace) (H : Nat)
    (h0 : DeriveStartAccepted nb T) (h : ∀ i, i + 1 < H → DeriveWindowAccepted nb T i) :
    ∀ i, i < H → T i PIDX = ((List.range i).map (fun r => T (r + 1) DBL)).sum := by
  intro i
  induction i with
  | zero => intro _; simpa using pidxStart_forces nb T h0
  | succ m ih =>
    intro hm
    rw [pidxThread_forces nb T m (h m hm), ih (by omega), List.range_succ, List.map_append]
    simp

/-- ⚑ **The `DBL` column's PATTERN: `1` exactly on a plane-boundary row.** This is NOT this file's
gate and this file does not pretend otherwise — it is `PastaMsmBound`'s, forced there by the emitted
lookup's exact-public balance (`bound_forces_doubling` / `bound_forces_dbl_off`), and it is what
`PastaMsmWindowed` §6.1 named as the one thing its row induction hypothesised.
`dblPattern_of_manifest` below composes with that rung so the pattern is DERIVED here too, and
§4e.1's `derive_balance_transport` supplies that rung's own hypothesis from the DEPLOYED
descriptor's balance — so nothing in this chain is left as prose. -/
def DblPattern (w : Nat) (T : WTrace) (H : Nat) : Prop :=
  ∀ i, i < H → T i DBL = if i % (w + 1) = 0 then 1 else 0

/-- Under the pattern, the doubling rows in `(0, i]` number exactly `i / (w + 1)`. -/
theorem count_doublings (w : Nat) (T : WTrace) (H : Nat) (hp : DblPattern w T H) :
    ∀ i, i < H → ((List.range i).map (fun r => T (r + 1) DBL)).sum = ((i / (w + 1) : Nat) : ℤ) := by
  have hiff : ∀ m : Nat, ((w + 1) ∣ (m + 1)) ↔ (m + 1) % (w + 1) = 0 := fun m =>
    ⟨fun hd => by obtain ⟨c, hc⟩ := hd; rw [hc]; exact Nat.mul_mod_right _ _,
     Nat.dvd_of_mod_eq_zero⟩
  intro i
  induction i with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    rw [List.range_succ, List.map_append, List.sum_append, ih (by omega)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [hp (m + 1) hm]
    by_cases hd : (m + 1) % (w + 1) = 0
    · rw [if_pos hd, Nat.succ_div, if_pos ((hiff m).mpr hd)]; push_cast; ring
    · rw [if_neg hd, Nat.succ_div, if_neg (fun hx => hd ((hiff m).mp hx))]; push_cast; ring

/-- ⚑⚑ **`pidx_is_the_plane_index` — `hpidx` DISCHARGED.** The emitted origin pin and the emitted
step make `PIDX` the row's OWN bit plane, `PastaMsmBound.planeAt w i`, for every row — so the plane
a row's selector reads is the plane the Horner schedule PUTS that row in, not one the prover picks.
`H` is universally quantified and occurs only as the induction bound. -/
theorem pidx_is_the_plane_index (nb w : Nat) (T : WTrace) (H : Nat)
    (h0 : DeriveStartAccepted nb T) (h : ∀ i, i + 1 < H → DeriveWindowAccepted nb T i)
    (hp : DblPattern w T H) :
    ∀ i, i < H → T i PIDX = ((planeAt w i : Nat) : ℤ) := by
  intro i hi
  rw [pidx_counts_doublings nb T H h0 h i hi, count_doublings w T H hp i hi, planeAt]

/-- ⚑ **`dblPattern_of_manifest`** — and the `DBL` pattern is not assumed either. `hman` is verbatim
`PastaMsmBound.row_tuple_is_its_manifest_row`'s CONCLUSION — whose own hypotheses are the emitted
lookup's exact-public balance, the threaded row index (`tidx_is_the_row_index`) and the `DBL`
column's booleanity, all forced one rung down — and `bound_forces_doubling` / `bound_forces_dbl_off`
are that rung's theorems, applied here and not restated. -/
theorem dblPattern_of_manifest (k w planes : Nat) (gens : List Pt) (scal : List Nat)
    (t : VmTrace) (H : Nat)
    (hman : ∀ i, i < H →
      tupleOf (rowAt t i) = (manifestRow (sliceLo w k) w planes gens scal i).map Int.ofNat)
    (htidx : ∀ i, i < H → rowAt t i TIDX = (i : ℤ))
    (hbit : ∀ i, rowAt t i DBL = 0 ∨ rowAt t i DBL = 1) :
    DblPattern w (fun i => rowAt t i) H := by
  intro i hi
  by_cases hb : i % (w + 1) = 0
  · rw [if_pos hb]
    exact Dregg2.Circuit.Emit.PastaMsmBound.bound_forces_doubling k w planes gens scal t i
      (hman i hi) hb (htidx i hi) (hbit i)
  · rw [if_neg hb]
    exact Dregg2.Circuit.Emit.PastaMsmBound.bound_forces_dbl_off k w planes gens scal t i
      (hman i hi) hb (htidx i hi) (hbit i)

/-! #### §4e.1 — ⚑⚑ THE BALANCE TRANSPORT, so the plane thread's chain reaches the emitted lookup.

`dblPattern_of_manifest` consumes `PastaMsmBound.row_tuple_is_its_manifest_row`'s conclusion, whose
own hypothesis is `PublicLookupBalanced (boundRowDesc …)`. The descriptor a prover actually runs is
`deriveRowDesc`. Nothing carried the balance from one to the other, so the composition existed on
paper and not in the kernel. It is here now, and its whole content is that **the derivation emits no
`.lookup`**: the declared table is the same object by `rfl` and the lookup LOG is unchanged. -/

/-- Every constraint of a `map`ped family is a non-lookup when its generator is. -/
theorem notLookup_map {α : Type} (L : List α) (f : α → VmConstraint2)
    (hf : ∀ x, isNotLookup (f x) = true) : ∀ c ∈ L.map f, isNotLookup c = true := by
  intro c hc; obtain ⟨x, -, rfl⟩ := List.mem_map.mp hc; exact hf x

/-- ⚑ **`deriveGates_noLookup`** — the derivation emits no `.lookup`, at every `(nb, planes)`. Every
family is a `map` of `cgH` / `binGate` / `cw` / `pinPi`, each of which is a `.base` or a
`.windowGate` by construction. -/
theorem deriveGates_noLookup (nb planes : Nat) :
    (deriveGates nb planes).all isNotLookup = true := by
  rw [List.all_eq_true]
  intro c hc
  cases c with
  | base b => rfl
  | memOp m => rfl
  | mapOp m => rfl
  | umemOp m => rfl
  | proofBind m => rfl
  | windowGate w => rfl
  | lookup l =>
    exfalso
    simp only [deriveGates, deriveWireGates, deriveRowGates, gidxBitGates, chalPinGates,
      chalThreadGates, mulSelGates, chainGates, sBitGates, selGates, canonGates,
      List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false, false_or] at hc
    simp_all [pidxStartGate, pidxThreadGate, gidxBitsGate, prdOneGate, sBitsGate, selOneGate,
      selIdxGate, cw, cgH, cg, binGate, pinPi,
      Dregg2.Circuit.Emit.PastaField.fqMulCore]

/-- The emitted list, split at the two rungs it extends. -/
theorem deriveRowDesc_constraints_split (nb n k w planes : Nat) (gens : List Pt)
    (scal : List Nat) :
    (deriveRowDesc nb n k w planes gens scal).constraints
      = (boundRowDesc n k w planes gens scal).constraints ++ onCurveRowGates
          ++ deriveGates nb planes := rfl

/-- ⚑ **The lookup LOG is the rung-below's, unchanged** — the derivation contributes nothing to it,
at any table id. -/
theorem derive_lookupLog (nb n k w planes : Nat) (gens : List Pt) (scal : List Nat)
    (t : VmTrace) (tid : TableId) :
    lookupLog (deriveRowDesc nb n k w planes gens scal) t tid
      = lookupLog (boundRowDesc n k w planes gens scal) t tid := by
  have key : ∀ {β : Type} (f : VmConstraint2 → Option β),
      (∀ c, isNotLookup c = true → f c = none) →
      (deriveRowDesc nb n k w planes gens scal).constraints.filterMap f
        = (boundRowDesc n k w planes gens scal).constraints.filterMap f := by
    intro β f hf
    rw [deriveRowDesc_constraints_split, List.filterMap_append, List.filterMap_append,
      filterMap_of_noLookup f onCurveRowGates hf (by rfl),
      filterMap_of_noLookup f (deriveGates nb planes) hf (deriveGates_noLookup nb planes)]
    simp
  unfold Dregg2.Circuit.DescriptorIR2.lookupLog
  exact congrArg (fun f => t.rows.flatMap f)
    (funext (fun row => key _ (fun c hc => by cases c <;> simp_all [isNotLookup])))

/-- ⚑⚑ **`derive_balance_transport`** — the exact-public balance of the DEPLOYED derived descriptor
IS the balance `PastaMsmBound`'s forcing theorems consume. This is what closes the chain: the
emitted lookup ⟹ the manifest per row ⟹ the `DBL` pattern ⟹ `PIDX = planeAt w i`. §6.1 named this
as the lemma nobody had written; it is written. -/
theorem derive_balance_transport (nb n k w planes : Nat) (gens : List Pt) (scal : List Nat)
    (t : VmTrace)
    (h : PublicLookupBalanced (deriveRowDesc nb n k w planes gens scal) t) :
    PublicLookupBalanced (boundRowDesc n k w planes gens scal) t := by
  intro td htd
  have htd' : td ∈ (deriveRowDesc nb n k w planes gens scal).tables := by
    rw [deriveRowDesc_tables, Dregg2.Circuit.Emit.PastaMsmOnCurve.onCurveRowDesc_tables]
    exact htd
  have := h td htd'
  rwa [derive_lookupLog] at this

/-- A row inside the trace is inside the plane count — the one arithmetic fact the capstone needs
about the shape, and it is about `planes·(w+1)`, not about any gate. -/
theorem planeAt_lt (w planes i : Nat) (hi : i < planes * (w + 1)) : planeAt w i < planes := by
  have h : i < (w + 1) * planes := by rw [Nat.mul_comm]; exact hi
  simpa [planeAt] using Nat.div_lt_of_lt_mul h

/-! ### §4f — ⚑⚑ THE DELIVERABLE OVER A TRACE: the wire and the plane are FORCED, not named.

§4d's conclusions range over a challenge list `cs` a caller names and a bit plane `pl` a caller
names. Here both come from the emitted object: the challenges are the DECLARED PUBLIC INPUTS'
(`csOfPi pv nb`, via `chalPinGates` + `chalThreadGates`) and the plane is the row's own
(`planeAt w i`, via `pidxStartGate` + `pidxThreadGate` + the `DBL` pattern the rung below forces,
carried here by §4e.1's balance transport). What remains carried is named in §6.1 and is not this
file's to discharge. -/

/-- ⚑⚑ **`derived_row_bit_is_the_wire_svec_bit`** — `derived_row_bit_is_block_svec_bit` with BOTH
of its carried hypotheses discharged from the emitted wire gates. The conditional-add row's `BIT` is
the digit, AT THE ROW'S OWN PLANE, of the canonical s-vector entry of the challenge vector THE
VERIFIER PUT ON THE WIRE. `H` and `i` are universally quantified; there is no row count in any
bound.

`hcond` is "row `i` is a conditional-add row" said as a fact about WHERE the row sits in the Horner
schedule (`i % (w + 1) ≠ 0`) rather than about a column a prover fills; `hdbl : T i DBL = 0` falls
out of it and the pattern. `hpl` is arithmetic — `planeAt_lt` supplies it from `i < planes·(w+1)`.

⚑ **The hypotheses are INHABITED** — §5d exhibits an eight-row trace satisfying `hrow` on every row
and `hstart`/`hpi`/`hwin`/`hdblpat` on every window, decided in the kernel. Without that this
theorem could be true because nothing satisfies it. -/
theorem derived_row_bit_is_the_wire_svec_bit
    (nb w planes idx i H : Nat) (T : WTrace) (pv : Nat → ℤ)
    (hrow : acceptB (deriveRowGates nb planes) (T i) = true)
    (hstart : DeriveStartAccepted nb T)
    (hpi : DerivePiAccepted nb T pv)
    (hwin : ∀ r, r + 1 < H → DeriveWindowAccepted nb T r)
    (hdblpat : DblPattern w T H)
    (hi : i < H)
    (hgidx : T i GIDX = (idx : ℤ))
    (hcond : i % (w + 1) ≠ 0)
    (hpl : planeAt w i < planes) :
    T i BIT
      = ((sNat (csOfPi pv nb) idx / 2 ^ (planes - 1 - planeAt w i) % 2 : Nat) : ℤ) := by
  have hdbl : T i DBL = 0 := by rw [hdblpat i hi, if_neg hcond]
  exact derived_row_bit_is_block_svec_bit (T i) nb planes idx (planeAt w i) (csOfPi pv nb)
    (csOfPi_length pv nb) hrow hgidx
    (wire_forces_challenges nb T pv H hpi hwin i hi) hdbl hpl
    (pidx_is_the_plane_index nb w T H hstart hwin hdblpat i hi)

/-- ⚑⚑ **`derived_row_bit_is_manifest_digit` — THE REDUNDANCY CLAIM, at the resolution it actually
holds.** `PastaMsmBound.manifestRow` declares trace row `i`'s digit as `scalarDigit scal planes
(lo + termAt w i) (planeAt w i)` — an INDEX argument and a PLANE argument. This theorem reproduces
BOTH from the emitted derivation: the index through `hgidx` (which `PastaMsmBound.bound_forces_gidx`
supplies from the same manifest) and the plane through the emitted plane thread. So on a satisfying
trace the manifest's `digit` field is derived twice and the second copy checks nothing a satisfying
trace could violate.

⚠ The manifest's other three fields are NOT redundant and this changes nothing about them: **no
emitted gate in this file relates a generator INDEX to generator COORDINATES.** Delete the manifest
and the substituted-generator forgery — same row key, same digit, a DIFFERENT real SRS point — has a
satisfying trace. The manifest stays; what is now one item long is the list of forgeries it is the
SOLE defence against. -/
theorem derived_row_bit_is_manifest_digit
    (nb w planes idx N i H : Nat) (T : WTrace) (pv : Nat → ℤ)
    (hidx : idx < N)
    (hrow : acceptB (deriveRowGates nb planes) (T i) = true)
    (hstart : DeriveStartAccepted nb T)
    (hpi : DerivePiAccepted nb T pv)
    (hwin : ∀ r, r + 1 < H → DeriveWindowAccepted nb T r)
    (hdblpat : DblPattern w T H)
    (hi : i < H)
    (hgidx : T i GIDX = (idx : ℤ))
    (hcond : i % (w + 1) ≠ 0)
    (hpl : planeAt w i < planes) :
    T i BIT
      = ((scalarDigit (sScalars (csOfPi pv nb) N) planes idx (planeAt w i) : Nat) : ℤ) := by
  rw [Dregg2.Circuit.Emit.PastaMsmScalarBound.digit_is_block_svec_bit
        (csOfPi pv nb) N planes idx (planeAt w i) hidx]
  exact derived_row_bit_is_the_wire_svec_bit nb w planes idx i H T pv hrow hstart hpi hwin
    hdblpat hi hgidx hcond hpl

#assert_axioms head_of_map
#assert_axioms limb_split
#assert_axioms mulSel_forces
#assert_axioms chain_forces
#assert_axioms sum_indicator
#assert_axioms sel_forces
#assert_axioms bool_of_map
#assert_axioms all_zero_of_sum_zero
#assert_axioms bool_sum_one_unique
#assert_axioms sel_shape_forced
#assert_axioms sel_forces_closed
#assert_axioms msbBits_unique
#assert_axioms lsbBits_unique
#assert_axioms sBits_sum
#assert_axioms canon_sum
#assert_axioms canon_forces
#assert_axioms sBits_are_the_digits
#assert_axioms gidxBits_are_testBits
#assert_axioms sAt_as_range_prod
#assert_axioms derived_is_sNat
#assert_axioms derived_row_bit_is_block_svec_bit
#assert_axioms derived_row_bit_is_manifest_digit_at_a_named_plane
#assert_axioms wireAccept_forces
#assert_axioms mem_chalPin
#assert_axioms mem_chalThread
#assert_axioms pidxStart_forces
#assert_axioms pidxThread_forces
#assert_axioms chalPin_forces
#assert_axioms chalThread_forces
#assert_axioms chal_is_the_wire
#assert_axioms chalOf_is_piChal
#assert_axioms csOfPi_length
#assert_axioms csOfPi_getD
#assert_axioms wire_forces_challenges
#assert_axioms pidx_counts_doublings
#assert_axioms count_doublings
#assert_axioms pidx_is_the_plane_index
#assert_axioms dblPattern_of_manifest
#assert_axioms notLookup_map
#assert_axioms deriveGates_noLookup
#assert_axioms deriveRowDesc_constraints_split
#assert_axioms derive_lookupLog
#assert_axioms derive_balance_transport
#assert_axioms planeAt_lt
#assert_axioms derived_row_bit_is_the_wire_svec_bit
#assert_axioms derived_row_bit_is_manifest_digit

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

/-- ⚑ The row's CANONICITY CERTIFICATE: the `p`-th bit of `q − 1 − s`, LSB-first. The honest prover
computes it; there is no search. It EXISTS for every real s-vector entry precisely because such an
entry is a reduced Pallas scalar, which is the fact §2.7's gate turns into a constraint. -/
def katCert (ds : List Nat) (idx p : Nat) : Nat := (qN - 1 - katS ds idx) / 2 ^ p % 2

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
  else if CBc 2 4 0 ≤ c ∧ c < CBc 2 4 0 + CBITS then ((katCert ds idx (c - CBc 2 4 0) : Nat) : ℤ)
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
-- ⚑ REFUTABLE — the CANONICITY CERTIFICATE alone: one bit of `q − 1 − s` moved. The certificate is
-- not a free-floating decoration the prover may fill however it likes.
#guard ! acceptB (deriveRowGates 2 4) (bump (katAsg katC katC 1 2) (CBc 2 4 0))
#guard ! acceptB (deriveRowGates 2 4) (bump (katAsg katC katC 1 2) (CBc 2 4 254))

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

/-! ### §5c — ⚑⚑ THE CANONICITY GATE, AT THE DEPLOYED PLANE COUNT.

§5 runs at `planes = 4`, where `2^planes ≪ q` and NO non-canonical representative fits the digit
budget at all — so the gap this rung closes is invisible there, and an exhibit at that shape would
be measuring nothing. It is visible at `planes = 256`: `q < 2^255`, so `s, s+q, s+2q, s+3q, s+4q`
all fit, `chainGates` accepts every one of them (`fqMulCore` witnesses a QUOTIENT, so moving the
landing block by `q` and the last quotient block by `1` leaves the gate exactly zero over ℤ) and
`sBitGates` accepts every one of them too. That is precisely what `9b88bc06e` measured on the
DEPLOYED prover: `s` and `s+q` differ at 58 of the 256 planes, and only the manifest refused.

Both polarities below are decided in the kernel over the ACTUALLY EMITTED `canonGates`. -/

/-- A row carrying a landing value `v` in the chain's last `PRc` block and a certificate `cb` in the
`CBc` block, and nothing else. §5 exercises the chain and the decomposition; this isolates the
certificate, which is the only thing this rung adds. -/
def canonAsg (v : Nat) (cb : Nat → ℤ) : Assignment := fun c =>
  if PRc 2 (2 * numLimbs) ≤ c ∧ c < PRc 2 (2 * numLimbs) + numLimbs then
    ((v / 2 ^ (limbBits * (c - PRc 2 (2 * numLimbs))) % 2 ^ limbBits : Nat) : ℤ)
  else if CBc 2 256 0 ≤ c ∧ c < CBc 2 256 0 + CBITS then cb (c - CBc 2 256 0)
  else 0

/-- The honest certificate for `v`: the bits of `q − 1 − v`, LSB-first. -/
def canonCert (v p : Nat) : ℤ := (((qN - 1 - v) / 2 ^ p % 2 : Nat) : ℤ)

-- ⚑ SATISFIABLE at the deployed plane count, across the whole admissible range — the honest
-- s-vector entry `s_1 = 5`, the bottom `0`, and the TOP `q − 1` (whose certificate is all zeros, so
-- the bound is TIGHT and not slack). A gadget that refused an honest trace would show up here.
#guard acceptB (canonGates 2 256) (canonAsg 5 (canonCert 5))
#guard acceptB (canonGates 2 256) (canonAsg 0 (canonCert 0))
#guard acceptB (canonGates 2 256) (canonAsg (qN - 1) (canonCert (qN - 1)))

-- ⚑⚑ REFUTABLE — **THE NON-CANONICAL REPRESENTATIVE.** `s + q` is the value every OTHER emitted
-- gate accepts. The certificate refuses it, and refuses it under every certificate a prover could
-- write: `q − 1 − (s + q)` is NEGATIVE, so no boolean assignment of 255 places reaches it.
#guard ! acceptB (canonGates 2 256) (canonAsg (5 + qN) (canonCert 5))
#guard ! acceptB (canonGates 2 256) (canonAsg (5 + qN) (fun _ => 0))
#guard ! acceptB (canonGates 2 256) (canonAsg (5 + qN) (fun _ => 1))
#guard ! acceptB (canonGates 2 256) (canonAsg (5 + qN) (fun p => (((2 ^ 255 - 6) / 2 ^ p % 2 : Nat) : ℤ)))
-- …and `q` itself — the representative of ZERO that is not zero, i.e. the s-vector entry `s_0 = 1`
-- shifted, which is the cheapest forgery of all — is refused.
#guard ! acceptB (canonGates 2 256) (canonAsg qN (fun p => (((2 ^ 255 - 1) / 2 ^ p % 2 : Nat) : ℤ)))
#guard ! acceptB (canonGates 2 256) (canonAsg (1 + qN) (canonCert 1))

-- ⚑ WHICH HALF DOES THE WORK, measured rather than asserted. The arithmetic gate ALONE accepts the
-- non-canonical representative once the certificate is allowed to go negative — so the 255 BOOLEAN
-- PINS are the whole content of the bound, and `CBITS` is not a formality.
#guard acceptB [cgH (canonHead 2 256)] (canonAsg (5 + qN) (fun p => if p = 0 then -6 else 0))
#guard ! acceptB (canonGates 2 256) (canonAsg (5 + qN) (fun p => if p = 0 then -6 else 0))

/-! ### §5d — ⚑⚑ THE WIRE GATES BITE, AND THE PER-ROW CHALLENGE SWAP IS THE FORGERY THEY KILL.

§5 exercises `deriveRowGates` on ONE row. The wire gates are not row-local and `acceptB` cannot
see them, so they need their own exhibit or §4e is four theorems about an object nothing satisfies.
Both polarities below are decided in the kernel over the ACTUALLY EMITTED `deriveWireGates`, on a
WHOLE TRACE at `nb = 2, planes = 4, w = 1` — eight rows, one doubling row every two, four planes.

⚑ **The forgery is the one §2.3's prose named and no theorem in this file could see before §4e:**
a prover who picks a FRESH CHALLENGE VECTOR PER ROW. `katSwapRow1`'s row 1 carries a complete,
internally consistent derivation against the OTHER block's challenges — its own challenge columns,
multipliers, running product, digits and `BIT` all agree with one another — so `deriveRowGates`
ACCEPTS it, and the guard below measures that acceptance rather than asserting it. Only the emitted
challenge thread refuses. -/

/-- The declared public inputs of the exhibit: challenge `0` is `3`, challenge `1` is `5` — this
block's own (`katC`), in the bottom limb of each nine-limb slot. -/
def katPv : Nat → ℤ := fun k =>
  if k = PI_COUNT then 3 else if k = PI_COUNT + numLimbs then 5 else 0

/-- ⚑ **The honest TRACE.** Row `i` is in plane `i / 2` and doubles iff `i` is even (`w = 1`); its
`PIDX` is that plane, its `DBL` is that pattern, its `BIT` is pinned on at a doubling row, and every
other cell is §5's honest row-local assignment at index 0 and the row's own plane. Nothing is
re-authored: the row-local half IS `katAsg`. -/
def katFull : WTrace := fun i => fun c =>
  if c = PIDX then ((i / 2 : Nat) : ℤ)
  else if c = DBL then (if i % 2 = 0 then 1 else 0)
  else if c = BIT ∧ i % 2 = 0 then 1
  else katAsg katC katC 0 (i / 2) c

/-- A one-cell perturbation of ONE ROW of a trace. -/
def bumpRow (T : WTrace) (r c : Nat) : WTrace :=
  fun i => if i = r then bump (T i) c else T i

/-- ⚑⚑ **THE PER-ROW CHALLENGE SWAP.** Row 1 derives against `katC' = [3,4]` — a different block's
challenges — consistently, and every other row is honest. -/
def katSwapRow1 : WTrace := fun i =>
  if i = 1 then
    (fun c => if c = PIDX then 0 else if c = DBL then 0 else katAsg katC' katC' 0 0 c)
  else katFull i

-- ⚑ SATISFIABLE, JOINTLY — the capstone's hypotheses are INHABITED, which is the thing a forcing
-- theorem is worthless without. Every row satisfies the ROW-LOCAL derivation…
#guard (List.range 8).all (fun i => acceptB (deriveRowGates 2 4) (katFull i))
-- …every window satisfies the WIRE gates against the SAME declared public inputs…
#guard (List.range 8).all (fun i => wireAcceptB 2 katFull katPv i)
-- …and the exhibit's `PIDX` really is `planeAt 1 i`, which is what `pidx_is_the_plane_index`
-- concludes and what `DblPattern` supplies on the way.
#guard (List.range 8).all (fun i => decide (katFull i PIDX = ((planeAt 1 i : Nat) : ℤ)))
#guard (List.range 8).all (fun i =>
  decide (katFull i DBL = (if i % (1 + 1) = 0 then 1 else 0)))

-- ⚑⚑ THE MEASUREMENT. Row 1's swapped derivation is ACCEPTED by the row-local denotation — every
-- theorem of §4–§4d sees nothing wrong with it…
#guard acceptB (deriveRowGates 2 4) (katSwapRow1 1)
-- …and REFUSED by the emitted challenge thread on the window that spans rows 0 and 1. A first-row
-- pin ALONE would not refuse it: row 0 is untouched and its PI pin still holds.
#guard ! wireAcceptB 2 katSwapRow1 katPv 0
#guard wireAcceptB 2 katSwapRow1 katPv 2

-- ⚑ REFUTABLE — the PI PIN alone: row 0's challenge limb differing from its declared public input.
#guard ! wireAcceptB 2 (bumpRow katFull 0 (CHc 2 0)) katPv 0
-- ⚑ REFUTABLE — the ORIGIN PIN alone: the plane thread starting anywhere but plane 0.
#guard ! wireAcceptB 2 (bumpRow katFull 0 PIDX) katPv 0
-- ⚑ REFUTABLE — the PLANE THREAD alone: a row claiming a plane that is not its own. This is the
-- tooth that makes `hpidx` a theorem instead of a hypothesis — without it a prover reads the right
-- scalar's digit at whatever plane it likes, and the manifest's PLANE argument is unchecked.
#guard ! wireAcceptB 2 (bumpRow katFull 2 PIDX) katPv 1
-- ⚑ …and the plane thread is not satisfied by an arbitrary monotone column either: advancing on a
-- NON-doubling row is refused too.
#guard ! wireAcceptB 2 (bumpRow katFull 1 PIDX) katPv 0

/-! ## §6 — ⚑⚑ WHAT THIS FILE DOES NOT DO.

Every sibling in this family carries this section and until now this one did not — while its header
forward-referenced a `§6` that did not exist, so the residuals were named NOWHERE and a Rust test
comment stated the stronger reading. What follows is the list, at the resolution it is true at.

### §6.1 — the hypotheses that remain CARRIED, and whose they are

`derived_row_bit_is_manifest_digit` takes six hypotheses beyond the emitted gates. Three are
discharged elsewhere in this file (`hstart`, `hpi`, `hwin` are the emitted wire gates themselves,
and §5d exhibits a trace satisfying all three). The rest:

1. **`hgidx : T i GIDX = idx` — NOT this file's.** `PastaMsmBound.bound_forces_gidx` forces the row's
   term-index column to the ABSOLUTE generator index, from the emitted lookup's exact-public
   balance. No gate here touches `GIDX` except to read its digits.
2. **`hdblpat : DblPattern w T H` — DISCHARGED, and now all the way down.**
   `dblPattern_of_manifest` derives it from `PastaMsmBound.row_tuple_is_its_manifest_row`'s
   conclusion plus `tidx_is_the_row_index`, and §4e.1's `derive_balance_transport` carries the
   exact-public balance from the DEPLOYED `deriveRowDesc` to the `boundRowDesc` those two theorems
   consume — so the chain runs: emitted lookup ⟹ manifest per row ⟹ `DBL` pattern ⟹ `PIDX =
   planeAt w i`. (An earlier revision of this list called that transport "a lemma nobody has
   written". It was, for about an hour. `deriveGates_noLookup` is its content: the derivation emits
   no `.lookup`, so the table is the same object by `rfl` and the lookup log is unchanged.) What a
   caller must still supply is `PastaMsmBound`'s OWN two side conditions — `htidx` from
   `tidx_is_the_row_index` and `hbit`, the `DBL` column's booleanity from the row template.
3. **`hcond : i % (w + 1) ≠ 0`** — "row `i` is a conditional-add row", which is a fact about WHERE
   the row is in the Horner schedule and not about any column. It replaces the older `hdbl : T i DBL
   = 0`, which was the same fact asserted about a column a prover fills.
4. **`hpl : planeAt w i < planes`** — arithmetic, supplied by `planeAt_lt` from `i < planes·(w+1)`.

### §6.2 — ⚑⚑ THE PUBLIC INPUTS THEMSELVES ARE NOT BOUND HERE, and that is the largest residual

`csOfPi pv nb` is *whatever the declared public inputs say*. `chalPinGates` and `chalThreadGates`
bind every row of the trace to `pv`; **nothing in this descriptor says `pv` is the Mina block's IPA
transcript challenges.** That binding is the light client's own: it recomputes the transcript and
supplies the PI vector, and if it supplies the wrong one, every theorem in this file is still true
and the conclusion is about the wrong s-vector. The rung this file closes is "the trace's scalar is
the tensor of the challenges ON THE WIRE"; "the challenges on the wire are the block's" is a
different rung and is not here.

### §6.3 — the cost, priced against the deployed four-way cut

The derivation is repeated once per ROW rather than once per TERM — exactly `planes`-fold redundant
WORK. It is nearly free because **an AIR's columns are global**: the derivation's `WD 15 256 − WOC =
1332` columns are committed on all `planes·(w+1)` rows whichever rows the gates fire on, and FRI
pays for committed area. A stride-`k` window arm firing only on plane-0 rows would commit the same
area and RAISE the gate degree (a guard is a multiplication), so it is strictly worse.

The one shape that IS cheaper is a SEPARATE, SHORTER instance — `w + 1` rows, not `planes·(w+1)` —
tied to the MSM rows by a bus. That needs a `provide` dual of `Lookup`, which this IR does not have:
`descriptor_ir2.rs`'s main arm calls `LookupBus::lookup_key` with multiplicity `ONE` and never
`table_entry`. Its price, at the deployed shape, decided in the kernel below rather than asserted:
the derivation block is 5,455,872 of the cut's 8,728,576 committed cells — **62.5% of everything the
deployed proof commits** — and the bussed shape would be 21,312, a factor of exactly `planes`. That
is the cost rung, and it is an IR change, not a re-parameterisation.

### §6.4 — K1, inherited unchanged

Every forcing theorem here — §4's and §4e's alike — is the ℤ reading of the emitted bodies. The
deployed prover reads the same bodies in BabyBear, where a weighted boolean sum can wrap.
`PastaMsmWindowed` §6.2 names that gap and this rung does not narrow it. `DeriveStartAccepted` /
`DerivePiAccepted` / `DeriveWindowAccepted` are stated the same way and inherit it identically; the
deployed `VmConstraint.holdsVm` and `WindowConstraint.holdsAt` both read `≡ 0 [ZMOD 2013265921]`.

### §6.5 — the manifest is still load-bearing, and `wireAcceptB` is fail-open by construction

**No emitted gate in this file relates a generator INDEX to generator COORDINATES.** Delete the
manifest and the substituted-generator forgery — same row key, same digit, a DIFFERENT real SRS
point — has a satisfying trace. The manifest stays; §4f only shortens the list of forgeries it is
the sole defence against to that one.

⚠ And `wireAcceptB`'s `match` ends in `_ => true`. That is correct for the four constructors
`deriveWireGates` emits today and it is a FAIL-OPEN shape: a fifth constructor added to that list
would be silently accepted by every `#guard` in §5d while `wireAccept_forces` kept proving three
predicates that no longer cover the emitted object. Any addition to `deriveWireGates` must extend
`wireAcceptB`'s match and the three predicates in the same commit. -/

-- ⚑ THE PRICE, AS AN OBJECT — the §6.3 arithmetic, decided rather than asserted. 4 slices,
-- `planes·(w+1) = 1024` rows each, `w = 3`.
#guard WD 15 256 - WOC == 1332
#guard 4 * (256 * (3 + 1)) * WD 15 256 == 8728576
#guard 4 * (256 * (3 + 1)) * (WD 15 256 - WOC) == 5455872
#guard 4 * (3 + 1) * (WD 15 256 - WOC) == 21312
#guard 5455872 / 21312 == 256
-- …and the canonicity certificate's own share of that, which §2.7 costs and nothing else does.
#guard 4 * (256 * (3 + 1)) * CBITS == 1044480

end Dregg2.Circuit.Emit.PastaMsmScalarDerive
