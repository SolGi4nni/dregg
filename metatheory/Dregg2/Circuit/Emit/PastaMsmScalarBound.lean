/-
# Dregg2.Circuit.Emit.PastaMsmScalarBound — the SCALARS, derived from the block's own challenges.

## Substrate, said out loud

**Lean-authored AIR.** This file adds no constraint of its own: it INSTANTIATES the emitted object
`PastaMsmBound.boundRowDesc` — whose every constraint is a `def` returning `VmConstraint2` — at a
scalar column that is a FUNCTION of the block's 15 IPA challenges, and proves what the ALREADY
EMITTED lookup then forces. No table is added, no manifest column is added, no wire id changes, and
the constraint count stays 82. Rust authors no constraint, no builder gadget, no `air_accepts`.

## The hole this file closes

`19638920d` bound the slice CONTENTS and named what it had not: *the manifest's generators are
Mina's; its DIGITS are a reproducible sequence, not the block's s-vector.* `bound_forces_digit`
proved a row's `BIT` column is the manifest's declared digit — of an arbitrary `scal : List Nat`
parameter that nothing tied to the block. So a verified proof said "these rows carry Mina's real
generators, folded by the RCB formula" over digits nobody had tied to anything.

## The structure that makes it affordable — and it is `sVec_eq_bPoly`'s

The terminal MSM has `2^15 = 32,768` terms, so the naive binding is 32,768 witnessed scalars — over
8,000× the deployed exact-public row cap, and a manifest that would have to be TRUSTED to be the
right list. K4c (`PastaIPA.sVec_eq_bPoly`) says the s-vector is the coefficient vector of
`b(X) = ∏_j (1 + c_j X^{2^j})`, i.e. `s_i = ∏_j c_j^{bit_j(i)}` — a TENSOR. `sAt` below is that
tensor read at ONE index: `|cs|` multiplications, one per challenge, testing one bit of `i` each.
`sVec_getElem?_eq_sAt` proves `sAt` IS the s-vector's `i`-th entry, so nothing is re-modelled.

Every theorem here is therefore ROW-COUNT-INDEPENDENT in the strong sense: `i`, `w`, `planes` and
`N` are universally quantified and occur in no bound, and no statement or proof ever materialises a
`2^15` list. `#guard BLOCK_S 32767` computes the LAST term of the 32,768-term MSM in 15
multiplications, in the kernel, from the block's own derived challenges.

## What is bound, and to WHAT

`MinaWrapOpeningGate.CHAL_F` is not a fixture: `#guard ipaTranscript CIP_SHIFTED LR_XY DELTA_XY ==
(T_FQ, IPA_PRECHALS, C_PRE)` runs the block's own Fq sponge forward, and
`derived_ipa_challenges : IPA_PRECHALS.map (endoMap ENDO_R) = CHAL_F` lifts its 15 outputs. So the
chain this file completes is

  block proof bytes → sponge → 15 prechallenges → endo → `CHAL_F` → `sAt` → digit → manifest →
  (the EMITTED lookup, `PublicLookupBalanced`) → the trace's `BIT` column.

## The tamper — §6, and it is the rung's defining test

A row whose digit is *a different valid s-vector entry* — the s-vector of a DIFFERENT block's
challenges, every row key identical, every generator identical, every `DBL` identical, the forgery
internally consistent — is REFUSED, and the same forged trace is exhibited BALANCING against its own
manifest so the refusal is the binding and not a malformity.

## What it does NOT buy — read §7 before citing this

The digit is bound to the DESCRIPTOR's manifest, which is a `def` of the challenges; the tensor is
not recomputed INSIDE the AIR. §7.1 prices what would be needed and why this IR cannot express it
today. The RCB→group-law transport, ℤ↔felt (K1), P10 and the 128-row exact-public cap are all
inherited unchanged.

## Axiom hygiene

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/
`native_decide`. `#guard`s reduce in the kernel. Imports read-only. Import line:
`import Dregg2.Circuit.Emit.PastaMsmScalarBound`
-/
import Dregg2.Circuit.Emit.PastaMsmBound
import Dregg2.Circuit.Emit.PastaIPA
import Dregg2.Circuit.Emit.MinaWrapOpeningGate

namespace Dregg2.Circuit.Emit.PastaMsmScalarBound

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 VmTrace exactPublicTable
  PublicLookupBalanced)
open Dregg2.Circuit.Emit.PastaField (qN)
open Dregg2.Circuit.Emit.PastaMsmWindowed (SRCX BIT DBL)
open Dregg2.Circuit.Emit.PastaMsmSliced (sliceLo)
open Dregg2.Circuit.Emit.PastaIPA (sVec sVec_length)
open Dregg2.Circuit.Emit.PastaMsmBound (Pt PTLIMBS TIDX GIDX coordLimb scalarDigit termAt planeAt
  manifestRow genManifest boundRowDesc tupleOf rowAt)
open Dregg2.Circuit.Emit.MinaWrapOpeningGate (Fq CHAL CHAL_F)

set_option autoImplicit false

/-! ## §1 — THE TENSOR ENTRY: the `i`-th s-vector entry, WITHOUT the s-vector.

`PastaIPA.sVec` is the doubling recursion `s ↦ s ++ (c · s)`, so it materialises `2^k` entries.
`sAt` reads ONE entry of that same object by descending the same recursion and testing one bit of
the index per challenge: `|cs|` multiplications, no list. §1b proves the two agree. -/

/-- ⚑ **The `i`-th entry of `PastaIPA.sVec cs`, computed in `|cs|` multiplications.** The head
challenge pairs with the HIGH bit, matching `sVec`'s `s ++ (c · s)` (the upper half is the one
scaled by the head). -/
def sAt {F : Type} [CommRing F] : List F → Nat → F
  | [], _ => 1
  | c :: rest, i => (if Nat.testBit i rest.length then c else 1) * sAt rest i

/-- The same product as a LIST of factors — one factor per challenge, each either `1` or `c_j`.
`sFactors_length` is the row-count independence, said as an object: the work is `|cs|`, never
`2^|cs|`. -/
def sFactors {F : Type} [CommRing F] : List F → Nat → List F
  | [], _ => []
  | c :: rest, i => (if Nat.testBit i rest.length then c else 1) :: sFactors rest i

/-- ⚑ **`sFactors_length`** — the derivation of ANY entry costs exactly `|cs|` factors, whatever
`i` is. At `|cs| = 15` that is 15, and the s-vector it indexes has 32,768 entries. -/
theorem sFactors_length {F : Type} [CommRing F] (cs : List F) (i : Nat) :
    (sFactors cs i).length = cs.length := by
  induction cs with
  | nil => rfl
  | cons c rest ih => simp [sFactors, ih]

/-- `sAt` IS that product. -/
theorem sAt_eq_prod {F : Type} [CommRing F] (cs : List F) (i : Nat) :
    sAt cs i = (sFactors cs i).prod := by
  induction cs with
  | nil => simp [sAt, sFactors]
  | cons c rest ih => simp [sAt, sFactors, List.prod_cons, ih]

/-- `sAt cs` reads only bits `0 .. |cs|-1` of its index — which is what lets the high half of the
doubling recursion reuse the low half's value. -/
theorem sAt_congr {F : Type} [CommRing F] :
    ∀ (cs : List F) (a b : Nat),
      (∀ j, j < cs.length → Nat.testBit a j = Nat.testBit b j) → sAt cs a = sAt cs b := by
  intro cs
  induction cs with
  | nil => intro a b _; rfl
  | cons c rest ih =>
    intro a b h
    have hh := h rest.length (by simp only [List.length_cons]; omega)
    have hr := ih a b (fun j hj => h j (by simp only [List.length_cons]; omega))
    simp only [sAt, hh, hr]

/-! ### §1b — the identity with `sVec`, so this is K4c's object and not a second model. -/

/-- ⚑⚑ **`sVec_getElem?_eq_sAt`** — the tensor read IS the s-vector's `i`-th entry. Every statement
below that mentions `sAt` is therefore a statement about `PastaIPA.sVec`, the list
`sVec_eq_bPoly` proves is `b_poly_coefficients`. -/
theorem sVec_getElem?_eq_sAt {F : Type} [CommRing F] :
    ∀ (cs : List F) (i : Nat), i < 2 ^ cs.length → (sVec cs)[i]? = some (sAt cs i) := by
  intro cs
  induction cs with
  | nil =>
    intro i hi
    have hz : i = 0 := by simpa using hi
    subst hz
    rfl
  | cons c rest ih =>
    intro i hi
    have hlen : (sVec rest).length = 2 ^ rest.length := sVec_length rest
    have hsplit : sVec (c :: rest) = sVec rest ++ (sVec rest).map (fun z => z * c) := rfl
    rw [List.length_cons, pow_succ] at hi
    by_cases hlt : i < 2 ^ rest.length
    · have htb : Nat.testBit i rest.length = false := Nat.testBit_lt_two_pow hlt
      rw [hsplit, List.getElem?_append_left (by rw [hlen]; exact hlt), ih i hlt]
      simp [sAt, htb]
    · have hge : 2 ^ rest.length ≤ i := Nat.le_of_not_lt hlt
      obtain ⟨r, hr, rfl⟩ : ∃ r, r < 2 ^ rest.length ∧ i = 2 ^ rest.length + r :=
        ⟨i - 2 ^ rest.length, by omega, by omega⟩
      have htb : Nat.testBit (2 ^ rest.length + r) rest.length = true := by
        rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hr]; rfl
      have hcong : sAt rest r = sAt rest (2 ^ rest.length + r) :=
        sAt_congr rest r (2 ^ rest.length + r)
          (fun j hj => (Nat.testBit_two_pow_add_gt hj r).symm)
      have hidx : 2 ^ rest.length + r - (sVec rest).length = r := by rw [hlen]; omega
      rw [hsplit, List.getElem?_append_right (by rw [hlen]; omega), hidx,
        List.getElem?_map, ih r hr]
      simp [sAt, htb, hcong, mul_comm]

#assert_axioms sFactors_length
#assert_axioms sAt_eq_prod
#assert_axioms sAt_congr
#assert_axioms sVec_getElem?_eq_sAt

/-! ## §2 — THE SCALAR COLUMN, DERIVED.

`PastaMsmBound.boundRowDesc` takes the scalars as a parameter. `sScalars` is that parameter as a
FUNCTION OF THE CHALLENGES: `N` bounds the indices the manifest reads, and `sScalars_getD` reads it
POINTWISE — the proofs never evaluate the list, so `N = 2^15` costs the same as `N = 2`. -/

/-- The block-derived scalar at ABSOLUTE index `i`, as the `Nat` the manifest carries. -/
def sNat (cs : List Fq) (i : Nat) : Nat := (sAt cs i).val

/-- The descriptor's scalar column. Not a fixture and not a witness: a function of `cs`. -/
def sScalars (cs : List Fq) (N : Nat) : List Nat := (List.range N).map (sNat cs)

/-- Pointwise read — the only way any theorem below touches `sScalars`. -/
theorem sScalars_getD (cs : List Fq) (N i : Nat) (hi : i < N) :
    (sScalars cs N).getD i 0 = sNat cs i := by
  simp [sScalars, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]

/-- ⚑ **`sNat_is_svec_entry`** — the derived scalar IS the block's s-vector entry, in the exact
shape `MinaWrapSgCore.SVEC` is DEFINED to be (`(PastaIPA.sVec CHAL_F).map ZMod.val`, `rfl`). -/
theorem sNat_is_svec_entry (cs : List Fq) (i : Nat) (hi : i < 2 ^ cs.length) :
    sNat cs i = ((sVec cs).map ZMod.val).getD i 0 := by
  simp [sNat, List.getD_eq_getElem?_getD, List.getElem?_map, sVec_getElem?_eq_sAt cs i hi]

/-- ⚑ **The CONTENTS-AND-SCALARS-BOUND descriptor.** `PastaMsmBound.boundRowDesc` verbatim — same
constraints, same table, same wire id, same manifest arity — with the scalar column derived from
the block's own IPA challenges. -/
def blockScalarDesc (cs : List Fq) (N n k w planes : Nat) (gens : List Pt) : EffectVmDescriptor2 :=
  boundRowDesc n k w planes gens (sScalars cs N)

/-- Nothing was re-authored: still the sliced descriptor's 78 constraints as a PREFIX. -/
theorem blockScalarDesc_extends_sliced (cs : List Fq) (N n k w planes : Nat) (gens : List Pt) :
    (Dregg2.Circuit.Emit.PastaMsmSliced.slicedRowDesc n k w).constraints <+:
      (blockScalarDesc cs N n k w planes gens).constraints :=
  Dregg2.Circuit.Emit.PastaMsmBound.boundRowDesc_extends_sliced n k w planes gens (sScalars cs N)

/-- Still 82 emitted constraints — this rung adds none. -/
theorem blockScalarDesc_constraints_length (cs : List Fq) (N n k w planes : Nat) (gens : List Pt) :
    (blockScalarDesc cs N n k w planes gens).constraints.length = 82 :=
  Dregg2.Circuit.Emit.PastaMsmBound.boundRowDesc_constraints_length n k w planes gens
    (sScalars cs N)

#assert_axioms sScalars_getD
#assert_axioms sNat_is_svec_entry
#assert_axioms blockScalarDesc_extends_sliced
#assert_axioms blockScalarDesc_constraints_length

-- ⚑ THE BUS HAZARD, RE-PINNED. This file adds no table and changes no manifest arity, so the
-- per-slice `GEN_TID k` split that keeps four co-batched slices off ONE LogUp bus is untouched —
-- and it is re-checked here rather than assumed, because a shared bus would let slice `j` cancel
-- slice `k`'s manifest and pool their scalars exactly as it would pool their generators.
#guard ((List.range 4).map (fun k => (Dregg2.Circuit.Emit.PastaMsmBound.GEN_TID k).wireId)).dedup.length == 4
#guard Dregg2.Circuit.Emit.PastaMsmBound.TUP == 30
#guard Dregg2.Circuit.Emit.PastaMsmBound.PTLIMBS == 27

/-! ## §3 — THE MANIFEST'S DIGIT IS THE BLOCK'S S-VECTOR BIT. -/

/-- The digit the emitted manifest declares at ABSOLUTE index `idx`, bit plane `plane`, once the
scalar column is challenge-derived: the `plane`-th binary digit (MSB-first over `planes` planes) of
the block's own s-vector entry. -/
theorem digit_is_block_svec_bit (cs : List Fq) (N planes idx plane : Nat) (hidx : idx < N) :
    scalarDigit (sScalars cs N) planes idx plane
      = sNat cs idx / 2 ^ (planes - 1 - plane) % 2 := by
  unfold scalarDigit
  rw [sScalars_getD cs N idx hidx]

/-- ⚑ **`manifest_digit_is_block_bit`** — said of the EMITTED manifest row: the third field of the
row the descriptor carries for trace row `i` is the block-derived bit at the absolute index that
same row names. `i`, `w`, `planes` and `N` occur in no bound. -/
theorem manifest_digit_is_block_bit (cs : List Fq) (N lo w planes i : Nat) (gens : List Pt)
    (hb : i % (w + 1) ≠ 0) (hN : lo + termAt w i < N) :
    (manifestRow lo w planes gens (sScalars cs N) i).getD 2 0
      = sNat cs (lo + termAt w i) / 2 ^ (planes - 1 - planeAt w i) % 2 := by
  rw [manifestRow, if_neg hb]
  simpa using digit_is_block_svec_bit cs N planes (lo + termAt w i) (planeAt w i) hN

#assert_axioms digit_is_block_svec_bit
#assert_axioms manifest_digit_is_block_bit

/-! ## §4 — ⚑⚑ THE FORCING: a satisfying trace's `BIT` column is the BLOCK'S s-vector bit.

The emitted lookup already forces the trace row to BE its manifest row
(`PastaMsmBound.row_tuple_is_its_manifest_row`); §3 says what that manifest row's digit is. The
composition is the deliverable, and it is row-count-independent: `i`, `w`, `planes`, `N` are
universally quantified and occur in no bound, so the statement at `planes*(w+1) = 128` is the
statement at `1,056,896`. -/

section Forcing
variable (cs : List Fq) (N n k w planes : Nat) (gens : List Pt) (t : VmTrace) (i : Nat)

/-- ⚑⚑ **`bound_forces_block_digit`** — **the theorem this rung exists for.** On a trace whose
emitted lookup multiset balances against the emitted manifest, whose `TIDX` column is the threaded
row index and whose `DBL` column is a bit, a conditional-add row's `BIT` column is the
`planeAt w i`-th binary digit of `s_{lo+t}`, the s-vector entry DERIVED from the block's own 15 IPA
challenges — not of any scalar list a prover chose. -/
theorem bound_forces_block_digit
    (hbal : PublicLookupBalanced (blockScalarDesc cs N n k w planes gens) t)
    (hlen : t.rows.length = planes * (w + 1))
    (htidx : ∀ j, j < t.rows.length → rowAt t j TIDX = (j : ℤ))
    (hdbl : ∀ j, rowAt t j DBL = 0 ∨ rowAt t j DBL = 1)
    (hi : i < planes * (w + 1)) (hb : i % (w + 1) ≠ 0)
    (hN : sliceLo w k + termAt w i < N) :
    rowAt t i BIT
      = ((sNat cs (sliceLo w k + termAt w i) / 2 ^ (planes - 1 - planeAt w i) % 2 : Nat) : ℤ) := by
  have hbal' : PublicLookupBalanced (boundRowDesc n k w planes gens (sScalars cs N)) t := hbal
  have hrow := Dregg2.Circuit.Emit.PastaMsmBound.row_tuple_is_its_manifest_row
    n k w planes gens (sScalars cs N) t i hbal' hlen htidx hdbl hi
  have hiL : i < t.rows.length := by omega
  have hd := Dregg2.Circuit.Emit.PastaMsmBound.bound_forces_dbl_off
    k w planes gens (sScalars cs N) t i hrow hb (htidx i hiL) (hdbl i)
  have hbit := Dregg2.Circuit.Emit.PastaMsmBound.bound_forces_digit
    k w planes gens (sScalars cs N) t i hrow hb hd
  rw [hbit, digit_is_block_svec_bit cs N planes _ _ hN]

/-- ⚑⚑ **`bound_row_is_block_term`** — **BOTH HALVES, in one statement.** A conditional-add row's
`SRC` limb columns are the limbs of the generator at the ABSOLUTE index the manifest names, its
`GIDX` column IS that absolute index, and its `BIT` column is the block-derived s-vector bit at that
same index. Generators from the manifest, digits from the block's challenges, joined at ONE index —
which is what makes the row a term of the block's own `⟨s, srs.g⟩` and not of a shape. -/
theorem bound_row_is_block_term
    (hbal : PublicLookupBalanced (blockScalarDesc cs N n k w planes gens) t)
    (hlen : t.rows.length = planes * (w + 1))
    (htidx : ∀ j, j < t.rows.length → rowAt t j TIDX = (j : ℤ))
    (hdbl : ∀ j, rowAt t j DBL = 0 ∨ rowAt t j DBL = 1)
    (hi : i < planes * (w + 1)) (hb : i % (w + 1) ≠ 0)
    (hN : sliceLo w k + termAt w i < N) :
    (∀ j, j < PTLIMBS →
        rowAt t i (SRCX + j)
          = ((coordLimb (gens.getD (sliceLo w k + termAt w i) (0, 0, 0)) j : Nat) : ℤ))
      ∧ rowAt t i GIDX = ((sliceLo w k + termAt w i : Nat) : ℤ)
      ∧ rowAt t i BIT
          = ((sNat cs (sliceLo w k + termAt w i) / 2 ^ (planes - 1 - planeAt w i) % 2 : Nat) : ℤ)
      ∧ rowAt t i DBL = 0 := by
  have hbal' : PublicLookupBalanced (boundRowDesc n k w planes gens (sScalars cs N)) t := hbal
  have hrow := Dregg2.Circuit.Emit.PastaMsmBound.row_tuple_is_its_manifest_row
    n k w planes gens (sScalars cs N) t i hbal' hlen htidx hdbl hi
  have hiL : i < t.rows.length := by omega
  have hd := Dregg2.Circuit.Emit.PastaMsmBound.bound_forces_dbl_off
    k w planes gens (sScalars cs N) t i hrow hb (htidx i hiL) (hdbl i)
  refine ⟨Dregg2.Circuit.Emit.PastaMsmBound.bound_forces_source_limbs
            k w planes gens (sScalars cs N) t i hrow hb hd,
          Dregg2.Circuit.Emit.PastaMsmBound.bound_forces_gidx
            k w planes gens (sScalars cs N) t i hrow hb hd,
          ?_, hd⟩
  exact bound_forces_block_digit cs N n k w planes gens t i hbal hlen htidx hdbl hi hb hN

end Forcing

#assert_axioms bound_forces_block_digit
#assert_axioms bound_row_is_block_term

/-! ## §5 — THE REAL BLOCK: Mina devnet 539508's own s-vector, 15 multiplications at a time. -/

/-- ⚑ **The block's s-vector entry at absolute index `i`** — from `CHAL_F`, which
`MinaWrapOpeningGate` DERIVES by running the block's Fq sponge forward
(`#guard ipaTranscript … == (T_FQ, IPA_PRECHALS, C_PRE)`) and lifting through `endoMap ENDO_R`
(`derived_ipa_challenges`). No fixture, and no 32,768-entry list. -/
def BLOCK_S (i : Nat) : Nat := sNat CHAL_F i

/-- The block carries 15 IPA challenges, so its s-vector has `2^15` entries. -/
theorem chal_f_length : CHAL_F.length = 15 := by simp [CHAL_F, CHAL]

/-- ⚑ **`block_s_is_svec_entry`** — `BLOCK_S i` IS the `i`-th entry of the block's s-vector, in the
exact shape `MinaWrapSgCore.SVEC` is DEFINED as (`(PastaIPA.sVec CHAL_F).map ZMod.val` — that
module's `def`, so this is its `i`-th entry by `rfl`, not by transcription). That module needs
~75 GB per chunk and is allowlisted out of the root; this statement needs none of it. -/
theorem block_s_is_svec_entry (i : Nat) (hi : i < 32768) :
    BLOCK_S i = ((sVec CHAL_F).map ZMod.val).getD i 0 :=
  sNat_is_svec_entry CHAL_F i (by rw [chal_f_length]; exact hi)

/-- ⚑ **`block_s_fits_255`** — every scalar of the terminal MSM fits the 255-bit budget
`PastaIpaFold.msmHorner_eq_msmN` requires. `MinaWrapSgCore.svec_fits_255` is the same fact by
`decide` over 32,768 entries; this is the same fact for EVERY index at once, in three lines, because
an s-vector entry is a field element and `q < 2^255`. -/
theorem block_s_fits_255 (i : Nat) : BLOCK_S i < 2 ^ 255 := by
  haveI : NeZero qN := ⟨by decide⟩
  have h1 : (sAt CHAL_F i).val < qN := ZMod.val_lt _
  have h2 : qN < 2 ^ 255 := by decide
  exact Nat.lt_trans h1 h2

#assert_axioms chal_f_length
#assert_axioms block_s_is_svec_entry
#assert_axioms block_s_fits_255

-- ⚑ NON-VACUITY, on the block's OWN challenges, in the kernel. `sAt`'s head challenge pairs with
-- the HIGH bit, so index `2^j` selects challenge `14 - j`.
#guard BLOCK_S 0 == 1
#guard BLOCK_S 1 == CHAL.getD 14 0
#guard BLOCK_S 2 == CHAL.getD 13 0
#guard BLOCK_S 16384 == CHAL.getD 0 0
#guard BLOCK_S 3 == ((CHAL_F.getD 13 0) * (CHAL_F.getD 14 0)).val
-- ⚑ THE LAST TERM OF THE 32,768-TERM MSM, computed in 15 multiplications: index `2^15 - 1` has
-- every bit set, so its scalar is the product of all 15 of the block's challenges.
#guard BLOCK_S 32767 == (CHAL_F.foldl (fun a b => a * b) 1).val
-- …and the challenges are load-bearing: perturb ONE and the entry moves.
#guard BLOCK_S 1 != (sAt (CHAL_F.set 14 (CHAL_F.getD 14 0 + 1)) 1).val

/-! ## §6 — ⚑⚑ THE TAMPER: A DIFFERENT BLOCK'S S-VECTOR IS REFUSED.

Both polarities over the ACTUALLY EMITTED manifest and the ACTUALLY EMITTED tuple, at
`(w, planes) = (2, 5)` — 15 rows, five doubling rows and ten conditional adds, two generators, so
the slice reaches an index where two challenge vectors disagree.

The forgery is not a malformity. It is the s-vector of a DIFFERENT challenge vector, laid into the
same schedule: same row keys, same `GIDX` thread, same `DBL` pattern, same generators, every RCB
add still holding. §6b exhibits it BALANCING against its own manifest — so what refuses it below is
the binding to THIS block's challenges and nothing else. -/

/-- Two challenges — a whole s-vector in four entries, so the tamper is a kernel decision. -/
def katC : List Fq := [(3 : Fq), (5 : Fq)]

/-- ⚑ A DIFFERENT block's challenges: one round's challenge differs. -/
def katC' : List Fq := [(3 : Fq), (6 : Fq)]

/-- Two exhibited generators. Not on-curve and not meant to be: what is under test is the SCALAR
binding, which is a multiset fact about the digit column. -/
def katG : List Pt := [(5, 7, 1), (11, 13, 1)]

/-- ⚑ The HONEST row for trace row `i` of the emitted schedule: a plane-boundary row doubles (its
tuple collapses to the manifest's all-zero row), every other row carries its own threaded key, the
absolute generator index, the declared digit and the generator's limbs. -/
def katRow (lo w planes : Nat) (gens : List Pt) (scal : List Nat) (i : Nat) : Assignment :=
  if i % (w + 1) = 0 then
    fun c => if c = DBL then 1 else if c = TIDX then (i : ℤ) else 0
  else
    fun c =>
      if c = TIDX then (i : ℤ)
      else if c = GIDX then ((lo + termAt w i : Nat) : ℤ)
      else if c = BIT then ((scalarDigit scal planes (lo + termAt w i) (planeAt w i) : Nat) : ℤ)
      else if SRCX ≤ c ∧ c < SRCX + PTLIMBS then
        ((coordLimb (gens.getD (lo + termAt w i) (0, 0, 0)) (c - SRCX) : Nat) : ℤ)
      else 0

/-- The honest trace of the emitted schedule. -/
def katTrace (lo w planes : Nat) (gens : List Pt) (scal : List Nat) : List Assignment :=
  (List.range (planes * (w + 1))).map (katRow lo w planes gens scal)

-- The derivation IS `sVec`, at concrete values — non-vacuity of `sVec_getElem?_eq_sAt`.
#guard sScalars katC 4 == (sVec katC).map ZMod.val
#guard sScalars katC 4 == [1, 5, 3, 15]
#guard sScalars katC' 4 == [1, 6, 3, 18]
-- …and the two blocks' s-vectors really do disagree at an index this slice reads.
#guard (sScalars katC 4).getD 1 0 != (sScalars katC' 4).getD 1 0

-- SATISFIABLE — the honest trace, digits derived from THIS block's challenges, balances against the
-- emitted manifest.
#guard decide (((katTrace 0 2 5 katG (sScalars katC 4)).map tupleOf).Perm
                 (exactPublicTable (genManifest 0 2 5 katG (sScalars katC 4))))

-- ⚑⚑ REFUTABLE — **THE WRONG BLOCK'S S-VECTOR.** Every generator identical, every row key
-- identical, every `DBL` identical; only the digits are the other block's. REFUSED.
#guard decide (¬ (((katTrace 0 2 5 katG (sScalars katC' 4)).map tupleOf).Perm
                    (exactPublicTable (genManifest 0 2 5 katG (sScalars katC 4)))))

-- ⚑ §6b — AND THE FORGERY IS INTERNALLY CONSISTENT: the same forged trace BALANCES against its own
-- manifest. So the refusal above is the binding to this block's challenges, not a malformity.
#guard decide (((katTrace 0 2 5 katG (sScalars katC' 4)).map tupleOf).Perm
                 (exactPublicTable (genManifest 0 2 5 katG (sScalars katC' 4))))

-- ⚑ …and symmetrically: the honest trace is refused by the OTHER block's manifest.
#guard decide (¬ (((katTrace 0 2 5 katG (sScalars katC 4)).map tupleOf).Perm
                    (exactPublicTable (genManifest 0 2 5 katG (sScalars katC' 4)))))

-- ⚑ The DESCRIPTOR is a function of the challenges: two challenge vectors, two manifests.
#guard decide (genManifest 0 2 5 katG (sScalars katC 4)
                 ≠ genManifest 0 2 5 katG (sScalars katC' 4))

-- ⚑ The GENERATOR half still bites on this same instance (the sibling rung's tamper, re-fired here
-- so the two halves are known to be live SIMULTANEOUSLY rather than one at a time).
#guard decide (¬ (((katTrace 0 2 5 [(6, 7, 1), (11, 13, 1)] (sScalars katC 4)).map tupleOf).Perm
                    (exactPublicTable (genManifest 0 2 5 katG (sScalars katC 4)))))

/-! ## §7 — WHAT A VERIFIED PROOF NOW ESTABLISHES, AND WHAT STILL STANDS.

**With both halves bound**, a verified proof of an instance of `blockScalarDesc cs N n k w planes
gens` establishes: every conditional-add row of the trace carries, at the absolute index `lo + t`
its own threaded `GIDX` names, the limbs of `gens[lo + t]` AND the `planeAt`-th binary digit of
`s_{lo+t} = ∏_j c_j^{bit_j(lo+t)}` derived from `cs`; that the `DBL` pattern is the schedule's and
not the prover's; and that the rows are exactly the manifest's, no more and no fewer, because the
exact-public balance is a PERMUTATION. Instantiated at `cs := CHAL_F` and `gens := SRS_G`, that is:
**these rows are the terms of Mina devnet block 539508's own `⟨s, srs.g⟩`.**

That is a statement about the TERMS. It is not yet the MSM. What still stands:

1. **The RCB-formula → group-law transport.** Every `Pasta*` rung's inherited residual (RCB'15
   Thm 1): the emitted adds are the complete-addition FORMULA, and that the formula computes the
   Pallas group law is assumed, not discharged here.
2. **ℤ ↔ felt (K1).** These theorems are in the ℤ model; the deployed prover reads the same
   constraints mod BabyBear. Unchanged by this file.
3. **P10, opening soundness.** The IPA/dlog extraction argument is undischarged here and everywhere
   in this stack.
4. **Scale.** `descriptor_ir2.rs` caps an exact-public manifest at 128 rows / 4096 cells and spends
   one batch AIR instance per manifest row, so a contents-bound instance is at most 128 rows tall —
   124 real generators against 32,768. **The theorems are row-count-independent; the
   DEMONSTRATION is not.** This file does not change that cap; it removes the OTHER reason the
   binding could not scale, which was that 32,768 scalars would have had to be carried.
5. **`gens` provenance.** The generator half is bound to the DECLARED `gens`; that those are
   o1-labs' `srs.g` is the extractor's, checked by `MinaWrapSgCore.srs_g_on_curve` and the chunk
   KATs, not by this file.

### §7.1 — the honest name for what is NOT here: the tensor is not recomputed IN the AIR

The digit is bound to the descriptor's manifest, and the manifest is a `def` of `cs`. It is not
recomputed by an emitted constraint. Making it so needs two things, and one of them this IR cannot
express today:

* **The challenges on the wire.** 15 Fq elements at the row layout's 9×30 limbs is 135 public-input
  slots against the current `PI_COUNT = 29`, plus a 15-step product chain of 255-bit modular
  multiplications per row. Constant in the row count, large in the row width. Buildable.
* **⚑ The digit ↔ scalar tie, which is NOT expressible.** A row carries ONE bit of its scalar; the
  other 254 live at the same term index in the other 254 bit planes. `WindowExpr` has exactly `loc`
  and `nxt` — ADJACENT rows only — and `PastaMsmWindowed`'s Horner schedule is plane-outer, so rows
  sharing a term index are `w + 1` apart. Recomposing a scalar from its per-plane digits therefore
  cannot be written as a window constraint at all without either a stride-`k` window arm in
  `DescriptorIR2` or a column-major schedule (which costs 255 doublings per term instead of 255
  shared). **That is the next rung, and it is an IR change, not a proof.**

### §7.2 — the descriptor DOES commit to the digits, and this was checked, not assumed

The sentence "the digit is bound at the descriptor" is only worth anything if the descriptor
commitment covers the manifest CONTENTS, so it was read rather than hoped:
`descriptor_ir2_canonical.rs` encodes `TableSem::ExactPublicRows.rows` value-by-value into the
canonical bytes, and `effect_vm_descriptor2_semantic_fingerprint` is blake3 over exactly those
bytes. So a manifest whose digits came from another block's challenges is a DIFFERENT semantic
fingerprint — the wrong-block forgery cannot be smuggled in under this instance's identity.

⚠ Note the contrast, because it would be easy to reach for the wrong one: `air_descriptor.rs`'s
`fingerprint` — the AIR-shape commitment in VK v2 — covers `air_id`, column count, PI layout,
constraint counts and max degree, and does NOT see a manifest. It is the IR2 SEMANTIC fingerprint
that carries the contents, and it is the one an instance of this descriptor must be pinned by.

What that leaves is exactly one link, and it is the same link the generator half has: whoever pins
the fingerprint must have built the manifest from the block. That build is now a `def` —
`sScalars CHAL_F` — whose agreement with `PastaIPA.sVec` of the block's DERIVED challenges is
machine-checked here, rather than a 32,768-entry list that would have had to be trusted.

Until §7.1 lands, the resolution to describe this at is: **the digits are the block's at the same
resolution the generators are Mina's** — both are carried by an exact-public manifest the descriptor
commits to, forced row-by-row into the trace by the emitted lookup, with the difference that the
scalar half's manifest is now a 15-element DERIVATION rather than a 32,768-element witness, and a
wrong-block derivation is refused. -/

end Dregg2.Circuit.Emit.PastaMsmScalarBound
