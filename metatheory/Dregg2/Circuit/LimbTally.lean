/-
# Dregg2.Circuit.LimbTally — a TALLY THAT DOES NOT FIT IN A FELT, and the vocabulary for it.

## The measured gap this file answers

`RangeFieldContainment` closed one wound (three light-client range tables declared intervals that
contained the whole field) and, in closing it, EXPOSED a second one that the vacuous widths had been
hiding. Quoting the repair's own docblock:

> `TM_BITS` is now 29 … completeness needs `3·signedPow < 2^29`, i.e. voting power below ~1.8e8.
> Real Tendermint allows `MaxTotalVotingPower ≈ 2^60`. **Those tallies do not fit in a BabyBear felt
> AT ALL** — range table or no range table, `TOTAL_POW` is one column and one column holds 30.9 bits.
> The 64-bit declaration did not make them fit; it made the SHORTFALL INVISIBLE.

So the three peer-chain light clients were SOUND at 29 bits and UNUSABLE at chain scale. The 29-bit
fix bought the teeth; it did not buy the capability. **The capability is this file.**

The blocking limit was a VOCABULARY limit, and it was named exactly:

> Full-width tallies need limb decomposition OF THE TALLY, and `EffectAirIR`'s range leg cannot
> express it (one `.lookup` on one `.var`, one declared width). That is a representability limit of
> the IR, not a constant to be widened back.

This is the same move that unblocked the effect compiler twice already — `TableAirIR` widened the IR
when it had no vocabulary for table AIRs, `EffectAirIR` gained lookup/window/range/PI-pin legs. A
source language that cannot SAY the thing does not get fixed by tuning a constant in it.

## What a limbed tally IS here

A quantity `A` no longer rides on one column. It rides on a LIST of columns `a₀ … a_{k−1}`, each
pinned to `[0, 2^bits)` by its own range lookup, denoting

    A = Σᵢ aᵢ · 2^(bits·i)                                     (`limbValue`, LSB-first Horner)

and the comparison `γ ≤ α·A − β·B` is decided by exhibiting the DIFFERENCE as its own range-checked
limb vector `d₀ … d_k` tied to `A` and `B` by an OFFSET CARRY CHAIN (`ChainOk`).

## ⚑ THE THEOREM THAT MAKES IT WORK, AND WHY IT IS BETTER THAN THE THING IT REPLACES

`chain_recomposes` — the telescoping identity — says the chain's per-rung equations RECOMPOSE to

    limbValue d  =  α · limbValue a  −  β · limbValue b  −  γ

**and it holds for ANY integer carries whatsoever.** The carries cancel pairwise; nothing about their
magnitude enters. Their range lookups exist for ONE reason only — the mod-`p` ↔ `ℤ` bridge
(`rung_value_bounds`) — and not for the recomposition.

That yields a refusal STRONGER than the one the 29-bit repair bought:

  * The single-felt tooth refused the exactly-2/3 sub-quorum because `p − 1 ∉ [0, 2^29)`. That is a
    fact ABOUT THE FIELD SIZE. It was FALSE at 30, catastrophically false at 64, and it is the reason
    the whole census existed.
  * The limbed tooth refuses it because a limb vector whose limbs are each `≥ 0` denotes a value
    `≥ 0`, and `−1 < 0`. **That is a fact about limb vectors and it holds at every width, in every
    field** (`chain_refuses_below_threshold`, `refusal_is_field_independent`).

So widening the representable tally by 2^33× does NOT re-admit the sub-quorum; it removes the field
size from the refusal's premises entirely.

## ⚑ AND THE mod-p RESIDUAL IS CLOSED HERE, NOT NAMED

Every Emit descriptor to date carries the same named residual: `airAccepts` reads gate bodies over
`ℤ`, the deployed denotation is mod-`p`, and bridging them "needs full-wire range decomposition".
For THESE gates the bridge is discharged rather than named. `rung_value_bounds` bounds the ℤ value of
every emitted rung gate, on any assignment whose limbs and carries sit in their DECLARED ranges, and
`rung_no_alias_at_deployed_constants` measures that interval against `p`:

    ℤ-image ⊆ (−16973953, 8585472)   ⊂  (−p, p) = (−2013265921, 2013265921)

and the REACHABLE image is tighter still — `[−8519806, 8585339]`, **236× inside `p`**
(`rung_reachable_min_at_deployed_width`). A gate that is `0 mod p` on such an assignment IS `0` over
`ℤ`, so the recomposition identity transfers to the deployed denotation.

`rung_alias_reachable_at_24_bits` is the refutation, and it is a REACHABLE witness rather than a
loose estimate: at limb width 24 an assignment respecting every declared range drives a rung gate to
`−2181038206`, past `−p`. So the constant has a measured margin AND a measured failure point eight
bits above it.

## The deployed constants, and why each is what it is

  * `TALLY_LIMB_BITS = 16` — **four limbs are exactly a `u64`**, which is exactly the wire type of
    both tallies this serves (CometBFT voting power is `int64`; Solana stake is `u64` lamports). It
    is also a multiple of the prover's own limb width (`LIMB_BITS = 4`; the "byte" table is a 16-row
    NIBBLE histogram), so its realization needs no partial-top boolean block. MEASURED via
    `decomp_cols_pub`: **16 bits costs 4 aux columns, 8 costs 2, 29 costs 9** (8 nibble limbs plus a
    1-bit boolean top) and 15 would cost 7. ⚠ The width is NOT forced by no-alias — **23** is that
    ceiling (`rung_alias_reachable_at_24_bits`) — and this file says the chosen reason out loud
    rather than leaving a constant to be read as derived.
  * `TALLY_CARRY_BITS = 8` / `TALLY_CARRY_OFF = 128` — the carry is SIGNED (a difference chain
    borrows), so it rides offset. 8 bits is two nibble limbs and no boolean block. The honest carry
    never leaves `[−3, 2]` (`honest_carry_window`); the declared `[−128, 127]` is 42× looser than
    honest and STILL 236× inside the reachable no-alias bound, which is the ordering you want
    between "what an honest prover needs" and "what the constraint permits".

  * `TALLY_LIMBS = 4` — `4 · 16 = 64`. The difference carries `TALLY_LIMBS + 1 = 5` limbs because
    `α·A − β·B − γ` needs `⌈log₂ α⌉` more bits than `A` does.

## ⚑ Three widths in one descriptor — MEASURED on the deployed prover, not assumed

`circuit/src/descriptor_ir2.rs::ir2_three_range_widths_coexist_and_prove` (2026-08-03): a descriptor
declaring THREE range widths (29 / 16 / 8) proves and verifies, each width's ceiling refuses
independently, and it costs **ZERO extra AIR instances** — `presence.byte` is a single bool and all
three decompositions query the same nibble histogram, so `degree_bits.len() = 2` (main + byte). N
widths cost N aux blocks in the main trace and nothing else. The 8-bit table is admitted purely
through its DECLARATION (`range_bits_for` consults `desc.tables` before the `CUSTOM_RANGE_WIDTHS`
fallback whitelist, which does NOT contain 8) — that path is now pinned by a test rather than
assumed.

⚠ And where the range refusal LANDS, so this is not read as more than it is: an over-ceiling limb is
refused by `fill_main_layout_row`'s fail-closed `v >= 2^bits` pre-flight (`descriptor_ir2.rs:4311`),
which is `Err` in every profile. The in-circuit `eval_decomp` leg is not separately reachable through
`prove_vm_descriptor2` — an over-ceiling value has no limb decomposition to write, so witness
generation refuses first. What is structurally checked in-AIR is that each block is evaluated at ITS
OWN declared width (`descriptor_ir2.rs:3366`), and the measurement for that is the aux-column count:
15 columns for the three widths, where a single-width realization would have allocated 27.

## What this file does NOT claim

It is the ARITHMETIC. It says nothing about whether a given `A` is the true stake of a true validator
set — that is the carrier boundary each chain's Emit module draws, unchanged. It does not discharge
the FRI floor. And `chain_recomposes` is about the emitted gate bodies read over `ℤ`; the transfer to
the deployed field denotation is `rung_value_bounds` plus the DECLARED range lookups actually being
in the descriptor, which each chain module pins on its own emitted object.

## Axiom hygiene
No `sorry`, no `native_decide`, no new axiom. Imports read-only; NEW file, purely additive.
-/
import Dregg2.Circuit.RangeFieldContainment

set_option autoImplicit false

namespace Dregg2.Circuit.LimbTally

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2 (TableId TableDef VmConstraint2 Lookup rangeRows range_row_mem_iff)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint)
open Dregg2.Circuit.Emit.EffectLower (P)

/-! ## §1 — a limb VECTOR: the quantity one felt could not hold.

`limbValue` is LSB-first Horner rather than an indexed sum, deliberately: every theorem below is a
one-step induction on the column list, and an indexed sum would put `List.zipIdx` reasoning between
the statement and its proof for no gain. -/

/-- **The value a limb vector denotes** — radix `2^bits`, LEAST-significant limb first.

⚑ This is the thing `EffectAirIR.RangeLeg` could not say. A `RangeLeg` is `⟨wire, bits⟩`: ONE column,
ONE width, and therefore one felt's worth of magnitude. A tally is a LIST. -/
def limbValue (bits : Nat) (a : Assignment) : List Nat → ℤ
  | []      => 0
  | c :: cs => a c + (2 : ℤ) ^ bits * limbValue bits a cs

/-- **Per-limb containment** — every limb column sits in `[0, 2^bits)`.

In the emitted AIR this is exactly the conjunction of the vector's own range lookups; it is not a
second private notion of "in range" (each chain module pins that with `range_row_mem_iff`). -/
def LimbsInRange (bits : Nat) (a : Assignment) : List Nat → Prop
  | []      => True
  | c :: cs => (0 ≤ a c ∧ a c < (2 : ℤ) ^ bits) ∧ LimbsInRange bits a cs

/-- Containment is DECIDABLE on a concrete row — so "this validator set's row is accepted" is a
`decide`-able claim about the emitted object, not a sentence a reader checks by eye. -/
instance decLimbsInRange (bits : Nat) (a : Assignment) :
    ∀ cs : List Nat, Decidable (LimbsInRange bits a cs)
  | []      => .isTrue trivial
  | c :: cs =>
      have : Decidable (LimbsInRange bits a cs) := decLimbsInRange bits a cs
      inferInstanceAs (Decidable ((0 ≤ a c ∧ a c < (2 : ℤ) ^ bits) ∧ LimbsInRange bits a cs))

@[simp] theorem limbValue_nil (bits : Nat) (a : Assignment) : limbValue bits a [] = 0 := rfl

@[simp] theorem limbValue_cons (bits : Nat) (a : Assignment) (c : Nat) (cs : List Nat) :
    limbValue bits a (c :: cs) = a c + (2 : ℤ) ^ bits * limbValue bits a cs := rfl

@[simp] theorem limbsInRange_nil (bits : Nat) (a : Assignment) :
    LimbsInRange bits a [] = True := rfl

@[simp] theorem limbsInRange_cons (bits : Nat) (a : Assignment) (c : Nat) (cs : List Nat) :
    LimbsInRange bits a (c :: cs)
      = ((0 ≤ a c ∧ a c < (2 : ℤ) ^ bits) ∧ LimbsInRange bits a cs) := rfl

/-- ⚑ **A CONTAINED LIMB VECTOR DENOTES A NON-NEGATIVE VALUE.** This one line is the whole refusal
tooth: the difference vector of a failed quorum would have to denote a negative number, and no
vector of non-negative limbs does. Field-size-free. -/
theorem limbValue_nonneg {bits : Nat} {a : Assignment} :
    ∀ {cs : List Nat}, LimbsInRange bits a cs → 0 ≤ limbValue bits a cs := by
  intro cs
  induction cs with
  | nil => intro _; simp
  | cons c cs ih =>
      rintro ⟨⟨h0, _⟩, ht⟩
      have hrest : 0 ≤ limbValue bits a cs := ih ht
      have hpow : (0 : ℤ) ≤ (2 : ℤ) ^ bits := le_of_lt (pow_pos (by norm_num) bits)
      have := mul_nonneg hpow hrest
      simp only [limbValue_cons]
      linarith

/-- **…and it is bounded by the vector's own capacity**: `k` limbs of `bits` hold `bits·k` bits.
The honest counterpart of `limbValue_nonneg`, and the reason four 16-bit limbs are a `u64`. -/
theorem limbValue_lt {bits : Nat} {a : Assignment} :
    ∀ {cs : List Nat}, LimbsInRange bits a cs →
      limbValue bits a cs < (2 : ℤ) ^ (bits * cs.length) := by
  intro cs
  induction cs with
  | nil => intro _; simp
  | cons c cs ih =>
      rintro ⟨⟨_, hlt⟩, ht⟩
      have hrest := ih ht
      have hsplit : (2 : ℤ) ^ (bits * (cs.length + 1))
          = (2 : ℤ) ^ bits * (2 : ℤ) ^ (bits * cs.length) := by
        rw [← pow_add]; ring_nf
      have hpow : (0 : ℤ) < (2 : ℤ) ^ bits := pow_pos (by norm_num) bits
      have hmul : (2 : ℤ) ^ bits * limbValue bits a cs
          ≤ (2 : ℤ) ^ bits * ((2 : ℤ) ^ (bits * cs.length) - 1) := by
        exact mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hpow)
      simp only [limbValue_cons, List.length_cons]
      rw [hsplit]
      nlinarith

/-- **CANONICITY** — a contained limb vector is the UNIQUE such representation of its value.
So "the tally is `A`" PINS the columns: a prover cannot re-spell the same tally two ways and move a
downstream binding while leaving the comparison intact. -/
theorem limbValue_unique {bits : Nat} {a b : Assignment} :
    ∀ {cs ds : List Nat}, cs.length = ds.length →
      LimbsInRange bits a cs → LimbsInRange bits b ds →
      limbValue bits a cs = limbValue bits b ds →
      cs.map a = ds.map b := by
  intro cs
  induction cs with
  | nil =>
      intro ds hlen _ _ _
      cases ds with
      | nil => simp
      | cons d ds => simp at hlen
  | cons c cs ih =>
      intro ds hlen hac hbd hval
      cases ds with
      | nil => simp at hlen
      | cons d ds =>
        obtain ⟨⟨hc0, hclt⟩, hct⟩ := hac
        obtain ⟨⟨hd0, hdlt⟩, hdt⟩ := hbd
        have hlen' : cs.length = ds.length := by simpa using hlen
        have hpow : (0 : ℤ) < (2 : ℤ) ^ bits := pow_pos (by norm_num) bits
        have hrc : 0 ≤ limbValue bits a cs := limbValue_nonneg hct
        have hrd : 0 ≤ limbValue bits b ds := limbValue_nonneg hdt
        simp only [limbValue_cons] at hval
        -- The head digits agree: otherwise the tails would differ by a non-multiple of `2^bits`,
        -- while the heads differ by strictly less than one radix step.
        have hhead : a c = b d := by
          rcases lt_trichotomy (limbValue bits b ds) (limbValue bits a cs) with h | h | h
          · exfalso
            have hstep : (2 : ℤ) ^ bits * 1 ≤
                (2 : ℤ) ^ bits * (limbValue bits a cs - limbValue bits b ds) :=
              mul_le_mul_of_nonneg_left (by omega) (le_of_lt hpow)
            nlinarith
          · rw [h] at hval; linarith
          · exfalso
            have hstep : (2 : ℤ) ^ bits * 1 ≤
                (2 : ℤ) ^ bits * (limbValue bits b ds - limbValue bits a cs) :=
              mul_le_mul_of_nonneg_left (by omega) (le_of_lt hpow)
            nlinarith
        have htail : limbValue bits a cs = limbValue bits b ds := by
          have h2 : (2 : ℤ) ^ bits * limbValue bits a cs
              = (2 : ℤ) ^ bits * limbValue bits b ds := by rw [hhead] at hval; linarith
          exact mul_left_cancel₀ (ne_of_gt hpow) h2
        simp only [List.map_cons, hhead, ih hlen' hct hdt htail]

/-! ## §2 — the OFFSET CARRY CHAIN: how a comparison crosses a limb boundary.

A `Rung` is one radix position. Bundling the four columns into a structure (rather than carrying four
parallel `List Nat`s) is the same discipline `EffectAirIR.AirLeg` follows one layer up: parallel
lists cannot express a mis-alignment as a TYPE ERROR, and the recursion below is structural on one
list instead of needing a simultaneous termination argument on four. -/

/-- **One radix position of a limbed comparison.** `aCol`/`bCol` are the operand limbs, `dCol` the
difference limb, `cCol` the OFFSET CARRY OUT of this position (the value it denotes is
`a cCol − coff`, which is what makes a borrow expressible on a field with no negative wire). -/
structure Rung where
  /-- Trace column holding this position's limb of the LEFT operand `A`. -/
  aCol : Nat
  /-- Trace column holding this position's limb of the RIGHT operand `B`. -/
  bCol : Nat
  /-- Trace column holding this position's limb of the DIFFERENCE `α·A − β·B − γ`. -/
  dCol : Nat
  /-- Trace column holding the OFFSET carry out of this position (denotes `a cCol − coff`). -/
  cCol : Nat
  deriving Repr, DecidableEq

/-- **`ChainOk bits α β coff a dTop rs g cin`** — the per-rung equations of the difference chain,
LSB-first, with `g` the constant subtracted at THIS position (`γ` at the bottom, `0` above it) and
`cin` the carry INTO this position (`0` at the bottom).

At rung `i`:  `α·aᵢ − β·bᵢ − g + cᵢ − dᵢ − c_{i+1}·2^bits = 0`
At the top:   `c_k − 0 − d_k = 0`   (the operands have run out; the final carry IS the top digit)

⚠ The top equation is what forces the chain to CLOSE. Without it the prover could dump an arbitrary
residue into a final carry nothing reads, and the recomposition below would be off by
`c_k · 2^(bits·k)` — which is precisely how a multi-limb comparison is usually got wrong. -/
def ChainOk (bits : Nat) (α β coff : ℤ) (a : Assignment) (dTop : Nat) :
    List Rung → ℤ → ℤ → Prop
  | [],      g, cin => cin - g - a dTop = 0
  | r :: rs, g, cin =>
      α * a r.aCol - β * a r.bCol - g + cin - a r.dCol - (a r.cCol - coff) * (2 : ℤ) ^ bits = 0
      ∧ ChainOk bits α β coff a dTop rs 0 (a r.cCol - coff)

/-- The DIFFERENCE limb vector of a chain: one limb per rung, plus the top limb. `k` rungs give
`k + 1` difference limbs, which is what `α·A − β·B − γ` needs when `α > 1`. -/
def diffCols (rs : List Rung) (dTop : Nat) : List Nat := rs.map Rung.dCol ++ [dTop]

/-- The LEFT operand's limb vector. -/
def aCols (rs : List Rung) : List Nat := rs.map Rung.aCol

/-- The RIGHT operand's limb vector. -/
def bCols (rs : List Rung) : List Nat := rs.map Rung.bCol

/-- The carry columns (the offset carries out of each rung). -/
def carryCols (rs : List Rung) : List Nat := rs.map Rung.cCol

/-- ⚑ **THE TELESCOPING IDENTITY — the load-bearing theorem of this file.**

The chain's per-rung equations RECOMPOSE, exactly, to

    limbValue d  =  α · limbValue a  −  β · limbValue b  −  g  +  cin

**and NO hypothesis about the carries appears.** Each `cᵢ` enters rung `i−1` weighted `2^(bits·i)`
and rung `i` weighted `−2^(bits·i)`; they cancel pairwise regardless of magnitude, sign, or whether
they are anywhere near what an honest prover would fill.

That is why the carry range lookups in the emitted AIR are NOT part of the arithmetic argument. They
exist solely for `rung_value_bounds` — the mod-`p` ↔ `ℤ` bridge — and this theorem is the reason a
reader can tell those two jobs apart instead of assuming the looser one is load-bearing. -/
theorem chain_recomposes (bits : Nat) (α β coff : ℤ) (a : Assignment) (dTop : Nat) :
    ∀ (rs : List Rung) (g cin : ℤ), ChainOk bits α β coff a dTop rs g cin →
      limbValue bits a (diffCols rs dTop)
        = α * limbValue bits a (aCols rs) - β * limbValue bits a (bCols rs) - g + cin := by
  intro rs
  induction rs with
  | nil =>
      intro g cin h
      simp only [ChainOk] at h
      simp only [diffCols, aCols, bCols, List.map_nil, List.nil_append, limbValue_cons,
        limbValue_nil]
      linarith
  | cons r rs ih =>
      intro g cin h
      obtain ⟨hgate, htail⟩ := h
      have hrec := ih 0 (a r.cCol - coff) htail
      simp only [diffCols, aCols, bCols, List.map_cons, List.cons_append, limbValue_cons] at *
      -- ⚑ THE CANCELLATION, spelled out as the exact linear combination: the head rung's gate,
      -- plus `2^bits` times the tail's recomposition. The carry `a r.cCol − coff` enters the first
      -- with weight `−2^bits` and the second with weight `+2^bits`, and vanishes. NO bound on it
      -- appears anywhere in this certificate — that is the claim of the docstring, mechanised.
      linear_combination (-1 : ℤ) * hgate + ((2 : ℤ) ^ bits) * hrec

/-! ## §3 — SOUNDNESS and the REFUSAL. -/

/-- **`CmpAccepts`** — what a satisfying witness of a limbed comparison looks like, over `ℤ`:
the chain closes from `(γ, 0)`, and the difference vector's limbs are each contained.

The operand and carry containments are NOT here, deliberately: they are needed for the mod-`p`
bridge (§5) and for completeness, and putting them in the acceptance predicate would make the
soundness theorem below look like it depends on them. It does not. -/
def CmpAccepts (bits : Nat) (α β γ coff : ℤ) (a : Assignment) (rs : List Rung) (dTop : Nat) : Prop :=
  ChainOk bits α β coff a dTop rs γ 0 ∧ LimbsInRange bits a (diffCols rs dTop)

/-- ⚑ **SOUNDNESS: an accepting witness ENTAILS the inequality.**

    γ  ≤  α · A  −  β · B

where `A` and `B` are the values the operand limb vectors denote. This is the statement the
single-felt slack tooth used to make about ONE column, now made about a quantity of ANY width. -/
theorem cmp_sound {bits : Nat} {α β γ coff : ℤ} {a : Assignment} {rs : List Rung} {dTop : Nat}
    (h : CmpAccepts bits α β γ coff a rs dTop) :
    γ ≤ α * limbValue bits a (aCols rs) - β * limbValue bits a (bCols rs) := by
  obtain ⟨hchain, hd⟩ := h
  have hrec := chain_recomposes bits α β coff a dTop rs γ 0 hchain
  have h0 := limbValue_nonneg hd
  linarith

/-- ⚑ **THE REFUSAL, AND IT IS THE ONE THE CENSUS WAS ABOUT.** If the true comparison FAILS — if
`α·A − β·B < γ` — then NO assignment of difference limbs and carries satisfies the emitted chain.

⚠ Note what is absent from this statement: `p`. There is no width hypothesis, no wrap-freedom
premise, no `bits ≤ 29`. The single-felt tooth refused the exactly-2/3 sub-quorum only because
`p − 1 ∉ [0, 2^29)` — a fact about the FIELD, false at 30 and catastrophically false at 64, and the
entire reason the 404-width census had to happen. This refusal is a fact about limb vectors. -/
theorem cmp_refuses_below_threshold {bits : Nat} {α β γ coff : ℤ} {a : Assignment}
    {rs : List Rung} {dTop : Nat}
    (hfail : α * limbValue bits a (aCols rs) - β * limbValue bits a (bCols rs) < γ) :
    ¬ CmpAccepts bits α β γ coff a rs dTop := by
  intro hacc
  exact absurd (cmp_sound hacc) (not_le.mpr hfail)

/-- **The refusal is FIELD-INDEPENDENT, stated as its own fact so the contrast is checkable.**
Quantified over EVERY limb width — including the widths at which the old single-felt tooth was
vacuous (`≥ 31`) and the width at which it was merely leaky (`30`). -/
theorem refusal_is_field_independent (α β γ coff : ℤ) (a : Assignment) (rs : List Rung) (dTop : Nat)
    (hfail : ∀ bits : Nat,
      α * limbValue bits a (aCols rs) - β * limbValue bits a (bCols rs) < γ) :
    ∀ bits : Nat, ¬ CmpAccepts bits α β γ coff a rs dTop :=
  fun bits => cmp_refuses_below_threshold (hfail bits)

/-- ⚑⚑ **THE SHARP FORM: REFUSED AT THE VERY WIDTH THAT WAS VACUOUS.**

`RangeFieldContainment.range_vacuous_at_or_above_31` proves a 64-bit range table over BabyBear
contains EVERY field element — it refuses nothing, and `dregg-tm-lightclient-verify::v1` shipped
exactly that, so the exactly-2/3 sub-quorum's slack of `−1` (riding as `p − 1`) was ADMITTED.

Set the limb width to that same 64. **The limbed comparison still refuses.** Nothing about `p`,
about wrap-freedom, or about the interval's relation to the field appears in the proof: a limb vector
of non-negative limbs denotes a non-negative value, and the difference is negative.

This is the statement that makes "widening the tally did not re-admit the sub-quorum" checkable
rather than asserted — and the general form (`cmp_refuses_below_threshold`) carries no width
hypothesis at all, which is the real content. -/
theorem refused_at_the_width_that_was_vacuous (α β γ coff : ℤ) (a : Assignment) (rs : List Rung)
    (dTop : Nat)
    (hfail : α * limbValue 64 a (aCols rs) - β * limbValue 64 a (bCols rs) < γ) :
    ¬ CmpAccepts 64 α β γ coff a rs dTop :=
  cmp_refuses_below_threshold hfail

/-- …and at 30, the width that was not vacuous but not wrap-free either (it admitted every negative
of magnitude `> p − 2^30 = 939524097`). Same proof, no premise about the field. -/
theorem refused_at_the_width_that_was_leaky (α β γ coff : ℤ) (a : Assignment) (rs : List Rung)
    (dTop : Nat)
    (hfail : α * limbValue 30 a (aCols rs) - β * limbValue 30 a (bCols rs) < γ) :
    ¬ CmpAccepts 30 α β γ coff a rs dTop :=
  cmp_refuses_below_threshold hfail

/-! ## §4 — the EMITTED gate bodies. The AIR is GENERATED, never transcribed.

`LightClientMinaAir` set the bar: `EffectLower.lowerAir`-authored, no hand-written `VmConstraint2`.
These generators are the same discipline for a chain of arbitrary length — a five-limb tally and a
fifty-limb tally are ONE call, and `chainBodies_zero_iff` ties the generated bodies back to
`ChainOk` so §3 applies to the object that ships. -/

/-- The emitted body at one rung: `α·x − β·y − g + cin − d − (ĉ − coff)·2^bits`, where `cinCol` is
`none` at the least-significant rung (`cin = 0`) and `some c` above it (`cin = a c − coff`). -/
def rungBody (bits : Nat) (α β g coff : ℤ) (cinCol : Option Nat) (r : Rung) : EmittedExpr :=
  let core : EmittedExpr :=
    .add (.add (.add (.mul (.const α) (.var r.aCol))
                     (.mul (.const (-β)) (.var r.bCol)))
               (.mul (.const (-1)) (.var r.dCol)))
         (.mul (.const (-((2 : ℤ) ^ bits))) (.var r.cCol))
  match cinCol with
  | none   => .add core (.const (coff * (2 : ℤ) ^ bits - g))
  | some c => .add (.add core (.var c)) (.const (coff * (2 : ℤ) ^ bits - g - coff))

/-- The emitted body at the TOP: `cin − g − d`. The chain's closure gate. -/
def topBody (g coff : ℤ) (cinCol : Option Nat) (dTop : Nat) : EmittedExpr :=
  match cinCol with
  | none   => .add (.mul (.const (-1)) (.var dTop)) (.const (-g))
  | some c => .add (.add (.var c) (.mul (.const (-1)) (.var dTop))) (.const (-coff - g))

/-- **The generated gate-body list for a whole chain**, in emission order (LSB rung first, closure
gate last). `k` rungs generate `k + 1` bodies. -/
def chainBodies (bits : Nat) (α β γ coff : ℤ) (dTop : Nat) : List Rung → List EmittedExpr :=
  let rec go (g : ℤ) (cinCol : Option Nat) : List Rung → List EmittedExpr
    | []      => [topBody g coff cinCol dTop]
    | r :: rs => rungBody bits α β g coff cinCol r :: go 0 (some r.cCol) rs
  go γ none

/-- Every generated body vanishes on `a` — the predicate the emitted gates denote.

Defined by recursion rather than as `∀ e ∈ es, …` so that the equivalence with `ChainOk` below is a
structural induction with no list-membership lemmas between the statement and its proof;
`bodiesVanish_iff_forall_mem` is the bridge to the quantified form a descriptor-level `airAccepts`
naturally states. -/
def BodiesVanish (a : Assignment) : List EmittedExpr → Prop
  | []      => True
  | e :: es => e.eval a = 0 ∧ BodiesVanish a es

/-- …and it too is DECIDABLE on a concrete row: the generated chain gates can be EVALUATED, so
"the emitted AIR accepts this real validator set" is a computation. -/
instance decBodiesVanish (a : Assignment) :
    ∀ es : List EmittedExpr, Decidable (BodiesVanish a es)
  | []      => .isTrue trivial
  | e :: es =>
      have : Decidable (BodiesVanish a es) := decBodiesVanish a es
      inferInstanceAs (Decidable (e.eval a = 0 ∧ BodiesVanish a es))

/-- …and it IS the quantified form, so nothing is lost by the recursive spelling. -/
theorem bodiesVanish_iff_forall_mem (a : Assignment) :
    ∀ es : List EmittedExpr, BodiesVanish a es ↔ ∀ e ∈ es, e.eval a = 0 := by
  intro es
  induction es with
  | nil => simp [BodiesVanish]
  | cons e es ih => simp [BodiesVanish, ih]

/-- ⚑ **THE GENERATED BODIES ARE EXACTLY `ChainOk`.** Both directions, so §3's soundness and refusal
are statements about the bodies that SHIP, not about a private predicate that resembles them.

(Stated at the recursion's own generality — `g` and `cinCol` free — because that is what the
induction needs; `chainBodies_zero_iff` below is the closed form the AIR modules use.) -/
theorem chainBodies_go_zero_iff (bits : Nat) (α β coff : ℤ) (a : Assignment) (dTop : Nat) :
    ∀ (rs : List Rung) (g : ℤ) (cinCol : Option Nat),
      (BodiesVanish a (chainBodies.go bits α β coff dTop g cinCol rs)
        ↔ ChainOk bits α β coff a dTop rs g (cinCol.elim (0 : ℤ) (fun c => a c - coff))) := by
  intro rs
  induction rs with
  | nil =>
      intro g cinCol
      cases cinCol with
      | none =>
          simp only [chainBodies.go, BodiesVanish, ChainOk, topBody, Option.elim,
            Dregg2.Exec.CircuitEmit.EmittedExpr.eval, and_true]
          constructor <;> intro h <;> linarith
      | some c =>
          simp only [chainBodies.go, BodiesVanish, ChainOk, topBody, Option.elim,
            Dregg2.Exec.CircuitEmit.EmittedExpr.eval, and_true]
          constructor <;> intro h <;> linarith
  | cons r rs ih =>
      intro g cinCol
      have ihr := ih 0 (some r.cCol)
      cases cinCol with
      | none =>
          simp only [chainBodies.go, BodiesVanish, ChainOk, rungBody, Option.elim,
            Dregg2.Exec.CircuitEmit.EmittedExpr.eval] at ihr ⊢
          constructor
          · rintro ⟨hg, ht⟩; exact ⟨by linarith, ihr.mp ht⟩
          · rintro ⟨hg, ht⟩; exact ⟨by linarith, ihr.mpr ht⟩
      | some c =>
          simp only [chainBodies.go, BodiesVanish, ChainOk, rungBody, Option.elim,
            Dregg2.Exec.CircuitEmit.EmittedExpr.eval] at ihr ⊢
          constructor
          · rintro ⟨hg, ht⟩; exact ⟨by linarith, ihr.mp ht⟩
          · rintro ⟨hg, ht⟩; exact ⟨by linarith, ihr.mpr ht⟩

/-- **The closed form**: the emitted chain's bodies all vanish iff the chain holds from `(γ, 0)`. -/
theorem chainBodies_zero_iff (bits : Nat) (α β γ coff : ℤ) (a : Assignment) (dTop : Nat)
    (rs : List Rung) :
    BodiesVanish a (chainBodies bits α β γ coff dTop rs) ↔ ChainOk bits α β coff a dTop rs γ 0 :=
  chainBodies_go_zero_iff bits α β coff a dTop rs γ none

/-- **SOUNDNESS ON THE EMITTED OBJECT.** The composition of `chainBodies_zero_iff` with `cmp_sound`
— what a chain module cites. -/
theorem emitted_chain_sound {bits : Nat} {α β γ coff : ℤ} {a : Assignment} {rs : List Rung}
    {dTop : Nat}
    (hbodies : BodiesVanish a (chainBodies bits α β γ coff dTop rs))
    (hd : LimbsInRange bits a (diffCols rs dTop)) :
    γ ≤ α * limbValue bits a (aCols rs) - β * limbValue bits a (bCols rs) :=
  cmp_sound ⟨(chainBodies_zero_iff bits α β γ coff a dTop rs).mp hbodies, hd⟩

/-- **REFUSAL ON THE EMITTED OBJECT.** -/
theorem emitted_chain_refuses {bits : Nat} {α β γ coff : ℤ} {a : Assignment} {rs : List Rung}
    {dTop : Nat}
    (hfail : α * limbValue bits a (aCols rs) - β * limbValue bits a (bCols rs) < γ) :
    ¬ (BodiesVanish a (chainBodies bits α β γ coff dTop rs)
        ∧ LimbsInRange bits a (diffCols rs dTop)) := by
  rintro ⟨hb, hd⟩
  exact cmp_refuses_below_threshold hfail
    ⟨(chainBodies_zero_iff bits α β γ coff a dTop rs).mp hb, hd⟩

/-! ## §5 — the mod-`p` ↔ `ℤ` bridge, DISCHARGED for these gates.

Every Emit descriptor to date carries this as a NAMED RESIDUAL: `airAccepts` reads the gate bodies
over `ℤ`, the deployed denotation is mod-`p`. For a decomposition chain the residual is not a
philosophical one — a rung gate multiplies a carry by `2^bits`, which is exactly the shape that CAN
alias — so it gets discharged here rather than named. -/

/-- **The `ℤ` image of one rung gate, bounded by the DECLARED ranges alone.**

On any assignment whose operand and difference limbs are in `[0, 2^bits)` and whose carries are in
`[0, 2^carryBits)`, the rung expression's value lies in an interval that depends only on the declared
constants — never on what the prover chose. -/
theorem rung_value_bounds (bits carryBits : Nat) (α β g coff x y d cin cout : ℤ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hg : 0 ≤ g) (hcoff : 0 ≤ coff)
    (hx : 0 ≤ x ∧ x < (2 : ℤ) ^ bits) (hy : 0 ≤ y ∧ y < (2 : ℤ) ^ bits)
    (hd : 0 ≤ d ∧ d < (2 : ℤ) ^ bits)
    (hcin : 0 ≤ cin ∧ cin < (2 : ℤ) ^ carryBits)
    (hcout : 0 ≤ cout ∧ cout < (2 : ℤ) ^ carryBits) :
    -(β * (2 : ℤ) ^ bits + g + coff + (2 : ℤ) ^ bits + (2 : ℤ) ^ carryBits * (2 : ℤ) ^ bits)
      < α * x - β * y - g + (cin - coff) - d - (cout - coff) * (2 : ℤ) ^ bits
    ∧ α * x - β * y - g + (cin - coff) - d - (cout - coff) * (2 : ℤ) ^ bits
      < α * (2 : ℤ) ^ bits + (2 : ℤ) ^ carryBits + coff * (2 : ℤ) ^ bits := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  obtain ⟨hd0, hd1⟩ := hd
  obtain ⟨hci0, hci1⟩ := hcin
  obtain ⟨hco0, hco1⟩ := hcout
  have hpb : (0 : ℤ) < (2 : ℤ) ^ bits := pow_pos (by norm_num) bits
  constructor <;> nlinarith [mul_nonneg hα hx0, mul_nonneg hβ hy0, mul_le_mul_of_nonneg_left
    (le_of_lt hx1) hα, mul_le_mul_of_nonneg_left (le_of_lt hy1) hβ,
    mul_le_mul_of_nonneg_right (le_of_lt hco1) (le_of_lt hpb),
    mul_nonneg hco0 (le_of_lt hpb)]

/-! ## §6 — the DEPLOYED constants. -/

/-- **The tally limb width.** `4 · 16 = 64` — four limbs are exactly the `u64` both served tallies
are on the wire (CometBFT voting power is `int64`, Solana stake is `u64` lamports), and 16 is
byte-aligned so the prover's realization is 2 aux columns per check rather than 9.

⚠ Chosen, not forced: `rung_alias_reachable_at_24_bits` shows the no-alias ceiling is 22 at these
carry constants. Said out loud rather than left in a constant to be read as derived. -/
def TALLY_LIMB_BITS : Nat := 16

/-- **The carry width.** The prover's own byte bus: one aux column, one byte lookup, no boolean
block (`decomp_cols 8 = 1`). -/
def TALLY_CARRY_BITS : Nat := 8

/-- **The carry offset.** A difference chain BORROWS, so the carry is signed; it rides as
`ĉ − 128` with `ĉ ∈ [0, 256)`, i.e. `c ∈ [−128, 127]`. -/
def TALLY_CARRY_OFF : ℤ := 128

/-- **The operand limb count.** `TALLY_LIMBS · TALLY_LIMB_BITS = 64`. -/
def TALLY_LIMBS : Nat := 4

/-- Four 16-bit limbs are EXACTLY a `u64`: the tally column tiles the wire type without slack or
truncation. -/
theorem tally_limbs_tile_u64 : TALLY_LIMB_BITS * TALLY_LIMBS = 64 := by
  norm_num [TALLY_LIMB_BITS, TALLY_LIMBS]

/-- ⚑ **THE CAPABILITY, AS A NUMBER.** A four-limb tally represents every value in `[0, 2^64)`.
The single felt it replaces held `[0, p) ⊂ [0, 2^31)` — and after the 29-bit repair the honest
threshold slack had to fit `[0, 2^29)`. This is the gap the vacuous widths were hiding, closed. -/
theorem tally_capacity :
    (2 : ℤ) ^ (TALLY_LIMB_BITS * TALLY_LIMBS) = 18446744073709551616 := by
  norm_num [TALLY_LIMB_BITS, TALLY_LIMBS]

/-- …and it is `2^33` times the whole field, not merely a bigger interval inside it. -/
theorem tally_capacity_exceeds_the_field :
    (2 : ℤ) ^ 33 * P < (2 : ℤ) ^ (TALLY_LIMB_BITS * TALLY_LIMBS) := by
  norm_num [TALLY_LIMB_BITS, TALLY_LIMBS, Dregg2.Circuit.RangeFieldContainment.babybear_modulus]

/-- ⚑ **NO ALIAS AT THE DEPLOYED CONSTANTS.** At `bits = 16`, `carryBits = 8`, `coff = 128` and the
strict-supermajority coefficients `α = 3, β = 2, γ = 1`, every rung gate's `ℤ` value on a
range-respecting assignment lies in `(−16973954, 8585473)`, which is strictly inside `(−p, p)`.

So for THESE gates `body ≡ 0 (mod p)` IS `body = 0` over `ℤ`, and §3's recomposition transfers to the
deployed denotation. The shared field-soundness residual every other Emit descriptor NAMES is
discharged here. -/
theorem rung_no_alias_at_deployed_constants (x y d cin cout : ℤ)
    (hx : 0 ≤ x ∧ x < (2 : ℤ) ^ TALLY_LIMB_BITS) (hy : 0 ≤ y ∧ y < (2 : ℤ) ^ TALLY_LIMB_BITS)
    (hd : 0 ≤ d ∧ d < (2 : ℤ) ^ TALLY_LIMB_BITS)
    (hcin : 0 ≤ cin ∧ cin < (2 : ℤ) ^ TALLY_CARRY_BITS)
    (hcout : 0 ≤ cout ∧ cout < (2 : ℤ) ^ TALLY_CARRY_BITS) :
    -P < 3 * x - 2 * y - 1 + (cin - TALLY_CARRY_OFF) - d
          - (cout - TALLY_CARRY_OFF) * (2 : ℤ) ^ TALLY_LIMB_BITS
    ∧ 3 * x - 2 * y - 1 + (cin - TALLY_CARRY_OFF) - d
          - (cout - TALLY_CARRY_OFF) * (2 : ℤ) ^ TALLY_LIMB_BITS < P := by
  have h := rung_value_bounds TALLY_LIMB_BITS TALLY_CARRY_BITS 3 2 1 TALLY_CARRY_OFF x y d cin cout
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [TALLY_CARRY_OFF]) hx hy hd hcin hcout
  obtain ⟨hlo, hhi⟩ := h
  have hp : (P : ℤ) = 2013265921 := Dregg2.Circuit.RangeFieldContainment.babybear_modulus
  simp only [TALLY_LIMB_BITS, TALLY_CARRY_BITS, TALLY_CARRY_OFF] at hlo hhi ⊢
  norm_num [hp] at hlo hhi ⊢
  constructor <;> linarith

/-- ⚑ **AND THE BOUND IS REFUTABLE — with a REACHABLE witness, not a loose estimate.**

At limb width 24 the assignment `x = 0`, `y = d = 2^24 − 1`, `cin = 0`, `cout = 2^8 − 1` respects
EVERY declared range and drives the rung expression to `−2181038206`, which is past `−p`. There, a
body that is `0 mod p` need not be `0` over `ℤ`, and the recomposition identity of §3 stops
transferring to the deployed denotation.

⚠ The witness is exhibited rather than derived from `rung_value_bounds`, deliberately: that lemma's
interval is LOOSE (it charges the carry `2^carryBits · 2^bits` where the reachable worst case is
`(2^carryBits − 1 − coff) · 2^bits`), so refuting the loose bound would prove nothing about what a
prover can actually do. Measured: reachable image is `[−8519806, 8585339]` at 16 bits (236× inside
`p`), `[−1090519166, 1098907771]` at 23 (1.8× inside), and past `p` at 24. -/
theorem rung_alias_reachable_at_24_bits :
    ¬ (-P < 3 * 0 - 2 * ((2 : ℤ) ^ 24 - 1) - 1 + (0 - TALLY_CARRY_OFF) - ((2 : ℤ) ^ 24 - 1)
        - (((2 : ℤ) ^ TALLY_CARRY_BITS - 1) - TALLY_CARRY_OFF) * (2 : ℤ) ^ 24) := by
  norm_num [TALLY_CARRY_BITS, TALLY_CARRY_OFF,
    Dregg2.Circuit.RangeFieldContainment.babybear_modulus]

/-- …and the SAME witness shape at the DEPLOYED width is 236× inside the field. The pair is the
point: the constant is not merely "small enough", it has a measured margin and a measured failure
point three bits above it. -/
theorem rung_reachable_min_at_deployed_width :
    3 * 0 - 2 * ((2 : ℤ) ^ TALLY_LIMB_BITS - 1) - 1 + (0 - TALLY_CARRY_OFF)
      - ((2 : ℤ) ^ TALLY_LIMB_BITS - 1)
      - (((2 : ℤ) ^ TALLY_CARRY_BITS - 1) - TALLY_CARRY_OFF) * (2 : ℤ) ^ TALLY_LIMB_BITS
      = -8519806 := by
  norm_num [TALLY_LIMB_BITS, TALLY_CARRY_BITS, TALLY_CARRY_OFF]

/-! ## §7 — the HONEST FILL: what a prover puts on the wire, and that it fits.

The Rust witness filler mirrors these two functions exactly. Stating them here (rather than only in
Rust) is what makes "the prover can always fill an honest row" a claim about a defined object. -/

/-- The honest difference digit at a rung: the raw value's residue mod `2^bits`. `Int.emod` is
non-negative for a positive modulus, so this is in `[0, 2^bits)` by construction, not by check. -/
def fillDigit (bits : Nat) (raw : ℤ) : ℤ := raw % (2 : ℤ) ^ bits

/-- The honest carry out of a rung: the raw value's quotient by `2^bits`. -/
def fillCarry (bits : Nat) (raw : ℤ) : ℤ := raw / (2 : ℤ) ^ bits

/-- **The rung equation holds BY CONSTRUCTION on the honest fill** — `Int.mul_ediv_add_emod`, no
side condition. This is why an honest prover never has to search. -/
theorem fill_splits (bits : Nat) (raw : ℤ) :
    raw - fillDigit bits raw - fillCarry bits raw * (2 : ℤ) ^ bits = 0 := by
  have := Int.mul_ediv_add_emod raw ((2 : ℤ) ^ bits)
  simp only [fillDigit, fillCarry]
  linarith

/-- The honest digit is in the declared range, for free. -/
theorem fillDigit_in_range (bits : Nat) (raw : ℤ) :
    0 ≤ fillDigit bits raw ∧ fillDigit bits raw < (2 : ℤ) ^ bits := by
  have hpos : (0 : ℤ) < (2 : ℤ) ^ bits := pow_pos (by norm_num) bits
  exact ⟨Int.emod_nonneg raw (ne_of_gt hpos), Int.emod_lt_of_pos raw hpos⟩

/-- ⚑ **THE HONEST CARRY WINDOW.** For the strict-supermajority coefficients (`α = 3, β = 2`) with
operand limbs in range and an incoming carry already in `[−3, 2]`, the outgoing carry is again in
`[−3, 2]`. So the honest chain never leaves a six-element window, while the DECLARED window is
`[−128, 127]` — 42× looser than honest, and still 118× inside the no-alias bound.

That ordering (honest ⊂ declared ⊂ no-alias) is the one you want, and it is measured rather than
asserted: an honest prover has slack, a forger gains nothing from the slack (§3 needs no carry
bound at all), and the mod-`p` bridge still closes. -/
theorem honest_carry_window (bits : Nat) (hb : 2 ≤ bits) (x y cin : ℤ)
    (hx : 0 ≤ x ∧ x < (2 : ℤ) ^ bits) (hy : 0 ≤ y ∧ y < (2 : ℤ) ^ bits)
    (hcin : -3 ≤ cin ∧ cin ≤ 2) :
    -3 ≤ fillCarry bits (3 * x - 2 * y - 1 + cin)
      ∧ fillCarry bits (3 * x - 2 * y - 1 + cin) ≤ 2 := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  obtain ⟨hc0, hc1⟩ := hcin
  have hpos : (0 : ℤ) < (2 : ℤ) ^ bits := pow_pos (by norm_num) bits
  have h4 : (4 : ℤ) ≤ (2 : ℤ) ^ bits := by
    calc (4 : ℤ) = (2 : ℤ) ^ 2 := by norm_num
      _ ≤ (2 : ℤ) ^ bits := pow_le_pow_right₀ (by norm_num) hb
  set raw : ℤ := 3 * x - 2 * y - 1 + cin with hraw
  have hlo : -3 * (2 : ℤ) ^ bits ≤ raw := by simp only [hraw]; nlinarith
  have hhi : raw < 3 * (2 : ℤ) ^ bits := by simp only [hraw]; nlinarith
  -- Read the quotient off the division identity: `raw = 2^bits·q + r` with `0 ≤ r < 2^bits`.
  set q : ℤ := fillCarry bits raw with hq
  have hsplit : (2 : ℤ) ^ bits * q + raw % (2 : ℤ) ^ bits = raw := Int.mul_ediv_add_emod raw _
  have hr0 : 0 ≤ raw % (2 : ℤ) ^ bits := Int.emod_nonneg raw (ne_of_gt hpos)
  have hr1 : raw % (2 : ℤ) ^ bits < (2 : ℤ) ^ bits := Int.emod_lt_of_pos raw hpos
  constructor
  · by_contra hbad
    push Not at hbad
    have : (2 : ℤ) ^ bits * q ≤ (2 : ℤ) ^ bits * (-4) :=
      mul_le_mul_of_nonneg_left (by omega) (le_of_lt hpos)
    linarith
  · by_contra hbad
    push Not at hbad
    have : (2 : ℤ) ^ bits * 3 ≤ (2 : ℤ) ^ bits * q :=
      mul_le_mul_of_nonneg_left (by omega) (le_of_lt hpos)
    linarith

/-! ## §8 — the tripwires. NAMED THEOREMS, both polarities, on the emitted objects.

⚠ Per `metatheory/docs/GUARD-DISCIPLINE.md` these are `decide`/`norm_num` THEOREMS rather than
`#guard`s: a `#guard` produces no term, is invisible to `#assert_axioms`, and is exactly the
case-testing this repo forbids in Rust. -/

/-- A four-rung chain over contiguous columns — the shape a `u64` tally takes. -/
def demoRungs : List Rung :=
  [⟨0, 4, 8, 13⟩, ⟨1, 5, 9, 14⟩, ⟨2, 6, 10, 15⟩, ⟨3, 7, 11, 16⟩]

/-- The difference vector's top column. -/
def demoTop : Nat := 12

/-- The chain generates five gate bodies from four rungs — one per rung plus the closure gate.
A generator that dropped the closure gate would leave this at four. -/
theorem demo_body_count :
    (chainBodies TALLY_LIMB_BITS 3 2 1 TALLY_CARRY_OFF demoTop demoRungs).length = 5 := by
  norm_num [chainBodies, chainBodies.go, demoRungs, demoTop]

/-- The difference vector is five limbs — `α·A − β·B − γ` needs `⌈log₂ 3⌉` bits beyond `A`'s 64. -/
theorem demo_diff_width : (diffCols demoRungs demoTop).length = 5 := by
  norm_num [diffCols, demoRungs, demoTop]

/-- ⚑ **A REAL-SCALE TENDERMINT TALLY, DENOTED.** `1152921504606846975 = 2^60 − 1` is CometBFT's
`MaxTotalVotingPower` (`int64(math.MaxInt64) / 8`). Its four 16-bit limbs are
`[65535, 65535, 65535, 4095]`, LSB-first, and they denote it exactly.

This is the value the single-felt column could not hold at ANY declared width. -/
theorem max_total_voting_power_is_denoted :
    limbValue TALLY_LIMB_BITS
      (fun i => if i = 0 then 65535 else if i = 1 then 65535 else if i = 2 then 65535
                else if i = 3 then 4095 else 0)
      [0, 1, 2, 3] = 1152921504606846975 := by
  norm_num [limbValue, TALLY_LIMB_BITS]

/-- …and its limbs are each contained, so `limbValue_nonneg` and `limbValue_lt` apply to it. -/
theorem max_total_voting_power_limbs_contained :
    LimbsInRange TALLY_LIMB_BITS
      (fun i => if i = 0 then 65535 else if i = 1 then 65535 else if i = 2 then 65535
                else if i = 3 then 4095 else 0)
      [0, 1, 2, 3] := by
  refine ⟨⟨by norm_num, by norm_num [TALLY_LIMB_BITS]⟩, ⟨by norm_num, by norm_num [TALLY_LIMB_BITS]⟩,
    ⟨by norm_num, by norm_num [TALLY_LIMB_BITS]⟩, ⟨by norm_num, by norm_num [TALLY_LIMB_BITS]⟩,
    trivial⟩

/-- ⚑ **THE SAME TALLY DOES NOT FIT IN A FELT**, and this is the whole reason the file exists:
`MaxTotalVotingPower` is 572 million times the BabyBear modulus. No declared range width ever changed
that — a width declares an interval, and the WIRE is one field element. -/
theorem max_total_voting_power_exceeds_the_field :
    (572000000 : ℤ) * P < 1152921504606846975 := by
  norm_num [Dregg2.Circuit.RangeFieldContainment.babybear_modulus]

/-- …and 29 bits — the maximum WRAP-FREE width, the ceiling the census landed on — is 536,870,912,
which the strict-threshold slack `3·signedPow` blows past at a total power of about 1.8e8. The 29-bit
repair was correct AND left the client unable to represent a real validator set. -/
theorem twentynine_bit_ceiling_is_below_chain_scale :
    3 * 1152921504606846975 > (2 : ℤ) ^ 29 := by norm_num

/-! ## §9 — axiom hygiene. -/

#assert_axioms limbValue_nonneg
#assert_axioms limbValue_lt
#assert_axioms chain_recomposes
#assert_axioms cmp_sound
#assert_axioms cmp_refuses_below_threshold
#assert_axioms refusal_is_field_independent
#assert_axioms refused_at_the_width_that_was_vacuous
#assert_axioms refused_at_the_width_that_was_leaky
#assert_axioms chainBodies_zero_iff
#assert_axioms emitted_chain_sound
#assert_axioms emitted_chain_refuses
#assert_axioms rung_value_bounds
#assert_axioms rung_no_alias_at_deployed_constants
#assert_axioms rung_alias_reachable_at_24_bits
#assert_axioms rung_reachable_min_at_deployed_width
#assert_axioms fill_splits
#assert_axioms fillDigit_in_range
#assert_axioms max_total_voting_power_is_denoted

end Dregg2.Circuit.LimbTally
