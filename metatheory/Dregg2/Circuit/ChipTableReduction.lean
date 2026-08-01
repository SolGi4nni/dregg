/-
# Dregg2.Circuit.ChipTableReduction — reducing `ChipTableSoundN` off the opaque-floor list.

## What this closes

`AcceptanceDischarge` reduced the `WitnessDecodes`/`<e>TraceReadout` per-effect readouts to a single
residual: `RotTableSide.chipTableFaithful : ChipTableSoundN permOut (t.tf .poseidon2)` — "every
committed chip row IS a genuine wide permutation tuple" — which it (correctly) declared NOT forced by
`Satisfied2`'s row-local satisfaction, hence a knowledge-extraction floor. That left `ChipTableSoundN`
looking like a STANDALONE opaque assumption in `kernelConfigSound`'s residual.

This module FACTORS that residual into its honest parts, so `ChipTableSoundN` is DERIVED, not fresh:

  * **RANGE half — STRUCTURAL (proven, no assumption).** The range-table faithfulness conjunct
    (`Satisfied2Faithful.rangeTableFaithful : t.tf .range = rangeRows bits`) is not a crypto lever: it
    binds `.range` to `rangeRows bits`, which is DEFINITIONALLY `[0, 2^bits)` (the honest range
    predicate's graph). `range_table_faithful_of_structural` reads off, from that one equation, that
    EVERY committed range row is `[v]` with `0 ≤ v < 2^bits` — reusing `range_row_mem_iff`, purely by
    bound arithmetic on `List.range`, NEVER enumerating the `2^30` rows. So the range part of the
    table-faithfulness residual is `rfl`/definitional, not an opaque floor.

  * **POSEIDON2 half — a NAMED, SEPARATE primitive (not `Poseidon2SpongeCR`), through which
    `ChipTableSoundN` is DISCHARGED.** `ChipTableSoundN permOut tbl` decomposes per row into (1) the
    STRUCTURAL row shape `arity :: padTo CHIP_RATE ins ++ outBlock` (from which `ins`/`outBlock` are
    UNIQUELY recoverable — `chipRowShaped_decode_unique`, pure list algebra, no crypto) and (2) the
    PERMUTATION-CORRECTNESS residual `outBlock = permOut ins`. Part (2) is EXACTLY what the deployed
    `Ir2Air::Chip` round gates (`poseidon2_permute_expr`, `descriptor_ir2.rs:1919`, KAT-conformed to
    the pinned p3 permutation) force on every committed chip row — but those round gates are NOT
    `VmConstraint2`s of any Lean descriptor (the chip is a fixed preprocessed table AIR in Rust), so
    `Satisfied2` cannot deliver them. We name that content precisely as `Poseidon2ChipArithSound` —
    the soundness of the Poseidon2 round-constraint arithmetization — and prove `ChipTableSoundN` is
    its composition with the acceptance-side fact that the deployed AIR gates hold on the extracted
    committed rows (`ChipRoundGatesAccepted`, the same epistemic class as the bus/FRI facts
    `AcceptanceDischarge` discharges). `chipTableSoundN_of_arith_and_accept` is the discharge.

    `Poseidon2ChipArithSound` is a DIFFERENT primitive from `Poseidon2SpongeCR`: CR is injectivity of
    the sponge; the chip floor is OUTPUT-CORRECTNESS of the specific permutation. `arithSound_not_CR`
    proves the separation concretely — the all-zero permutation is arith-consistent as a chip table
    yet its lane-0 digest is constant, violating CR. So the honest residual is a named
    hash-arithmetization primitive `Poseidon2ChipArithSound`, NOT a re-assumption of `ChipTableSoundN`
    and NOT `Poseidon2SpongeCR`.

## The honest residual of `ChipTableSoundN`

`ChipTableSoundN` is REDUCED to `{Poseidon2ChipArithSound (the round-gate arithmetization soundness,
a named hash primitive — sibling of, not implied by, `Poseidon2SpongeCR`) + the acceptance-side
round-gate satisfaction + the structural row decode}`; the accompanying range-table faithfulness is
STRUCTURAL (`rfl` to `rangeRows`). No fresh opaque floor; the sole crypto residual is the named
Poseidon2 chip-arithmetization soundness.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Sorry-free; NO `decide`/`Fintype` over
field-sized objects (BabyBear noncomputable); NO enumeration of any `2^bits` table (range is symbolic).
NEW file; imports read-only; builds targeted (`lake build Dregg2.Circuit.ChipTableReduction`).
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.Poseidon2Binding

namespace Dregg2.Circuit.ChipTableReduction

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmRange VmRowEnv)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

set_option autoImplicit false

/-! ## §1 — RANGE half: the range-table faithfulness is STRUCTURAL (`rfl` to `[0, 2^bits)`).

The `Satisfied2Faithful.rangeTableFaithful` conjunct is `t.tf .range = rangeRows bits`. `rangeRows bits`
is DEFINITIONALLY `(List.range (2^bits)).map (fun n => [(n : ℤ)])` — the graph of the honest range
predicate. So faithfulness is not a lever; it is read off symbolically (bound arithmetic on
`List.range`), NEVER by materializing the `2^bits` rows. -/

/-- **`range_table_faithful_of_structural` — the range half is proven, not assumed.** From the single
structural equation `tf .range = rangeRows bits` (the deployed range AIR's height), the committed range
table's rows are EXACTLY the honest interval: `[v] ∈ tf .range ↔ 0 ≤ v < 2^bits` (reusing
`range_row_mem_iff`). Symbolic — the `2^bits` rows are never enumerated. -/
theorem range_table_faithful_of_structural (tf : TraceFamily) (bits : Nat)
    (hr : tf .range = rangeRows bits) :
    ∀ v : ℤ, [v] ∈ tf .range ↔ 0 ≤ v ∧ v < (2 : ℤ) ^ bits := by
  intro v; rw [hr]; exact range_row_mem_iff v bits

/-- **The range lookup ENFORCES exactly the honest predicate** (`lookup_replaces_range`, re-exported):
against the structurally-faithful range table, a range lookup on wire `w` forces `0 ≤ loc w < 2^bits`
— `VmRange.holds` verbatim, the field-soundness tooth. So both directions (the table IS honest, and
the lookup FORCES honesty) are structural consequences of the one `rangeRows` equation. -/
theorem range_lookup_forces_honest (bits : Nat) (tf : TraceFamily)
    (hr : tf .range = rangeRows bits) (env : VmRowEnv) (w : Nat)
    (h : Lookup.holdsAt tf env ⟨.range, [.var w]⟩) :
    0 ≤ env.loc w ∧ env.loc w < (2 : ℤ) ^ bits :=
  lookup_replaces_range bits tf hr env w h

/-! ### §1b — RANGE non-vacuity: fire on the DEPLOYED height `BAL_LIMB_BITS = 30`, symbolically. -/

/-- A concrete in-range limb `[90]` is a committed row of the DEPLOYED range table (`bits = 30`),
proven by `range_row_mem_iff` + bound arithmetic — NOT by scanning the `2^30` rows. -/
theorem in_range_row_mem : ([90] : List ℤ) ∈ rangeRows BAL_LIMB_BITS := by
  rw [range_row_mem_iff]
  refine ⟨by norm_num, ?_⟩
  rw [BAL_LIMB_BITS]; norm_num

/-- The boundary value `2^30` is OUT of the deployed range table — the field-wraparound the range
tooth forbids. Again symbolic (the interval bound), never an enumeration. -/
theorem boundary_row_not_mem : ([(2 : ℤ) ^ BAL_LIMB_BITS]) ∉ rangeRows BAL_LIMB_BITS := by
  rw [range_row_mem_iff]
  rintro ⟨_, hlt⟩
  exact (lt_irrefl _) hlt

/-! ## §2 — POSEIDON2 half, STRUCTURE: the row layout, and the unique input/output decode.

`chipRowN permOut ins = (ins.length : ℤ) :: (padTo CHIP_RATE ins ++ permOut ins)`. The STRUCTURAL
skeleton — the arity tag, the padded-input block, a fixed-width output block — is independent of the
permutation VALUES. `ChipRowShaped` captures it, and the decode is UNIQUE: the arity tag pins the
input length, `padTo` injectivity pins the inputs, and the append splits off the output block. Pure
list algebra, no crypto. -/

/-- The STRUCTURAL chip-row shape the deployed layout fixes: `arity :: (padTo CHIP_RATE ins ++
outBlock)` with `arity = ins.length` ADMITTED by the chip and a fixed `CHIP_OUT_LANES`-wide output
block.

⚑ The arity condition is `ChipArityAdmitted`, not `≤ CHIP_RATE`, and it belongs in the STRUCTURAL
half exactly as much as the padded-block width does: the deployed admission is a degree-7 POLYNOMIAL
IDENTITY on the arity column (`descriptor_ir2.rs:3073`), not a crypto fact. A row at arity 8 is as
unrepresentable on the deployed chip as a row of the wrong length, and the shape predicate has to
say so or it describes a chip nobody built. -/
def ChipRowShaped (r : List ℤ) : Prop :=
  ∃ ins outBlock : List ℤ, ChipArityAdmitted ins.length ∧ outBlock.length = CHIP_OUT_LANES ∧
    r = (ins.length : ℤ) :: (padTo CHIP_RATE ins ++ outBlock)

/-- Every genuine wide chip row (of a `CHIP_OUT_LANES`-wide permutation) is `ChipRowShaped` — the
structural projection of chip soundness (no crypto: the output block is just *some* 8-felt list). -/
theorem chipRowN_shaped (permOut : List ℤ → List ℤ) (ins : List ℤ)
    (hlen : ChipArityAdmitted ins.length) (hw : (permOut ins).length = CHIP_OUT_LANES) :
    ChipRowShaped (chipRowN permOut ins) :=
  ⟨ins, permOut ins, hlen, hw, rfl⟩

/-- **`chipRowShaped_decode_unique` — the input/output decode is UNIQUE.** Two shaped decodings of the
SAME row agree on the recovered inputs AND the recovered output block. The arity tag forces equal
input lengths; `padTo_inj` recovers the inputs; `List.append_inj` splits off the output. Pure list
algebra — this is the load-bearing structural content (no "padding confusion" survives). -/
theorem chipRowShaped_decode_unique (r : List ℤ)
    (ins₁ out₁ ins₂ out₂ : List ℤ)
    (hlen₁ : ins₁.length ≤ CHIP_RATE) (hlen₂ : ins₂.length ≤ CHIP_RATE)
    (h₁ : r = (ins₁.length : ℤ) :: (padTo CHIP_RATE ins₁ ++ out₁))
    (h₂ : r = (ins₂.length : ℤ) :: (padTo CHIP_RATE ins₂ ++ out₂)) :
    ins₁ = ins₂ ∧ out₁ = out₂ := by
  rw [h₁] at h₂
  injection h₂ with hhead htail
  have hlens : ins₁.length = ins₂.length := Int.natCast_inj.mp hhead
  have hpad : (padTo CHIP_RATE ins₁).length = (padTo CHIP_RATE ins₂).length := by
    rw [padTo_length hlen₁, padTo_length hlen₂]
  obtain ⟨hpe, hoe⟩ := List.append_inj htail hpad
  exact ⟨padTo_inj hlens hpe, hoe⟩

/-- **The genuineness ↔ shape + output split.** A row is a genuine `chipRowN permOut ins` iff it is
`ChipRowShaped` AND its recovered output block equals `permOut` of its recovered inputs. This ISOLATES
the residual: everything but `outBlock = permOut ins` is structural. -/
theorem chipRowGenuine_of_shaped_output (permOut : List ℤ → List ℤ) (r : List ℤ)
    (ins outBlock : List ℤ) (hlen : ChipArityAdmitted ins.length)
    (hshape : r = (ins.length : ℤ) :: (padTo CHIP_RATE ins ++ outBlock))
    (hout : outBlock = permOut ins) :
    ∃ ins' : List ℤ, ChipArityAdmitted ins'.length ∧ r = chipRowN permOut ins' :=
  ⟨ins, hlen, by rw [hshape, hout]; rfl⟩

/-! ### §2b — the STRUCTURE already rejects malformed rows (real content, no crypto). -/

/-- The all-zero width-8 squeeze — a concrete `CHIP_OUT_LANES`-wide permutation (a degenerate-but-real
chip with the all-zero output for the all-zero state). -/
def permZ : List ℤ → List ℤ := fun _ => List.replicate CHIP_OUT_LANES 0

theorem permZ_width (ins : List ℤ) : (permZ ins).length = CHIP_OUT_LANES := by simp [permZ]

/-- A genuine chip row for `permZ` (arity-0 absorb). -/
def genRow : List ℤ := chipRowN permZ []

theorem genRow_shaped : ChipRowShaped genRow :=
  chipRowN_shaped permZ [] (of_decide_eq_true (Eq.refl true)) (permZ_width [])

/-- A malformed row `[0]` (length 1) is NOT `ChipRowShaped`: a genuine row has length
`1 + CHIP_RATE + CHIP_OUT_LANES = 25 ≠ 1`. So the STRUCTURAL skeleton alone rejects the forgery. -/
theorem forged_not_shaped : ¬ ChipRowShaped ([0] : List ℤ) := by
  rintro ⟨ins, out, hlen, hw, heq⟩
  have hl : ([0] : List ℤ).length = ((ins.length : ℤ) :: (padTo CHIP_RATE ins ++ out)).length := by
    rw [heq]
  simp only [List.length_cons, List.length_append, padTo_length (chipArity_le_rate hlen), hw] at hl
  simp [CHIP_RATE, CHIP_OUT_LANES] at hl

/-! ## §3 — POSEIDON2 half, the RESIDUAL: named as `Poseidon2ChipArithSound`, and the DISCHARGE.

The deployed `Ir2Air::Chip` (`poseidon2_permute_expr`) pins every committed chip row so that its output
block IS the real permutation squeeze of its inputs. Those round gates are NOT `VmConstraint2`s of any
descriptor (the chip is a fixed preprocessed table AIR in Rust), so `Satisfied2` cannot force them. We
model the round-gate denotation as an abstract per-row predicate `roundGates`, and name its SOUNDNESS —
gate satisfaction ⟹ genuine chip tuple — precisely. -/

/-- **THE NAMED PRIMITIVE — `Poseidon2ChipArithSound`.** The Poseidon2 chip round-constraint
arithmetization (`poseidon2_permute_expr`) is SOUND: any row whose committed round cells satisfy the
deployed round gates IS a genuine wide chip tuple of the REAL permutation `permOut`. This is the
correctness of the round-by-round S-box + linear-layer gates the Rust KAT conformance pins
(`poseidon2_plonky3_cross_check_kat`). It is a SEPARATE primitive from `Poseidon2SpongeCR`
(collision-resistance): here we need `output = permutation(input)`, NOT injectivity. -/
def Poseidon2ChipArithSound (permOut : List ℤ → List ℤ) (roundGates : List ℤ → Prop) : Prop :=
  ∀ r : List ℤ, roundGates r →
    ∃ ins : List ℤ, ChipArityAdmitted ins.length ∧ r = chipRowN permOut ins

/-- **The ACCEPTANCE-side fact** the deployed proof delivers: every committed chip row satisfies the
round gates (the `Ir2Air::Chip` AIR holds on the extracted trace). Same epistemic class as the bus /
FRI extraction facts `AcceptanceDischarge` discharges — NOT a fresh opaque assumption; it is what proof
acceptance produces for the fixed chip table. -/
def ChipRoundGatesAccepted (roundGates : List ℤ → Prop) (tbl : Table) : Prop :=
  ∀ r ∈ tbl, roundGates r

/-- **`chipTableSoundN_of_arith_and_accept` — THE DISCHARGE.** `ChipTableSoundN` is the composition of
the named round-gate arithmetization soundness with the acceptance-side round-gate satisfaction. So the
readout residual is DERIVED, not a fresh floor: it reduces to `{Poseidon2ChipArithSound, the
extraction-side gate acceptance}`. -/
theorem chipTableSoundN_of_arith_and_accept (permOut : List ℤ → List ℤ)
    (roundGates : List ℤ → Prop) (tbl : Table)
    (harith : Poseidon2ChipArithSound permOut roundGates)
    (haccept : ChipRoundGatesAccepted roundGates tbl) :
    ChipTableSoundN permOut tbl :=
  fun r hr => harith r (haccept r hr)

/-! ### §3b — the residual is a SEPARATE primitive, not `Poseidon2SpongeCR`.

`arithSound_not_CR` exhibits a chip whose round-gate arithmetization is SOUND (the all-zero
permutation, pinned by the honest gates) yet whose lane-0 digest is constant — violating CR. So
`Poseidon2ChipArithSound` does NOT reduce to `Poseidon2SpongeCR`; naming it is the honest floor. -/

/-- The concrete round-gate denotation for the all-zero permutation: the row is shaped and its output
block is the all-zero squeeze. This is a GENUINE, output-constraining predicate (it rejects both
malformed rows AND shaped rows with the wrong output — see `roundGatesZ_separates`), not `True`. -/
def roundGatesZ (r : List ℤ) : Prop :=
  ChipRowShaped r ∧
    ∀ ins outBlock : List ℤ, ins.length ≤ CHIP_RATE →
      r = (ins.length : ℤ) :: (padTo CHIP_RATE ins ++ outBlock) → outBlock = permZ ins

/-- The round-gate arithmetization for `permZ` is SOUND: shape + the output leg ⟹ genuine. Real work
(the output leg forces `outBlock = permZ ins`, then `chipRowGenuine_of_shaped_output`). -/
theorem arithSound_permZ : Poseidon2ChipArithSound permZ roundGatesZ := by
  rintro r ⟨⟨ins, outBlock, hlen, _hw, hshape⟩, hout⟩
  exact chipRowGenuine_of_shaped_output permZ r ins outBlock hlen hshape
    (hout ins outBlock (chipArity_le_rate hlen) hshape)

/-- The genuine row satisfies the round gates (its output block IS `permZ` of its inputs — forced by
the unique decode). -/
theorem genRow_roundGates : roundGatesZ genRow := by
  refine ⟨genRow_shaped, ?_⟩
  intro ins outBlock hlen hdecode
  -- decode genRow canonically (ins = [], out = permZ []) and against the given (ins, outBlock)
  have hcanon : genRow = (([] : List ℤ).length : ℤ) :: (padTo CHIP_RATE [] ++ permZ []) := rfl
  obtain ⟨_, hout⟩ := chipRowShaped_decode_unique genRow [] (permZ []) ins outBlock
    (by simp [CHIP_RATE]) hlen hcanon hdecode
  -- `permZ` is constant, so `permZ [] = permZ ins`.
  exact hout.symm.trans rfl

/-- The one-row genuine table has all rows round-gate-accepted. -/
theorem genRow_accepted : ChipRoundGatesAccepted roundGatesZ [genRow] := by
  intro r hr
  rw [List.mem_singleton] at hr
  subst hr; exact genRow_roundGates

/-- **The discharge FIRES** end-to-end: `ChipTableSoundN permZ [genRow]` PRODUCED from the named
arithmetization soundness + the acceptance-side gate satisfaction. -/
theorem chipTableSoundN_fires : ChipTableSoundN permZ [genRow] :=
  chipTableSoundN_of_arith_and_accept permZ roundGatesZ [genRow] arithSound_permZ genRow_accepted

/-- The round gates genuinely CONSTRAIN the output: a shaped row with the WRONG output block (all-ones)
FAILS them. So `roundGatesZ` is not `True`; the residual is genuinely permutation-OUTPUT correctness. -/
theorem roundGatesZ_separates :
    ¬ roundGatesZ ((([] : List ℤ).length : ℤ) ::
        (padTo CHIP_RATE [] ++ List.replicate CHIP_OUT_LANES (1 : ℤ))) := by
  rintro ⟨_, hout⟩
  have h := hout [] (List.replicate CHIP_OUT_LANES (1 : ℤ)) (by simp [CHIP_RATE]) rfl
  -- `replicate n 1 = permZ [] = replicate n 0` forces `1 = 0` at head (n = 8 > 0).
  rw [permZ] at h
  have hc := congrArg (fun l => l.headD (2 : ℤ)) h
  simp [CHIP_OUT_LANES] at hc

/-- **`arithSound_not_CR` — the Poseidon2 half is NOT `Poseidon2SpongeCR`.** There is a permutation
whose chip round-gate arithmetization is SOUND (`permZ`, pinned by `roundGatesZ`) yet whose exposed
lane-0 digest is the CONSTANT `0` — which is not injective, so it VIOLATES `Poseidon2SpongeCR`. Hence
chip-arithmetization soundness does not entail (and does not reduce to) collision-resistance: they are
distinct named primitives. -/
theorem arithSound_not_CR :
    ∃ (permOut : List ℤ → List ℤ) (roundGates : List ℤ → Prop),
      Poseidon2ChipArithSound permOut roundGates ∧
      ¬ Poseidon2SpongeCR (fun ins => (permOut ins).headD 0) := by
  refine ⟨permZ, roundGatesZ, arithSound_permZ, ?_⟩
  intro hCR
  -- the lane-0 digest of `permZ` is constant `0`, so CR would force `[0] = [1]`.
  have hdig : (fun ins => (permZ ins).headD 0) = (fun _ => (0 : ℤ)) := by
    funext ins; simp [permZ, CHIP_OUT_LANES]
  rw [hdig] at hCR
  have : ([0] : List ℤ) = [1] := hCR [0] [1] rfl
  simp at this

/-! ## §4 — ASSEMBLY: the full table-faithfulness residual (chip + range), matching `Satisfied2Faithful`.

`Satisfied2Faithful` carries TWO table-faithfulness conjuncts: `chipTableFaithful` (= `ChipTableSoundN`)
and `rangeTableFaithful` (= `t.tf .range = rangeRows bits`). This assembles both from the honest
residual: the chip conjunct from `{Poseidon2ChipArithSound + acceptance}`, the range conjunct being the
STRUCTURAL equation itself (which `range_table_faithful_of_structural` shows binds the honest
interval). No fresh opaque floor beyond the single named `Poseidon2ChipArithSound`. -/

/-- **`tableFaithfulness_of_arith_and_range` — the WHOLE residual, DERIVED.** From the named chip
arithmetization soundness + the acceptance-side gate satisfaction + the structural range equation, BOTH
faithfulness conjuncts of `Satisfied2Faithful` hold — chip soundness discharged through the round-gate
primitive, range faithfulness structural. -/
theorem tableFaithfulness_of_arith_and_range (permOut : List ℤ → List ℤ)
    (roundGates : List ℤ → Prop) (t : VmTrace) (bits : Nat)
    (harith : Poseidon2ChipArithSound permOut roundGates)
    (haccept : ChipRoundGatesAccepted roundGates (t.tf .poseidon2))
    (hrange : t.tf .range = rangeRows bits) :
    ChipTableSoundN permOut (t.tf .poseidon2) ∧ t.tf .range = rangeRows bits :=
  ⟨chipTableSoundN_of_arith_and_accept permOut roundGates (t.tf .poseidon2) harith haccept, hrange⟩

/-! ## §5 — axiom hygiene. -/

#assert_axioms range_table_faithful_of_structural
#assert_axioms range_lookup_forces_honest
#assert_axioms in_range_row_mem
#assert_axioms boundary_row_not_mem
#assert_axioms chipRowShaped_decode_unique
#assert_axioms chipRowGenuine_of_shaped_output
#assert_axioms forged_not_shaped
#assert_axioms chipTableSoundN_of_arith_and_accept
#assert_axioms arithSound_permZ
#assert_axioms genRow_roundGates
#assert_axioms chipTableSoundN_fires
#assert_axioms roundGatesZ_separates
#assert_axioms arithSound_not_CR
#assert_axioms tableFaithfulness_of_arith_and_range

end Dregg2.Circuit.ChipTableReduction
