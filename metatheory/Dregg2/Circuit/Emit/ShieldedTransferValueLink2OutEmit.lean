/-
# Dregg2.Circuit.Emit.ShieldedTransferValueLink2OutEmit — the shielded transfer's SPLIT, in the AIR.

## SAY THE SUBSTRATE OUT LOUD

This is **Lean-authored AIR**. The constraint list below IS the emitted object; Rust's only job is
to decode it (`parse_vm_descriptor2`), fill a witness trace and prove/verify it. Rust authors no
constraint here.

## The wound this closes

`dregg-shielded-transfer-value-link::v1` binds ONE spent note to ONE minted note of equal value.
That is a whole-note transfer — a change of owner — and it is all the deployed path admits
(`circuit-prove/src/shielded/transfer.rs` refuses every other arity by name). **So a shielded note
is all-or-nothing: you can spend it, but you can never get change.** Holding `1000` and owing `7`,
the only move the chain states is to hand over the whole `1000`.

That is not a missing convenience. It is a value-carrying relation that cannot express the most
ordinary thing value does, and the workaround — pre-splitting into denomination notes at shield
time — leaks the amount into the note COUNT, which is public.

## What `shieldedTransferValueLink2OutDesc` IS

One row, over a private witness
`(value, asset, inRand, inBlind^6, out¹Value, out¹Owner, out¹Rand, out²Value, out²Owner, out²Rand)`:

    (R1) every one of the 4 × 4 × 16 bit cells is BOOLEAN
    (R2) limb_{k,i} = Σ_{b<16} 2^b · bit_{k,i,b}   for k ∈ {value, asset, out¹, out²}
    (R3) asset_mod_p / out¹_mod_p / out²_mod_p are the reductions of their limbs — three, not
         four: the sidecar's `value mod p` slot is NOT gated here, because unlike the 1-out link
         no site in this relation hashes it (each mint hashes its own value)
    (R4) inWideA[0..8] = cap_node8([DOMAIN_A, v0..v3, a0,a1,a2], [a3, inRand, inBlind0..5])
    (R5) inWideB[0..8] = the SAME node8 at DOMAIN_B
    (R6) outCm_k = hash_fact(out^k_mod_p, [asset_mod_p, outOwner_k, outRand_k])   for k < 2
    (R7) **THE CARRY CHAIN** — `v_i = o¹_i + o²_i − 65536·c_i + c_{i−1}`, every `c_i` boolean,
         `c_{−1}` structurally ABSENT (no term to forget) and `c_3` GATE-PINNED to zero
    (R8) row 0 publishes `[inWideA[0..8], inWideB[0..8], outCm¹, outCm²]` — 18 public inputs

**THE CONSERVATION IS (R7) READING THE SAME LIMB COLUMNS (R4)/(R5) ABSORB AND (R6) HASHES.** The
sixteen published carrier lanes are the carrier of the note the transfer SPENDS — the verifier
supplies them from the complete-spend proof's own PI-pinned `wide[16]`, so they are not this
prover's claim. The two published `outCm`s are the leaves the executor APPENDS.

`link2_conservation` is the theorem: on a satisfying trace with canonical cells,
`u64Of a 0 = u64Of a 2 + u64Of a 3` — an equation over **ℤ**, not a residue. It is not assumed of
the witness; it is produced by four gates whose every term is bounded far below `p/2`, so the
mod-`p` vanishing lifts to an integer identity.

## ⚑ Why the final carry is a GATE and not a comment

`carry_chain_sums` states the algebraic core with `c₃` FREE:

    o¹ + o² = v + 2^64 · c₃

That is the whole attack surface of a limbwise chain, written out. A prover who could set `c₃ = 1`
would mint `2^64` from nothing while every other gate stayed satisfied — the four limb equations
balance perfectly, because the overflow is exactly what a carry is FOR. `carry_top_zero` is the one
gate that collapses that to conservation, and `overflow_carry_unsat` is its refusal.

The `c₋₁` end is closed the other way, and deliberately: `carryChainHead 0` has **no incoming-carry
term at all** — not a term pinned to zero, which is a pin that can be dropped in a refactor, but an
absence in the emitted object. The two ends of the chain are closed by two different mechanisms
because only one of them can be closed structurally.

## Column-for-column with the objects it joins

Columns `0..16` are `WideValueBindingEmit`'s columns `0..16`, index for index
(`layout_agrees_with_sidecar`), and `wideLeft`/`wideRight` are **IMPORTED** from that module rather
than re-typed — the same term, from the same source `dregg-shielded-transfer-value-link::v1` reads
it from (`carrier_absorb_is_the_sidecar_absorb`). So the carrier this relation publishes and the
carrier the complete spend PI-pins are the same function of the same opening, and the Rust join is
a felt-for-felt equality on 16 lanes rather than a re-derivation.

Each `outCm_k`'s preimage is the deployed note commitment `hash_fact(vmod, [amod, owner, rand])` —
`ShieldedSpendCompleteEmit`'s `lkCM` and `dregg-shielded-shield::v1`'s mint, same site. **So BOTH
minted notes are SPENDABLE by exactly the complete-spend relation**, which is what makes the
conservation claim mean anything: the value that leaves is the value that arrives, split in two, in
the same domain, openable by the same circuit.

The asset is SHARED — one `cAMOD` column, hashed into both commitments. A split cannot change what
it is a split of.

## ⚑ FLAG DAY

`dregg-shielded-transfer-value-link-2out::v1` is a NEW descriptor (309 columns, 18 PIs, 305
constraints) and needs its VK epoch rolled with the shielded family. The transfer payload gains a
second output and its link proof moves from PER-OUTPUT to PER-TRANSFER — conservation across two
outputs is a JOINT statement and cannot be carried by two independent per-output proofs, each of
which would separately claim the whole input value. A pre-cutover payload does not decode as a
current one. Details in `circuit-prove/src/shielded/transfer.rs`.

## Axiom hygiene

Definitional descriptor, named theorems (no `#guard`), the wire golden pinned by `native_decide` +
`#assert_compiled`. NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.WideValueBindingRefine

namespace Dregg2.Circuit.Emit.ShieldedTransferValueLink2OutEmit

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId Table VmTrace envAt Satisfied2
   chipLookupTupleN chipLookupTupleNarrow poseidon2narrow CHIP_RATE CHIP_OUT_LANES
   ChipTableSoundN ChipTableSound chip_lookup_sound_N emitVmJson2)
open Dregg2.Circuit.ChipNarrowLookup (narrowTable narrow_lookup_holdsAt_sound)
open Dregg2.Circuit.Emit.WideValueBindingRefine
  (Canon bin_of_gate bitSum bitSum_bounds limbWeight_modEq sum_modEq)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.Emit.AirBuilder
open Dregg2.Circuit.Emit.WideValueBindingEmit
  (U64_LIMBS LIMB_BITS WIDE_LANES BLIND_LANES DOMAIN_A DOMAIN_B P limbWeight FACT_MARK
   wideLeft wideRight wideOut factIns)

set_option autoImplicit false
set_option maxRecDepth 100000

/-! ## §1 — the column layout.

Columns `0..16` are `WideValueBindingEmit`'s columns `0..16`, index for index, so the imported
`wideLeft`/`wideRight` absorb blocks denote THIS relation's cells (`layout_agrees_with_sidecar`).
The two minted notes' own witnesses, their commitments and the carry chain sit above them. -/

/-- Value limb `i` of the SPENT note. Little-endian: `value = Σ 2^{16i}·v_i`. -/
def cV (i : Nat) : Nat := i
/-- Asset limb `i` — SHARED by the spent note and BOTH minted notes. A split cannot change what it
is a split of, so there is one asset column and both commitments hash it. -/
def cA (i : Nat) : Nat := U64_LIMBS + i
/-- The sidecar's `value mod p` slot. **This relation emits NO gate over it and reads it nowhere**
— and that is the difference from `dregg-shielded-transfer-value-link::v1`, where the minted note
reused the spent value and so hashed this cell. Here each mint hashes its OWN `cOMOD k`, so a
reduction gate on this column would constrain a cell nothing consumes.

The column index is kept because columns `0..16` must be the sidecar's index for index for the
IMPORTED `wideLeft`/`wideRight` absorb term to denote the right cells (`layout_agrees_with_sidecar`)
— the absorb reads `cV`, `cA`, `cRAND`, `cBL` and skips `8`/`9`, so `8` is an alignment slot, not a
value this relation binds. `reduction_gates_are_exactly_the_consumed_ones` says so as a fact. -/
def cVMOD : Nat := 2 * U64_LIMBS
/-- `asset mod p`. -/
def cAMOD : Nat := cVMOD + 1
/-- The SPENT note's randomness (absorbed by the carrier the spend proof published). -/
def cRAND : Nat := cVMOD + 2
/-- The SPENT note's carrier blind lane `i`. -/
def cBL (i : Nat) : Nat := cVMOD + 3 + i

/-- Base of the two minted notes' value limbs — the first column ABOVE the sidecar block. -/
def OUT_LIMBS_BASE : Nat := cVMOD + 3 + BLIND_LANES
/-- Value limb `i` of minted note `k` (`k < 2`). These are FREE witness cells; the carry chain is
what ties them to `cV`. -/
def cO (k i : Nat) : Nat := OUT_LIMBS_BASE + k * U64_LIMBS + i
/-- `out^k mod p` — the felt minted note `k`'s commitment hashes. -/
def cOMOD (k : Nat) : Nat := OUT_LIMBS_BASE + 2 * U64_LIMBS + k
/-- Minted note `k`'s owner felt (`hash_fact(key0,[key1,key2,key3])` of the recipient). Free
witness: the payees are the sender's choice, and — with the randomness — the ONLY things about the
outputs the sender gets to choose. Not their values: those are chained to the spent note's. -/
def cOWNER (k : Nat) : Nat := OUT_LIMBS_BASE + 2 * U64_LIMBS + 2 + 2 * k
/-- Minted note `k`'s randomness. Free witness — it is what makes `outCm_k` hiding. -/
def cORAND (k : Nat) : Nat := OUT_LIMBS_BASE + 2 * U64_LIMBS + 3 + 2 * k
/-- Lane `j` of the SPENT note's `DOMAIN_A` carrier. -/
def cWA (j : Nat) : Nat := OUT_LIMBS_BASE + 2 * U64_LIMBS + 6 + j
/-- Lane `j` of the SPENT note's `DOMAIN_B` carrier. -/
def cWB (j : Nat) : Nat := OUT_LIMBS_BASE + 2 * U64_LIMBS + 14 + j
/-- Minted note `k`'s commitment `hash_fact(cOMOD k, [cAMOD, cOWNER k, cORAND k])` — a 32-byte leaf
the executor appends to `note_shielded`, and a leaf the complete-spend relation can open. -/
def cOUTCM (k : Nat) : Nat := OUT_LIMBS_BASE + 2 * U64_LIMBS + 22 + k
/-- **The carry out of limb `i`.** `c_3` is gate-pinned to zero (`carryTopZero`); `c_0..c_2` are
boolean-pinned. There is no `c_{-1}` column and no gate pinning one: the incoming-carry term is
structurally absent from `carryChainHead 0`. -/
def cCARRY (i : Nat) : Nat := OUT_LIMBS_BASE + 2 * U64_LIMBS + 24 + i
/-- Base of the bit-decomposition block. -/
def BITS_BASE : Nat := OUT_LIMBS_BASE + 2 * U64_LIMBS + 24 + U64_LIMBS
/-- Bit `b` of limb `i` of kind `k` (`0 = value, 1 = asset, 2 = out¹, 3 = out²`). -/
def cBit (k i b : Nat) : Nat := BITS_BASE + (k * U64_LIMBS + i) * LIMB_BITS + b
/-- **The main-trace width.** -/
def LINK2_WIDTH : Nat := BITS_BASE + 4 * U64_LIMBS * LIMB_BITS

/-- Limb `i` of kind `k`: `0 = spent value`, `1 = asset`, `2 = minted¹`, `3 = minted²`. -/
def cLimb (k i : Nat) : Nat :=
  if k = 0 then cV i else if k = 1 then cA i else cO (k - 2) i

theorem cVMOD_eq : cVMOD = 8 := rfl
theorem cAMOD_eq : cAMOD = 9 := rfl
theorem cRAND_eq : cRAND = 10 := rfl
theorem cBL_lo : cBL 0 = 11 := rfl
theorem cBL_hi : cBL 5 = 16 := rfl
theorem cO_lo : cO 0 0 = 17 := rfl
theorem cO_hi : cO 1 3 = 24 := rfl
theorem cOMOD_eq : (cOMOD 0, cOMOD 1) = (25, 26) := rfl
theorem cOWNER_eq : (cOWNER 0, cOWNER 1) = (27, 29) := rfl
theorem cORAND_eq : (cORAND 0, cORAND 1) = (28, 30) := rfl
theorem cWA_eq : cWA 0 = 31 := rfl
theorem cWB_eq : cWB 0 = 39 := rfl
theorem cOUTCM_eq : (cOUTCM 0, cOUTCM 1) = (47, 48) := rfl
theorem cCARRY_eq : (cCARRY 0, cCARRY 3) = (49, 52) := rfl
theorem BITS_BASE_eq : BITS_BASE = 53 := rfl
theorem LINK2_WIDTH_eq : LINK2_WIDTH = 309 := rfl

theorem cLimb_value (i : Nat) : cLimb 0 i = cV i := rfl
theorem cLimb_asset (i : Nat) : cLimb 1 i = cA i := rfl
theorem cLimb_out0 (i : Nat) : cLimb 2 i = cO 0 i := rfl
theorem cLimb_out1 (i : Nat) : cLimb 3 i = cO 1 i := rfl

/-- **THE LAYOUT JOIN, as a fact rather than a comment.** Columns `0..16` are the sidecar's columns
`0..16`, index for index — which is why importing `wideLeft`/`wideRight` (defined over THOSE column
functions) emits absorb blocks over THESE cells, and why the sixteen lanes this relation publishes
are comparable felt-for-felt with the ones the complete spend PI-pins AND with the ones the 1-out
value link publishes. Move a column here and this theorem, not a downstream test, is what goes
red. -/
theorem layout_agrees_with_sidecar :
    (∀ i, cV i = Dregg2.Circuit.Emit.WideValueBindingEmit.cV i)
    ∧ (∀ i, cA i = Dregg2.Circuit.Emit.WideValueBindingEmit.cA i)
    ∧ cVMOD = Dregg2.Circuit.Emit.WideValueBindingEmit.cVMOD
    ∧ cAMOD = Dregg2.Circuit.Emit.WideValueBindingEmit.cAMOD
    ∧ cRAND = Dregg2.Circuit.Emit.WideValueBindingEmit.cRAND
    ∧ (∀ i, cBL i = Dregg2.Circuit.Emit.WideValueBindingEmit.cBL i) :=
  ⟨fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, fun _ => rfl⟩

/-- **Nothing new collides with the sidecar block.** Every column this relation adds sits strictly
above `cBL 5 = 16`, so the imported absorb term cannot be reading a cell the split writes. -/
theorem new_columns_above_the_sidecar :
    (∀ k i, k < 2 → i < U64_LIMBS → 16 < cO k i)
    ∧ (∀ k, k < 2 → 16 < cOMOD k ∧ 16 < cOWNER k ∧ 16 < cORAND k ∧ 16 < cOUTCM k)
    ∧ (∀ i, i < U64_LIMBS → 16 < cCARRY i)
    ∧ (∀ k i b, 16 < cBit k i b) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;>
    simp only [cO, cOMOD, cOWNER, cORAND, cOUTCM, cCARRY, cBit, OUT_LIMBS_BASE, BITS_BASE,
      cVMOD, U64_LIMBS, LIMB_BITS, BLIND_LANES] <;> omega

/-! ## §2 — the public-input layout.

`[inWideA[0..8], inWideB[0..8], outCm¹, outCm²]`. The sixteen carrier lanes are NOT this prover's
claim: the verifier supplies them from the complete-spend proof's own `wide[16]` public inputs,
which that proof's `carrierPins` force to the spent note's opening. The two `outCm`s are the leaves
the executor appends. -/

/-- PI 0 — the first lane of the spent note's carrier. -/
def PI_WIDE : Nat := 0
/-- PI 16 — minted note 0's commitment; PI 17 — minted note 1's. -/
def PI_OUTCM : Nat := WIDE_LANES
/-- Total public inputs. -/
def LINK2_PI_COUNT : Nat := WIDE_LANES + 2

theorem PI_OUTCM_eq : PI_OUTCM = 16 := rfl
theorem LINK2_PI_COUNT_eq : LINK2_PI_COUNT = 18 := rfl

/-! ## §3 — the gates. -/

/-- R2 — `limb_{k,i} − Σ_{b<16} 2^b·bit_{k,i,b}`. -/
def limbRecomposeHead (k i : Nat) : Head :=
  (List.range LIMB_BITS).foldl (fun h b => h.addLin (-(2 ^ b : ℤ)) (cBit k i b))
    (Head.lin 1 (cLimb k i))

/-- R1+R2 for one limb: its sixteen boolean pins, then its recomposition. -/
def limbGates (k i : Nat) : List VmConstraint2 :=
  ((List.range LIMB_BITS).map fun b => binGate (cBit k i b))
  ++ [cgH (limbRecomposeHead k i)]

/-- R3 — `out − Σ_{i<4} (2^{16i} mod p)·limb_{k,i}`: the felt a note commitment hashes is DERIVED
from the full limbs, never independent of them. -/
def u64RecomposeHead (k out : Nat) : Head :=
  (List.range U64_LIMBS).foldl (fun h i => h.addLin (-(limbWeight i)) (cLimb k i))
    (Head.lin 1 out)

/-- The limb-`i` body of the carry chain WITHOUT the incoming carry:
`v_i − o¹_i − o²_i + 65536·c_i`. -/
def carryBody (i : Nat) : Head :=
  (((Head.lin 1 (cV i)).addLin (-1) (cO 0 i)).addLin (-1) (cO 1 i)).addLin
    (2 ^ LIMB_BITS : ℤ) (cCARRY i)

/-- **R7 — THE CARRY CHAIN.** `v_i = o¹_i + o²_i − 65536·c_i + c_{i−1}`, emitted as
`v_i − o¹_i − o²_i + 65536·c_i − c_{i−1} = 0`.

⚑ At `i = 0` there is **no incoming-carry term at all**. `c_{−1} = 0` is therefore a property of
the emitted object, not a pin over a column that a later refactor could drop. The other end of the
chain cannot be closed that way — `c_3` is a real column the chain writes — so it gets a gate
(`carryTopZero`) and a refusal (`overflow_carry_unsat`). -/
def carryChainHead : Nat → Head
  | 0     => carryBody 0
  | j + 1 => (carryBody (j + 1)).addLin (-1) (cCARRY j)

/-- **The gate that forbids minting `2^64`.** `carry_chain_sums` shows the four chain gates alone
give `o¹ + o² = v + 2^64·c₃`; this is what collapses it to conservation. -/
def carryTopZero : VmConstraint2 := cgH (Head.lin 1 (cCARRY (U64_LIMBS - 1)))

/-- One domain-separated wide carrier site over the SPENT note's opening. The absorb block is the
imported `wideLeft ++ wideRight` — the sidecar's, the complete spend's `carrierIns`, and the 1-out
value link's. -/
def wideSite (domain : ℤ) (base : Nat) : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2, chipLookupTupleN (wideLeft domain ++ wideRight) (wideOut base)⟩

/-- R6 — `outCm_k = hash_fact(out^k_mod_p, [asset_mod_p, outOwner_k, outRand_k])`: the deployed
note commitment, over the SAME shared asset felt and over minted note `k`'s own reduced value. -/
def outCmSite (k : Nat) : VmConstraint2 :=
  .lookup ⟨poseidon2narrow,
    chipLookupTupleNarrow
      (factIns [.var (cOMOD k), .var cAMOD, .var (cOWNER k), .var (cORAND k)]) (cOUTCM k)⟩

/-- The published lane `lane`'s column. -/
def laneCol (lane : Nat) : Nat := if lane < 8 then cWA lane else cWB (lane - 8)

/-- The 18 first-row PI bindings. -/
def piPins : List VmConstraint2 :=
  ((List.range WIDE_LANES).map fun lane => pinPi (laneCol lane) (PI_WIDE + lane))
  ++ ((List.range 2).map fun k => pinPi (cOUTCM k) (PI_OUTCM + k))

/-! ## §4 — THE DESCRIPTOR. -/

/-- The full constraint list: the per-limb boolean+recompose blocks (value, asset, both mints), the
four compatibility reductions, the carry chain with its booleanity pins and its terminal zero, the
two carrier sites, the two output note-commitment sites, the pins. -/
def shieldedTransferValueLink2OutConstraints : List VmConstraint2 :=
  ((List.range 4).flatMap fun k => (List.range U64_LIMBS).flatMap fun i => limbGates k i)
  ++ [cgH (u64RecomposeHead 1 cAMOD),
      cgH (u64RecomposeHead 2 (cOMOD 0)), cgH (u64RecomposeHead 3 (cOMOD 1))]
  ++ ((List.range U64_LIMBS).map fun i => cgH (carryChainHead i))
  ++ ((List.range (U64_LIMBS - 1)).map fun i => binGate (cCARRY i))
  ++ [carryTopZero]
  ++ [wideSite DOMAIN_A (cWA 0), wideSite DOMAIN_B (cWB 0)]
  ++ [outCmSite 0, outCmSite 1]
  ++ piPins

/-- **`shieldedTransferValueLink2OutDesc`** — the Lean-authored 1-in/2-out value-link AIR. Chip
tables are Presence-detected from the lookups, and the limb range check is an explicit bit
decomposition, so `tables` and `ranges` are both empty. -/
def shieldedTransferValueLink2OutDesc : EffectVmDescriptor2 :=
  { name        := "dregg-shielded-transfer-value-link-2out::v1"
  , traceWidth  := LINK2_WIDTH
  , piCount     := LINK2_PI_COUNT
  , tables      := []
  , constraints := shieldedTransferValueLink2OutConstraints
  , hashSites   := []
  , ranges      := [] }

/-! ## §5 — the census, as named theorems (`#guard` is a unit test in Lean clothes). -/

/-- 256 boolean pins + 16 limb recompositions + 3 reductions + 4 chain gates + 3 carry booleanity
pins + 1 terminal zero + 2 carriers + 2 fact sites + 18 pins. -/
theorem constraint_census : shieldedTransferValueLink2OutDesc.constraints.length = 305 := by decide

/-- The algebraic gates: the 256 booleanity pins, the 16 limb recompositions, the 3 reductions, the
4 chain gates, the 3 carry booleanity pins, the terminal zero. -/
theorem gate_census :
    (shieldedTransferValueLink2OutDesc.constraints.filter
      (fun c => match c with | .base (.gate _) => true | _ => false)).length
      = 4 * U64_LIMBS * LIMB_BITS + 4 * U64_LIMBS + 3 + U64_LIMBS + (U64_LIMBS - 1) + 1 := by
  decide

/-- The bodies of every emitted algebraic gate. `EmittedExpr` carries `DecidableEq`, so facts about
WHICH gates were emitted are decidable over this list rather than restatements of the definition. -/
def emittedGateBodies : List EmittedExpr :=
  shieldedTransferValueLink2OutDesc.constraints.filterMap
    (fun c => match c with | .base (.gate e) => some e | _ => none)

/-- **The reduction gates are exactly the three cells this relation CONSUMES** — the shared asset
felt and the two minted values, each hashed by a note-commitment site. There is no fourth: a gate
over the sidecar's `cVMOD` slot would pin a cell nothing reads, and a reader who found one would
reasonably conclude the spent note's value felt was bound to something here. It is not; the carrier
is what binds the spent note. -/
theorem reduction_gates_are_exactly_the_consumed_ones :
    headToExpr (u64RecomposeHead 1 cAMOD) ∈ emittedGateBodies
    ∧ headToExpr (u64RecomposeHead 2 (cOMOD 0)) ∈ emittedGateBodies
    ∧ headToExpr (u64RecomposeHead 3 (cOMOD 1)) ∈ emittedGateBodies
    ∧ headToExpr (u64RecomposeHead 0 cVMOD) ∉ emittedGateBodies := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- Every public input is pinned, and nothing else is. -/
theorem pi_census :
    (shieldedTransferValueLink2OutDesc.constraints.filter
      (fun c => match c with | .base (.piBinding _ _ _) => true | _ => false)).length
      = LINK2_PI_COUNT := by decide

/-- Exactly two WIDE (arity-16, eight-lane) carrier sites — the sidecar's two, at the sidecar's two
domains. A third would be a second opening to decouple. -/
theorem wide_site_census :
    (shieldedTransferValueLink2OutDesc.constraints.filterMap
      (fun c => match c with
        | .lookup l => if l.table == TableId.poseidon2 then some l.tuple.length else none
        | _ => none)) = [25, 25] := by decide

/-- Exactly TWO narrow sites: the two output note commitments. There is no third hash an output
could be tied to instead. -/
theorem narrow_site_census :
    (shieldedTransferValueLink2OutDesc.constraints.filterMap
      (fun c => match c with
        | .lookup l => if l.table == poseidon2narrow then some l.tuple.length else none
        | _ => none)) = [18, 18] := by decide

/-- **The bit columns are 256 distinct in-range columns — as a GENERAL fact.** `cBit` is injective
on the emitted index range; the felt-width repair is a property of the indexing function, not of
one enumerated list. -/
theorem cBit_injective {k i b k' i' b' : Nat} (hi : i < U64_LIMBS)
    (hb : b < LIMB_BITS) (hi' : i' < U64_LIMBS) (hb' : b' < LIMB_BITS)
    (h : cBit k i b = cBit k' i' b') : k = k' ∧ i = i' ∧ b = b' := by
  simp only [cBit, BITS_BASE, U64_LIMBS, LIMB_BITS, OUT_LIMBS_BASE, cVMOD, BLIND_LANES] at *
  omega

/-- Every emitted bit column is inside the trace. -/
theorem cBit_in_range {k i b : Nat} (hk : k < 4) (hi : i < U64_LIMBS) (hb : b < LIMB_BITS) :
    cBit k i b < LINK2_WIDTH := by
  simp only [cBit, BITS_BASE, LINK2_WIDTH, U64_LIMBS, LIMB_BITS, OUT_LIMBS_BASE, cVMOD,
    BLIND_LANES] at *
  omega

/-- The four carry columns are distinct, in range, and — over the emitted index range — disjoint
from the bit block. (The `i < U64_LIMBS` bound on the last clause is load-bearing, not decoration:
`cCARRY 4` IS `cBit 0 0 0`, which is exactly why the chain emits four carries and no more.) -/
theorem carry_columns_distinct_and_in_range :
    (∀ i j, i < U64_LIMBS → j < U64_LIMBS → cCARRY i = cCARRY j → i = j)
    ∧ (∀ i, i < U64_LIMBS → cCARRY i < LINK2_WIDTH)
    ∧ (∀ i k l b, i < U64_LIMBS → cCARRY i ≠ cBit k l b) := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;>
    simp only [cCARRY, cBit, BITS_BASE, LINK2_WIDTH, U64_LIMBS, LIMB_BITS, OUT_LIMBS_BASE, cVMOD,
      BLIND_LANES] at * <;> omega

/-- **The absorb block this relation publishes is the sidecar's, expression for expression.** Not
"the same shape" — the same term, because `wideLeft`/`wideRight` are imported from
`WideValueBindingEmit`, exactly as `dregg-shielded-transfer-value-link::v1` imports them. This is
what makes the Rust join a felt equality rather than a re-derivation, and what makes the 1-out and
2-out members of the family comparable against the same complete-spend carrier. -/
theorem carrier_absorb_is_the_sidecar_absorb (domain : ℤ) :
    wideLeft domain ++ wideRight
      = Dregg2.Circuit.Emit.WideValueBindingEmit.wideLeft domain
        ++ Dregg2.Circuit.Emit.WideValueBindingEmit.wideRight := rfl

/-- The two carrier sites, both output sites, all four chain gates and the terminal zero are
present in the emitted list. -/
theorem sites_emitted :
    wideSite DOMAIN_A (cWA 0) ∈ shieldedTransferValueLink2OutDesc.constraints
    ∧ wideSite DOMAIN_B (cWB 0) ∈ shieldedTransferValueLink2OutDesc.constraints
    ∧ outCmSite 0 ∈ shieldedTransferValueLink2OutDesc.constraints
    ∧ outCmSite 1 ∈ shieldedTransferValueLink2OutDesc.constraints
    ∧ carryTopZero ∈ shieldedTransferValueLink2OutDesc.constraints := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [shieldedTransferValueLink2OutDesc,
    shieldedTransferValueLink2OutConstraints]

/-! ## §6 — THE BYTE-PIN. Rust reads THIS raw string (`include_str!` + split +
`parse_vm_descriptor2`), so the Lean emission is the only copy that exists. -/

/-- **`SHIELDED_TRANSFER_VALUE_LINK_2OUT_GOLDEN`** — the byte-pinned wire string. -/
def SHIELDED_TRANSFER_VALUE_LINK_2OUT_GOLDEN : String := r#"{"name":"dregg-shielded-transfer-value-link-2out::v1","ir":2,"trace_width":309,"public_input_count":18,"challenges":0,"tables":[],"constraints":[{"t":"gate","body":{"t":"mul","l":{"t":"var","v":53},"r":{"t":"add","l":{"t":"var","v":53},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":54},"r":{"t":"add","l":{"t":"var","v":54},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":55},"r":{"t":"add","l":{"t":"var","v":55},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":56},"r":{"t":"add","l":{"t":"var","v":56},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":57},"r":{"t":"add","l":{"t":"var","v":57},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":58},"r":{"t":"add","l":{"t":"var","v":58},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":59},"r":{"t":"add","l":{"t":"var","v":59},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":60},"r":{"t":"add","l":{"t":"var","v":60},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":61},"r":{"t":"add","l":{"t":"var","v":61},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":62},"r":{"t":"add","l":{"t":"var","v":62},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":63},"r":{"t":"add","l":{"t":"var","v":63},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":64},"r":{"t":"add","l":{"t":"var","v":64},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":65},"r":{"t":"add","l":{"t":"var","v":65},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":66},"r":{"t":"add","l":{"t":"var","v":66},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":67},"r":{"t":"add","l":{"t":"var","v":67},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":68},"r":{"t":"add","l":{"t":"var","v":68},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":0}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":53}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":54}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":55}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":56}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":57}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":58}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":59}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":60}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":61}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":62}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":63}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":64}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":65}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":66}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":67}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":68}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":69},"r":{"t":"add","l":{"t":"var","v":69},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":70},"r":{"t":"add","l":{"t":"var","v":70},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":71},"r":{"t":"add","l":{"t":"var","v":71},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":72},"r":{"t":"add","l":{"t":"var","v":72},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":73},"r":{"t":"add","l":{"t":"var","v":73},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":74},"r":{"t":"add","l":{"t":"var","v":74},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":75},"r":{"t":"add","l":{"t":"var","v":75},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":76},"r":{"t":"add","l":{"t":"var","v":76},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":77},"r":{"t":"add","l":{"t":"var","v":77},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":78},"r":{"t":"add","l":{"t":"var","v":78},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":79},"r":{"t":"add","l":{"t":"var","v":79},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":80},"r":{"t":"add","l":{"t":"var","v":80},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":81},"r":{"t":"add","l":{"t":"var","v":81},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":82},"r":{"t":"add","l":{"t":"var","v":82},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":83},"r":{"t":"add","l":{"t":"var","v":83},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":84},"r":{"t":"add","l":{"t":"var","v":84},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":1}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":69}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":70}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":71}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":72}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":73}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":74}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":75}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":76}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":77}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":78}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":79}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":80}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":81}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":82}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":83}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":84}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":85},"r":{"t":"add","l":{"t":"var","v":85},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":86},"r":{"t":"add","l":{"t":"var","v":86},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":87},"r":{"t":"add","l":{"t":"var","v":87},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":88},"r":{"t":"add","l":{"t":"var","v":88},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":89},"r":{"t":"add","l":{"t":"var","v":89},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":90},"r":{"t":"add","l":{"t":"var","v":90},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":91},"r":{"t":"add","l":{"t":"var","v":91},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":92},"r":{"t":"add","l":{"t":"var","v":92},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":93},"r":{"t":"add","l":{"t":"var","v":93},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":94},"r":{"t":"add","l":{"t":"var","v":94},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":95},"r":{"t":"add","l":{"t":"var","v":95},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":96},"r":{"t":"add","l":{"t":"var","v":96},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":97},"r":{"t":"add","l":{"t":"var","v":97},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":98},"r":{"t":"add","l":{"t":"var","v":98},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":99},"r":{"t":"add","l":{"t":"var","v":99},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":100},"r":{"t":"add","l":{"t":"var","v":100},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":2}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":85}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":86}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":87}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":88}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":89}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":90}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":91}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":92}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":93}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":94}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":95}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":96}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":97}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":98}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":99}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":100}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":101},"r":{"t":"add","l":{"t":"var","v":101},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":102},"r":{"t":"add","l":{"t":"var","v":102},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":103},"r":{"t":"add","l":{"t":"var","v":103},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":104},"r":{"t":"add","l":{"t":"var","v":104},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":105},"r":{"t":"add","l":{"t":"var","v":105},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":106},"r":{"t":"add","l":{"t":"var","v":106},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":107},"r":{"t":"add","l":{"t":"var","v":107},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":108},"r":{"t":"add","l":{"t":"var","v":108},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":109},"r":{"t":"add","l":{"t":"var","v":109},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":110},"r":{"t":"add","l":{"t":"var","v":110},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":111},"r":{"t":"add","l":{"t":"var","v":111},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":112},"r":{"t":"add","l":{"t":"var","v":112},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":113},"r":{"t":"add","l":{"t":"var","v":113},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":114},"r":{"t":"add","l":{"t":"var","v":114},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":115},"r":{"t":"add","l":{"t":"var","v":115},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":116},"r":{"t":"add","l":{"t":"var","v":116},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":3}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":101}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":102}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":103}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":104}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":105}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":106}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":107}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":108}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":109}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":110}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":111}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":112}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":113}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":114}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":115}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":116}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":117},"r":{"t":"add","l":{"t":"var","v":117},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":118},"r":{"t":"add","l":{"t":"var","v":118},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":119},"r":{"t":"add","l":{"t":"var","v":119},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":120},"r":{"t":"add","l":{"t":"var","v":120},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":121},"r":{"t":"add","l":{"t":"var","v":121},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":122},"r":{"t":"add","l":{"t":"var","v":122},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":123},"r":{"t":"add","l":{"t":"var","v":123},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":124},"r":{"t":"add","l":{"t":"var","v":124},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":125},"r":{"t":"add","l":{"t":"var","v":125},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":126},"r":{"t":"add","l":{"t":"var","v":126},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":127},"r":{"t":"add","l":{"t":"var","v":127},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":128},"r":{"t":"add","l":{"t":"var","v":128},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":129},"r":{"t":"add","l":{"t":"var","v":129},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":130},"r":{"t":"add","l":{"t":"var","v":130},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":131},"r":{"t":"add","l":{"t":"var","v":131},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":132},"r":{"t":"add","l":{"t":"var","v":132},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":4}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":117}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":118}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":119}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":120}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":121}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":122}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":123}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":124}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":125}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":126}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":127}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":128}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":129}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":130}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":131}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":132}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":133},"r":{"t":"add","l":{"t":"var","v":133},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":134},"r":{"t":"add","l":{"t":"var","v":134},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":135},"r":{"t":"add","l":{"t":"var","v":135},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":136},"r":{"t":"add","l":{"t":"var","v":136},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":137},"r":{"t":"add","l":{"t":"var","v":137},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":138},"r":{"t":"add","l":{"t":"var","v":138},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":139},"r":{"t":"add","l":{"t":"var","v":139},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":140},"r":{"t":"add","l":{"t":"var","v":140},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":141},"r":{"t":"add","l":{"t":"var","v":141},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":142},"r":{"t":"add","l":{"t":"var","v":142},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":143},"r":{"t":"add","l":{"t":"var","v":143},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":144},"r":{"t":"add","l":{"t":"var","v":144},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":145},"r":{"t":"add","l":{"t":"var","v":145},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":146},"r":{"t":"add","l":{"t":"var","v":146},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":147},"r":{"t":"add","l":{"t":"var","v":147},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":148},"r":{"t":"add","l":{"t":"var","v":148},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":5}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":133}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":134}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":135}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":136}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":137}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":138}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":139}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":140}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":141}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":142}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":143}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":144}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":145}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":146}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":147}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":148}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":149},"r":{"t":"add","l":{"t":"var","v":149},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":150},"r":{"t":"add","l":{"t":"var","v":150},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":151},"r":{"t":"add","l":{"t":"var","v":151},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":152},"r":{"t":"add","l":{"t":"var","v":152},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":153},"r":{"t":"add","l":{"t":"var","v":153},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":154},"r":{"t":"add","l":{"t":"var","v":154},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":155},"r":{"t":"add","l":{"t":"var","v":155},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":156},"r":{"t":"add","l":{"t":"var","v":156},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":157},"r":{"t":"add","l":{"t":"var","v":157},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":158},"r":{"t":"add","l":{"t":"var","v":158},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":159},"r":{"t":"add","l":{"t":"var","v":159},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":160},"r":{"t":"add","l":{"t":"var","v":160},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":161},"r":{"t":"add","l":{"t":"var","v":161},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":162},"r":{"t":"add","l":{"t":"var","v":162},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":163},"r":{"t":"add","l":{"t":"var","v":163},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":164},"r":{"t":"add","l":{"t":"var","v":164},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":6}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":149}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":150}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":151}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":152}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":153}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":154}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":155}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":156}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":157}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":158}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":159}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":160}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":161}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":162}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":163}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":164}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":165},"r":{"t":"add","l":{"t":"var","v":165},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":166},"r":{"t":"add","l":{"t":"var","v":166},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":167},"r":{"t":"add","l":{"t":"var","v":167},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":168},"r":{"t":"add","l":{"t":"var","v":168},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":169},"r":{"t":"add","l":{"t":"var","v":169},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":170},"r":{"t":"add","l":{"t":"var","v":170},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":171},"r":{"t":"add","l":{"t":"var","v":171},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":172},"r":{"t":"add","l":{"t":"var","v":172},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":173},"r":{"t":"add","l":{"t":"var","v":173},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":174},"r":{"t":"add","l":{"t":"var","v":174},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":175},"r":{"t":"add","l":{"t":"var","v":175},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":176},"r":{"t":"add","l":{"t":"var","v":176},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":177},"r":{"t":"add","l":{"t":"var","v":177},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":178},"r":{"t":"add","l":{"t":"var","v":178},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":179},"r":{"t":"add","l":{"t":"var","v":179},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":180},"r":{"t":"add","l":{"t":"var","v":180},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":7}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":165}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":166}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":167}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":168}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":169}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":170}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":171}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":172}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":173}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":174}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":175}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":176}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":177}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":178}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":179}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":180}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":181},"r":{"t":"add","l":{"t":"var","v":181},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":182},"r":{"t":"add","l":{"t":"var","v":182},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":183},"r":{"t":"add","l":{"t":"var","v":183},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":184},"r":{"t":"add","l":{"t":"var","v":184},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":185},"r":{"t":"add","l":{"t":"var","v":185},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":186},"r":{"t":"add","l":{"t":"var","v":186},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":187},"r":{"t":"add","l":{"t":"var","v":187},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":188},"r":{"t":"add","l":{"t":"var","v":188},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":189},"r":{"t":"add","l":{"t":"var","v":189},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":190},"r":{"t":"add","l":{"t":"var","v":190},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":191},"r":{"t":"add","l":{"t":"var","v":191},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":192},"r":{"t":"add","l":{"t":"var","v":192},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":193},"r":{"t":"add","l":{"t":"var","v":193},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":194},"r":{"t":"add","l":{"t":"var","v":194},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":195},"r":{"t":"add","l":{"t":"var","v":195},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":196},"r":{"t":"add","l":{"t":"var","v":196},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":17}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":181}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":182}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":183}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":184}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":185}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":186}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":187}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":188}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":189}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":190}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":191}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":192}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":193}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":194}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":195}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":196}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":197},"r":{"t":"add","l":{"t":"var","v":197},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":198},"r":{"t":"add","l":{"t":"var","v":198},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":199},"r":{"t":"add","l":{"t":"var","v":199},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":200},"r":{"t":"add","l":{"t":"var","v":200},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":201},"r":{"t":"add","l":{"t":"var","v":201},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":202},"r":{"t":"add","l":{"t":"var","v":202},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":203},"r":{"t":"add","l":{"t":"var","v":203},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":204},"r":{"t":"add","l":{"t":"var","v":204},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":205},"r":{"t":"add","l":{"t":"var","v":205},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":206},"r":{"t":"add","l":{"t":"var","v":206},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":207},"r":{"t":"add","l":{"t":"var","v":207},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":208},"r":{"t":"add","l":{"t":"var","v":208},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":209},"r":{"t":"add","l":{"t":"var","v":209},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":210},"r":{"t":"add","l":{"t":"var","v":210},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":211},"r":{"t":"add","l":{"t":"var","v":211},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":212},"r":{"t":"add","l":{"t":"var","v":212},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":18}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":197}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":198}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":199}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":200}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":201}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":202}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":203}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":204}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":205}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":206}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":207}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":208}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":209}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":210}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":211}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":212}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":213},"r":{"t":"add","l":{"t":"var","v":213},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":214},"r":{"t":"add","l":{"t":"var","v":214},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":215},"r":{"t":"add","l":{"t":"var","v":215},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":216},"r":{"t":"add","l":{"t":"var","v":216},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":217},"r":{"t":"add","l":{"t":"var","v":217},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":218},"r":{"t":"add","l":{"t":"var","v":218},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":219},"r":{"t":"add","l":{"t":"var","v":219},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":220},"r":{"t":"add","l":{"t":"var","v":220},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":221},"r":{"t":"add","l":{"t":"var","v":221},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":222},"r":{"t":"add","l":{"t":"var","v":222},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":223},"r":{"t":"add","l":{"t":"var","v":223},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":224},"r":{"t":"add","l":{"t":"var","v":224},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":225},"r":{"t":"add","l":{"t":"var","v":225},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":226},"r":{"t":"add","l":{"t":"var","v":226},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":227},"r":{"t":"add","l":{"t":"var","v":227},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":228},"r":{"t":"add","l":{"t":"var","v":228},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":19}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":213}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":214}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":215}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":216}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":217}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":218}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":219}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":220}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":221}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":222}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":223}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":224}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":225}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":226}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":227}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":228}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":229},"r":{"t":"add","l":{"t":"var","v":229},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":230},"r":{"t":"add","l":{"t":"var","v":230},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":231},"r":{"t":"add","l":{"t":"var","v":231},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":232},"r":{"t":"add","l":{"t":"var","v":232},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":233},"r":{"t":"add","l":{"t":"var","v":233},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":234},"r":{"t":"add","l":{"t":"var","v":234},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":235},"r":{"t":"add","l":{"t":"var","v":235},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":236},"r":{"t":"add","l":{"t":"var","v":236},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":237},"r":{"t":"add","l":{"t":"var","v":237},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":238},"r":{"t":"add","l":{"t":"var","v":238},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":239},"r":{"t":"add","l":{"t":"var","v":239},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":240},"r":{"t":"add","l":{"t":"var","v":240},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":241},"r":{"t":"add","l":{"t":"var","v":241},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":242},"r":{"t":"add","l":{"t":"var","v":242},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":243},"r":{"t":"add","l":{"t":"var","v":243},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":244},"r":{"t":"add","l":{"t":"var","v":244},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":20}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":229}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":230}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":231}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":232}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":233}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":234}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":235}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":236}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":237}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":238}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":239}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":240}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":241}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":242}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":243}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":244}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":245},"r":{"t":"add","l":{"t":"var","v":245},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":246},"r":{"t":"add","l":{"t":"var","v":246},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":247},"r":{"t":"add","l":{"t":"var","v":247},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":248},"r":{"t":"add","l":{"t":"var","v":248},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":249},"r":{"t":"add","l":{"t":"var","v":249},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":250},"r":{"t":"add","l":{"t":"var","v":250},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":251},"r":{"t":"add","l":{"t":"var","v":251},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":252},"r":{"t":"add","l":{"t":"var","v":252},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":253},"r":{"t":"add","l":{"t":"var","v":253},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":254},"r":{"t":"add","l":{"t":"var","v":254},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":255},"r":{"t":"add","l":{"t":"var","v":255},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":256},"r":{"t":"add","l":{"t":"var","v":256},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":257},"r":{"t":"add","l":{"t":"var","v":257},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":258},"r":{"t":"add","l":{"t":"var","v":258},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":259},"r":{"t":"add","l":{"t":"var","v":259},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":260},"r":{"t":"add","l":{"t":"var","v":260},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":21}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":245}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":246}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":247}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":248}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":249}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":250}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":251}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":252}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":253}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":254}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":255}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":256}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":257}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":258}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":259}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":260}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":261},"r":{"t":"add","l":{"t":"var","v":261},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":262},"r":{"t":"add","l":{"t":"var","v":262},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":263},"r":{"t":"add","l":{"t":"var","v":263},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":264},"r":{"t":"add","l":{"t":"var","v":264},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":265},"r":{"t":"add","l":{"t":"var","v":265},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":266},"r":{"t":"add","l":{"t":"var","v":266},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":267},"r":{"t":"add","l":{"t":"var","v":267},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":268},"r":{"t":"add","l":{"t":"var","v":268},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":269},"r":{"t":"add","l":{"t":"var","v":269},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":270},"r":{"t":"add","l":{"t":"var","v":270},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":271},"r":{"t":"add","l":{"t":"var","v":271},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":272},"r":{"t":"add","l":{"t":"var","v":272},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":273},"r":{"t":"add","l":{"t":"var","v":273},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":274},"r":{"t":"add","l":{"t":"var","v":274},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":275},"r":{"t":"add","l":{"t":"var","v":275},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":276},"r":{"t":"add","l":{"t":"var","v":276},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":22}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":261}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":262}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":263}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":264}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":265}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":266}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":267}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":268}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":269}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":270}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":271}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":272}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":273}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":274}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":275}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":276}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":277},"r":{"t":"add","l":{"t":"var","v":277},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":278},"r":{"t":"add","l":{"t":"var","v":278},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":279},"r":{"t":"add","l":{"t":"var","v":279},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":280},"r":{"t":"add","l":{"t":"var","v":280},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":281},"r":{"t":"add","l":{"t":"var","v":281},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":282},"r":{"t":"add","l":{"t":"var","v":282},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":283},"r":{"t":"add","l":{"t":"var","v":283},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":284},"r":{"t":"add","l":{"t":"var","v":284},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":285},"r":{"t":"add","l":{"t":"var","v":285},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":286},"r":{"t":"add","l":{"t":"var","v":286},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":287},"r":{"t":"add","l":{"t":"var","v":287},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":288},"r":{"t":"add","l":{"t":"var","v":288},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":289},"r":{"t":"add","l":{"t":"var","v":289},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":290},"r":{"t":"add","l":{"t":"var","v":290},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":291},"r":{"t":"add","l":{"t":"var","v":291},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":292},"r":{"t":"add","l":{"t":"var","v":292},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":23}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":277}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":278}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":279}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":280}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":281}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":282}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":283}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":284}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":285}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":286}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":287}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":288}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":289}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":290}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":291}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":292}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":293},"r":{"t":"add","l":{"t":"var","v":293},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":294},"r":{"t":"add","l":{"t":"var","v":294},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":295},"r":{"t":"add","l":{"t":"var","v":295},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":296},"r":{"t":"add","l":{"t":"var","v":296},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":297},"r":{"t":"add","l":{"t":"var","v":297},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":298},"r":{"t":"add","l":{"t":"var","v":298},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":299},"r":{"t":"add","l":{"t":"var","v":299},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":300},"r":{"t":"add","l":{"t":"var","v":300},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":301},"r":{"t":"add","l":{"t":"var","v":301},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":302},"r":{"t":"add","l":{"t":"var","v":302},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":303},"r":{"t":"add","l":{"t":"var","v":303},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":304},"r":{"t":"add","l":{"t":"var","v":304},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":305},"r":{"t":"add","l":{"t":"var","v":305},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":306},"r":{"t":"add","l":{"t":"var","v":306},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":307},"r":{"t":"add","l":{"t":"var","v":307},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":308},"r":{"t":"add","l":{"t":"var","v":308},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":24}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":293}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":294}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":295}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":296}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":297}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":298}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":299}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":300}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":301}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":302}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":303}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":304}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":305}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":306}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":307}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":308}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":9}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":4}}},"r":{"t":"mul","l":{"t":"const","v":-65536},"r":{"t":"var","v":5}}},"r":{"t":"mul","l":{"t":"const","v":-268435454},"r":{"t":"var","v":6}}},"r":{"t":"mul","l":{"t":"const","v":-268295646},"r":{"t":"var","v":7}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":25}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":17}}},"r":{"t":"mul","l":{"t":"const","v":-65536},"r":{"t":"var","v":18}}},"r":{"t":"mul","l":{"t":"const","v":-268435454},"r":{"t":"var","v":19}}},"r":{"t":"mul","l":{"t":"const","v":-268295646},"r":{"t":"var","v":20}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":26}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":21}}},"r":{"t":"mul","l":{"t":"const","v":-65536},"r":{"t":"var","v":22}}},"r":{"t":"mul","l":{"t":"const","v":-268435454},"r":{"t":"var","v":23}}},"r":{"t":"mul","l":{"t":"const","v":-268295646},"r":{"t":"var","v":24}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":0}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":17}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":21}}},"r":{"t":"mul","l":{"t":"const","v":65536},"r":{"t":"var","v":49}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":1}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":18}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":22}}},"r":{"t":"mul","l":{"t":"const","v":65536},"r":{"t":"var","v":50}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":49}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":2}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":19}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":23}}},"r":{"t":"mul","l":{"t":"const","v":65536},"r":{"t":"var","v":51}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":50}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":3}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":20}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":24}}},"r":{"t":"mul","l":{"t":"const","v":65536},"r":{"t":"var","v":52}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":51}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":49},"r":{"t":"add","l":{"t":"var","v":49},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":50},"r":{"t":"add","l":{"t":"var","v":50},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":51},"r":{"t":"add","l":{"t":"var","v":51},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":52}}},{"t":"lookup","table":1,"tuple":[{"t":"const","v":16},{"t":"const","v":1447185968},{"t":"var","v":0},{"t":"var","v":1},{"t":"var","v":2},{"t":"var","v":3},{"t":"var","v":4},{"t":"var","v":5},{"t":"var","v":6},{"t":"var","v":7},{"t":"var","v":10},{"t":"var","v":11},{"t":"var","v":12},{"t":"var","v":13},{"t":"var","v":14},{"t":"var","v":15},{"t":"var","v":16},{"t":"var","v":31},{"t":"var","v":32},{"t":"var","v":33},{"t":"var","v":34},{"t":"var","v":35},{"t":"var","v":36},{"t":"var","v":37},{"t":"var","v":38}]},{"t":"lookup","table":1,"tuple":[{"t":"const","v":16},{"t":"const","v":1447185969},{"t":"var","v":0},{"t":"var","v":1},{"t":"var","v":2},{"t":"var","v":3},{"t":"var","v":4},{"t":"var","v":5},{"t":"var","v":6},{"t":"var","v":7},{"t":"var","v":10},{"t":"var","v":11},{"t":"var","v":12},{"t":"var","v":13},{"t":"var","v":14},{"t":"var","v":15},{"t":"var","v":16},{"t":"var","v":39},{"t":"var","v":40},{"t":"var","v":41},{"t":"var","v":42},{"t":"var","v":43},{"t":"var","v":44},{"t":"var","v":45},{"t":"var","v":46}]},{"t":"lookup","table":8,"tuple":[{"t":"const","v":7},{"t":"var","v":25},{"t":"var","v":9},{"t":"var","v":27},{"t":"var","v":28},{"t":"const","v":0},{"t":"const","v":64207},{"t":"const","v":1},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":47}]},{"t":"lookup","table":8,"tuple":[{"t":"const","v":7},{"t":"var","v":26},{"t":"var","v":9},{"t":"var","v":29},{"t":"var","v":30},{"t":"const","v":0},{"t":"const","v":64207},{"t":"const","v":1},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":48}]},{"t":"pi_binding","row":"first","col":31,"pi_index":0},{"t":"pi_binding","row":"first","col":32,"pi_index":1},{"t":"pi_binding","row":"first","col":33,"pi_index":2},{"t":"pi_binding","row":"first","col":34,"pi_index":3},{"t":"pi_binding","row":"first","col":35,"pi_index":4},{"t":"pi_binding","row":"first","col":36,"pi_index":5},{"t":"pi_binding","row":"first","col":37,"pi_index":6},{"t":"pi_binding","row":"first","col":38,"pi_index":7},{"t":"pi_binding","row":"first","col":39,"pi_index":8},{"t":"pi_binding","row":"first","col":40,"pi_index":9},{"t":"pi_binding","row":"first","col":41,"pi_index":10},{"t":"pi_binding","row":"first","col":42,"pi_index":11},{"t":"pi_binding","row":"first","col":43,"pi_index":12},{"t":"pi_binding","row":"first","col":44,"pi_index":13},{"t":"pi_binding","row":"first","col":45,"pi_index":14},{"t":"pi_binding","row":"first","col":46,"pi_index":15},{"t":"pi_binding","row":"first","col":47,"pi_index":16},{"t":"pi_binding","row":"first","col":48,"pi_index":17}],"hash_sites":[],"ranges":[]}"#

/-- The emitted wire bytes ARE the pinned golden. Compiled-string equality, with the compiler
trust said out loud (`#assert_compiled` below) rather than hidden inside a `#guard`. -/
theorem link2_emits_golden :
    emitVmJson2 shieldedTransferValueLink2OutDesc = SHIELDED_TRANSFER_VALUE_LINK_2OUT_GOLDEN := by
  native_decide

/-! ## §7 — THE REFINEMENT: what a SATISFYING trace is forced to say.

Everything above is about the emitted OBJECT. This section is about its MEANING, over the actual
emitted constraint list — the SAT ⟹ SEM direction. The apparatus is the sidecar's, because §1's
layout join makes the relations share their absorb block; the carry chain is new. -/

section Refine
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
variable {permOut : List ℤ → List ℤ}

/-- The row assignment at index `i`. -/
def rowOf (t : VmTrace) (i : Nat) : Assignment := (envAt t i).loc

/-- Any emitted `Head` gate vanishes mod `p` on a transition row. -/
theorem lkGate (hsat : Satisfied2 hash shieldedTransferValueLink2OutDesc minit mfin maddrs t)
    (i : Nat) (hi : i + 1 < t.rows.length) {h : Head}
    (hm : cgH h ∈ shieldedTransferValueLink2OutDesc.constraints) :
    evalH h (rowOf t i) ≡ 0 [ZMOD 2013265921] := by
  have hrc := hsat.rowConstraints i (by omega) _ hm
  have hlf : (i + 1 == t.rows.length) = false := by
    have hne : i + 1 ≠ t.rows.length := by omega
    simpa using hne
  have hb : (headToExpr h).eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
    simpa only [cgH, cg, VmConstraint2.holdsAt, VmConstraint.holdsVm, hlf] using hrc
  rwa [headToExpr_eval] at hb

/-- The booleanity form. -/
theorem lkBin (hsat : Satisfied2 hash shieldedTransferValueLink2OutDesc minit mfin maddrs t)
    (i : Nat) (hi : i + 1 < t.rows.length) {c : Nat}
    (hm : binGate c ∈ shieldedTransferValueLink2OutDesc.constraints)
    (hcan : Canon (rowOf t i c)) :
    rowOf t i c = 0 ∨ rowOf t i c = 1 := by
  have hrc := hsat.rowConstraints i (by omega) _ hm
  have hlf : (i + 1 == t.rows.length) = false := by
    have hne : i + 1 ≠ t.rows.length := by omega
    simpa using hne
  have hb : (gBin c).eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
    simpa only [binGate, cg, VmConstraint2.holdsAt, VmConstraint.holdsVm, hlf] using hrc
  exact bin_of_gate hb hcan

/-- A lookup HOLDS on any row of a satisfying trace. -/
theorem lkLookup (hsat : Satisfied2 hash shieldedTransferValueLink2OutDesc minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) {l : Lookup}
    (hm : VmConstraint2.lookup l ∈ shieldedTransferValueLink2OutDesc.constraints) :
    l.holdsAt t.tf (envAt t i) := hsat.rowConstraints i hi _ hm

/-- A first-row PI binding forces the column to its public input. -/
theorem lkPin (hsat : Satisfied2 hash shieldedTransferValueLink2OutDesc minit mfin maddrs t)
    (hne : 0 < t.rows.length) {c k : Nat}
    (hm : pinPi c k ∈ shieldedTransferValueLink2OutDesc.constraints) :
    rowOf t 0 c ≡ (envAt t 0).pub k [ZMOD 2013265921] := by
  have hrc := hsat.rowConstraints 0 hne _ hm
  simpa only [pinPi, VmConstraint2.holdsAt, VmConstraint.holdsVm, rowOf] using hrc rfl

end Refine

/-! ### §7.1 — membership of each family in the emitted list. These are the ONLY place the
emission order is relied on. -/

section Membership
variable {x : VmConstraint2}

theorem mem_limbGates {k i : Nat} (hk : k < 4) (hi : i < U64_LIMBS) (hx : x ∈ limbGates k i) :
    x ∈ shieldedTransferValueLink2OutDesc.constraints := by
  have h1 : x ∈ (List.range 4).flatMap
      (fun k => (List.range U64_LIMBS).flatMap fun i => limbGates k i) := by
    refine List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, ?_⟩
    exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, hx⟩
  simp only [shieldedTransferValueLink2OutDesc, shieldedTransferValueLink2OutConstraints,
    List.mem_append]
  tauto

theorem mem_bin {k i b : Nat} (hk : k < 4) (hi : i < U64_LIMBS) (hb : b < LIMB_BITS) :
    binGate (cBit k i b) ∈ shieldedTransferValueLink2OutDesc.constraints :=
  mem_limbGates hk hi (by
    refine List.mem_append_left _ ?_
    exact List.mem_map.mpr ⟨b, List.mem_range.mpr hb, rfl⟩)

theorem mem_limbRecompose {k i : Nat} (hk : k < 4) (hi : i < U64_LIMBS) :
    cgH (limbRecomposeHead k i) ∈ shieldedTransferValueLink2OutDesc.constraints :=
  mem_limbGates hk hi (List.mem_append_right _ (by simp))

theorem mem_u64Recompose_asset :
    cgH (u64RecomposeHead 1 cAMOD) ∈ shieldedTransferValueLink2OutDesc.constraints := by
  simp only [shieldedTransferValueLink2OutDesc, shieldedTransferValueLink2OutConstraints,
    List.mem_append, List.mem_cons]
  tauto

theorem mem_u64Recompose_out0 :
    cgH (u64RecomposeHead 2 (cOMOD 0)) ∈ shieldedTransferValueLink2OutDesc.constraints := by
  simp only [shieldedTransferValueLink2OutDesc, shieldedTransferValueLink2OutConstraints,
    List.mem_append, List.mem_cons]
  tauto

theorem mem_u64Recompose_out1 :
    cgH (u64RecomposeHead 3 (cOMOD 1)) ∈ shieldedTransferValueLink2OutDesc.constraints := by
  simp only [shieldedTransferValueLink2OutDesc, shieldedTransferValueLink2OutConstraints,
    List.mem_append, List.mem_cons]
  tauto

/-- The limb-`i` chain gate is emitted. -/
theorem mem_carryChain {i : Nat} (hi : i < U64_LIMBS) :
    cgH (carryChainHead i) ∈ shieldedTransferValueLink2OutDesc.constraints := by
  have h1 : cgH (carryChainHead i)
      ∈ (List.range U64_LIMBS).map (fun i => cgH (carryChainHead i)) :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  simp only [shieldedTransferValueLink2OutDesc, shieldedTransferValueLink2OutConstraints,
    List.mem_append]
  tauto

/-- Carry `i`'s booleanity pin is emitted, for the three carries that are not the terminal one. -/
theorem mem_carryBin {i : Nat} (hi : i < U64_LIMBS - 1) :
    binGate (cCARRY i) ∈ shieldedTransferValueLink2OutDesc.constraints := by
  have h1 : binGate (cCARRY i) ∈ (List.range (U64_LIMBS - 1)).map (fun i => binGate (cCARRY i)) :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  simp only [shieldedTransferValueLink2OutDesc, shieldedTransferValueLink2OutConstraints,
    List.mem_append]
  tauto

/-- **The gate that forbids `2^64`** is in the emitted list. -/
theorem mem_carryTopZero :
    cgH (Head.lin 1 (cCARRY (U64_LIMBS - 1)))
      ∈ shieldedTransferValueLink2OutDesc.constraints := sites_emitted.2.2.2.2

theorem mem_wideA : wideSite DOMAIN_A (cWA 0) ∈ shieldedTransferValueLink2OutDesc.constraints :=
  sites_emitted.1

theorem mem_wideB : wideSite DOMAIN_B (cWB 0) ∈ shieldedTransferValueLink2OutDesc.constraints :=
  sites_emitted.2.1

theorem mem_outCm {k : Nat} (hk : k < 2) :
    outCmSite k ∈ shieldedTransferValueLink2OutDesc.constraints := by
  interval_cases k
  · exact sites_emitted.2.2.1
  · exact sites_emitted.2.2.2.1

theorem mem_pinLane {lane : Nat} (hl : lane < WIDE_LANES) :
    pinPi (laneCol lane) (PI_WIDE + lane) ∈ shieldedTransferValueLink2OutDesc.constraints := by
  have h1 : pinPi (laneCol lane) (PI_WIDE + lane)
      ∈ (List.range WIDE_LANES).map (fun l => pinPi (laneCol l) (PI_WIDE + l)) :=
    List.mem_map.mpr ⟨lane, List.mem_range.mpr hl, rfl⟩
  simp only [shieldedTransferValueLink2OutDesc, shieldedTransferValueLink2OutConstraints, piPins,
    List.mem_append]
  tauto

theorem mem_pinOutCm {k : Nat} (hk : k < 2) :
    pinPi (cOUTCM k) (PI_OUTCM + k) ∈ shieldedTransferValueLink2OutDesc.constraints := by
  have h1 : pinPi (cOUTCM k) (PI_OUTCM + k)
      ∈ (List.range 2).map (fun k => pinPi (cOUTCM k) (PI_OUTCM + k)) :=
    List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩
  simp only [shieldedTransferValueLink2OutDesc, shieldedTransferValueLink2OutConstraints, piPins,
    List.mem_append]
  tauto

end Membership

/-! ### §7.2 — the limbs are canonical, so every value in the relation is a genuine `u64`. -/

/-- The recomposition head evaluates to `limb − Σ 2^b·bit`. -/
theorem limbRecomposeHead_eval (a : Assignment) (k i : Nat) :
    evalH (limbRecomposeHead k i) a
      = a (cLimb k i) - bitSum a (fun b => cBit k i b) LIMB_BITS := by
  simp only [limbRecomposeHead, evalH_foldl_addLinG, evalH_lin, bitSum]
  have : ∀ xs : List Nat,
      (xs.map fun b => -(2 ^ b : ℤ) * a (cBit k i b)).sum
        = -(xs.map fun b => (2 ^ b : ℤ) * a (cBit k i b)).sum := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  rw [this]
  ring

section Canonical
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- **Each limb cell IS the weighted sum of its own boolean bit cells, hence `< 2^16`.** The
16-bit-ness is PRODUCED by the emitted gates, not assumed of the witness — for all FOUR kinds, so
the two minted values are genuine `u64`s and not residues, exactly as the spent one is.

This is what lets the carry chain be an INTEGER statement: every term in a chain gate is bounded
far below `p/2`, so `≡ 0 [ZMOD p]` lifts to `= 0` over ℤ (`exact_of_small_modEq_zero`). Without it
the chain would only say the values agree modulo `p`, which is not conservation. -/
theorem link2_limb_canonical
    (hsat : Satisfied2 hash shieldedTransferValueLink2OutDesc minit mfin maddrs t) (i₀ : Nat)
    (hi₀ : i₀ + 1 < t.rows.length) {k i : Nat} (hk : k < 4) (hi : i < U64_LIMBS)
    (hcan : Canon (rowOf t i₀ (cLimb k i)))
    (hcanb : ∀ b, b < LIMB_BITS → Canon (rowOf t i₀ (cBit k i b))) :
    rowOf t i₀ (cLimb k i) = bitSum (rowOf t i₀) (fun b => cBit k i b) LIMB_BITS
      ∧ 0 ≤ rowOf t i₀ (cLimb k i) ∧ rowOf t i₀ (cLimb k i) < 65536 := by
  have hbits : ∀ b, b < LIMB_BITS → rowOf t i₀ (cBit k i b) = 0 ∨ rowOf t i₀ (cBit k i b) = 1 :=
    fun b hb => lkBin hsat i₀ hi₀ (mem_bin hk hi hb) (hcanb b hb)
  obtain ⟨hs0, hs1⟩ := bitSum_bounds (rowOf t i₀) (fun b => cBit k i b) LIMB_BITS hbits
  have hgate := lkGate hsat i₀ hi₀ (mem_limbRecompose hk hi)
  rw [limbRecomposeHead_eval] at hgate
  have hdvd : (2013265921 : ℤ) ∣
      rowOf t i₀ (cLimb k i) - bitSum (rowOf t i₀) (fun b => cBit k i b) LIMB_BITS :=
    Int.modEq_zero_iff_dvd.mp hgate
  obtain ⟨hc0, hc1⟩ := hcan
  have hlt : (2 : ℤ) ^ LIMB_BITS = 65536 := by norm_num [LIMB_BITS]
  rw [hlt] at hs1
  obtain ⟨c, hc⟩ := hdvd
  have heq : rowOf t i₀ (cLimb k i) = bitSum (rowOf t i₀) (fun b => cBit k i b) LIMB_BITS := by
    omega
  exact ⟨heq, by omega, by omega⟩

end Canonical

/-! ### §7.3 — the value each compatibility felt denotes is the value its limbs denote. -/

/-- The `u64` a kind's four limb cells denote. -/
def u64Of (a : Assignment) (k : Nat) : ℤ :=
  ((List.range U64_LIMBS).map fun i => 2 ^ (LIMB_BITS * i) * a (cLimb k i)).sum

/-- The little-endian sum, written out — the form the carry-chain algebra consumes. -/
theorem u64Of_expand (a : Assignment) (k : Nat) :
    u64Of a k = a (cLimb k 0) + 65536 * a (cLimb k 1) + 4294967296 * a (cLimb k 2)
      + 281474976710656 * a (cLimb k 3) := by
  have hr : List.range U64_LIMBS = [0, 1, 2, 3] := rfl
  have e0 : (2 : ℤ) ^ (LIMB_BITS * 0) = 1 := by norm_num [LIMB_BITS]
  have e1 : (2 : ℤ) ^ (LIMB_BITS * 1) = 65536 := by norm_num [LIMB_BITS]
  have e2 : (2 : ℤ) ^ (LIMB_BITS * 2) = 4294967296 := by norm_num [LIMB_BITS]
  have e3 : (2 : ℤ) ^ (LIMB_BITS * 3) = 281474976710656 := by norm_num [LIMB_BITS]
  simp only [u64Of, hr, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, e0, e1, e2, e3]
  ring

/-- The compatibility head evaluates to `out − Σ (2^{16i} mod p)·limb_i`. -/
theorem u64RecomposeHead_eval (a : Assignment) (k out : Nat) :
    evalH (u64RecomposeHead k out) a
      = a out - ((List.range U64_LIMBS).map fun i => limbWeight i * a (cLimb k i)).sum := by
  simp only [u64RecomposeHead, evalH_foldl_addLinG, evalH_lin]
  have : ∀ xs : List Nat,
      (xs.map fun i => -(limbWeight i) * a (cLimb k i)).sum
        = -(xs.map fun i => limbWeight i * a (cLimb k i)).sum := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  rw [this]
  ring

section Reduction
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- **A compatibility felt is the reduction of the full `u64` its limbs denote** — the value a note
commitment hashes is never a second, free value. Stated once, over any emitted reduction gate, and
instantiated four times below. -/
theorem link2_mod_is_the_reduction
    (hsat : Satisfied2 hash shieldedTransferValueLink2OutDesc minit mfin maddrs t) (i₀ : Nat)
    (hi₀ : i₀ + 1 < t.rows.length) {k out : Nat}
    (hm : cgH (u64RecomposeHead k out) ∈ shieldedTransferValueLink2OutDesc.constraints) :
    rowOf t i₀ out ≡ u64Of (rowOf t i₀) k [ZMOD 2013265921] := by
  have hgate := lkGate hsat i₀ hi₀ hm
  rw [u64RecomposeHead_eval] at hgate
  have hs : ((List.range U64_LIMBS).map fun i => limbWeight i * rowOf t i₀ (cLimb k i)).sum
      ≡ u64Of (rowOf t i₀) k [ZMOD 2013265921] := by
    refine sum_modEq _ _ _ fun i _ => ?_
    exact Int.ModEq.mul_right _ (limbWeight_modEq i)
  have h2 : rowOf t i₀ out
      ≡ ((List.range U64_LIMBS).map fun i => limbWeight i * rowOf t i₀ (cLimb k i)).sum
      [ZMOD 2013265921] := by
    simpa using Int.ModEq.add_right
      (((List.range U64_LIMBS).map fun i => limbWeight i * rowOf t i₀ (cLimb k i)).sum) hgate
  exact h2.trans hs

end Reduction

/-! ### §7.4 — ⚑ THE CARRY CHAIN, and CONSERVATION over ℤ. -/

/-- **The four emitted chain gates, evaluated.** Limb 0 carries NO incoming term — `c₋₁` is an
absence in the object, not a pin. Limbs 1..3 each subtract the carry out of the limb below. -/
theorem carryChain_eval (a : Assignment) :
    evalH (carryChainHead 0) a
        = a (cV 0) - a (cO 0 0) - a (cO 1 0) + 65536 * a (cCARRY 0)
    ∧ evalH (carryChainHead 1) a
        = a (cV 1) - a (cO 0 1) - a (cO 1 1) + 65536 * a (cCARRY 1) - a (cCARRY 0)
    ∧ evalH (carryChainHead 2) a
        = a (cV 2) - a (cO 0 2) - a (cO 1 2) + 65536 * a (cCARRY 2) - a (cCARRY 1)
    ∧ evalH (carryChainHead 3) a
        = a (cV 3) - a (cO 0 3) - a (cO 1 3) + 65536 * a (cCARRY 3) - a (cCARRY 2) := by
  have h2 : ((2 : ℤ) ^ LIMB_BITS) = 65536 := by norm_num [LIMB_BITS]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show evalH (carryBody 0) a = _
    simp only [carryBody, evalH_addLin, evalH_lin, h2]; ring
  · show evalH ((carryBody 1).addLin (-1) (cCARRY 0)) a = _
    simp only [carryBody, evalH_addLin, evalH_lin, h2]; ring
  · show evalH ((carryBody 2).addLin (-1) (cCARRY 1)) a = _
    simp only [carryBody, evalH_addLin, evalH_lin, h2]; ring
  · show evalH ((carryBody 3).addLin (-1) (cCARRY 2)) a = _
    simp only [carryBody, evalH_addLin, evalH_lin, h2]; ring

/-- **The lift from residue to integer.** A gate value bounded well inside `(−p/2, p/2)` that
vanishes mod `p` vanishes over ℤ. Every chain gate is bounded by `link2_limb_canonical` and carry
booleanity, which is the entire reason this relation states conservation rather than
conservation-modulo-`p`. -/
theorem exact_of_small_modEq_zero {x : ℤ} (h : x ≡ 0 [ZMOD 2013265921])
    (hlo : -300000 < x) (hhi : x < 300000) : x = 0 := by
  obtain ⟨c, hc⟩ := Int.modEq_zero_iff_dvd.mp h
  omega

/-- **⚑ WHAT THE FINAL CARRY WOULD BUY — the floor, stated with `c₃` FREE.** The four chain gates
ALONE give

    o¹ + o² = v + 2^64 · c₃

and every one of them is satisfied by a witness with `c₃ = 1`: the limb equations balance perfectly,
because absorbing an overflow is exactly what a carry is FOR. So a limbwise chain without a terminal
pin does not state conservation — it states conservation up to a free `2^64`, which is the whole
`u64` range minted from nothing. `carryTopZero` is the gate that collapses this to
`link2_conservation`, and `overflow_carry_unsat` is its refusal. -/
theorem carry_chain_sums {a : Assignment}
    (e0 : a (cV 0) - a (cO 0 0) - a (cO 1 0) + 65536 * a (cCARRY 0) = 0)
    (e1 : a (cV 1) - a (cO 0 1) - a (cO 1 1) + 65536 * a (cCARRY 1) - a (cCARRY 0) = 0)
    (e2 : a (cV 2) - a (cO 0 2) - a (cO 1 2) + 65536 * a (cCARRY 2) - a (cCARRY 1) = 0)
    (e3 : a (cV 3) - a (cO 0 3) - a (cO 1 3) + 65536 * a (cCARRY 3) - a (cCARRY 2) = 0) :
    u64Of a 2 + u64Of a 3 = u64Of a 0 + 18446744073709551616 * a (cCARRY 3) := by
  simp only [u64Of_expand, cLimb_value, cLimb_out0, cLimb_out1]
  linear_combination (-1 : ℤ) * e0 - 65536 * e1 - 4294967296 * e2 - 281474976710656 * e3

section Conservation
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- Carries `0..2` are boolean — the emitted pins say so. -/
theorem link2_carry_boolean
    (hsat : Satisfied2 hash shieldedTransferValueLink2OutDesc minit mfin maddrs t) (i₀ : Nat)
    (hi₀ : i₀ + 1 < t.rows.length) {i : Nat} (hi : i < U64_LIMBS - 1)
    (hcan : Canon (rowOf t i₀ (cCARRY i))) :
    rowOf t i₀ (cCARRY i) = 0 ∨ rowOf t i₀ (cCARRY i) = 1 :=
  lkBin hsat i₀ hi₀ (mem_carryBin hi) hcan

/-- **The terminal carry is ZERO** — so nothing is created. -/
theorem link2_final_carry_zero
    (hsat : Satisfied2 hash shieldedTransferValueLink2OutDesc minit mfin maddrs t) (i₀ : Nat)
    (hi₀ : i₀ + 1 < t.rows.length) (hcan : Canon (rowOf t i₀ (cCARRY 3))) :
    rowOf t i₀ (cCARRY 3) = 0 := by
  have hgate := lkGate hsat i₀ hi₀ mem_carryTopZero
  have hv : evalH (Head.lin 1 (cCARRY (U64_LIMBS - 1))) (rowOf t i₀) = rowOf t i₀ (cCARRY 3) := by
    simp [evalH_lin, U64_LIMBS]
  rw [hv] at hgate
  obtain ⟨c, hc⟩ := Int.modEq_zero_iff_dvd.mp hgate
  obtain ⟨h0, h1⟩ := hcan
  omega

/-- **⚑ CONSERVATION, AS A THEOREM, OVER ℤ.** On a satisfying trace with canonical cells, the spent
note's `u64` value is EXACTLY the sum of the two minted notes' `u64` values.

Not a residue: `link2_limb_canonical` bounds every limb below `2^16` and the carry pins bound every
carry by `1`, so each chain gate's value is bounded by `2^18` — far inside `(−p/2, p/2)` — and its
mod-`p` vanishing lifts to an integer identity (`exact_of_small_modEq_zero`). The terminal carry
being zero is what removes the `2^64` term `carry_chain_sums` leaves free.

There is no output-value column the chain does not reach, and no second value the commitments could
hash instead: `cOMOD k` is pinned to `cO k`'s own limbs by `link2_mod_is_the_reduction`. So "the two
minted notes are worth more than the spent one" is not a statement a satisfying assignment can
make. -/
theorem link2_conservation
    (hsat : Satisfied2 hash shieldedTransferValueLink2OutDesc minit mfin maddrs t) (i₀ : Nat)
    (hi₀ : i₀ + 1 < t.rows.length)
    (hcanL : ∀ k i, k < 4 → i < U64_LIMBS → Canon (rowOf t i₀ (cLimb k i)))
    (hcanB : ∀ k i b, k < 4 → i < U64_LIMBS → b < LIMB_BITS → Canon (rowOf t i₀ (cBit k i b)))
    (hcanC : ∀ i, i < U64_LIMBS → Canon (rowOf t i₀ (cCARRY i))) :
    u64Of (rowOf t i₀) 0 = u64Of (rowOf t i₀) 2 + u64Of (rowOf t i₀) 3 := by
  have hL : ∀ k i, k < 4 → i < U64_LIMBS →
      0 ≤ rowOf t i₀ (cLimb k i) ∧ rowOf t i₀ (cLimb k i) < 65536 := by
    intro k i hk hi
    obtain ⟨_, h0, h1⟩ := link2_limb_canonical hsat i₀ hi₀ hk hi (hcanL k i hk hi)
      (fun b hb => hcanB k i b hk hi hb)
    exact ⟨h0, h1⟩
  have V : ∀ i, i < U64_LIMBS → 0 ≤ rowOf t i₀ (cV i) ∧ rowOf t i₀ (cV i) < 65536 := by
    intro i hi; simpa only [cLimb_value] using hL 0 i (by decide) hi
  have O0 : ∀ i, i < U64_LIMBS → 0 ≤ rowOf t i₀ (cO 0 i) ∧ rowOf t i₀ (cO 0 i) < 65536 := by
    intro i hi; simpa only [cLimb_out0] using hL 2 i (by decide) hi
  have O1 : ∀ i, i < U64_LIMBS → 0 ≤ rowOf t i₀ (cO 1 i) ∧ rowOf t i₀ (cO 1 i) < 65536 := by
    intro i hi; simpa only [cLimb_out1] using hL 3 i (by decide) hi
  have hC3 : rowOf t i₀ (cCARRY 3) = 0 :=
    link2_final_carry_zero hsat i₀ hi₀ (hcanC 3 (by decide))
  have hC : ∀ i, i < U64_LIMBS - 1 →
      0 ≤ rowOf t i₀ (cCARRY i) ∧ rowOf t i₀ (cCARRY i) ≤ 1 := by
    intro i hi
    rcases link2_carry_boolean hsat i₀ hi₀ hi (hcanC i (by omega)) with h | h <;> omega
  have hE := carryChain_eval (rowOf t i₀)
  obtain ⟨hv0, hv0'⟩ := V 0 (by decide); obtain ⟨hv1, hv1'⟩ := V 1 (by decide)
  obtain ⟨hv2, hv2'⟩ := V 2 (by decide); obtain ⟨hv3, hv3'⟩ := V 3 (by decide)
  obtain ⟨ha0, ha0'⟩ := O0 0 (by decide); obtain ⟨ha1, ha1'⟩ := O0 1 (by decide)
  obtain ⟨ha2, ha2'⟩ := O0 2 (by decide); obtain ⟨ha3, ha3'⟩ := O0 3 (by decide)
  obtain ⟨hb0, hb0'⟩ := O1 0 (by decide); obtain ⟨hb1, hb1'⟩ := O1 1 (by decide)
  obtain ⟨hb2, hb2'⟩ := O1 2 (by decide); obtain ⟨hb3, hb3'⟩ := O1 3 (by decide)
  obtain ⟨hc0, hc0'⟩ := hC 0 (by decide); obtain ⟨hc1, hc1'⟩ := hC 1 (by decide)
  obtain ⟨hc2, hc2'⟩ := hC 2 (by decide)
  have E0 : rowOf t i₀ (cV 0) - rowOf t i₀ (cO 0 0) - rowOf t i₀ (cO 1 0)
      + 65536 * rowOf t i₀ (cCARRY 0) = 0 := by
    have hm := lkGate hsat i₀ hi₀ (mem_carryChain (show (0 : Nat) < U64_LIMBS by decide))
    rw [hE.1] at hm
    exact exact_of_small_modEq_zero hm (by omega) (by omega)
  have E1 : rowOf t i₀ (cV 1) - rowOf t i₀ (cO 0 1) - rowOf t i₀ (cO 1 1)
      + 65536 * rowOf t i₀ (cCARRY 1) - rowOf t i₀ (cCARRY 0) = 0 := by
    have hm := lkGate hsat i₀ hi₀ (mem_carryChain (show (1 : Nat) < U64_LIMBS by decide))
    rw [hE.2.1] at hm
    exact exact_of_small_modEq_zero hm (by omega) (by omega)
  have E2 : rowOf t i₀ (cV 2) - rowOf t i₀ (cO 0 2) - rowOf t i₀ (cO 1 2)
      + 65536 * rowOf t i₀ (cCARRY 2) - rowOf t i₀ (cCARRY 1) = 0 := by
    have hm := lkGate hsat i₀ hi₀ (mem_carryChain (show (2 : Nat) < U64_LIMBS by decide))
    rw [hE.2.2.1] at hm
    exact exact_of_small_modEq_zero hm (by omega) (by omega)
  have E3 : rowOf t i₀ (cV 3) - rowOf t i₀ (cO 0 3) - rowOf t i₀ (cO 1 3)
      + 65536 * rowOf t i₀ (cCARRY 3) - rowOf t i₀ (cCARRY 2) = 0 := by
    have hm := lkGate hsat i₀ hi₀ (mem_carryChain (show (3 : Nat) < U64_LIMBS by decide))
    rw [hE.2.2.2] at hm
    exact exact_of_small_modEq_zero hm (by omega) (by omega)
  have hsum := carry_chain_sums E0 E1 E2 E3
  rw [hC3] at hsum
  simpa using hsum.symm

end Conservation

/-! ### §7.5 — the published objects, forced. -/

/-- The 16 chip inputs a carrier site absorbs, as VALUES. Definitionally the sidecar's `wideIns`,
because §1's layout join makes the absorb block the same term over the same columns. -/
def linkIns (a : Assignment) (domain : ℤ) : List ℤ :=
  [domain, a (cV 0), a (cV 1), a (cV 2), a (cV 3), a (cA 0), a (cA 1), a (cA 2),
   a (cA 3), a cRAND, a (cBL 0), a (cBL 1), a (cBL 2), a (cBL 3), a (cBL 4), a (cBL 5)]

theorem linkIns_eval (a : Assignment) (domain : ℤ) :
    (wideLeft domain ++ wideRight).map (·.eval a) = linkIns a domain := rfl

/-- Reading lane `j` off a carrier's output block. -/
theorem linkOut_getD (a : Assignment) (base j : Nat) (hj : j < 8) :
    ((wideOut base).map a).getD j 0 = a (base + j) := by
  interval_cases j <;> rfl

/-- The seven values minted note `k`'s commitment site absorbs. Note `cAMOD` — the SHARED asset
column — appears in both. -/
def outCmIns (a : Assignment) (k : Nat) : List ℤ :=
  [a (cOMOD k), a cAMOD, a (cOWNER k), a (cORAND k), 0, FACT_MARK, 1]

theorem outCmIns_eval (a : Assignment) (k : Nat) :
    (factIns [.var (cOMOD k), .var cAMOD, .var (cOWNER k), .var (cORAND k)]).map (·.eval a)
      = outCmIns a k := rfl

section Sites
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
variable {permOut : List ℤ → List ℤ}

/-- All EIGHT lanes of a carrier site are the genuine squeeze over THIS row's own limb cells. -/
theorem link2_wide_lanes_forced_at
    (hsat : Satisfied2 hash shieldedTransferValueLink2OutDesc minit mfin maddrs t)
    (hSound : ChipTableSoundN permOut (t.tf TableId.poseidon2)) (i : Nat) (hi : i < t.rows.length)
    {domain : ℤ} {base : Nat}
    (hm : wideSite domain base ∈ shieldedTransferValueLink2OutDesc.constraints) :
    (wideOut base).map (rowOf t i) = permOut (linkIns (rowOf t i) domain) := by
  have hh := lkLookup hsat i hi hm
  simp only [Lookup.holdsAt] at hh
  have := chip_lookup_sound_N permOut (t.tf TableId.poseidon2) hSound (rowOf t i)
    (wideLeft domain ++ wideRight) (wideOut base) (of_decide_eq_true (Eq.refl true)) hh
  rwa [linkIns_eval] at this

/-- **BOTH minted note commitments are FORCED to `hash_fact` of their own reduced value and the
SHARED asset felt.** Neither is a free cell the prover picks. -/
theorem link2_outcm_forced
    (hsat : Satisfied2 hash shieldedTransferValueLink2OutDesc minit mfin maddrs t)
    (hwire : t.tf poseidon2narrow = narrowTable (t.tf TableId.poseidon2))
    (hSound : ChipTableSound hash (t.tf TableId.poseidon2))
    (i : Nat) (hi : i < t.rows.length) {k : Nat} (hk : k < 2) :
    rowOf t i (cOUTCM k) = hash (outCmIns (rowOf t i) k) := by
  have hh := lkLookup hsat i hi (mem_outCm hk)
  have hlen : Dregg2.Circuit.DescriptorIR2.ChipArityAdmitted
      (factIns [EmittedExpr.var (cOMOD k), .var cAMOD, .var (cOWNER k),
        .var (cORAND k)]).length := by
    chip_arity_admitted
  have := narrow_lookup_holdsAt_sound hash t.tf hwire hSound (envAt t i)
    (factIns [EmittedExpr.var (cOMOD k), .var cAMOD, .var (cOWNER k), .var (cORAND k)])
    (cOUTCM k) hlen hh
  rwa [outCmIns_eval] at this

/-- **⚑ THE SPLIT VALUE LINK, AS A THEOREM.** On a satisfying trace, the sixteen published carrier
lanes and BOTH published note commitments are functions of row 0's own limb cells, and the two
minted values sum EXACTLY to the spent one.

The carrier lanes are the SPENT note's (the verifier supplies them from the complete-spend proof's
PI-pinned `wide[16]`); each `outCm_k` is `hash (outCmIns … k)` whose first entry is pinned to the
reduction of minted note `k`'s own limbs and whose second is the SHARED asset. Conservation is the
carry chain over those same limb columns. -/
theorem value_link2_reads_one_opening
    (hsat : Satisfied2 hash shieldedTransferValueLink2OutDesc minit mfin maddrs t)
    (hSound : ChipTableSoundN permOut (t.tf TableId.poseidon2))
    (hwire : t.tf poseidon2narrow = narrowTable (t.tf TableId.poseidon2))
    (hNarrow : ChipTableSound hash (t.tf TableId.poseidon2))
    (hrows : 0 < t.rows.length) (htr : 0 + 1 < t.rows.length)
    (hcanL : ∀ k i, k < 4 → i < U64_LIMBS → Canon (rowOf t 0 (cLimb k i)))
    (hcanB : ∀ k i b, k < 4 → i < U64_LIMBS → b < LIMB_BITS → Canon (rowOf t 0 (cBit k i b)))
    (hcanC : ∀ i, i < U64_LIMBS → Canon (rowOf t 0 (cCARRY i)))
    {j : Nat} (hj : j < 8) {k : Nat} (hk : k < 2) :
    (envAt t 0).pub (PI_WIDE + j)
        ≡ (permOut (linkIns (rowOf t 0) DOMAIN_A)).getD j 0 [ZMOD 2013265921]
      ∧ (envAt t 0).pub (PI_OUTCM + k) ≡ hash (outCmIns (rowOf t 0) k) [ZMOD 2013265921]
      ∧ rowOf t 0 (cOMOD k) ≡ u64Of (rowOf t 0) (k + 2) [ZMOD 2013265921]
      ∧ rowOf t 0 cAMOD ≡ u64Of (rowOf t 0) 1 [ZMOD 2013265921]
      ∧ u64Of (rowOf t 0) 0 = u64Of (rowOf t 0) 2 + u64Of (rowOf t 0) 3 := by
  refine ⟨?_, ?_, ?_, link2_mod_is_the_reduction hsat 0 htr mem_u64Recompose_asset,
    link2_conservation hsat 0 htr hcanL hcanB hcanC⟩
  · have hlanes := link2_wide_lanes_forced_at hsat hSound 0 hrows mem_wideA
    have hpin : rowOf t 0 (laneCol j) ≡ (envAt t 0).pub (PI_WIDE + j) [ZMOD 2013265921] :=
      lkPin hsat hrows (mem_pinLane (by simp only [WIDE_LANES]; omega))
    have hcol : laneCol j = cWA 0 + j := by simp only [laneCol, cWA, if_pos hj]
    have hval : rowOf t 0 (cWA 0 + j)
        = (permOut (linkIns (rowOf t 0) DOMAIN_A)).getD j 0 := by
      rw [← linkOut_getD (rowOf t 0) (cWA 0) j hj, hlanes]
    rw [hcol, hval] at hpin
    exact Int.ModEq.symm hpin
  · have hpin := lkPin hsat hrows (mem_pinOutCm hk)
    rw [link2_outcm_forced hsat hwire hNarrow 0 hrows hk] at hpin
    exact Int.ModEq.symm hpin
  · interval_cases k
    · exact link2_mod_is_the_reduction hsat 0 htr mem_u64Recompose_out0
    · exact link2_mod_is_the_reduction hsat 0 htr mem_u64Recompose_out1

end Sites

/-! ### §7.6 — THE NEGATIVE TEETH. Each is a REFUSAL of a constructible attack, not a restatement
of a positive. -/

section Negative
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- **⚑ THE INFLATING SPLIT IS UNSATISFIABLE.** A trace whose two minted notes are worth anything
other than exactly the spent note — more OR less — has no satisfying assignment. Not "is rejected
by a check": there is no such trace. -/
theorem inflating_split_unsat (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) (hne : 0 + 1 < t.rows.length)
    (hcanL : ∀ k i, k < 4 → i < U64_LIMBS → Canon (rowOf t 0 (cLimb k i)))
    (hcanB : ∀ k i b, k < 4 → i < U64_LIMBS → b < LIMB_BITS → Canon (rowOf t 0 (cBit k i b)))
    (hcanC : ∀ i, i < U64_LIMBS → Canon (rowOf t 0 (cCARRY i)))
    (hinflate : u64Of (rowOf t 0) 2 + u64Of (rowOf t 0) 3 ≠ u64Of (rowOf t 0) 0) :
    ¬ Satisfied2 hash shieldedTransferValueLink2OutDesc minit mfin maddrs t :=
  fun hsat => hinflate (link2_conservation hsat 0 hne hcanL hcanB hcanC).symm

/-- **⚑ THE `2^64` SMUGGLE IS UNSATISFIABLE.** `carry_chain_sums` shows a nonzero terminal carry
buys exactly `2^64` of minted value with every chain gate still satisfied; `carryTopZero` is what
makes that trace not exist. -/
theorem overflow_carry_unsat (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) (hne : 0 + 1 < t.rows.length)
    (hcan : Canon (rowOf t 0 (cCARRY 3))) (hnz : rowOf t 0 (cCARRY 3) ≠ 0) :
    ¬ Satisfied2 hash shieldedTransferValueLink2OutDesc minit mfin maddrs t :=
  fun hsat => hnz (link2_final_carry_zero hsat 0 hne hcan)

/-- **⚑ A NON-BOOLEAN CARRY IS UNSATISFIABLE.** The other half of the chain attack: a carry cell
holding `2`, say, would move `2·65536` across a limb boundary for free. The booleanity pins refuse
it. -/
theorem nonboolean_carry_unsat (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) (hne : 0 + 1 < t.rows.length) {i : Nat}
    (hi : i < U64_LIMBS - 1) (hcan : Canon (rowOf t 0 (cCARRY i)))
    (hbad : rowOf t 0 (cCARRY i) ≠ 0 ∧ rowOf t 0 (cCARRY i) ≠ 1) :
    ¬ Satisfied2 hash shieldedTransferValueLink2OutDesc minit mfin maddrs t := by
  intro hsat
  rcases link2_carry_boolean hsat 0 hne hi hcan with h | h
  · exact hbad.1 h
  · exact hbad.2 h

/-- **The negative tooth on an OUTPUT.** Publishing a note commitment that is not the trace's own
forced `outCm_k` cell is UNSAT — for EITHER output. -/
theorem decoupled_outcm_unsat (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) (hne : 0 < t.rows.length) {k : Nat} (hk : k < 2)
    (hforge : ¬ (rowOf t 0 (cOUTCM k) ≡ (envAt t 0).pub (PI_OUTCM + k) [ZMOD 2013265921])) :
    ¬ Satisfied2 hash shieldedTransferValueLink2OutDesc minit mfin maddrs t :=
  fun hsat => hforge (lkPin hsat hne (mem_pinOutCm hk))

/-- **The negative tooth on the CARRIER.** Publishing a lane that is not the trace's own carrier
cell is UNSAT — so the sixteen lanes the executor hands this relation from the complete-spend proof
cannot be "matched" by anything but a trace whose limbs really do squeeze to them. -/
theorem decoupled_carrier_unsat (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) (hne : 0 < t.rows.length) {lane : Nat}
    (hl : lane < WIDE_LANES)
    (hforge : ¬ (rowOf t 0 (laneCol lane) ≡ (envAt t 0).pub (PI_WIDE + lane)
      [ZMOD 2013265921])) :
    ¬ Satisfied2 hash shieldedTransferValueLink2OutDesc minit mfin maddrs t :=
  fun hsat => hforge (lkPin hsat hne (mem_pinLane hl))

end Negative

/-! ## §8 — axiom hygiene. -/

#assert_axioms layout_agrees_with_sidecar
#assert_axioms new_columns_above_the_sidecar
#assert_axioms carrier_absorb_is_the_sidecar_absorb
#assert_axioms constraint_census
#assert_axioms gate_census
#assert_axioms pi_census
#assert_axioms wide_site_census
#assert_axioms narrow_site_census
#assert_axioms reduction_gates_are_exactly_the_consumed_ones
#assert_axioms cBit_injective
#assert_axioms cBit_in_range
#assert_axioms carry_columns_distinct_and_in_range
#assert_axioms sites_emitted
#assert_axioms link2_limb_canonical
#assert_axioms link2_mod_is_the_reduction
#assert_axioms carryChain_eval
#assert_axioms carry_chain_sums
#assert_axioms link2_carry_boolean
#assert_axioms link2_final_carry_zero
#assert_axioms link2_conservation
#assert_axioms link2_outcm_forced
#assert_axioms value_link2_reads_one_opening
#assert_axioms inflating_split_unsat
#assert_axioms overflow_carry_unsat
#assert_axioms nonboolean_carry_unsat
#assert_axioms decoupled_outcm_unsat
#assert_axioms decoupled_carrier_unsat
#assert_compiled link2_emits_golden

end Dregg2.Circuit.Emit.ShieldedTransferValueLink2OutEmit
