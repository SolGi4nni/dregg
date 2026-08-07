/-
# Dregg2.Circuit.Emit.ShieldedTransferValueLinkEmit — the shielded transfer's VALUE LINK, in the AIR.

## SAY THE SUBSTRATE OUT LOUD

This is **Lean-authored AIR**. The constraint list below IS the emitted object; Rust's only job is
to decode it (`parse_vm_descriptor2`), fill a witness trace and prove/verify it. Rust authors no
constraint here.

## The wound this closes (residual after seam #15)

`turn-prover/src/shielded_transfer_verifier.rs` carried a NAMED RESIDUAL, verbatim:

> the Pedersen leg's own `v` is bound to the STARK-side `v` only through this TRANSCRIPT, not by an
> equality the circuit enforces … The wide join makes both proofs open the SAME `(value, asset)` as
> each other; it does not make either of them open the value the Ristretto commitment holds.

That was exact. A spender who genuinely owned a note worth `1` published input/output Ristretto legs
committing to `1_000_000`, and `verify_full_conservation_bytes` cleared `Σ C_in = Σ C_out` over
those PROVER-CHOSEN legs. The complete-spend STARK proved membership + nullifier + a `u64` carrier
for the REAL note; nothing compared the two. The value the transfer moved was decided by the leg.

**It cannot be closed by adding a check between the two systems.** A BabyBear STARK cannot open a
Ristretto point without non-native curve arithmetic in-AIR, and a Ristretto sigma protocol cannot
open a Poseidon2 image without the hash in-group. `cell-crypto/src/value_link_zk.rs` says so in its
own module docs and names the way out:

> The production PQ direction instead removes this curve bridge: faithfully encode value/asset in a
> wide in-AIR hash commitment and enforce no-mint in AIR.

That is what this file does. There is no Pedersen leg any more, so there is nothing left to
decouple: the value a transfer moves is read off ONE set of limb columns.

## What `shieldedTransferValueLinkDesc` IS

One row, over a private witness
`(value : u64, asset : u64, inRand : felt, inBlind : felt^6, outOwner : felt, outRand : felt)`:

    (R1) every one of the 2 × 4 × 16 bit cells is BOOLEAN
    (R2) limb_{k,i} = Σ_{b<16} 2^b · bit_{k,i,b}
    (R3) value_mod_p = Σ_{i<4} (2^{16i} mod p)·value_limb_i ;  asset_mod_p likewise
    (R4) inWideA[0..8] = cap_node8([DOMAIN_A, v0..v3, a0,a1,a2], [a3, inRand, inBlind0..5])
    (R5) inWideB[0..8] = the SAME node8 at DOMAIN_B
    (R6) outCm = hash_fact(value_mod_p, [asset_mod_p, outOwner, outRand])
    (R7) row 0 publishes `[inWideA[0..8], inWideB[0..8], outCm]` — 17 public inputs

**THE LINK IS (R4)/(R5) AND (R6) READING THE SAME `cV`/`cA` COLUMNS.** The sixteen published
carrier lanes are the carrier of the note the transfer SPENDS — the verifier supplies them from the
complete-spend proof's own PI-pinned `wide[16]`, so they are not this prover's claim. The published
`outCm` is the note commitment the executor APPENDS to the shielded accumulator, and it is
`hash_fact` of the very same recomposed value/asset felts. There is no second value column, so a
trace in which the minted note is worth more than the spent one does not exist — not "is rejected",
does not exist (`inflating_output_unsat`).

## Column-for-column with the objects it joins

`wideLeft`/`wideRight` are IMPORTED from `WideValueBindingEmit`, not re-typed: columns 0..16 of this
relation ARE that relation's columns 0..16 (`layout_agrees_with_sidecar`), which are in turn the
`carrierIns` shape the complete spend PI-pins (`ShieldedSpendCompleteEmit.spendWideIns_is_carrierIns`).
So "the carrier this relation publishes" and "the carrier the spend publishes" are the same function
of the same opening, and the Rust join is a felt-for-felt equality on 16 lanes.

`outCm`'s preimage is the deployed note commitment `hash_fact(vmod, [amod, owner, rand])` —
`ShieldedSpendCompleteEmit`'s `lkCM` and `dregg-shielded-shield::v1`'s mint, same site. So the note
this relation creates is SPENDABLE by exactly the complete-spend relation, which is what makes the
conservation claim mean anything: the value that leaves is the value that arrives, in the same
domain, openable by the same circuit.

## Deployed arity, and what is REFUSED

One input, one output, equal value. That is a whole-note transfer (a change of owner), and it is the
arity the Rust route admits; anything else REFUSES (`turn-prover/src/shielded_transfer_verifier.rs`).
Splitting — `1-in / 2-out` with change — needs the limbwise carry chain
`v_in_i = o1_i + o2_i − 65536·c_i + c_{i−1}` with `c_i` boolean and `c_3 = 0`, and is the next
descriptor in this family. It is NOT a "later phase" for the value link: the link is closed here at
the arity the executor accepts, and widening the arity cannot reopen it, because every arity in the
family reads its values off the same limb columns its carriers absorb.

## What is NOT in this file

The range proof is gone and is not missed: `value` rides four 16-bit limb cells whose booleanity is
FORCED (R1/R2), so `0 ≤ value < 2^64` is a theorem of the trace (`link_value_in_u64`), not a
Bulletproof. The negative-value inflation hole the Bulletproofs guarded existed only because the
Pedersen group has no notion of range.

## Axiom hygiene

Definitional descriptor, named theorems (no `#guard`), the wire golden pinned by `native_decide` +
`#assert_compiled`. NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.WideValueBindingRefine

namespace Dregg2.Circuit.Emit.ShieldedTransferValueLinkEmit

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
set_option maxRecDepth 40000

/-! ## §1 — the column layout.

Columns `0..16` are `WideValueBindingEmit`'s columns `0..16`, index for index, so the imported
`wideLeft`/`wideRight` absorb blocks denote THIS relation's cells (`layout_agrees_with_sidecar`).
The output note's own witness (`cOWNER`, `cORAND`) and its commitment sit above them. -/

/-- Value limb `i` of the SPENT note — and, because there is no second value, of the MINTED one.
Little-endian: `value = Σ 2^{16i}·v_i`. -/
def cV (i : Nat) : Nat := i
/-- Asset limb `i` (shared for the same reason). -/
def cA (i : Nat) : Nat := U64_LIMBS + i
/-- Limb `i` of kind `k` (`0 = value`, `1 = asset`). -/
def cLimb (k i : Nat) : Nat := if k = 0 then cV i else cA i
/-- `value mod p` — the felt the note commitment hashes. -/
def cVMOD : Nat := 2 * U64_LIMBS
/-- `asset mod p`. -/
def cAMOD : Nat := cVMOD + 1
/-- The SPENT note's randomness (absorbed by the carrier the spend proof published). -/
def cRAND : Nat := cVMOD + 2
/-- The SPENT note's carrier blind lane `i`. -/
def cBL (i : Nat) : Nat := cVMOD + 3 + i
/-- The MINTED note's owner felt (`hash_fact(key0,[key1,key2,key3])` of the recipient). Free
witness: it is the sender's choice of payee, and it is the only thing about the output the sender
gets to choose. -/
def cOWNER : Nat := cVMOD + 3 + BLIND_LANES
/-- The MINTED note's randomness. Free witness — it is what makes the published `outCm` hiding. -/
def cORAND : Nat := cOWNER + 1
/-- Lane `j` of the SPENT note's `DOMAIN_A` carrier. -/
def cWA (j : Nat) : Nat := cORAND + 1 + j
/-- Lane `j` of the SPENT note's `DOMAIN_B` carrier. -/
def cWB (j : Nat) : Nat := cORAND + 9 + j
/-- The MINTED note's commitment `hash_fact(cVMOD,[cAMOD,cOWNER,cORAND])` — the 32-byte leaf the
executor appends to `note_shielded`, and a leaf the complete-spend relation can open. -/
def cOUTCM : Nat := cORAND + 17
/-- Base of the bit-decomposition block. -/
def BITS_BASE : Nat := cOUTCM + 1
/-- Bit `b` of limb `i` of kind `k`. -/
def cBit (k i b : Nat) : Nat := BITS_BASE + (k * U64_LIMBS + i) * LIMB_BITS + b
/-- **The main-trace width.** -/
def LINK_WIDTH : Nat := BITS_BASE + 2 * U64_LIMBS * LIMB_BITS

theorem cVMOD_eq : cVMOD = 8 := rfl
theorem cAMOD_eq : cAMOD = 9 := rfl
theorem cRAND_eq : cRAND = 10 := rfl
theorem cBL_lo : cBL 0 = 11 := rfl
theorem cBL_hi : cBL 5 = 16 := rfl
theorem cOWNER_eq : cOWNER = 17 := rfl
theorem cORAND_eq : cORAND = 18 := rfl
theorem cWA_eq : cWA 0 = 19 := rfl
theorem cWB_eq : cWB 0 = 27 := rfl
theorem cOUTCM_eq : cOUTCM = 35 := rfl
theorem BITS_BASE_eq : BITS_BASE = 36 := rfl
theorem LINK_WIDTH_eq : LINK_WIDTH = 164 := rfl

/-- **THE LAYOUT JOIN, as a fact rather than a comment.** Columns `0..16` are the sidecar's columns
`0..16`, index for index — which is why importing `wideLeft`/`wideRight` (defined over THOSE column
functions) emits absorb blocks over THESE cells, and why the sixteen lanes this relation publishes
are comparable felt-for-felt with the ones the complete spend PI-pins. Move a column here and this
theorem, not a downstream test, is what goes red. -/
theorem layout_agrees_with_sidecar :
    (∀ i, cV i = Dregg2.Circuit.Emit.WideValueBindingEmit.cV i)
    ∧ (∀ i, cA i = Dregg2.Circuit.Emit.WideValueBindingEmit.cA i)
    ∧ cVMOD = Dregg2.Circuit.Emit.WideValueBindingEmit.cVMOD
    ∧ cAMOD = Dregg2.Circuit.Emit.WideValueBindingEmit.cAMOD
    ∧ cRAND = Dregg2.Circuit.Emit.WideValueBindingEmit.cRAND
    ∧ (∀ i, cBL i = Dregg2.Circuit.Emit.WideValueBindingEmit.cBL i) :=
  ⟨fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, fun _ => rfl⟩

/-! ## §2 — the public-input layout.

`[inWideA[0..8], inWideB[0..8], outCm]`. The sixteen carrier lanes are NOT this prover's claim: the
verifier supplies them from the complete-spend proof's own `wide[16]` public inputs, which that
proof's `carrierPins` force to the spent note's opening. `outCm` is the leaf the executor appends. -/

/-- PI 0 — the first lane of the spent note's carrier. -/
def PI_WIDE : Nat := 0
/-- PI 16 — the minted note's commitment. -/
def PI_OUTCM : Nat := WIDE_LANES
/-- Total public inputs. -/
def LINK_PI_COUNT : Nat := WIDE_LANES + 1

theorem PI_OUTCM_eq : PI_OUTCM = 16 := rfl
theorem LINK_PI_COUNT_eq : LINK_PI_COUNT = 17 := rfl

/-! ## §3 — the gates. -/

/-- R2 — `limb_{k,i} − Σ_{b<16} 2^b·bit_{k,i,b}`. -/
def limbRecomposeHead (k i : Nat) : Head :=
  (List.range LIMB_BITS).foldl (fun h b => h.addLin (-(2 ^ b : ℤ)) (cBit k i b))
    (Head.lin 1 (cLimb k i))

/-- R1+R2 for one limb: its sixteen boolean pins, then its recomposition. -/
def limbGates (k i : Nat) : List VmConstraint2 :=
  ((List.range LIMB_BITS).map fun b => binGate (cBit k i b))
  ++ [cgH (limbRecomposeHead k i)]

/-- R3 — `out − Σ_{i<4} (2^{16i} mod p)·limb_{k,i}`: the felt the note commitment hashes is DERIVED
from the full limbs, never independent of them. -/
def u64RecomposeHead (k out : Nat) : Head :=
  (List.range U64_LIMBS).foldl (fun h i => h.addLin (-(limbWeight i)) (cLimb k i))
    (Head.lin 1 out)

/-- One domain-separated wide carrier site over the SPENT note's opening. The absorb block is the
imported `wideLeft ++ wideRight` — the sidecar's, the complete spend's `carrierIns`. -/
def wideSite (domain : ℤ) (base : Nat) : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2, chipLookupTupleN (wideLeft domain ++ wideRight) (wideOut base)⟩

/-- R6 — `outCm = hash_fact(value_mod_p, [asset_mod_p, outOwner, outRand])`: the deployed note
commitment, over the SAME recomposed value/asset felts the carriers above absorb the limbs of. This
single shared reading is the value link. -/
def outCmSite : VmConstraint2 :=
  .lookup ⟨poseidon2narrow,
    chipLookupTupleNarrow (factIns [.var cVMOD, .var cAMOD, .var cOWNER, .var cORAND]) cOUTCM⟩

/-- The published lane `lane`'s column. -/
def laneCol (lane : Nat) : Nat := if lane < 8 then cWA lane else cWB (lane - 8)

/-- The 17 first-row PI bindings. -/
def piPins : List VmConstraint2 :=
  ((List.range WIDE_LANES).map fun lane => pinPi (laneCol lane) (PI_WIDE + lane))
  ++ [pinPi cOUTCM PI_OUTCM]

/-! ## §4 — THE DESCRIPTOR. -/

/-- The full constraint list: the per-limb boolean+recompose blocks (value then asset), the two
compatibility reductions, the two carrier sites, the output note-commitment site, the pins. -/
def shieldedTransferValueLinkConstraints : List VmConstraint2 :=
  ((List.range 2).flatMap fun k => (List.range U64_LIMBS).flatMap fun i => limbGates k i)
  ++ [cgH (u64RecomposeHead 0 cVMOD), cgH (u64RecomposeHead 1 cAMOD)]
  ++ [wideSite DOMAIN_A (cWA 0), wideSite DOMAIN_B (cWB 0)]
  ++ [outCmSite]
  ++ piPins

/-- **`shieldedTransferValueLinkDesc`** — the Lean-authored value-link AIR. Chip tables are
Presence-detected from the lookups, and the limb range check is an explicit bit decomposition, so
`tables` and `ranges` are both empty. -/
def shieldedTransferValueLinkDesc : EffectVmDescriptor2 :=
  { name        := "dregg-shielded-transfer-value-link::v1"
  , traceWidth  := LINK_WIDTH
  , piCount     := LINK_PI_COUNT
  , tables      := []
  , constraints := shieldedTransferValueLinkConstraints
  , hashSites   := []
  , ranges      := [] }

/-! ## §5 — the census, as named theorems (`#guard` is a unit test in Lean clothes). -/

/-- 128 boolean pins + 8 limb recompositions + 2 reductions + 2 carriers + 1 fact site + 17 pins. -/
theorem constraint_census : shieldedTransferValueLinkDesc.constraints.length = 158 := by decide

/-- The algebraic gates: the 128 booleanity pins, the 8 limb recompositions, the 2 reductions. -/
theorem gate_census :
    (shieldedTransferValueLinkDesc.constraints.filter
      (fun c => match c with | .base (.gate _) => true | _ => false)).length
      = 2 * U64_LIMBS * LIMB_BITS + 2 * U64_LIMBS + 2 := by decide

/-- Every public input is pinned, and nothing else is. -/
theorem pi_census :
    (shieldedTransferValueLinkDesc.constraints.filter
      (fun c => match c with | .base (.piBinding _ _ _) => true | _ => false)).length
      = LINK_PI_COUNT := by decide

/-- Exactly two WIDE (arity-16, eight-lane) carrier sites — the sidecar's two, at the sidecar's two
domains. A third would be a second opening to decouple. -/
theorem wide_site_census :
    (shieldedTransferValueLinkDesc.constraints.filterMap
      (fun c => match c with
        | .lookup l => if l.table == TableId.poseidon2 then some l.tuple.length else none
        | _ => none)) = [25, 25] := by decide

/-- Exactly ONE narrow site: the output note commitment. There is no second hash the output could
be tied to instead. -/
theorem narrow_site_census :
    (shieldedTransferValueLinkDesc.constraints.filterMap
      (fun c => match c with
        | .lookup l => if l.table == poseidon2narrow then some l.tuple.length else none
        | _ => none)) = [18] := by decide

/-- The 128 boolean cells are 128 DISTINCT in-range columns — the felt-width repair, present. -/
theorem bit_columns_distinct_and_in_range :
    (((List.range 2).flatMap fun k => (List.range U64_LIMBS).flatMap fun i =>
        (List.range LIMB_BITS).map fun b => cBit k i b).dedup).length = 128
    ∧ ((List.range 2).flatMap fun k => (List.range U64_LIMBS).flatMap fun i =>
        (List.range LIMB_BITS).map fun b => cBit k i b).all (fun c => c < LINK_WIDTH) = true := by
  decide

/-- **The absorb block this relation publishes is the sidecar's, expression for expression.** Not
"the same shape" — the same term, because `wideLeft`/`wideRight` are imported. This is what makes
the Rust join a felt equality rather than a re-derivation. -/
theorem carrier_absorb_is_the_sidecar_absorb (domain : ℤ) :
    wideLeft domain ++ wideRight
      = Dregg2.Circuit.Emit.WideValueBindingEmit.wideLeft domain
        ++ Dregg2.Circuit.Emit.WideValueBindingEmit.wideRight := rfl

/-- The two carrier sites and the output site are all present in the emitted list. -/
theorem sites_emitted :
    wideSite DOMAIN_A (cWA 0) ∈ shieldedTransferValueLinkDesc.constraints
    ∧ wideSite DOMAIN_B (cWB 0) ∈ shieldedTransferValueLinkDesc.constraints
    ∧ outCmSite ∈ shieldedTransferValueLinkDesc.constraints := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [shieldedTransferValueLinkDesc,
    shieldedTransferValueLinkConstraints]

/-! ## §6 — THE BYTE-PIN. Rust reads THIS raw string (`include_str!` + split +
`parse_vm_descriptor2`), so the Lean emission is the only copy that exists. -/

/-- **`SHIELDED_TRANSFER_VALUE_LINK_GOLDEN`** — the byte-pinned wire string. -/
def SHIELDED_TRANSFER_VALUE_LINK_GOLDEN : String := r#"{"name":"dregg-shielded-transfer-value-link::v1","ir":2,"trace_width":164,"public_input_count":17,"challenges":0,"tables":[],"constraints":[{"t":"gate","body":{"t":"mul","l":{"t":"var","v":36},"r":{"t":"add","l":{"t":"var","v":36},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"add","l":{"t":"var","v":37},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":38},"r":{"t":"add","l":{"t":"var","v":38},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":39},"r":{"t":"add","l":{"t":"var","v":39},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":40},"r":{"t":"add","l":{"t":"var","v":40},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":41},"r":{"t":"add","l":{"t":"var","v":41},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":42},"r":{"t":"add","l":{"t":"var","v":42},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":43},"r":{"t":"add","l":{"t":"var","v":43},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":44},"r":{"t":"add","l":{"t":"var","v":44},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":45},"r":{"t":"add","l":{"t":"var","v":45},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":46},"r":{"t":"add","l":{"t":"var","v":46},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":47},"r":{"t":"add","l":{"t":"var","v":47},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":48},"r":{"t":"add","l":{"t":"var","v":48},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":49},"r":{"t":"add","l":{"t":"var","v":49},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":50},"r":{"t":"add","l":{"t":"var","v":50},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":51},"r":{"t":"add","l":{"t":"var","v":51},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":0}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":36}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":37}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":38}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":39}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":40}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":41}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":42}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":43}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":44}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":45}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":46}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":47}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":48}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":49}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":50}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":51}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":52},"r":{"t":"add","l":{"t":"var","v":52},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":53},"r":{"t":"add","l":{"t":"var","v":53},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":54},"r":{"t":"add","l":{"t":"var","v":54},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":55},"r":{"t":"add","l":{"t":"var","v":55},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":56},"r":{"t":"add","l":{"t":"var","v":56},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":57},"r":{"t":"add","l":{"t":"var","v":57},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":58},"r":{"t":"add","l":{"t":"var","v":58},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":59},"r":{"t":"add","l":{"t":"var","v":59},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":60},"r":{"t":"add","l":{"t":"var","v":60},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":61},"r":{"t":"add","l":{"t":"var","v":61},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":62},"r":{"t":"add","l":{"t":"var","v":62},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":63},"r":{"t":"add","l":{"t":"var","v":63},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":64},"r":{"t":"add","l":{"t":"var","v":64},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":65},"r":{"t":"add","l":{"t":"var","v":65},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":66},"r":{"t":"add","l":{"t":"var","v":66},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":67},"r":{"t":"add","l":{"t":"var","v":67},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":1}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":52}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":53}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":54}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":55}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":56}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":57}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":58}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":59}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":60}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":61}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":62}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":63}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":64}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":65}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":66}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":67}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":68},"r":{"t":"add","l":{"t":"var","v":68},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":69},"r":{"t":"add","l":{"t":"var","v":69},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":70},"r":{"t":"add","l":{"t":"var","v":70},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":71},"r":{"t":"add","l":{"t":"var","v":71},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":72},"r":{"t":"add","l":{"t":"var","v":72},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":73},"r":{"t":"add","l":{"t":"var","v":73},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":74},"r":{"t":"add","l":{"t":"var","v":74},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":75},"r":{"t":"add","l":{"t":"var","v":75},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":76},"r":{"t":"add","l":{"t":"var","v":76},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":77},"r":{"t":"add","l":{"t":"var","v":77},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":78},"r":{"t":"add","l":{"t":"var","v":78},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":79},"r":{"t":"add","l":{"t":"var","v":79},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":80},"r":{"t":"add","l":{"t":"var","v":80},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":81},"r":{"t":"add","l":{"t":"var","v":81},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":82},"r":{"t":"add","l":{"t":"var","v":82},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":83},"r":{"t":"add","l":{"t":"var","v":83},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":2}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":68}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":69}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":70}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":71}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":72}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":73}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":74}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":75}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":76}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":77}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":78}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":79}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":80}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":81}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":82}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":83}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":84},"r":{"t":"add","l":{"t":"var","v":84},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":85},"r":{"t":"add","l":{"t":"var","v":85},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":86},"r":{"t":"add","l":{"t":"var","v":86},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":87},"r":{"t":"add","l":{"t":"var","v":87},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":88},"r":{"t":"add","l":{"t":"var","v":88},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":89},"r":{"t":"add","l":{"t":"var","v":89},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":90},"r":{"t":"add","l":{"t":"var","v":90},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":91},"r":{"t":"add","l":{"t":"var","v":91},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":92},"r":{"t":"add","l":{"t":"var","v":92},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":93},"r":{"t":"add","l":{"t":"var","v":93},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":94},"r":{"t":"add","l":{"t":"var","v":94},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":95},"r":{"t":"add","l":{"t":"var","v":95},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":96},"r":{"t":"add","l":{"t":"var","v":96},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":97},"r":{"t":"add","l":{"t":"var","v":97},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":98},"r":{"t":"add","l":{"t":"var","v":98},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":99},"r":{"t":"add","l":{"t":"var","v":99},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":3}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":84}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":85}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":86}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":87}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":88}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":89}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":90}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":91}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":92}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":93}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":94}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":95}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":96}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":97}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":98}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":99}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":100},"r":{"t":"add","l":{"t":"var","v":100},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":101},"r":{"t":"add","l":{"t":"var","v":101},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":102},"r":{"t":"add","l":{"t":"var","v":102},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":103},"r":{"t":"add","l":{"t":"var","v":103},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":104},"r":{"t":"add","l":{"t":"var","v":104},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":105},"r":{"t":"add","l":{"t":"var","v":105},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":106},"r":{"t":"add","l":{"t":"var","v":106},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":107},"r":{"t":"add","l":{"t":"var","v":107},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":108},"r":{"t":"add","l":{"t":"var","v":108},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":109},"r":{"t":"add","l":{"t":"var","v":109},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":110},"r":{"t":"add","l":{"t":"var","v":110},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":111},"r":{"t":"add","l":{"t":"var","v":111},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":112},"r":{"t":"add","l":{"t":"var","v":112},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":113},"r":{"t":"add","l":{"t":"var","v":113},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":114},"r":{"t":"add","l":{"t":"var","v":114},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":115},"r":{"t":"add","l":{"t":"var","v":115},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":4}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":100}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":101}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":102}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":103}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":104}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":105}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":106}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":107}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":108}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":109}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":110}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":111}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":112}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":113}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":114}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":115}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":116},"r":{"t":"add","l":{"t":"var","v":116},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":117},"r":{"t":"add","l":{"t":"var","v":117},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":118},"r":{"t":"add","l":{"t":"var","v":118},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":119},"r":{"t":"add","l":{"t":"var","v":119},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":120},"r":{"t":"add","l":{"t":"var","v":120},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":121},"r":{"t":"add","l":{"t":"var","v":121},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":122},"r":{"t":"add","l":{"t":"var","v":122},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":123},"r":{"t":"add","l":{"t":"var","v":123},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":124},"r":{"t":"add","l":{"t":"var","v":124},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":125},"r":{"t":"add","l":{"t":"var","v":125},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":126},"r":{"t":"add","l":{"t":"var","v":126},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":127},"r":{"t":"add","l":{"t":"var","v":127},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":128},"r":{"t":"add","l":{"t":"var","v":128},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":129},"r":{"t":"add","l":{"t":"var","v":129},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":130},"r":{"t":"add","l":{"t":"var","v":130},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":131},"r":{"t":"add","l":{"t":"var","v":131},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":5}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":116}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":117}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":118}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":119}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":120}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":121}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":122}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":123}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":124}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":125}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":126}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":127}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":128}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":129}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":130}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":131}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":132},"r":{"t":"add","l":{"t":"var","v":132},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":133},"r":{"t":"add","l":{"t":"var","v":133},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":134},"r":{"t":"add","l":{"t":"var","v":134},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":135},"r":{"t":"add","l":{"t":"var","v":135},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":136},"r":{"t":"add","l":{"t":"var","v":136},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":137},"r":{"t":"add","l":{"t":"var","v":137},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":138},"r":{"t":"add","l":{"t":"var","v":138},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":139},"r":{"t":"add","l":{"t":"var","v":139},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":140},"r":{"t":"add","l":{"t":"var","v":140},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":141},"r":{"t":"add","l":{"t":"var","v":141},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":142},"r":{"t":"add","l":{"t":"var","v":142},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":143},"r":{"t":"add","l":{"t":"var","v":143},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":144},"r":{"t":"add","l":{"t":"var","v":144},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":145},"r":{"t":"add","l":{"t":"var","v":145},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":146},"r":{"t":"add","l":{"t":"var","v":146},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":147},"r":{"t":"add","l":{"t":"var","v":147},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":6}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":132}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":133}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":134}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":135}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":136}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":137}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":138}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":139}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":140}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":141}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":142}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":143}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":144}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":145}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":146}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":147}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":148},"r":{"t":"add","l":{"t":"var","v":148},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":149},"r":{"t":"add","l":{"t":"var","v":149},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":150},"r":{"t":"add","l":{"t":"var","v":150},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":151},"r":{"t":"add","l":{"t":"var","v":151},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":152},"r":{"t":"add","l":{"t":"var","v":152},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":153},"r":{"t":"add","l":{"t":"var","v":153},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":154},"r":{"t":"add","l":{"t":"var","v":154},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":155},"r":{"t":"add","l":{"t":"var","v":155},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":156},"r":{"t":"add","l":{"t":"var","v":156},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":157},"r":{"t":"add","l":{"t":"var","v":157},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":158},"r":{"t":"add","l":{"t":"var","v":158},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":159},"r":{"t":"add","l":{"t":"var","v":159},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":160},"r":{"t":"add","l":{"t":"var","v":160},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":161},"r":{"t":"add","l":{"t":"var","v":161},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":162},"r":{"t":"add","l":{"t":"var","v":162},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":163},"r":{"t":"add","l":{"t":"var","v":163},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":7}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":148}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":149}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":150}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":151}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":152}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":153}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":154}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":155}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":156}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":157}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":158}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":159}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":160}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":161}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":162}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":163}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":8}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":0}}},"r":{"t":"mul","l":{"t":"const","v":-65536},"r":{"t":"var","v":1}}},"r":{"t":"mul","l":{"t":"const","v":-268435454},"r":{"t":"var","v":2}}},"r":{"t":"mul","l":{"t":"const","v":-268295646},"r":{"t":"var","v":3}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":9}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":4}}},"r":{"t":"mul","l":{"t":"const","v":-65536},"r":{"t":"var","v":5}}},"r":{"t":"mul","l":{"t":"const","v":-268435454},"r":{"t":"var","v":6}}},"r":{"t":"mul","l":{"t":"const","v":-268295646},"r":{"t":"var","v":7}}}},{"t":"lookup","table":1,"tuple":[{"t":"const","v":16},{"t":"const","v":1447185968},{"t":"var","v":0},{"t":"var","v":1},{"t":"var","v":2},{"t":"var","v":3},{"t":"var","v":4},{"t":"var","v":5},{"t":"var","v":6},{"t":"var","v":7},{"t":"var","v":10},{"t":"var","v":11},{"t":"var","v":12},{"t":"var","v":13},{"t":"var","v":14},{"t":"var","v":15},{"t":"var","v":16},{"t":"var","v":19},{"t":"var","v":20},{"t":"var","v":21},{"t":"var","v":22},{"t":"var","v":23},{"t":"var","v":24},{"t":"var","v":25},{"t":"var","v":26}]},{"t":"lookup","table":1,"tuple":[{"t":"const","v":16},{"t":"const","v":1447185969},{"t":"var","v":0},{"t":"var","v":1},{"t":"var","v":2},{"t":"var","v":3},{"t":"var","v":4},{"t":"var","v":5},{"t":"var","v":6},{"t":"var","v":7},{"t":"var","v":10},{"t":"var","v":11},{"t":"var","v":12},{"t":"var","v":13},{"t":"var","v":14},{"t":"var","v":15},{"t":"var","v":16},{"t":"var","v":27},{"t":"var","v":28},{"t":"var","v":29},{"t":"var","v":30},{"t":"var","v":31},{"t":"var","v":32},{"t":"var","v":33},{"t":"var","v":34}]},{"t":"lookup","table":8,"tuple":[{"t":"const","v":7},{"t":"var","v":8},{"t":"var","v":9},{"t":"var","v":17},{"t":"var","v":18},{"t":"const","v":0},{"t":"const","v":64207},{"t":"const","v":1},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":35}]},{"t":"pi_binding","row":"first","col":19,"pi_index":0},{"t":"pi_binding","row":"first","col":20,"pi_index":1},{"t":"pi_binding","row":"first","col":21,"pi_index":2},{"t":"pi_binding","row":"first","col":22,"pi_index":3},{"t":"pi_binding","row":"first","col":23,"pi_index":4},{"t":"pi_binding","row":"first","col":24,"pi_index":5},{"t":"pi_binding","row":"first","col":25,"pi_index":6},{"t":"pi_binding","row":"first","col":26,"pi_index":7},{"t":"pi_binding","row":"first","col":27,"pi_index":8},{"t":"pi_binding","row":"first","col":28,"pi_index":9},{"t":"pi_binding","row":"first","col":29,"pi_index":10},{"t":"pi_binding","row":"first","col":30,"pi_index":11},{"t":"pi_binding","row":"first","col":31,"pi_index":12},{"t":"pi_binding","row":"first","col":32,"pi_index":13},{"t":"pi_binding","row":"first","col":33,"pi_index":14},{"t":"pi_binding","row":"first","col":34,"pi_index":15},{"t":"pi_binding","row":"first","col":35,"pi_index":16}],"hash_sites":[],"ranges":[]}"#

/-- The emitted wire bytes ARE the pinned golden. Compiled-string equality, with the compiler
trust said out loud (`#assert_compiled` below) rather than hidden inside a `#guard`. -/
theorem link_emits_golden :
    emitVmJson2 shieldedTransferValueLinkDesc = SHIELDED_TRANSFER_VALUE_LINK_GOLDEN := by
  native_decide


/-! ## §7 — THE REFINEMENT: what a SATISFYING trace is forced to say.

Everything above is about the emitted OBJECT. This section is about its MEANING, over the actual
emitted constraint list — the SAT ⟹ SEM direction, mirroring `WideValueBindingRefine` for the
relation this file emits. The apparatus is deliberately the sidecar's, because §1's layout join
makes the two relations share their absorb block; only the output site is new. -/

section Refine
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
variable {permOut : List ℤ → List ℤ}

/-- The row assignment at index `i`. -/
def rowOf (t : VmTrace) (i : Nat) : Assignment := (envAt t i).loc

/-- Any emitted `Head` gate vanishes mod `p` on a transition row. -/
theorem lkGate (hsat : Satisfied2 hash shieldedTransferValueLinkDesc minit mfin maddrs t) (i : Nat)
    (hi : i + 1 < t.rows.length) {h : Head}
    (hm : cgH h ∈ shieldedTransferValueLinkDesc.constraints) :
    evalH h (rowOf t i) ≡ 0 [ZMOD 2013265921] := by
  have hrc := hsat.rowConstraints i (by omega) _ hm
  have hlf : (i + 1 == t.rows.length) = false := by
    have hne : i + 1 ≠ t.rows.length := by omega
    simpa using hne
  have hb : (headToExpr h).eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
    simpa only [cgH, cg, VmConstraint2.holdsAt, VmConstraint.holdsVm, hlf] using hrc
  rwa [headToExpr_eval] at hb

/-- The booleanity form. -/
theorem lkBin (hsat : Satisfied2 hash shieldedTransferValueLinkDesc minit mfin maddrs t) (i : Nat)
    (hi : i + 1 < t.rows.length) {c : Nat}
    (hm : binGate c ∈ shieldedTransferValueLinkDesc.constraints) (hcan : Canon (rowOf t i c)) :
    rowOf t i c = 0 ∨ rowOf t i c = 1 := by
  have hrc := hsat.rowConstraints i (by omega) _ hm
  have hlf : (i + 1 == t.rows.length) = false := by
    have hne : i + 1 ≠ t.rows.length := by omega
    simpa using hne
  have hb : (gBin c).eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
    simpa only [binGate, cg, VmConstraint2.holdsAt, VmConstraint.holdsVm, hlf] using hrc
  exact bin_of_gate hb hcan

/-- A lookup HOLDS on any row of a satisfying trace. -/
theorem lkLookup (hsat : Satisfied2 hash shieldedTransferValueLinkDesc minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) {l : Lookup}
    (hm : VmConstraint2.lookup l ∈ shieldedTransferValueLinkDesc.constraints) :
    l.holdsAt t.tf (envAt t i) := hsat.rowConstraints i hi _ hm

/-- A first-row PI binding forces the column to its public input. -/
theorem lkPin (hsat : Satisfied2 hash shieldedTransferValueLinkDesc minit mfin maddrs t)
    (hne : 0 < t.rows.length) {c k : Nat}
    (hm : pinPi c k ∈ shieldedTransferValueLinkDesc.constraints) :
    rowOf t 0 c ≡ (envAt t 0).pub k [ZMOD 2013265921] := by
  have hrc := hsat.rowConstraints 0 hne _ hm
  simpa only [pinPi, VmConstraint2.holdsAt, VmConstraint.holdsVm, rowOf] using hrc rfl

end Refine

/-! ### §7.1 — membership of each family in the emitted list. These are the ONLY place the
emission order is relied on. -/

section Membership
variable {x : VmConstraint2}

theorem mem_limbGates {k i : Nat} (hk : k < 2) (hi : i < U64_LIMBS) (hx : x ∈ limbGates k i) :
    x ∈ shieldedTransferValueLinkDesc.constraints := by
  have h1 : x ∈ (List.range 2).flatMap
      (fun k => (List.range U64_LIMBS).flatMap fun i => limbGates k i) := by
    refine List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, ?_⟩
    exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, hx⟩
  simp only [shieldedTransferValueLinkDesc, shieldedTransferValueLinkConstraints,
    List.mem_append]
  tauto

theorem mem_bin {k i b : Nat} (hk : k < 2) (hi : i < U64_LIMBS) (hb : b < LIMB_BITS) :
    binGate (cBit k i b) ∈ shieldedTransferValueLinkDesc.constraints :=
  mem_limbGates hk hi (by
    refine List.mem_append_left _ ?_
    exact List.mem_map.mpr ⟨b, List.mem_range.mpr hb, rfl⟩)

theorem mem_limbRecompose {k i : Nat} (hk : k < 2) (hi : i < U64_LIMBS) :
    cgH (limbRecomposeHead k i) ∈ shieldedTransferValueLinkDesc.constraints :=
  mem_limbGates hk hi (List.mem_append_right _ (by simp))

theorem mem_u64Recompose_value :
    cgH (u64RecomposeHead 0 cVMOD) ∈ shieldedTransferValueLinkDesc.constraints := by
  simp only [shieldedTransferValueLinkDesc, shieldedTransferValueLinkConstraints,
    List.mem_append, List.mem_cons]
  tauto

theorem mem_u64Recompose_asset :
    cgH (u64RecomposeHead 1 cAMOD) ∈ shieldedTransferValueLinkDesc.constraints := by
  simp only [shieldedTransferValueLinkDesc, shieldedTransferValueLinkConstraints,
    List.mem_append, List.mem_cons]
  tauto

theorem mem_wideA : wideSite DOMAIN_A (cWA 0) ∈ shieldedTransferValueLinkDesc.constraints :=
  sites_emitted.1

theorem mem_wideB : wideSite DOMAIN_B (cWB 0) ∈ shieldedTransferValueLinkDesc.constraints :=
  sites_emitted.2.1

theorem mem_outCm : outCmSite ∈ shieldedTransferValueLinkDesc.constraints :=
  sites_emitted.2.2

theorem mem_pinLane {lane : Nat} (hl : lane < WIDE_LANES) :
    pinPi (laneCol lane) (PI_WIDE + lane) ∈ shieldedTransferValueLinkDesc.constraints := by
  have h1 : pinPi (laneCol lane) (PI_WIDE + lane)
      ∈ (List.range WIDE_LANES).map (fun l => pinPi (laneCol l) (PI_WIDE + l)) :=
    List.mem_map.mpr ⟨lane, List.mem_range.mpr hl, rfl⟩
  simp only [shieldedTransferValueLinkDesc, shieldedTransferValueLinkConstraints, piPins,
    List.mem_append]
  tauto

theorem mem_pinOutCm : pinPi cOUTCM PI_OUTCM ∈ shieldedTransferValueLinkDesc.constraints := by
  simp only [shieldedTransferValueLinkDesc, shieldedTransferValueLinkConstraints, piPins,
    List.mem_append, List.mem_cons]
  tauto

end Membership

/-! ### §7.2 — the limbs are canonical, so the value is a genuine `u64`. -/

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
16-bit-ness is PRODUCED by the emitted gates, not assumed of the witness. This is what makes the
value the carrier absorbs and the value the note commitment hashes the SAME `u64` rather than the
same residue. -/
theorem link_limb_canonical
    (hsat : Satisfied2 hash shieldedTransferValueLinkDesc minit mfin maddrs t) (i₀ : Nat)
    (hi₀ : i₀ + 1 < t.rows.length) {k i : Nat} (hk : k < 2) (hi : i < U64_LIMBS)
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

/-! ### §7.3 — the value the compatibility felts denote is the value the limbs denote. -/

/-- The `u64` a kind's four limb cells denote. -/
def u64Of (a : Assignment) (k : Nat) : ℤ :=
  ((List.range U64_LIMBS).map fun i => 2 ^ (LIMB_BITS * i) * a (cLimb k i)).sum

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

/-- **`cVMOD` is the reduction of the full `u64` the carrier absorbs** — the value the note
commitment hashes is not a second, free value. -/
theorem link_vmod_is_the_reduction
    (hsat : Satisfied2 hash shieldedTransferValueLinkDesc minit mfin maddrs t) (i₀ : Nat)
    (hi₀ : i₀ + 1 < t.rows.length) :
    rowOf t i₀ cVMOD ≡ u64Of (rowOf t i₀) 0 [ZMOD 2013265921] := by
  have hgate := lkGate hsat i₀ hi₀ mem_u64Recompose_value
  rw [u64RecomposeHead_eval] at hgate
  have hs : ((List.range U64_LIMBS).map fun i => limbWeight i * rowOf t i₀ (cLimb 0 i)).sum
      ≡ u64Of (rowOf t i₀) 0 [ZMOD 2013265921] := by
    refine sum_modEq _ _ _ fun i _ => ?_
    exact Int.ModEq.mul_right _ (limbWeight_modEq i)
  have h2 : rowOf t i₀ cVMOD
      ≡ ((List.range U64_LIMBS).map fun i => limbWeight i * rowOf t i₀ (cLimb 0 i)).sum
      [ZMOD 2013265921] := by
    simpa using Int.ModEq.add_right
      (((List.range U64_LIMBS).map fun i => limbWeight i * rowOf t i₀ (cLimb 0 i)).sum) hgate
  exact h2.trans hs

/-- The asset half of the same statement. -/
theorem link_amod_is_the_reduction
    (hsat : Satisfied2 hash shieldedTransferValueLinkDesc minit mfin maddrs t) (i₀ : Nat)
    (hi₀ : i₀ + 1 < t.rows.length) :
    rowOf t i₀ cAMOD ≡ u64Of (rowOf t i₀) 1 [ZMOD 2013265921] := by
  have hgate := lkGate hsat i₀ hi₀ mem_u64Recompose_asset
  rw [u64RecomposeHead_eval] at hgate
  have hs : ((List.range U64_LIMBS).map fun i => limbWeight i * rowOf t i₀ (cLimb 1 i)).sum
      ≡ u64Of (rowOf t i₀) 1 [ZMOD 2013265921] := by
    refine sum_modEq _ _ _ fun i _ => ?_
    exact Int.ModEq.mul_right _ (limbWeight_modEq i)
  have h2 : rowOf t i₀ cAMOD
      ≡ ((List.range U64_LIMBS).map fun i => limbWeight i * rowOf t i₀ (cLimb 1 i)).sum
      [ZMOD 2013265921] := by
    simpa using Int.ModEq.add_right
      (((List.range U64_LIMBS).map fun i => limbWeight i * rowOf t i₀ (cLimb 1 i)).sum) hgate
  exact h2.trans hs

end Reduction

/-! ### §7.4 — the two published objects, forced. -/

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

/-- The seven values the output note-commitment site absorbs:
`hash_fact(value_mod_p, [asset_mod_p, outOwner, outRand])`. -/
def outCmIns (a : Assignment) : List ℤ :=
  [a cVMOD, a cAMOD, a cOWNER, a cORAND, 0, FACT_MARK, 1]

theorem outCmIns_eval (a : Assignment) :
    (factIns [.var cVMOD, .var cAMOD, .var cOWNER, .var cORAND]).map (·.eval a) = outCmIns a := rfl

section Sites
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
variable {permOut : List ℤ → List ℤ}

/-- The generic per-site forcing: all EIGHT lanes of a carrier site are the genuine squeeze over
THIS row's own limb cells. -/
theorem link_wide_lanes_forced_at
    (hsat : Satisfied2 hash shieldedTransferValueLinkDesc minit mfin maddrs t)
    (hSound : ChipTableSoundN permOut (t.tf TableId.poseidon2)) (i : Nat) (hi : i < t.rows.length)
    {domain : ℤ} {base : Nat}
    (hm : wideSite domain base ∈ shieldedTransferValueLinkDesc.constraints) :
    (wideOut base).map (rowOf t i) = permOut (linkIns (rowOf t i) domain) := by
  have hh := lkLookup hsat i hi hm
  simp only [Lookup.holdsAt] at hh
  have := chip_lookup_sound_N permOut (t.tf TableId.poseidon2) hSound (rowOf t i)
    (wideLeft domain ++ wideRight) (wideOut base) (of_decide_eq_true (Eq.refl true)) hh
  rwa [linkIns_eval] at this

/-- **The output note commitment is FORCED to `hash_fact` of the SAME recomposed felts.** Not a
free cell the prover picks: the value the minted note is worth is the value this row's limbs
denote. -/
theorem link_outcm_forced
    (hsat : Satisfied2 hash shieldedTransferValueLinkDesc minit mfin maddrs t)
    (hwire : t.tf poseidon2narrow = narrowTable (t.tf TableId.poseidon2))
    (hSound : ChipTableSound hash (t.tf TableId.poseidon2))
    (i : Nat) (hi : i < t.rows.length) :
    rowOf t i cOUTCM = hash (outCmIns (rowOf t i)) := by
  have hh := lkLookup hsat i hi mem_outCm
  have hlen : Dregg2.Circuit.DescriptorIR2.ChipArityAdmitted
      (factIns [EmittedExpr.var cVMOD, .var cAMOD, .var cOWNER, .var cORAND]).length := by
    chip_arity_admitted
  have := narrow_lookup_holdsAt_sound hash t.tf hwire hSound (envAt t i)
    (factIns [EmittedExpr.var cVMOD, .var cAMOD, .var cOWNER, .var cORAND]) cOUTCM hlen hh
  rwa [outCmIns_eval] at this

/-- **⚑ THE VALUE LINK, AS A THEOREM.** On a satisfying trace, the sixteen published carrier lanes
and the published note commitment are BOTH functions of row 0's own limb cells:
lane `j < 8` is lane `j` of `permOut (linkIns … DOMAIN_A)`, and the note commitment is
`hash (outCmIns …)` whose first two entries are pinned to the reductions of exactly those limbs
(`link_vmod_is_the_reduction`, `link_amod_is_the_reduction`).

There is no second value cell in the relation, so "the minted note is worth more than the spent
note" is not a statement a satisfying assignment can make. That is the difference between this and
the transcript weld it replaces: the retired Pedersen leg's `v` was a free group element the prover
chose, absorbed into a Fiat-Shamir message and compared to nothing. -/
theorem value_link_reads_one_opening
    (hsat : Satisfied2 hash shieldedTransferValueLinkDesc minit mfin maddrs t)
    (hSound : ChipTableSoundN permOut (t.tf TableId.poseidon2))
    (hwire : t.tf poseidon2narrow = narrowTable (t.tf TableId.poseidon2))
    (hNarrow : ChipTableSound hash (t.tf TableId.poseidon2))
    (hrows : 0 < t.rows.length) (htr : 0 + 1 < t.rows.length) {j : Nat} (hj : j < 8) :
    (envAt t 0).pub (PI_WIDE + j)
        ≡ (permOut (linkIns (rowOf t 0) DOMAIN_A)).getD j 0 [ZMOD 2013265921]
      ∧ (envAt t 0).pub PI_OUTCM ≡ hash (outCmIns (rowOf t 0)) [ZMOD 2013265921]
      ∧ rowOf t 0 cVMOD ≡ u64Of (rowOf t 0) 0 [ZMOD 2013265921]
      ∧ rowOf t 0 cAMOD ≡ u64Of (rowOf t 0) 1 [ZMOD 2013265921] := by
  refine ⟨?_, ?_, link_vmod_is_the_reduction hsat 0 htr, link_amod_is_the_reduction hsat 0 htr⟩
  · have hlanes := link_wide_lanes_forced_at hsat hSound 0 hrows mem_wideA
    have hpin : rowOf t 0 (laneCol j) ≡ (envAt t 0).pub (PI_WIDE + j) [ZMOD 2013265921] :=
      lkPin hsat hrows (mem_pinLane (by simp only [WIDE_LANES]; omega))
    have hcol : laneCol j = cWA 0 + j := by
      simp only [laneCol, cWA, if_pos hj]
    have hval : rowOf t 0 (cWA 0 + j)
        = (permOut (linkIns (rowOf t 0) DOMAIN_A)).getD j 0 := by
      rw [← linkOut_getD (rowOf t 0) (cWA 0) j hj, hlanes]
    rw [hcol, hval] at hpin
    exact Int.ModEq.symm hpin
  · have hpin := lkPin hsat hrows mem_pinOutCm
    rw [link_outcm_forced hsat hwire hNarrow 0 hrows] at hpin
    exact Int.ModEq.symm hpin

/-- **The negative tooth on the OUTPUT.** Publishing a note commitment that is not the trace's own
forced `outCm` cell is UNSAT — there is no satisfying assignment that mints a note the relation did
not compute from the limbs it carries. -/
theorem decoupled_outcm_unsat (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) (hne : 0 < t.rows.length)
    (hforge : ¬ (rowOf t 0 cOUTCM ≡ (envAt t 0).pub PI_OUTCM [ZMOD 2013265921])) :
    ¬ Satisfied2 hash shieldedTransferValueLinkDesc minit mfin maddrs t :=
  fun hsat => hforge (lkPin hsat hne mem_pinOutCm)

/-- **The negative tooth on the CARRIER.** Publishing a lane that is not the trace's own carrier
cell is UNSAT — so the sixteen lanes the executor hands this relation from the complete-spend proof
cannot be "matched" by anything but a trace whose limbs really do squeeze to them. -/
theorem decoupled_carrier_unsat (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) (hne : 0 < t.rows.length) {lane : Nat}
    (hl : lane < WIDE_LANES)
    (hforge : ¬ (rowOf t 0 (laneCol lane) ≡ (envAt t 0).pub (PI_WIDE + lane)
      [ZMOD 2013265921])) :
    ¬ Satisfied2 hash shieldedTransferValueLinkDesc minit mfin maddrs t :=
  fun hsat => hforge (lkPin hsat hne (mem_pinLane hl))

end Sites

/-! ## §7 — axiom hygiene. -/

#assert_axioms layout_agrees_with_sidecar
#assert_axioms carrier_absorb_is_the_sidecar_absorb
#assert_axioms constraint_census
#assert_axioms gate_census
#assert_axioms pi_census
#assert_axioms wide_site_census
#assert_axioms narrow_site_census
#assert_axioms bit_columns_distinct_and_in_range
#assert_axioms sites_emitted
#assert_axioms link_limb_canonical
#assert_axioms link_vmod_is_the_reduction
#assert_axioms link_amod_is_the_reduction
#assert_axioms link_outcm_forced
#assert_axioms value_link_reads_one_opening
#assert_axioms decoupled_outcm_unsat
#assert_axioms decoupled_carrier_unsat
#assert_compiled link_emits_golden

end Dregg2.Circuit.Emit.ShieldedTransferValueLinkEmit
