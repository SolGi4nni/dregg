/-
# Dregg2.Circuit.Emit.WideValueBindingEmit — the Lean-authored FULL-`u64` VALUE/ASSET BINDING AIR,
the replacement route for the hand-written Rust `CircuitDescriptor` in
`circuit-prove/src/shielded/wide_value_binding.rs`.

## SAY THE SUBSTRATE OUT LOUD

This is **Lean-authored AIR**. The constraint list below IS the emitted object; Rust's only job is
to decode it (`parse_vm_descriptor2`) and prove it (`prove_vm_descriptor2`).

`circuit-prove/src/shielded/wide_value_binding.rs` is 639 lines of Rust that hand-writes a
`CircuitDescriptor` — 144 `ConstraintExpr` values and 17 `BoundaryDef`s built by Rust helper
functions (`constant_gate`, `limb_recompose`, `u64_recompose`, `wide_input_columns`) — and reaches
outside its crate for the hash semantics (`dregg_circuit::cap_root::cap_node8`,
`dregg_circuit::poseidon2::hash_fact`). It is the PUREST instance of the drift the law names,
because it was authored FOR THE FELT-WIDTH REPAIR: a correctness fix went into Rust because the
Rust AIR crate was right there. The law-1 ratchet scores it at 7 authored sites
(`law1_enforcement_gate.rs` BASELINE).

## The specification, extracted from the Rust BEFORE authoring

One row (the Rust producer emits a constant two-row trace), over a private witness
`(value : u64, asset : u64, randomness : felt, blind : felt^6)`. The relation:

    (R1) every one of the 2 × 4 × 16 bit cells is BOOLEAN                      [`Binary`]
    (R2) limb_{k,i} = Σ_{b<16} 2^b · bit_{k,i,b}                               [`limb_recompose`]
    (R3) value_mod_p = Σ_{i<4} (2^{16i} mod p) · value_limb_i                  [`u64_recompose`]
         asset_mod_p = Σ_{i<4} (2^{16i} mod p) · asset_limb_i
    (R4) domain_a = 0x5642_4e30, domain_b = 0x5642_4e31, zero = 0              [`constant_gate`]
    (R5) wide_a[0..8] = cap_node8([domain_a, v0,v1,v2,v3, a0,a1,a2],
                                  [a3, randomness, blind0..blind5])            [`MerkleHash8`]
    (R6) wide_b[0..8] = the SAME node8 at `domain_b`                           [`MerkleHash8`]
    (R7) legacy_binding = hash_fact(value_mod_p, [asset_mod_p, randomness, 0]) [`Hash`]
    (R8) row 0 publishes `[legacy_binding, wide_a[0..8], wide_b[0..8]]` as the 17 public inputs
                                                                              [`BoundaryDef::PiBinding`]

R1+R2 are the felt-width repair: they are what makes the limb vector the CANONICAL 16-bit
decomposition, so the full `u64` is representable and nothing aliases mod `p` before hashing.
R7 is the compatibility join to the deployed spend circuit's one-felt C7 — kept, and provably
NOT injective on `u64` (see `WideValueBindingRefine.legacy_join_cannot_separate_aliases`).

## The IR-v2 re-expression (what each Rust node became, and why it is the SAME AIR)

| Rust `ConstraintExpr` | here | why it is the same object |
|---|---|---|
| `Binary { col }` | `binGate` | `x·(x−1)` |
| `Polynomial { terms }` | `cgH (Head …)` | `Σ coeff·∏cols + const` |
| `MerkleHash8 {out8,l8,r8}` | `chipLookupTupleN` at 16 inputs | `cap_node8` IS `chip_absorb_all_lanes(CHIP_NODE8_ARITY=16, L8‖R8)` (`cap_root.rs:149-157`), which is exactly the arity-16 wide chip row |
| `Hash {out, [a,b,c,d]}` | `chipLookupTupleNarrow (factIns …)` | `hash_fact(a,[b,c,d])` IS the arity-7 chip absorb of `[a,b,c,0,0,0xFACF,1]` squeezed at lane 0 (`poseidon2.rs:604-625`; the same reading `note_spend_witness.rs:127` records) |
| `BoundaryDef::PiBinding` | `pinPi` | first-row `col = pi[idx]` |

## Two deliberate deviations from the Rust build (improvements, stated not hidden)

1. **No `domain_a` / `domain_b` columns.** Rust allocates two witness columns and pins them to the
   two domain separators with `constant_gate`. Here the separator is the literal `.const` in the
   chip tuple — strictly stronger, because a constant cannot be tampered whereas a pinned column
   is one more gate that must hold.
2. **No `zero` column.** Same argument for the `hash_fact` pad slot.

Both remove witness columns whose only content was a constant pin. NOTHING else moved: the limb
order, the node8 input packing (left half then right half, felt for felt), the domain tags, the
`hash_fact` argument order and the PI layout are the Rust ones felt-for-felt. §6 accounts for the
delta exactly: **−3 columns and −3 constraints, at the same 17 PIs and the same 2 node8 sites.**

## One SEMANTIC delta, NAMED (not a deviation this file chose)

The v1 Rust AIR asserts `Binary`/`Polynomial` on EVERY row (`dsl_p3_air.rs:611`, a bare
`assert_zero`). IR-v2's `.base (.gate _)` rides the deployed `when_transition()` domain, so the
algebraic gates below bind on every row EXCEPT the last. The chip lookups carry no such guard —
they bind on every row — and all 17 PI pins are FIRST-row, so the published claim is row 0's and
row 0 is a transition row on any trace of two or more rows (which is what the Rust producer emits).
The last row is therefore unconstrained-and-unread rather than constrained; a consumer that ever
reads a non-first row would need the `.base (.boundary .last …)` twin of each gate (the
`ShieldedValueLinkDescriptor` last-row re-lowering pattern, 138 extra constraints). Not emitted
here, because nothing reads that row.

## Honest scope of THIS file

This file emits the descriptor and pins its wire bytes. The SAT ⟹ SEM bridge is the sibling
`WideValueBindingRefine.lean`, which also records exactly which of the constraints below are
covered by a proven theorem and which are emitted-but-not-yet-refined.

## Axiom hygiene

Definitional descriptor + a byte-pinned `#guard` on its wire string + shape/census `#guard`s.
NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.AirBuilder
import Dregg2.Circuit.ChipNarrowLookup

namespace Dregg2.Circuit.Emit.WideValueBindingEmit

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId chipLookupTupleN chipLookupTupleNarrow
   poseidon2narrow CHIP_RATE CHIP_OUT_LANES padToE emitVmJson2)
open Dregg2.Circuit.Emit.AirBuilder

set_option autoImplicit false

/-! ## §1 — The shape constants (`wide_value_binding.rs:36-48`). -/

/-- `U64_LIMBS` — 16-bit limbs per canonical `u64`. -/
def U64_LIMBS : Nat := 4
/-- `LIMB_BITS` — bits per limb. -/
def LIMB_BITS : Nat := 16
/-- `WIDE_VALUE_BINDING_LANES` — independently constrained public binding lanes. -/
def WIDE_LANES : Nat := 16
/-- `BINDING_BLIND_LANES` — field-valued blinding lanes beyond the legacy randomness felt. -/
def BLIND_LANES : Nat := 6

/-- `DOMAIN_A = 0x5642_4e30` ("VBN0"). -/
def DOMAIN_A : ℤ := 1447185968
/-- `DOMAIN_B = 0x5642_4e31` ("VBN1"). -/
def DOMAIN_B : ℤ := 1447185969

#guard DOMAIN_A == (0x56424e30 : ℤ)
#guard DOMAIN_B == (0x56424e31 : ℤ)

/-- The BabyBear prime. -/
def P : ℤ := 2013265921

/-- `limb_weight i` — the reduced limb place value `2^{16i} mod p`, byte-for-byte the Rust
`BabyBear::new(((1u64 << shift) % BABYBEAR_P as u64) as u32)`. -/
def limbWeight (i : Nat) : ℤ := (2 ^ (LIMB_BITS * i)) % P

#guard limbWeight 0 == 1
#guard limbWeight 1 == 65536
#guard limbWeight 2 == 268435454
#guard limbWeight 3 == 268295646

/-- The `hash_fact` domain marker (`poseidon2.rs::hash_fact` `state[5]` = `0xFACF`). -/
def FACT_MARK : ℤ := 64207

/-! ## §2 — The column layout.

The Rust `col` module, MINUS the three constant-pinned columns (§6 accounts for the shift). Every
index below `cLEGACY` is the Rust index unchanged; every index at or above it is the Rust index
minus 3. -/

/-- Value limb `i` (little-endian; `value = Σ 2^{16i}·v_i`). -/
def cV (i : Nat) : Nat := i
/-- Asset limb `i`. -/
def cA (i : Nat) : Nat := U64_LIMBS + i
/-- Limb `i` of kind `k` (`0 = value`, `1 = asset`) — the Rust `col::limb`. -/
def cLimb (k i : Nat) : Nat := if k = 0 then cV i else cA i
/-- The compatibility felt `value mod p`. -/
def cVMOD : Nat := 2 * U64_LIMBS
/-- The compatibility felt `asset mod p`. -/
def cAMOD : Nat := cVMOD + 1
/-- The legacy randomness felt (absorbed by BOTH the compatibility fact and the wide carrier). -/
def cRAND : Nat := cVMOD + 2
/-- Binding blind lane `i`. -/
def cBL (i : Nat) : Nat := cVMOD + 3 + i
/-- The compatibility one-felt binding (`hash_fact` out0). -/
def cLEGACY : Nat := cVMOD + 3 + BLIND_LANES
/-- Wide carrier lane `j` of the `DOMAIN_A` `node8`. -/
def cWA (j : Nat) : Nat := cLEGACY + 1 + j
/-- Wide carrier lane `j` of the `DOMAIN_B` `node8`. -/
def cWB (j : Nat) : Nat := cLEGACY + 9 + j
/-- Base of the bit-decomposition block. -/
def BITS_BASE : Nat := cLEGACY + 17
/-- Bit `b` of limb `i` of kind `k` — the Rust `col::bit`. -/
def cBit (k i b : Nat) : Nat := BITS_BASE + (k * U64_LIMBS + i) * LIMB_BITS + b
/-- **The main-trace width.** -/
def WVB_WIDTH : Nat := BITS_BASE + 2 * U64_LIMBS * LIMB_BITS

#guard cVMOD == 8
#guard cAMOD == 9
#guard cRAND == 10
#guard cBL 0 == 11
#guard cBL 5 == 16
#guard cLEGACY == 17
#guard cWA 0 == 18
#guard cWB 0 == 26
#guard BITS_BASE == 34
#guard WVB_WIDTH == 162

/-! ## §3 — The public-input layout (`wide_value_binding.rs::pi`). -/

/-- PI 0 — the compatibility join to the deployed spend circuit's C7 claim. -/
def PI_LEGACY : Nat := 0
/-- PI 1 — the first lane of the faithful wide binding. -/
def PI_WIDE : Nat := 1
/-- Total public inputs (`pi::COUNT`). -/
def WVB_PI_COUNT : Nat := 1 + WIDE_LANES

#guard WVB_PI_COUNT == 17

/-! ## §4 — The gates.

R1/R2 — canonical 16-bit encodings: there is exactly ONE limb vector per `u64`, and the bit cells
are what make it canonical. This is the felt-width repair, in the AIR. -/

/-- R2 — `limb_{k,i} − Σ_{b<16} 2^b·bit_{k,i,b}` (the Rust `limb_recompose`). -/
def limbRecomposeHead (k i : Nat) : Head :=
  (List.range LIMB_BITS).foldl (fun h b => h.addLin (-(2 ^ b : ℤ)) (cBit k i b))
    (Head.lin 1 (cLimb k i))

/-- R1+R2 for one limb: its sixteen boolean pins, then its recomposition. -/
def limbGates (k i : Nat) : List VmConstraint2 :=
  ((List.range LIMB_BITS).map fun b => binGate (cBit k i b))
  ++ [cgH (limbRecomposeHead k i)]

/-- R3 — `out − Σ_{i<4} (2^{16i} mod p)·limb_{k,i}` (the Rust `u64_recompose`): the compatibility
felt is DERIVED from, never independent of, the full limbs. This is the exact field reduction the
deployed v1 spend circuit sees. -/
def u64RecomposeHead (k out : Nat) : Head :=
  (List.range U64_LIMBS).foldl (fun h i => h.addLin (-(limbWeight i)) (cLimb k i))
    (Head.lin 1 out)

/-! ### R5/R6 — the two domain-separated `node8` carriers.

`cap_node8(l8, r8)` IS `chip_absorb_all_lanes(16, l8 ‖ r8)` — the arity-16 wide chip row with all
eight output lanes program-owned. So one `chipLookupTupleN` per site, and the soundness lever is
`chip_lookup_sound_N`. -/

/-- The `node8` LEFT half at a domain separator: `[domain, v0, v1, v2, v3, a0, a1, a2]`
(`wide_input_columns`, the Rust `left`). -/
def wideLeft (domain : ℤ) : List EmittedExpr :=
  (.const domain) :: ((List.range U64_LIMBS).map fun i => EmittedExpr.var (cV i))
  ++ ((List.range 3).map fun i => EmittedExpr.var (cA i))

/-- The `node8` RIGHT half, SHARED by both domains: `[a3, randomness, blind0..blind5]`
(`wide_input_columns`, the Rust `right`). -/
def wideRight : List EmittedExpr :=
  (.var (cA 3)) :: (.var cRAND)
  :: ((List.range BLIND_LANES).map fun i => EmittedExpr.var (cBL i))

/-- The 8 output columns of a carrier based at `base`. -/
def wideOut (base : Nat) : List Nat := (List.range CHIP_OUT_LANES).map (base + ·)

/-- One domain-separated wide carrier site. -/
def wideSite (domain : ℤ) (base : Nat) : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2, chipLookupTupleN (wideLeft domain ++ wideRight) (wideOut base)⟩

#guard (wideLeft DOMAIN_A).length == 8
#guard wideRight.length == 8
#guard (wideLeft DOMAIN_A ++ wideRight).length == CHIP_RATE
#guard (chipLookupTupleN (wideLeft DOMAIN_A ++ wideRight) (wideOut (cWA 0))).length
         == 1 + CHIP_RATE + CHIP_OUT_LANES

/-! ### R7 — the compatibility `hash_fact` site.

`hash_fact(x, [f0, f1, f2])` seeds `state[0..4] = [x, f0, f1, f2, 0]`, `state[5] = 0xFACF`,
`state[6] = 1` and squeezes `state[0]` — i.e. the arity-7 chip absorb of
`[x, f0, f1, f2, 0, 0xFACF, 1]`, lane 0 only. Single output ⇒ the NARROW bus (18-wide tuple), which
is why no lane columns appear: `chip_lookup_sound_narrow` forces the same hash equation the 25-wide
lookup does, carrying nothing extra. -/

/-- The 7-slot `hash_fact` absorb block `[x, f0, f1, f2, f3, MARK, 1]` over general expressions
(the Rust `fact_site_always` tuple, term for term). -/
def factIns (es : List EmittedExpr) : List EmittedExpr :=
  padToE 5 es ++ [.const FACT_MARK, .const 1]

/-- R7 — `legacy_binding = hash_fact(value_mod_p, [asset_mod_p, randomness, 0])`. The Rust passes
its constant-pinned `zero` COLUMN as the fourth term; here it is the literal `0`. -/
def legacySite : VmConstraint2 :=
  .lookup ⟨poseidon2narrow,
    chipLookupTupleNarrow (factIns [.var cVMOD, .var cAMOD, .var cRAND, .const 0]) cLEGACY⟩

#guard (factIns [.var cVMOD, .var cAMOD, .var cRAND, .const 0]).length == 7
#guard (chipLookupTupleNarrow (factIns [.var cVMOD, .var cAMOD, .var cRAND, .const 0])
          cLEGACY).length == 1 + CHIP_RATE + 1

/-! ### R8 — the boundary pins (`wide_value_binding.rs` `boundaries`). -/

/-- The published lane `lane`'s column: the `DOMAIN_A` carrier for `0..8`, the `DOMAIN_B` carrier
for `8..16` — the Rust `if lane < 8 { WIDE_A + lane } else { WIDE_B + lane - 8 }`. -/
def laneCol (lane : Nat) : Nat := if lane < 8 then cWA lane else cWB (lane - 8)

/-- The 17 first-row PI bindings, in the Rust boundary order. -/
def piPins : List VmConstraint2 :=
  pinPi cLEGACY PI_LEGACY
  :: ((List.range WIDE_LANES).map fun lane => pinPi (laneCol lane) (PI_WIDE + lane))

/-! ## §5 — THE DESCRIPTOR. -/

/-- The full constraint list, in the Rust emission order: the per-limb boolean+recompose blocks
(value then asset), the two compatibility reductions, the two wide carriers, the compatibility
fact, then the boundary pins. -/
def wideValueBindingConstraints : List VmConstraint2 :=
  ((List.range 2).flatMap fun k => (List.range U64_LIMBS).flatMap fun i => limbGates k i)
  ++ [cgH (u64RecomposeHead 0 cVMOD), cgH (u64RecomposeHead 1 cAMOD)]
  ++ [wideSite DOMAIN_A (cWA 0), wideSite DOMAIN_B (cWB 0)]
  ++ [legacySite]
  ++ piPins

/-- **`wideValueBindingDesc`** — the Lean-authored full-`u64` value/asset binding AIR. The chip
tables are IMPLICITLY present (Presence-detected from the lookups), so `tables` is empty; the limb
range check is an explicit bit decomposition exactly as the Rust one is, so `ranges` is empty. -/
def wideValueBindingDesc : EffectVmDescriptor2 :=
  { name        := "dregg-shielded-wide-value-binding-v1::poseidon2-node8"
  , traceWidth  := WVB_WIDTH
  , piCount     := WVB_PI_COUNT
  , tables      := []
  , constraints := wideValueBindingConstraints
  , hashSites   := []
  , ranges      := [] }

/-! ## §6 — THE STRUCTURAL CROSS-CHECK against the Rust crate's own census.

The Rust `col` module computes its width from the SAME shape constants. Transcribed here as
`rustWidth`, the accounting is exact and per-column: the Lean layout is the Rust layout with the
three constant-pinned columns (`domain_a`, `domain_b`, `zero`) removed, so every Lean index below
`legacy_binding` equals the Rust index and every index at or above it is the Rust index minus 3.
The constraint census moves by the SAME 3 — the three `constant_gate`s those columns needed. -/

/-- The Rust `col::WIDTH`, transcribed from `wide_value_binding.rs:50-79`. -/
def rustWidth : Nat := 2 * U64_LIMBS + 3 + BLIND_LANES + 3 + 1 + 16 + 2 * U64_LIMBS * LIMB_BITS

/-- The Rust `col` indices, transcribed. -/
def rustLegacy : Nat := 2 * U64_LIMBS + 3 + BLIND_LANES + 3
def rustWideA : Nat := rustLegacy + 1
def rustWideB : Nat := rustWideA + 8
def rustBits : Nat := rustWideB + 8

#guard rustWidth == 165
#guard rustLegacy == 20
#guard rustWideA == 21
#guard rustWideB == 29
#guard rustBits == 37

-- THE COLUMN DELTA: exactly 3, and it is the three constant-pinned columns.
#guard WVB_WIDTH + 3 == rustWidth
#guard cLEGACY + 3 == rustLegacy
#guard cWA 0 + 3 == rustWideA
#guard cWB 0 + 3 == rustWideB
#guard BITS_BASE + 3 == rustBits
-- Everything BELOW the dropped block is index-identical to Rust.
#guard cV 0 == 0 && cA 0 == 4 && cVMOD == 8 && cAMOD == 9 && cRAND == 10 && cBL 0 == 11

/-- The Rust `constraints.len()` (144) plus `boundaries.len()` (17): 128 `Binary` + 8 limb
recompositions + 2 `u64` recompositions + 3 `constant_gate`s + 2 `MerkleHash8` + 1 `Hash` + 17
`PiBinding`. -/
def rustConstraintCensus : Nat := 2 * U64_LIMBS * LIMB_BITS + 2 * U64_LIMBS + 2 + 3 + 2 + 1
                                  + (1 + WIDE_LANES)

#guard rustConstraintCensus == 161

-- THE CONSTRAINT DELTA: exactly 3, the three `constant_gate`s whose columns are gone.
#guard wideValueBindingDesc.constraints.length == 158
#guard wideValueBindingDesc.constraints.length + 3 == rustConstraintCensus

-- The census, by form. Every number here is the Rust number.
#guard (wideValueBindingDesc.constraints.filter
          (fun c => match c with | .base (.gate _) => true | _ => false)).length
        == 2 * U64_LIMBS * LIMB_BITS + 2 * U64_LIMBS + 2
#guard (wideValueBindingDesc.constraints.filter
          (fun c => match c with | .base (.piBinding _ _ _) => true | _ => false)).length
        == WVB_PI_COUNT
#guard (wideValueBindingDesc.constraints.filterMap
          (fun c => match c with
            | .lookup l => if l.table == TableId.poseidon2 then some l.tuple.length else none
            | _ => none)) == [25, 25]
#guard (wideValueBindingDesc.constraints.filterMap
          (fun c => match c with
            | .lookup l => if l.table == poseidon2narrow then some l.tuple.length else none
            | _ => none)) == [18]
-- The 128 boolean pins of the felt-width repair are all present and all distinct columns.
#guard ((List.range 2).flatMap fun k => (List.range U64_LIMBS).flatMap fun i =>
          (List.range LIMB_BITS).map fun b => cBit k i b).length == 128
#guard (((List.range 2).flatMap fun k => (List.range U64_LIMBS).flatMap fun i =>
          (List.range LIMB_BITS).map fun b => cBit k i b).dedup).length == 128
#guard ((List.range 2).flatMap fun k => (List.range U64_LIMBS).flatMap fun i =>
          (List.range LIMB_BITS).map fun b => cBit k i b).all (fun c => c < WVB_WIDTH)

/-! ## §7 — THE BYTE-PIN (the Rust decoder ingests THIS string).

`emitVmJson2 wideValueBindingDesc` is pinned verbatim. This is the drift gate on the whole
authoring chain: a change to any column offset, any gate head, any limb weight, any domain tag,
any PI index, or the `Head` lowering itself moves these bytes and breaks the `#guard`.

Exposed as a named raw-string `def` (not an inline literal) so the Rust wire canary
`circuit-prove/tests/wide_value_binding_lean_route.rs` can `include_str!` THIS module and split the
golden straight out of it — the Lean emission is then the only copy that exists, and a
hand-transcription hop cannot open between author and consumer. That canary also cross-checks the
census below against the LIVE `wide_value_binding_descriptor()`, reading the Rust numbers rather
than transcribing them. -/

/-- **`WIDE_VALUE_BINDING_GOLDEN`** — the byte-pinned wire string of `wideValueBindingDesc`. -/
def WIDE_VALUE_BINDING_GOLDEN : String := r#"{"name":"dregg-shielded-wide-value-binding-v1::poseidon2-node8","ir":2,"trace_width":162,"public_input_count":17,"tables":[],"constraints":[{"t":"gate","body":{"t":"mul","l":{"t":"var","v":34},"r":{"t":"add","l":{"t":"var","v":34},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":35},"r":{"t":"add","l":{"t":"var","v":35},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":36},"r":{"t":"add","l":{"t":"var","v":36},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"add","l":{"t":"var","v":37},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":38},"r":{"t":"add","l":{"t":"var","v":38},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":39},"r":{"t":"add","l":{"t":"var","v":39},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":40},"r":{"t":"add","l":{"t":"var","v":40},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":41},"r":{"t":"add","l":{"t":"var","v":41},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":42},"r":{"t":"add","l":{"t":"var","v":42},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":43},"r":{"t":"add","l":{"t":"var","v":43},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":44},"r":{"t":"add","l":{"t":"var","v":44},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":45},"r":{"t":"add","l":{"t":"var","v":45},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":46},"r":{"t":"add","l":{"t":"var","v":46},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":47},"r":{"t":"add","l":{"t":"var","v":47},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":48},"r":{"t":"add","l":{"t":"var","v":48},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":49},"r":{"t":"add","l":{"t":"var","v":49},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":0}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":34}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":35}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":36}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":37}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":38}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":39}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":40}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":41}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":42}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":43}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":44}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":45}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":46}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":47}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":48}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":49}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":50},"r":{"t":"add","l":{"t":"var","v":50},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":51},"r":{"t":"add","l":{"t":"var","v":51},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":52},"r":{"t":"add","l":{"t":"var","v":52},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":53},"r":{"t":"add","l":{"t":"var","v":53},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":54},"r":{"t":"add","l":{"t":"var","v":54},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":55},"r":{"t":"add","l":{"t":"var","v":55},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":56},"r":{"t":"add","l":{"t":"var","v":56},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":57},"r":{"t":"add","l":{"t":"var","v":57},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":58},"r":{"t":"add","l":{"t":"var","v":58},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":59},"r":{"t":"add","l":{"t":"var","v":59},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":60},"r":{"t":"add","l":{"t":"var","v":60},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":61},"r":{"t":"add","l":{"t":"var","v":61},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":62},"r":{"t":"add","l":{"t":"var","v":62},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":63},"r":{"t":"add","l":{"t":"var","v":63},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":64},"r":{"t":"add","l":{"t":"var","v":64},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":65},"r":{"t":"add","l":{"t":"var","v":65},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":1}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":50}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":51}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":52}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":53}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":54}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":55}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":56}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":57}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":58}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":59}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":60}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":61}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":62}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":63}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":64}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":65}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":66},"r":{"t":"add","l":{"t":"var","v":66},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":67},"r":{"t":"add","l":{"t":"var","v":67},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":68},"r":{"t":"add","l":{"t":"var","v":68},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":69},"r":{"t":"add","l":{"t":"var","v":69},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":70},"r":{"t":"add","l":{"t":"var","v":70},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":71},"r":{"t":"add","l":{"t":"var","v":71},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":72},"r":{"t":"add","l":{"t":"var","v":72},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":73},"r":{"t":"add","l":{"t":"var","v":73},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":74},"r":{"t":"add","l":{"t":"var","v":74},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":75},"r":{"t":"add","l":{"t":"var","v":75},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":76},"r":{"t":"add","l":{"t":"var","v":76},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":77},"r":{"t":"add","l":{"t":"var","v":77},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":78},"r":{"t":"add","l":{"t":"var","v":78},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":79},"r":{"t":"add","l":{"t":"var","v":79},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":80},"r":{"t":"add","l":{"t":"var","v":80},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":81},"r":{"t":"add","l":{"t":"var","v":81},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":2}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":66}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":67}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":68}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":69}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":70}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":71}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":72}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":73}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":74}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":75}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":76}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":77}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":78}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":79}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":80}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":81}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":82},"r":{"t":"add","l":{"t":"var","v":82},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":83},"r":{"t":"add","l":{"t":"var","v":83},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":84},"r":{"t":"add","l":{"t":"var","v":84},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":85},"r":{"t":"add","l":{"t":"var","v":85},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":86},"r":{"t":"add","l":{"t":"var","v":86},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":87},"r":{"t":"add","l":{"t":"var","v":87},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":88},"r":{"t":"add","l":{"t":"var","v":88},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":89},"r":{"t":"add","l":{"t":"var","v":89},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":90},"r":{"t":"add","l":{"t":"var","v":90},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":91},"r":{"t":"add","l":{"t":"var","v":91},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":92},"r":{"t":"add","l":{"t":"var","v":92},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":93},"r":{"t":"add","l":{"t":"var","v":93},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":94},"r":{"t":"add","l":{"t":"var","v":94},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":95},"r":{"t":"add","l":{"t":"var","v":95},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":96},"r":{"t":"add","l":{"t":"var","v":96},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":97},"r":{"t":"add","l":{"t":"var","v":97},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":3}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":82}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":83}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":84}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":85}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":86}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":87}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":88}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":89}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":90}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":91}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":92}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":93}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":94}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":95}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":96}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":97}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":98},"r":{"t":"add","l":{"t":"var","v":98},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":99},"r":{"t":"add","l":{"t":"var","v":99},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":100},"r":{"t":"add","l":{"t":"var","v":100},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":101},"r":{"t":"add","l":{"t":"var","v":101},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":102},"r":{"t":"add","l":{"t":"var","v":102},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":103},"r":{"t":"add","l":{"t":"var","v":103},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":104},"r":{"t":"add","l":{"t":"var","v":104},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":105},"r":{"t":"add","l":{"t":"var","v":105},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":106},"r":{"t":"add","l":{"t":"var","v":106},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":107},"r":{"t":"add","l":{"t":"var","v":107},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":108},"r":{"t":"add","l":{"t":"var","v":108},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":109},"r":{"t":"add","l":{"t":"var","v":109},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":110},"r":{"t":"add","l":{"t":"var","v":110},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":111},"r":{"t":"add","l":{"t":"var","v":111},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":112},"r":{"t":"add","l":{"t":"var","v":112},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":113},"r":{"t":"add","l":{"t":"var","v":113},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":4}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":98}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":99}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":100}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":101}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":102}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":103}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":104}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":105}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":106}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":107}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":108}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":109}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":110}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":111}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":112}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":113}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":114},"r":{"t":"add","l":{"t":"var","v":114},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":115},"r":{"t":"add","l":{"t":"var","v":115},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":116},"r":{"t":"add","l":{"t":"var","v":116},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":117},"r":{"t":"add","l":{"t":"var","v":117},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":118},"r":{"t":"add","l":{"t":"var","v":118},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":119},"r":{"t":"add","l":{"t":"var","v":119},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":120},"r":{"t":"add","l":{"t":"var","v":120},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":121},"r":{"t":"add","l":{"t":"var","v":121},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":122},"r":{"t":"add","l":{"t":"var","v":122},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":123},"r":{"t":"add","l":{"t":"var","v":123},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":124},"r":{"t":"add","l":{"t":"var","v":124},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":125},"r":{"t":"add","l":{"t":"var","v":125},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":126},"r":{"t":"add","l":{"t":"var","v":126},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":127},"r":{"t":"add","l":{"t":"var","v":127},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":128},"r":{"t":"add","l":{"t":"var","v":128},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":129},"r":{"t":"add","l":{"t":"var","v":129},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":5}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":114}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":115}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":116}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":117}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":118}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":119}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":120}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":121}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":122}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":123}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":124}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":125}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":126}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":127}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":128}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":129}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":130},"r":{"t":"add","l":{"t":"var","v":130},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":131},"r":{"t":"add","l":{"t":"var","v":131},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":132},"r":{"t":"add","l":{"t":"var","v":132},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":133},"r":{"t":"add","l":{"t":"var","v":133},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":134},"r":{"t":"add","l":{"t":"var","v":134},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":135},"r":{"t":"add","l":{"t":"var","v":135},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":136},"r":{"t":"add","l":{"t":"var","v":136},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":137},"r":{"t":"add","l":{"t":"var","v":137},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":138},"r":{"t":"add","l":{"t":"var","v":138},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":139},"r":{"t":"add","l":{"t":"var","v":139},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":140},"r":{"t":"add","l":{"t":"var","v":140},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":141},"r":{"t":"add","l":{"t":"var","v":141},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":142},"r":{"t":"add","l":{"t":"var","v":142},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":143},"r":{"t":"add","l":{"t":"var","v":143},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":144},"r":{"t":"add","l":{"t":"var","v":144},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":145},"r":{"t":"add","l":{"t":"var","v":145},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":6}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":130}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":131}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":132}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":133}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":134}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":135}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":136}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":137}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":138}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":139}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":140}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":141}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":142}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":143}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":144}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":145}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":146},"r":{"t":"add","l":{"t":"var","v":146},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":147},"r":{"t":"add","l":{"t":"var","v":147},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":148},"r":{"t":"add","l":{"t":"var","v":148},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":149},"r":{"t":"add","l":{"t":"var","v":149},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":150},"r":{"t":"add","l":{"t":"var","v":150},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":151},"r":{"t":"add","l":{"t":"var","v":151},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":152},"r":{"t":"add","l":{"t":"var","v":152},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":153},"r":{"t":"add","l":{"t":"var","v":153},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":154},"r":{"t":"add","l":{"t":"var","v":154},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":155},"r":{"t":"add","l":{"t":"var","v":155},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":156},"r":{"t":"add","l":{"t":"var","v":156},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":157},"r":{"t":"add","l":{"t":"var","v":157},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":158},"r":{"t":"add","l":{"t":"var","v":158},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":159},"r":{"t":"add","l":{"t":"var","v":159},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":160},"r":{"t":"add","l":{"t":"var","v":160},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":161},"r":{"t":"add","l":{"t":"var","v":161},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":7}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":146}}},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":147}}},"r":{"t":"mul","l":{"t":"const","v":-4},"r":{"t":"var","v":148}}},"r":{"t":"mul","l":{"t":"const","v":-8},"r":{"t":"var","v":149}}},"r":{"t":"mul","l":{"t":"const","v":-16},"r":{"t":"var","v":150}}},"r":{"t":"mul","l":{"t":"const","v":-32},"r":{"t":"var","v":151}}},"r":{"t":"mul","l":{"t":"const","v":-64},"r":{"t":"var","v":152}}},"r":{"t":"mul","l":{"t":"const","v":-128},"r":{"t":"var","v":153}}},"r":{"t":"mul","l":{"t":"const","v":-256},"r":{"t":"var","v":154}}},"r":{"t":"mul","l":{"t":"const","v":-512},"r":{"t":"var","v":155}}},"r":{"t":"mul","l":{"t":"const","v":-1024},"r":{"t":"var","v":156}}},"r":{"t":"mul","l":{"t":"const","v":-2048},"r":{"t":"var","v":157}}},"r":{"t":"mul","l":{"t":"const","v":-4096},"r":{"t":"var","v":158}}},"r":{"t":"mul","l":{"t":"const","v":-8192},"r":{"t":"var","v":159}}},"r":{"t":"mul","l":{"t":"const","v":-16384},"r":{"t":"var","v":160}}},"r":{"t":"mul","l":{"t":"const","v":-32768},"r":{"t":"var","v":161}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":8}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":0}}},"r":{"t":"mul","l":{"t":"const","v":-65536},"r":{"t":"var","v":1}}},"r":{"t":"mul","l":{"t":"const","v":-268435454},"r":{"t":"var","v":2}}},"r":{"t":"mul","l":{"t":"const","v":-268295646},"r":{"t":"var","v":3}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":9}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":4}}},"r":{"t":"mul","l":{"t":"const","v":-65536},"r":{"t":"var","v":5}}},"r":{"t":"mul","l":{"t":"const","v":-268435454},"r":{"t":"var","v":6}}},"r":{"t":"mul","l":{"t":"const","v":-268295646},"r":{"t":"var","v":7}}}},{"t":"lookup","table":1,"tuple":[{"t":"const","v":16},{"t":"const","v":1447185968},{"t":"var","v":0},{"t":"var","v":1},{"t":"var","v":2},{"t":"var","v":3},{"t":"var","v":4},{"t":"var","v":5},{"t":"var","v":6},{"t":"var","v":7},{"t":"var","v":10},{"t":"var","v":11},{"t":"var","v":12},{"t":"var","v":13},{"t":"var","v":14},{"t":"var","v":15},{"t":"var","v":16},{"t":"var","v":18},{"t":"var","v":19},{"t":"var","v":20},{"t":"var","v":21},{"t":"var","v":22},{"t":"var","v":23},{"t":"var","v":24},{"t":"var","v":25}]},{"t":"lookup","table":1,"tuple":[{"t":"const","v":16},{"t":"const","v":1447185969},{"t":"var","v":0},{"t":"var","v":1},{"t":"var","v":2},{"t":"var","v":3},{"t":"var","v":4},{"t":"var","v":5},{"t":"var","v":6},{"t":"var","v":7},{"t":"var","v":10},{"t":"var","v":11},{"t":"var","v":12},{"t":"var","v":13},{"t":"var","v":14},{"t":"var","v":15},{"t":"var","v":16},{"t":"var","v":26},{"t":"var","v":27},{"t":"var","v":28},{"t":"var","v":29},{"t":"var","v":30},{"t":"var","v":31},{"t":"var","v":32},{"t":"var","v":33}]},{"t":"lookup","table":8,"tuple":[{"t":"const","v":7},{"t":"var","v":8},{"t":"var","v":9},{"t":"var","v":10},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":64207},{"t":"const","v":1},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":17}]},{"t":"pi_binding","row":"first","col":17,"pi_index":0},{"t":"pi_binding","row":"first","col":18,"pi_index":1},{"t":"pi_binding","row":"first","col":19,"pi_index":2},{"t":"pi_binding","row":"first","col":20,"pi_index":3},{"t":"pi_binding","row":"first","col":21,"pi_index":4},{"t":"pi_binding","row":"first","col":22,"pi_index":5},{"t":"pi_binding","row":"first","col":23,"pi_index":6},{"t":"pi_binding","row":"first","col":24,"pi_index":7},{"t":"pi_binding","row":"first","col":25,"pi_index":8},{"t":"pi_binding","row":"first","col":26,"pi_index":9},{"t":"pi_binding","row":"first","col":27,"pi_index":10},{"t":"pi_binding","row":"first","col":28,"pi_index":11},{"t":"pi_binding","row":"first","col":29,"pi_index":12},{"t":"pi_binding","row":"first","col":30,"pi_index":13},{"t":"pi_binding","row":"first","col":31,"pi_index":14},{"t":"pi_binding","row":"first","col":32,"pi_index":15},{"t":"pi_binding","row":"first","col":33,"pi_index":16}],"hash_sites":[],"ranges":[]}"#

#guard emitVmJson2 wideValueBindingDesc == WIDE_VALUE_BINDING_GOLDEN

#assert_axioms wideValueBindingDesc

end Dregg2.Circuit.Emit.WideValueBindingEmit
