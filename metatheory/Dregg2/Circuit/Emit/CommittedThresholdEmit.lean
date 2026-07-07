/-
# Dregg2.Circuit.Emit.CommittedThresholdEmit — the emit-from-Lean descriptor for the
committed-threshold predicate family (`circuit/src/committed_threshold.rs` +
`circuit/src/dsl/committed_threshold.rs`).

## What this file IS

A REAL `EffectVmDescriptor2` that DECLARES, in the IR-v2 grammar, the committed-threshold
statement: "I know a private value ≥ a committed threshold, and the threshold commitment matches a
public Poseidon2 commitment" — WITHOUT revealing either the value or the threshold. It replaces the
hand-written `CommittedThresholdAir` (`circuit/src/committed_threshold.rs`) SEMANTICS with an
emitted descriptor that maps every constraint the production DSL twin
(`crate::dsl::committed_threshold`) enforces onto a `VmConstraint2`:

  * `c1` threshold_commitment == pi[0]        → `PiBinding .first 34 0`
  * `c2` fact_commitment == pi[1]             → `PiBinding .first 35 1`
  * the HASH BINDING poseidon2_result == hash_2_to_1(threshold, blinding)
                                              → an arity-2 `Poseidon2Chip` LOOKUP (out0 = col 36)
  * `c3` poseidon2_result == threshold_commitment (Equality) → Base `.gate (col36 − col34)`
  * `c4` diff == private_value − threshold    → Base `.gate (col3 − col0 + col1)`
  * `c5` Σ_{i<30} bit_i·2^i == diff (bit recomposition) → Base `.gate (Σ 2^i·bit_i − diff)`
  * `bit_i·(bit_i−1) == 0` per bit (Binary)   → 30 × Base `.gate (bit_i·(bit_i−1))`
  * `c7` diff_bit(29) == 0 (high bit, so diff < 2^29 < p/2) → Base `.gate (col33)`

### ⚑ THE SOUNDNESS FIX this emission carries (load-bearing)

The hand `CommittedThresholdAir::eval_constraints` NEVER enforces
`Poseidon2(threshold, blinding) == poseidon2_result` — its only tie is `c3`
(`poseidon2_result == threshold_commitment`), so a hand-AIR prover could set the pair to ANY equal
value with NO genuine hash preimage. The production DSL twin fixes this with a `Hash2to1`
constraint. This emission carries that fix as the arity-2 chip lookup: out0 (col 36) is FORCED to
`hash_2_to_1(threshold, blinding)` by the `TID_P2` chip AIR (`chip_absorb_all_lanes(2, ·)[0]`), so a
forged `poseidon2_result` names a digest no genuine chip row serves → UNSAT. The gate test's
`forged_poseidon2_result_refuses` canary bites on EXACTLY this tooth.

## Trace column layout (width 44 = the hand AIR's 37 + 7 chip out-lane columns)

`private_value 0 · threshold 1 · blinding 2 · diff 3 · diff_bits[0..30] 4..33 ·
threshold_commitment 34 · fact_commitment 35 · poseidon2_result 36 · chip lanes 1..7 at 37..43`
(the chip's out-lanes 1..7 are auxiliary witness columns the prover fills from the genuine
permutation; out0 IS the `poseidon2_result` column).

## Axiom hygiene

Definitional descriptor + a byte-pinned `#guard` on its wire string + two genuinely-proven,
non-vacuous semantic lemmas (`binary_body_zero_iff` — the range-gadget crux, TRUE iff the bit is
0/1; `diff_body_zero_iff` — the difference gate). `#assert_axioms` on both ⊆ {} (pure algebra).
NEW file; imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Circuit.Emit.CommittedThresholdEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId chipLookupTuple CHIP_RATE CHIP_OUT_LANES
   emitVmJson2)

set_option autoImplicit false

/-! ## §1 — The trace column layout (matching `committed_threshold.rs::col`, 30-bit range). -/

/-- The private attribute value (witness). -/
def PRIVATE_VALUE : Nat := 0
/-- The verifier's threshold (witness — NOT public input). -/
def THRESHOLD : Nat := 1
/-- The verifier's blinding randomness (witness). -/
def BLINDING : Nat := 2
/-- The computed difference `private_value − threshold`. -/
def DIFF : Nat := 3
/-- Start of the 30 bit-decomposition columns (`diff_bit i = DIFF_BITS_START + i`). -/
def DIFF_BITS_START : Nat := 4
/-- The number of range-check bits (`committed_threshold.rs::COMMITTED_DIFF_BITS`). With 30 bits the
high bit is bit 29; `bit29 = 0 ⇒ diff < 2^29 = 536870912 < p/2`, proving `value ≥ threshold`. -/
def COMMITTED_DIFF_BITS : Nat := 30
/-- The column of `diff_bit i`. -/
def diffBit (i : Nat) : Nat := DIFF_BITS_START + i
/-- The threshold commitment (bound to public input 0). -/
def THRESHOLD_COMMITMENT : Nat := DIFF_BITS_START + COMMITTED_DIFF_BITS   -- 34
/-- The fact commitment (bound to public input 1). -/
def FACT_COMMITMENT : Nat := THRESHOLD_COMMITMENT + 1                     -- 35
/-- The computed `Poseidon2(threshold, blinding)` = the chip lookup's out0 (digest) column. -/
def POSEIDON2_RESULT : Nat := FACT_COMMITMENT + 1                         -- 36

/-- The seven exposed permutation out-lane columns 1..7 of the arity-2 chip lookup (out0 is the
`POSEIDON2_RESULT` digest column above; lanes 1..7 are witnessed by the chip AIR's `out[i] == lane[i]`
equalities and filled by the prover). -/
def CHIP_LANES : List Nat := [37, 38, 39, 40, 41, 42, 43]

/-- Total main-trace width: the hand AIR's 37 columns + 7 chip out-lane columns. -/
def CT_WIDTH : Nat := 44

/-! ## §2 — The constraint bodies. -/

/-- `2^n` as an `Int`, kernel-reducible in O(n) (avoids `HPow` unfolding in `#guard`). -/
def pow2 : Nat → Int
  | 0     => 1
  | n + 1 => 2 * pow2 n

/-- `a − b` as an `EmittedExpr` (`.add a ((-1)·b)`, the emitter's canonical subtraction). -/
def subE (a b : Nat) : EmittedExpr := .add (.var a) (.mul (.const (-1)) (.var b))

/-- The HASH-BINDING chip lookup: an arity-2 `Poseidon2Chip` absorb of `[threshold, blinding]`,
binding out0 to `POSEIDON2_RESULT` (col 36) and out-lanes 1..7 to `CHIP_LANES`. The chip AIR forces
`out0 = hash_2_to_1(threshold, blinding)` — the soundness fix the hand `eval_constraints` omits. -/
def hash2Lookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2,
    chipLookupTuple [.var THRESHOLD, .var BLINDING] POSEIDON2_RESULT CHIP_LANES⟩

/-- `c3`: `poseidon2_result − threshold_commitment` (the DSL `Equality` gate). -/
def c3Body : EmittedExpr := subE POSEIDON2_RESULT THRESHOLD_COMMITMENT

/-- `c4`: `diff − private_value + threshold` (the DSL diff `Polynomial`, `= diff − (value − thr)`). -/
def c4Body : EmittedExpr :=
  .add (.var DIFF) (.add (.mul (.const (-1)) (.var PRIVATE_VALUE)) (.var THRESHOLD))

/-- `c5`: `Σ_{i<30} 2^i·bit_i − diff` (the DSL bit-recomposition `Polynomial`). Right-folded over the
30 bit columns with `−diff` as the innermost term (matched byte-for-byte on the Rust side). -/
def recompBody : EmittedExpr :=
  (List.range COMMITTED_DIFF_BITS).foldr
    (fun i acc => .add (.mul (.const (pow2 i)) (.var (diffBit i))) acc)
    (.mul (.const (-1)) (.var DIFF))

/-- The per-bit binary gate body `bit_i·(bit_i − 1)` (the DSL `Binary` constraint). -/
def binBody (i : Nat) : EmittedExpr :=
  .mul (.var (diffBit i)) (.add (.var (diffBit i)) (.const (-1)))

/-! ## §3 — The descriptor. -/

/-- The 30 per-bit binary gates. -/
def binaryGates : List VmConstraint2 :=
  (List.range COMMITTED_DIFF_BITS).map (fun i => VmConstraint2.base (.gate (binBody i)))

/-- **`committedThresholdDesc`** — the committed-threshold predicate descriptor. Constraint order:
the hash-binding chip lookup, the equality/diff/recomposition gates, the 30 binary gates, the two
commitment PI pins, and the high-bit-zero gate. The chip table (`TID_P2`) is IMPLICITLY present
(Presence-detected from the lookup), so `tables` is empty (as `node8`/`merkle-membership` leave it). -/
def committedThresholdDesc : EffectVmDescriptor2 :=
  { name        := "dregg-committed-threshold::poseidon2-v2"
  , traceWidth  := CT_WIDTH
  , piCount     := 2
  , tables      := []
  , constraints :=
      [ hash2Lookup
      , .base (.gate c3Body)
      , .base (.gate c4Body)
      , .base (.gate recompBody) ]
      ++ binaryGates
      ++ [ .base (.piBinding VmRow.first THRESHOLD_COMMITMENT 0)
         , .base (.piBinding VmRow.first FACT_COMMITMENT 1)
         , .base (.gate (.var (diffBit (COMMITTED_DIFF_BITS - 1)))) ]
  , hashSites   := []
  , ranges      := [] }

/-! ## §4 — The byte-pinned wire golden (the Rust decoder ingests THIS string). -/

#guard emitVmJson2 committedThresholdDesc ==
  "{\"name\":\"dregg-committed-threshold::poseidon2-v2\",\"ir\":2,\"trace_width\":44,\"public_input_count\":2,\"tables\":[],\"constraints\":[{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":2},{\"t\":\"var\",\"v\":1},{\"t\":\"var\",\"v\":2},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":36},{\"t\":\"var\",\"v\":37},{\"t\":\"var\",\"v\":38},{\"t\":\"var\",\"v\":39},{\"t\":\"var\",\"v\":40},{\"t\":\"var\",\"v\":41},{\"t\":\"var\",\"v\":42},{\"t\":\"var\",\"v\":43}]},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":36},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":34}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":0}},\"r\":{\"t\":\"var\",\"v\":1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":4}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"var\",\"v\":5}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":6}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":8},\"r\":{\"t\":\"var\",\"v\":7}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":16},\"r\":{\"t\":\"var\",\"v\":8}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":9}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":64},\"r\":{\"t\":\"var\",\"v\":10}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":128},\"r\":{\"t\":\"var\",\"v\":11}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":12}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":512},\"r\":{\"t\":\"var\",\"v\":13}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1024},\"r\":{\"t\":\"var\",\"v\":14}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2048},\"r\":{\"t\":\"var\",\"v\":15}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":4096},\"r\":{\"t\":\"var\",\"v\":16}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":8192},\"r\":{\"t\":\"var\",\"v\":17}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":16384},\"r\":{\"t\":\"var\",\"v\":18}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":32768},\"r\":{\"t\":\"var\",\"v\":19}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":65536},\"r\":{\"t\":\"var\",\"v\":20}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":131072},\"r\":{\"t\":\"var\",\"v\":21}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":262144},\"r\":{\"t\":\"var\",\"v\":22}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":524288},\"r\":{\"t\":\"var\",\"v\":23}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1048576},\"r\":{\"t\":\"var\",\"v\":24}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2097152},\"r\":{\"t\":\"var\",\"v\":25}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":4194304},\"r\":{\"t\":\"var\",\"v\":26}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":8388608},\"r\":{\"t\":\"var\",\"v\":27}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":16777216},\"r\":{\"t\":\"var\",\"v\":28}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":33554432},\"r\":{\"t\":\"var\",\"v\":29}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":67108864},\"r\":{\"t\":\"var\",\"v\":30}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":134217728},\"r\":{\"t\":\"var\",\"v\":31}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":268435456},\"r\":{\"t\":\"var\",\"v\":32}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":536870912},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":3}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":12},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":12},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":24},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":24},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":26},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":26},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":27},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":27},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":28},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":28},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":29},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":29},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":30},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":30},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":31},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":31},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":33},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":33},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":34,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":35,\"pi_index\":1},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":33}}],\"hash_sites\":[],\"ranges\":[]}"

/-! ## §5 — Genuinely-proven, non-vacuous semantic lemmas. -/

/-- **The range-gadget crux.** The per-bit binary gate body is zero over `ℤ` EXACTLY when the bit
column is 0 or 1 — TRUE for a genuine bit, FALSE otherwise. This is the tooth that makes the 30-bit
recomposition an honest range proof (a non-binary "bit" can forge the weighted sum). -/
theorem binary_body_zero_iff (i : Nat) (a : Assignment) :
    (binBody i).eval a = 0 ↔ a (diffBit i) = 0 ∨ a (diffBit i) = 1 := by
  simp only [binBody, EmittedExpr.eval]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by omega)
  · rintro (h | h) <;> rw [h] <;> ring

/-- **The difference gate.** `c4Body` is zero EXACTLY when `diff = private_value − threshold` — the
witnessed difference is the honest one. TRUE when it agrees, FALSE otherwise. -/
theorem diff_body_zero_iff (a : Assignment) :
    c4Body.eval a = 0 ↔ a DIFF = a PRIVATE_VALUE - a THRESHOLD := by
  simp only [c4Body, EmittedExpr.eval]
  constructor <;> intro h <;> omega

-- Non-vacuity witnesses: the binary gate ACCEPTS a genuine bit (0 or 1) and REJECTS a "2".
#guard decide ((binBody 5).eval (fun j => if j = diffBit 5 then 1 else 0) = 0)
#guard decide ((binBody 5).eval (fun j => if j = diffBit 5 then 0 else 0) = 0)
#guard decide (¬ ((binBody 5).eval (fun j => if j = diffBit 5 then 2 else 0) = 0))
-- Non-vacuity: the diff gate ACCEPTS `diff = value − thr` and REJECTS an off-by-one diff.
#guard decide (c4Body.eval (fun j => if j = DIFF then 5 else if j = PRIVATE_VALUE then 12
                                     else if j = THRESHOLD then 7 else 0) = 0)
#guard decide (¬ (c4Body.eval (fun j => if j = DIFF then 6 else if j = PRIVATE_VALUE then 12
                                        else if j = THRESHOLD then 7 else 0) = 0))

-- Shape pins.
#guard committedThresholdDesc.traceWidth == CT_WIDTH
#guard committedThresholdDesc.piCount == 2
#guard committedThresholdDesc.constraints.length == 4 + COMMITTED_DIFF_BITS + 3
#guard (chipLookupTuple [.var THRESHOLD, .var BLINDING] POSEIDON2_RESULT CHIP_LANES).length
         == CHIP_RATE + 1 + CHIP_OUT_LANES

#assert_axioms binary_body_zero_iff
#assert_axioms diff_body_zero_iff

end Dregg2.Circuit.Emit.CommittedThresholdEmit
