/-
# Dregg2.Circuit.Emit.EffectActionBindingEmit — the emit-from-Lean twin of the generalized
effect-action binding AIR (`circuit/src/effect_action_air.rs`).

## What this file IS (the family: `effect_action`)

The binding schema binds an effect's typed parameters into a STARK proof's public inputs at full
fidelity: a 32-byte field becomes 8 BabyBear limbs (4 bytes each), a u64 amount becomes
`AMOUNT_LIMBS = 4` limbs of `LIMB_BITS = 16` bits, and each such limb is pinned to a row-0 trace
column by a boundary constraint. A transition constraint forces every row to equal row 0, so a
malicious prover cannot stash a different parameter set in a later row. One schema (`Burn`)
additionally witnesses the four-limb u64 subtraction `new_balance == old_balance - amount` with a
three-bit borrow CHAIN, and pins the `was_burn` disclosure flag to `1`.

## ⚑ THE FLAG DAY THIS FILE IS (2026-08-06): 32-bit limbs have no BabyBear felt

Until this commit a u64 amount was TWO 32-bit limbs and the borrow rode a coefficient
`TWO_POW_32 = 4294967296`. BabyBear's `p = 2013265921 < 2^32`, so **neither the coefficient nor the
limbs fit a felt**:

  * `parse_vm_descriptor2` REFUSED the emitted descriptor outright —
    *"constant at byte 3619 does not fit a BabyBear felt (10 decimal digits, p_babybear =
    2013265921)"* — so `dregg-effect-burn-v1` could not be read by its own parser. That refusal
    predates the `challenges` flag day; the retired inline golden failed one check EARLIER (the
    missing `"challenges"` key), so the deeper refusal was never reached.
  * and `encode_amount`'s 32-bit limbs are not INJECTIVE into a felt either: `BabyBear::new` reduces,
    so `lo = 0` and `lo = p` are the same cell. A "full-fidelity binding" that collides on the
    amount is not full fidelity.

Fixing only the coefficient (writing `2^32 mod p`) would be laundering: the gate would parse and its
ℤ reading would no longer be the subtraction it claims. The ENCODING is what was wrong. `16` is the
felt-sized width the rest of the tree already uses for exactly this fact — `EffectVmEmitBurn`'s
availability weld and `CrossCellConservation` both do a balance borrow chain on **15-bit** limbs
precisely so no residual reaches `p`, mirroring `vault_weld.rs::borrow_compare`. At 16 bits a u64 is
exactly four limbs (`4·16 = 64`, no wasted capacity, no truncation), the borrow weight is
`2^16 = 65536`, and every gate body is bounded by `2^18 ≪ p` (`chainBody_abs_lt_p`), so `p ∣ body`
FORCES `body = 0` over ℤ. That is the whole difference between a gate whose integer semantics
survive the prover's field and one whose do not.

⚠ **What re-emits / refuses to load.** `AMOUNT_LIMBS` 2 → 4 in `circuit/src/effect_action_air.rs`,
so EVERY schema's `pi_count` grows by `2·amount_count` and every previously-produced effect-binding
proof fails `verify_vm_descriptor2` on the PI count — it cannot be reinterpreted, only rejected. The
burn aux block grows 1 → 3 (the borrow chain), so `SCHEMA_BURN.width()` is 27, not 17. Both Rust
goldens (`circuit-prove/tests/effect_action_emit_gate.rs`,
`circuit-prove/tests/effect_action_extra_tamper_audit.rs`) and
`circuit/tests/burn_air_conservation_gap.rs`'s counts move with it.

## The constraint → IR2 map

  * Row-continuity `next[c] - local[c] == 0` for every column `c ∈ [0, width)`
    ↦ `VmConstraint2.windowGate ⟨Nxt c - Loc c, onTransition := true⟩`, one per column.
  * PI binding `local[c] == public_inputs[c]` on row 0 for every `c ∈ [0, pi_count)`
    ↦ `VmConstraint2.base (VmConstraint.piBinding .first c c)`.
  * Domain separation ↦ the descriptor `name` (the schema's exact `kind_name`), so a proof for
    kind A cannot Fiat-Shamir-replay as B.
  * Burn borrow chain, limbs 0..2: `new_i + amt_i + b_{i-1} - 2^16·b_i - old_i == 0` ↦ three Base
    gates (`b_{-1}` absent on limb 0).
  * Burn borrow chain, limb 3: `new_3 + amt_3 + b_2 - old_3 == 0` ↦ a Base gate. ⚑ It carries NO
    outgoing borrow, which is the availability tooth: a closing chain with no final borrow is
    exactly `amount ≤ old_balance`. The retired two-limb shape had `borrow*2^32` on the low limb and
    a bare `+borrow` on the high one, and enforced no such thing.
  * Burn borrow booleanity `b_i·(b_i-1) == 0` ↦ three Base gates.
  * Burn disclosure pins `wb_0 - 1 == 0`, `wb_1 == 0`, `wb_2 == 0`, `wb_3 == 0` ↦ four Base gates.

The three borrow bits live in prover-supplied AUX columns at `pi_count + i` (bound to no PI).

⚑ **The largest coefficient any emitted gate carries is `2^16`** (`burnGates_coeffs_fit_felt`). The
SPEC below names `2^32` and `2^48` — in `u64Of`, the recomposition a reader decodes the limbs with —
and that is fine and is the point: a spec may name a 2^64-scale number, a GATE BODY may not.

## What is NOT here

No range lookup pins the limbs to `[0, 2^16)`. The exactness theorems below therefore carry
`BurnLimbsCanonical` as a NAMED hypothesis and never assume it — see `§5`, which states precisely
what a satisfying trace forces without it (the per-limb field congruences) and with it (the exact
`old_balance = new_balance + amount` over ℤ, plus `amount ≤ old_balance`). Closing that hypothesis in
the circuit is a `.lookup` into a declared `rangeTableDef 16` table on each of the twelve chain
limbs; it is a table/lookup shape change to this descriptor, not a coefficient one, and it is the
next item on this file.

## Axiom hygiene
Definitional descriptors + byte-pinned wire goldens + genuinely-proven, non-vacuous semantic lemmas
(each TRUE and FALSE witnessed, as NAMED theorems). `#assert_axioms` on the lemmas is `⊆ {}`.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.GateExpr

namespace Dregg2.Circuit.Emit.EffectActionBindingEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 WindowExpr WindowConstraint emitVmJson2)

set_option autoImplicit false

/-! ## §0 — The felt-sized amount encoding.

`LIMB_BITS = 16` and `AMOUNT_LIMBS = 4`: a u64 is EXACTLY four limbs, every limb is `< 2^16 ≪ p`,
and the borrow weight `2^16` is a felt. This is the whole repair — see the header. -/

/-- Bits per amount limb. -/
def LIMB_BITS : Nat := 16
/-- Limbs per u64 amount: `4·16 = 64`, exact, no truncation. -/
def AMOUNT_LIMBS : Nat := 4
/-- The limb base / borrow weight, `2^16`. **This is the largest constant any emitted gate body
carries**, and `65536 < 2013265921 = p`. -/
def LIMB_BASE : Int := 65536

theorem limb_base_fits_felt : LIMB_BASE < 2013265921 := by decide
theorem limbs_cover_u64 : AMOUNT_LIMBS * LIMB_BITS = 64 := by decide

/-- ⚑ **WHY WIDENING WAS THE ONLY REPAIR — THE PIGEONHOLE, AS A THEOREM.** Two BabyBear felts
carry `p² = 4_053_239_737_456_637_441` distinct pairs and a u64 has `2^64` values, so `p² < 2^64`
and by pigeonhole EVERY 2-felt encoding of a u64 collides — on average 4.55 amounts per pair. No
choice of coefficients or reduction could have fixed the retired 2 × 32-bit split; only widening
could. This is what forces `AMOUNT_LIMBS = 4`.

⚑ **RE-HOMED HERE 2026-08-07.** This statement lived only in `BridgeActionEmit.two_felts_cannot_
carry_a_u64` and in `bridge_action_witness.rs`'s test of the same name. Both were deleted with the
bridge-action binding AIR, and the fact is not about that AIR — it is about BabyBear and u64, and
it is the reason THIS family's width is 4. A fact worth asserting is worth keeping named. -/
theorem two_felts_cannot_carry_a_u64 : 2013265921 * 2013265921 < 2 ^ 64 := by decide

/-- Four 16-bit limbs are EXACTLY enough and not more: `(2^16)^4 = 2^64`. -/
theorem four_limbs_carry_u64_exactly : (2 ^ LIMB_BITS) ^ AMOUNT_LIMBS = 2 ^ 64 := by decide

/-- Each limb fits a felt without reduction — the structural reason injectivity holds at all. -/
theorem amount_limb_fits_felt : 2 ^ LIMB_BITS < 2013265921 := by decide

/-- The ℤ value a canonical four-limb amount decodes to. ⚑ This is the SPEC's recomposition; it
names `2^32` and `2^48`, which is exactly why it may never be a gate coefficient. -/
def u64Of (l0 l1 l2 l3 : ℤ) : ℤ := l0 + 65536 * l1 + 4294967296 * l2 + 281474976710656 * l3

/-! ## §1 — The generic binding constraints (parametric over every schema). -/

/-- The continuity `window_gate` body for column `c`: `Nxt c - Loc c`. -/
def contWindowBody (c : Nat) : WindowExpr :=
  Dregg2.Circuit.GateExpr.render Dregg2.Circuit.GateExpr.toWindow (Dregg2.Circuit.GateExpr.gThread c c)

/-- ⚑ **THE BYTE PIN.** `contWindowBody` is `GateExpr.gThread` at the window view -- the SAME object
`AccumulatorNonRevocationEmit.constBody`,
`EffectActionBindingEmit.contWindowBody`, `ExactNullifierAafiRotatedStateWeld.carryBody` and
`DyckStackEmit.wThread` each wrote out separately. `rfl`, for every column: no emitted byte moved. -/
theorem contWindowBody_eq (c : Nat) :
    contWindowBody c = WindowExpr.add (.nxt c) (.mul (.const (-1)) (.loc c)) := rfl

/-- The per-column continuity constraint (asserted on the transition domain). -/
def contGate (c : Nat) : VmConstraint2 :=
  .windowGate { body := contWindowBody c, onTransition := true }

/-- Row-continuity over ALL `width` columns (incl. the Burn borrow aux). -/
def contGates (width : Nat) : List VmConstraint2 :=
  (List.range width).map contGate

/-- The per-slot PI binding: row-0 column `c` equals public input `c`. -/
def piGate (c : Nat) : VmConstraint2 :=
  .base (.piBinding .first c c)

/-- The full PI-binding boundary (one pin per public-input slot). -/
def piGates (piCount : Nat) : List VmConstraint2 :=
  (List.range piCount).map piGate

/-- **`effectActionDesc name fieldCount amountCount`** — a PURE-BINDING schema descriptor:
`pi_count = fieldCount*8 + amountCount*4` columns, continuity over all of them, one PI pin per slot,
no aux, no extra tables. The `name` is the schema's exact `kind_name` (Fiat-Shamir separation). -/
def effectActionDesc (name : String) (fieldCount amountCount : Nat) : EffectVmDescriptor2 :=
  let pi := fieldCount * 8 + amountCount * 4
  { name        := name
  , traceWidth  := pi
  , piCount     := pi
  , tables      := []
  , constraints := contGates pi ++ piGates pi
  , hashSites   := []
  , ranges      := [] }

/-! ## §2 — The `Burn` schema's algebraic gates.

Burn layout (`SCHEMA_BURN`: 1 field, 4 amounts): field limbs 0..8, then `old_balance` (8..12),
`new_balance` (12..16), `amount` (16..20), `was_burn_flag` (20..24); the three prover-supplied
borrow bits are columns 24, 25, 26 = `pi_count + i`. -/

def B_OLD0 : Nat := 8
def B_OLD1 : Nat := 9
def B_OLD2 : Nat := 10
def B_OLD3 : Nat := 11
def B_NEW0 : Nat := 12
def B_NEW1 : Nat := 13
def B_NEW2 : Nat := 14
def B_NEW3 : Nat := 15
def B_AMT0 : Nat := 16
def B_AMT1 : Nat := 17
def B_AMT2 : Nat := 18
def B_AMT3 : Nat := 19
def B_WB0 : Nat := 20
def B_WB1 : Nat := 21
def B_WB2 : Nat := 22
def B_WB3 : Nat := 23
def B_BRW0 : Nat := 24
def B_BRW1 : Nat := 25
def B_BRW2 : Nat := 26

/-- Borrow-chain limb 0: `new_0 + amt_0 - 2^16·b_0 - old_0`. -/
def cSub0Body : EmittedExpr :=
  .add (.add (.var B_NEW0) (.var B_AMT0))
       (.add (.mul (.const (-LIMB_BASE)) (.var B_BRW0))
             (.mul (.const (-1)) (.var B_OLD0)))

/-- Borrow-chain limb 1: `new_1 + amt_1 + b_0 - 2^16·b_1 - old_1`. -/
def cSub1Body : EmittedExpr :=
  .add (.add (.var B_NEW1) (.var B_AMT1))
       (.add (.var B_BRW0)
             (.add (.mul (.const (-LIMB_BASE)) (.var B_BRW1))
                   (.mul (.const (-1)) (.var B_OLD1))))

/-- Borrow-chain limb 2: `new_2 + amt_2 + b_1 - 2^16·b_2 - old_2`. -/
def cSub2Body : EmittedExpr :=
  .add (.add (.var B_NEW2) (.var B_AMT2))
       (.add (.var B_BRW1)
             (.add (.mul (.const (-LIMB_BASE)) (.var B_BRW2))
                   (.mul (.const (-1)) (.var B_OLD2))))

/-- Borrow-chain limb 3 (TOP): `new_3 + amt_3 + b_2 - old_3`. ⚑ NO outgoing borrow — the chain
closes, which is exactly `amount ≤ old_balance` (`burn_no_underflow`). -/
def cSub3Body : EmittedExpr :=
  .add (.add (.var B_NEW3) (.var B_AMT3))
       (.add (.var B_BRW2) (.mul (.const (-1)) (.var B_OLD3)))

/-- A borrow-bit booleanity body `b·(b-1)`. -/
def cBoolBody (b : Nat) : EmittedExpr :=
  Dregg2.Circuit.GateExpr.render Dregg2.Circuit.GateExpr.toEmitted
    (Dregg2.Circuit.GateExpr.gBool (.leaf b))

theorem cBoolBody_eq (b : Nat) :
    cBoolBody b = .mul (.var b) (.add (.var b) (.const (-1))) := rfl

/-- Disclosure pin, limb 0: `wb_0 - 1 == 0`. -/
def cWasBurn0Body : EmittedExpr := .add (.var B_WB0) (.const (-1))
/-- Disclosure pin, limbs 1..3: the flag is exactly `1`, so its upper limbs are `0`. -/
def cWasBurn1Body : EmittedExpr := .var B_WB1
def cWasBurn2Body : EmittedExpr := .var B_WB2
def cWasBurn3Body : EmittedExpr := .var B_WB3

/-- The eleven Burn algebraic Base gates, in chain order. -/
def burnGates : List VmConstraint2 :=
  [ .base (.gate cSub0Body)
  , .base (.gate cSub1Body)
  , .base (.gate cSub2Body)
  , .base (.gate cSub3Body)
  , .base (.gate (cBoolBody B_BRW0))
  , .base (.gate (cBoolBody B_BRW1))
  , .base (.gate (cBoolBody B_BRW2))
  , .base (.gate cWasBurn0Body)
  , .base (.gate cWasBurn1Body)
  , .base (.gate cWasBurn2Body)
  , .base (.gate cWasBurn3Body) ]

/-! ## §3 — Two concrete descriptors. -/

/-- **`revokeCapabilityDesc`** — `SCHEMA_REVOKE_CAPABILITY` (1 field, 1 amount): pure binding,
`pi_count = 12`, width 12. -/
def revokeCapabilityDesc : EffectVmDescriptor2 :=
  effectActionDesc "dregg-effect-revoke-capability-v1" 1 1

/-- **`burnDesc`** — `SCHEMA_BURN` (1 field, 4 amounts + 3 borrow aux): `pi_count = 24`, width 27,
with the eleven algebraic gates appended past the continuity + PI-binding block. -/
def burnDesc : EffectVmDescriptor2 :=
  { name        := "dregg-effect-burn-v1"
  , traceWidth  := 27
  , piCount     := 24
  , tables      := []
  , constraints := contGates 27 ++ piGates 24 ++ burnGates
  , hashSites   := []
  , ranges      := [] }

/-! ## §4 — The wire goldens (the Rust decoder ingests THESE strings). -/

#guard emitVmJson2 revokeCapabilityDesc == "{\"name\":\"dregg-effect-revoke-capability-v1\",\"ir\":2,\"trace_width\":12,\"public_input_count\":12,\"challenges\":0,\"tables\":[],\"constraints\":[{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":0}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":1}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":2}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":3}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":4}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":5}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":6}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":7}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":8},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":8}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":9},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":9}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":10},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":10}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":11},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":11}}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":0,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":1,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":2,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":3,\"pi_index\":3},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":4,\"pi_index\":4},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":5,\"pi_index\":5},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":6,\"pi_index\":6},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":7,\"pi_index\":7},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":8,\"pi_index\":8},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":9,\"pi_index\":9},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":10,\"pi_index\":10},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":11,\"pi_index\":11}],\"hash_sites\":[],\"ranges\":[]}"

#guard emitVmJson2 burnDesc == "{\"name\":\"dregg-effect-burn-v1\",\"ir\":2,\"trace_width\":27,\"public_input_count\":24,\"challenges\":0,\"tables\":[],\"constraints\":[{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":0}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":1}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":2}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":3}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":4}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":5}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":6}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":7}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":8},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":8}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":9},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":9}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":10},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":10}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":11},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":11}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":12},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":12}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":13},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":13}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":14},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":14}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":15},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":15}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":16},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":16}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":17},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":17}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":18},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":18}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":19},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":19}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":20},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":20}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":21},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":21}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":22},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":22}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":23},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":23}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":24},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":24}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":25},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":25}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":26},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":26}}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":0,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":1,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":2,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":3,\"pi_index\":3},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":4,\"pi_index\":4},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":5,\"pi_index\":5},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":6,\"pi_index\":6},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":7,\"pi_index\":7},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":8,\"pi_index\":8},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":9,\"pi_index\":9},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":10,\"pi_index\":10},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":11,\"pi_index\":11},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":12,\"pi_index\":12},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":13,\"pi_index\":13},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":14,\"pi_index\":14},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":15,\"pi_index\":15},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":16,\"pi_index\":16},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":17,\"pi_index\":17},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":18,\"pi_index\":18},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":19,\"pi_index\":19},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":20,\"pi_index\":20},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":21,\"pi_index\":21},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":22,\"pi_index\":22},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":23,\"pi_index\":23},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":12},\"r\":{\"t\":\"var\",\"v\":16}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-65536},\"r\":{\"t\":\"var\",\"v\":24}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":8}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"var\",\"v\":17}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":24},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-65536},\"r\":{\"t\":\"var\",\"v\":25}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":9}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"var\",\"v\":18}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-65536},\"r\":{\"t\":\"var\",\"v\":26}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":10}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"var\",\"v\":19}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":26},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":11}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":24},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":24},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":26},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":26},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":21}},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":22}},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":23}}],\"hash_sites\":[],\"ranges\":[]}"

/-! ## §5 — The constraint teeth.

Two layers, and the boundary between them is the point of this file.

**Layer A (unconditional).** Each gate body vanishes EXACTLY when its per-limb relation holds. These
are ℤ statements about the body, and because every coefficient is `≤ 2^16` they are also what the
prover's field reading says on canonical cells.

**Layer B (under `BurnLimbsCanonical`).** The chain composes to the EXACT u64 identity
`old_balance = new_balance + amount` over ℤ, and to `amount ≤ old_balance`. The hypothesis is what a
range lookup would discharge; it is named, never assumed. -/

theorem cont_zero_iff (env : VmRowEnv) (c : Nat) :
    (contWindowBody c).eval env = 0 ↔ env.nxt c = env.loc c := by
  simp only [contWindowBody_eq, WindowExpr.eval]
  constructor <;> intro h <;> omega

theorem cSub0_zero_iff (a : Assignment) :
    cSub0Body.eval a = 0 ↔ a B_NEW0 + a B_AMT0 = a B_OLD0 + LIMB_BASE * a B_BRW0 := by
  simp only [cSub0Body, EmittedExpr.eval, LIMB_BASE]
  constructor <;> intro h <;> omega

theorem cSub1_zero_iff (a : Assignment) :
    cSub1Body.eval a = 0 ↔
      a B_NEW1 + a B_AMT1 + a B_BRW0 = a B_OLD1 + LIMB_BASE * a B_BRW1 := by
  simp only [cSub1Body, EmittedExpr.eval, LIMB_BASE]
  constructor <;> intro h <;> omega

theorem cSub2_zero_iff (a : Assignment) :
    cSub2Body.eval a = 0 ↔
      a B_NEW2 + a B_AMT2 + a B_BRW1 = a B_OLD2 + LIMB_BASE * a B_BRW2 := by
  simp only [cSub2Body, EmittedExpr.eval, LIMB_BASE]
  constructor <;> intro h <;> omega

theorem cSub3_zero_iff (a : Assignment) :
    cSub3Body.eval a = 0 ↔ a B_NEW3 + a B_AMT3 + a B_BRW2 = a B_OLD3 := by
  simp only [cSub3Body, EmittedExpr.eval]
  constructor <;> intro h <;> omega

theorem cBool_zero_iff (a : Assignment) (b : Nat) :
    (cBoolBody b).eval a = 0 ↔ a b = 0 ∨ a b = 1 := by
  simp only [cBoolBody_eq, EmittedExpr.eval]
  rw [mul_eq_zero]; omega

theorem cWasBurn0_zero_iff (a : Assignment) :
    cWasBurn0Body.eval a = 0 ↔ a B_WB0 = 1 := by
  simp only [cWasBurn0Body, EmittedExpr.eval]
  constructor <;> intro h <;> omega

/-! ### The felt-fit facts — the reason this encoding exists. -/

/-- **Every emitted Burn gate coefficient fits a BabyBear felt.** The largest is `2^16 = 65536`;
the retired shape's was `2^32 = 4294967296 > p`. -/
theorem burnGates_coeffs_fit_felt : LIMB_BASE < 2013265921 ∧ (1 : Int) < 2013265921 := by decide

/-- **`BurnLimbsCanonical env`** — every chain limb is in `[0, 2^16)` and every borrow bit in
`{0,1}`. This is what a `rangeTableDef 16` lookup on the twelve chain limbs would force; it is a
NAMED hypothesis here, never assumed. -/
def BurnLimbsCanonical (a : Assignment) : Prop :=
  (∀ c, c = B_OLD0 ∨ c = B_OLD1 ∨ c = B_OLD2 ∨ c = B_OLD3
      ∨ c = B_NEW0 ∨ c = B_NEW1 ∨ c = B_NEW2 ∨ c = B_NEW3
      ∨ c = B_AMT0 ∨ c = B_AMT1 ∨ c = B_AMT2 ∨ c = B_AMT3 → 0 ≤ a c ∧ a c < 65536)
  ∧ (a B_BRW0 = 0 ∨ a B_BRW0 = 1)
  ∧ (a B_BRW1 = 0 ∨ a B_BRW1 = 1)
  ∧ (a B_BRW2 = 0 ∨ a B_BRW2 = 1)

/-- **`chainBody_abs_lt_p`** — on canonical limbs EVERY chain gate body is confined to `(-p, p)`
(crudely, `|body| < 2^18 = 262144 ≪ 2013265921`). This is the fact that makes the field reading the
prover checks and the ℤ reading these lemmas state COINCIDE — the property the retired `2^32` shape
could not have, at any assignment. -/
theorem chainBody_abs_lt_p (a : Assignment) (h : BurnLimbsCanonical a) :
    -2013265921 < cSub0Body.eval a ∧ cSub0Body.eval a < 2013265921
    ∧ -2013265921 < cSub1Body.eval a ∧ cSub1Body.eval a < 2013265921
    ∧ -2013265921 < cSub2Body.eval a ∧ cSub2Body.eval a < 2013265921
    ∧ -2013265921 < cSub3Body.eval a ∧ cSub3Body.eval a < 2013265921 := by
  obtain ⟨hl, hb0, hb1, hb2⟩ := h
  have o0 := hl B_OLD0 (by simp); have o1 := hl B_OLD1 (by simp)
  have o2 := hl B_OLD2 (by simp); have o3 := hl B_OLD3 (by simp)
  have n0 := hl B_NEW0 (by simp); have n1 := hl B_NEW1 (by simp)
  have n2 := hl B_NEW2 (by simp); have n3 := hl B_NEW3 (by simp)
  have m0 := hl B_AMT0 (by simp); have m1 := hl B_AMT1 (by simp)
  have m2 := hl B_AMT2 (by simp); have m3 := hl B_AMT3 (by simp)
  simp only [cSub0Body, cSub1Body, cSub2Body, cSub3Body, EmittedExpr.eval, LIMB_BASE]
  omega

/-- **`burn_chain_exact` — LAYER B, the prize.** The four chain gates vanishing OVER ℤ force the
EXACT u64 identity `old_balance = new_balance + amount` on the decoded values — and note it needs NO
canonicality: weighting the four gates by `1, 2^16, 2^32, 2^48` telescopes the three borrow terms
away identically. This is what the retired shape could not say at any resolution: a single field
congruence over a `lo + 2^32·hi` recomposition is not a `2^64` ℤ equality, because the recomposition
is not injective into the field.

Canonicality is what carries a satisfying trace INTO this theorem's hypotheses — the prover checks
the bodies mod `p`, not over ℤ, and `burn_chain_exact_of_modEq` is where that step is taken. -/
theorem burn_chain_exact (a : Assignment)
    (h0 : cSub0Body.eval a = 0) (h1 : cSub1Body.eval a = 0)
    (h2 : cSub2Body.eval a = 0) (h3 : cSub3Body.eval a = 0) :
    u64Of (a B_OLD0) (a B_OLD1) (a B_OLD2) (a B_OLD3)
      = u64Of (a B_NEW0) (a B_NEW1) (a B_NEW2) (a B_NEW3)
        + u64Of (a B_AMT0) (a B_AMT1) (a B_AMT2) (a B_AMT3) := by
  rw [cSub0_zero_iff] at h0
  rw [cSub1_zero_iff] at h1
  rw [cSub2_zero_iff] at h2
  rw [cSub3_zero_iff] at h3
  simp only [u64Of, LIMB_BASE] at *
  omega

/-- **`burn_chain_exact_of_modEq` — THE FIELD-TO-ℤ BRIDGE, and the reason `16` is the width.** The
deployed prover checks each gate body `≡ 0 (mod p)`, never `= 0` over ℤ. On canonical limbs every
chain body is confined to `(-p, p)` (`chainBody_abs_lt_p`), so `p ∣ body` FORCES `body = 0`, the two
readings COINCIDE, and the exact u64 identity follows. At `2^32` limbs no such confinement exists at
any assignment — the body reaches `2^33` — which is precisely why that encoding's ℤ-level lemmas
said nothing about any proof over it. -/
theorem burn_chain_exact_of_modEq (a : Assignment) (h : BurnLimbsCanonical a)
    (h0 : cSub0Body.eval a ≡ 0 [ZMOD 2013265921]) (h1 : cSub1Body.eval a ≡ 0 [ZMOD 2013265921])
    (h2 : cSub2Body.eval a ≡ 0 [ZMOD 2013265921]) (h3 : cSub3Body.eval a ≡ 0 [ZMOD 2013265921]) :
    u64Of (a B_OLD0) (a B_OLD1) (a B_OLD2) (a B_OLD3)
      = u64Of (a B_NEW0) (a B_NEW1) (a B_NEW2) (a B_NEW3)
        + u64Of (a B_AMT0) (a B_AMT1) (a B_AMT2) (a B_AMT3) := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := chainBody_abs_lt_p a h
  rw [Int.modEq_zero_iff_dvd] at h0 h1 h2 h3
  obtain ⟨k0, e0⟩ := h0; obtain ⟨k1, e1⟩ := h1
  obtain ⟨k2, e2⟩ := h2; obtain ⟨k3, e3⟩ := h3
  exact burn_chain_exact a (by omega) (by omega) (by omega) (by omega)

/-- **`burn_no_underflow` — the availability tooth the retired shape did not have.** The top limb
carries NO outgoing borrow, so on canonical limbs a closing chain forces `amount ≤ old_balance`. -/
theorem burn_no_underflow (a : Assignment) (h : BurnLimbsCanonical a)
    (h0 : cSub0Body.eval a = 0) (h1 : cSub1Body.eval a = 0)
    (h2 : cSub2Body.eval a = 0) (h3 : cSub3Body.eval a = 0) :
    u64Of (a B_AMT0) (a B_AMT1) (a B_AMT2) (a B_AMT3)
      ≤ u64Of (a B_OLD0) (a B_OLD1) (a B_OLD2) (a B_OLD3) := by
  have hx := burn_chain_exact a h0 h1 h2 h3
  obtain ⟨hl, _, _, _⟩ := h
  have n0 := hl B_NEW0 (by simp); have n1 := hl B_NEW1 (by simp)
  have n2 := hl B_NEW2 (by simp); have n3 := hl B_NEW3 (by simp)
  simp only [u64Of] at *
  omega

/-! ### Non-vacuity: each tooth ACCEPTS a satisfying row and REJECTS a violating one. -/

/-- A genuine burn row: `old = 1000`, `amount = 400`, `new = 600`, no borrows, `was_burn = 1`. -/
def demoBurnRow : Assignment := fun c =>
  if c = B_OLD0 then 1000 else if c = B_NEW0 then 600 else if c = B_AMT0 then 400
  else if c = B_WB0 then 1 else 0

/-- A borrowing burn row: `old = 2^16` (limb1 = 1, limb0 = 0), `amount = 1`, `new = 65535`. The
low-limb subtraction UNDERFLOWS, so `b_0 = 1` — the borrow is genuinely exercised, not pinned to
zero by the witness. -/
def borrowBurnRow : Assignment := fun c =>
  if c = B_OLD1 then 1 else if c = B_NEW0 then 65535 else if c = B_AMT0 then 1
  else if c = B_BRW0 then 1 else if c = B_WB0 then 1 else 0

theorem demoBurnRow_canonical : BurnLimbsCanonical demoBurnRow := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> [skip; decide; decide; decide]
  intro c hc
  rcases hc with h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> exact ⟨by decide, by decide⟩

theorem borrowBurnRow_canonical : BurnLimbsCanonical borrowBurnRow := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> [skip; decide; decide; decide]
  intro c hc
  rcases hc with h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> exact ⟨by decide, by decide⟩

theorem demoBurnRow_chain_holds :
    cSub0Body.eval demoBurnRow = 0 ∧ cSub1Body.eval demoBurnRow = 0
    ∧ cSub2Body.eval demoBurnRow = 0 ∧ cSub3Body.eval demoBurnRow = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem borrowBurnRow_chain_holds :
    cSub0Body.eval borrowBurnRow = 0 ∧ cSub1Body.eval borrowBurnRow = 0
    ∧ cSub2Body.eval borrowBurnRow = 0 ∧ cSub3Body.eval borrowBurnRow = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **The exactness theorem FIRES on the borrowing witness**, recovering `65536 = 65535 + 1` over ℤ
across a limb boundary — the case the borrow bit exists for. -/
theorem borrowBurnRow_exact :
    u64Of (borrowBurnRow B_OLD0) (borrowBurnRow B_OLD1) (borrowBurnRow B_OLD2) (borrowBurnRow B_OLD3)
      = u64Of (borrowBurnRow B_NEW0) (borrowBurnRow B_NEW1) (borrowBurnRow B_NEW2)
          (borrowBurnRow B_NEW3)
        + u64Of (borrowBurnRow B_AMT0) (borrowBurnRow B_AMT1) (borrowBurnRow B_AMT2)
            (borrowBurnRow B_AMT3) :=
  burn_chain_exact borrowBurnRow
    borrowBurnRow_chain_holds.1 borrowBurnRow_chain_holds.2.1
    borrowBurnRow_chain_holds.2.2.1 borrowBurnRow_chain_holds.2.2.2

/-- …and the recovered values are the GENUINE ones (`65536 = 65535 + 1`), not a trivial `0 = 0`. -/
theorem borrowBurnRow_values :
    u64Of (borrowBurnRow B_OLD0) (borrowBurnRow B_OLD1) (borrowBurnRow B_OLD2)
        (borrowBurnRow B_OLD3) = 65536
    ∧ u64Of (borrowBurnRow B_NEW0) (borrowBurnRow B_NEW1) (borrowBurnRow B_NEW2)
        (borrowBurnRow B_NEW3) = 65535 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **REJECT — a FORGED BORROW.** The same row with `b_0` flipped to `1` while the low limbs are
unchanged: the low-limb gate no longer vanishes. This is the pole the whole encoding exists for —
the borrow may not be conjured to fabricate `2^16` of balance. -/
theorem forgedBorrow_rejects :
    cSub0Body.eval (fun c => if c = B_BRW0 then 1 else demoBurnRow c) ≠ 0 := by decide

/-- **REJECT — a broken subtraction** (`601 + 400 ≠ 1000`). -/
theorem brokenSubtraction_rejects :
    cSub0Body.eval (fun c => if c = B_NEW0 then 601 else demoBurnRow c) ≠ 0 := by decide

/-- **REJECT — a non-boolean borrow** (`b_0 = 2`). -/
theorem nonBooleanBorrow_rejects :
    (cBoolBody B_BRW0).eval (fun c => if c = B_BRW0 then 2 else demoBurnRow c) ≠ 0 := by decide

/-- **REJECT — an undisclosed burn** (`was_burn = 0`). -/
theorem undisclosedBurn_rejects :
    cWasBurn0Body.eval (fun c => if c = B_WB0 then 0 else demoBurnRow c) ≠ 0 := by decide

/-- **REJECT — an UNDERFLOWING burn.** `old = 0`, `amount = 1`, `new = 65535` with `b_0 = 1`: the
low limb closes, but the TOP limb cannot, because there is no outgoing borrow to absorb it. The
availability tooth, exhibited. -/
theorem underflowingBurn_rejects :
    cSub3Body.eval (fun c =>
      if c = B_NEW0 then 65535 else if c = B_AMT0 then 1 else if c = B_BRW2 then 1
      else if c = B_WB0 then 1 else 0) ≠ 0 := by decide

/-! ### ⚑ THE FLOOR, PROVED FALSE — `BurnLimbsCanonical` is NECESSARY, not decorative.

`burn_chain_exact_of_modEq` and `burn_no_underflow` both carry `BurnLimbsCanonical` as a named
hypothesis. What decides whether a `rangeTableDef 16` lookup is worth BUILDING is whether that
hypothesis is DISCHARGEABLE — whether the eleven gates plus the four-limb structure already force
it. **They do not**, and the witness is one subtraction from the honest row.

`pRow` sets `old = 0`, `new = 1`, `amt = p - 1 = 2013265920`, every borrow `0`, `was_burn = 1`.
Every cell is a legal field element. The low chain body is then `1 + (p-1) - 0 - 0 = p`, which the
prover's field reading sees as ZERO while its ℤ reading is `p`; the other ten bodies are `0`
outright. So the row SATISFIES the whole algebraic block — and its decoded u64s say
`old_balance = 0`, `amount = 2013265920`, `new_balance = 1`: a burn of two billion units out of an
empty balance, ending RICHER than it started.

The hypothesis is therefore SATISFIABLE (`demoBurnRow_canonical`), the theorems genuinely FIRE under
it (`borrowBurnRow_exact`), and it is REFUTABLE and NOT PROVABLE from the gates
(`burnLimbsCanonical_is_load_bearing`). A real floor, not a decorative one. Nothing weaker than a
range lookup on the twelve chain limbs closes it INSIDE this descriptor.

⚠ **What stands in for it today, named at its call site.** On the deployed executor path the twelve
limbs are not prover-chosen at all: `verify_effect_binding_proofs_with_ledger`
(`turn/src/executor/proof_verify.rs:2029-2103`) reconstructs all four amounts from its OWN ledger
snapshot, builds the PI vector through `EffectActionWitness::public_inputs` — i.e. through the
INJECTIVE 16-bit `encode_amount` — and STARK-verifies against THAT vector, which the `piBinding`
gates pin to row 0. Every chain limb is `< 2^16` by the verifier's own construction, so `pRow` is
unreachable there. It is reachable for any consumer that verifies such a proof STANDALONE, which is
exactly the reader this theorem exists for. (⚠ That deployed path also runs the *Rust*-lowered
descriptor, which carries NONE of the eleven gates — `circuit/tests/burn_air_conservation_gap.rs`
is the falsifier for that separate, larger gap.) -/

/-- The counterexample row: `old = 0`, `new = 1`, `amt = p - 1`, no borrows, `was_burn = 1`. Every
cell is in `[0, p)`; only the CANONICALITY of the amount limb is violated. -/
def pRow : Assignment := fun c =>
  if c = B_NEW0 then 1 else if c = B_AMT0 then 2013265920
  else if c = B_WB0 then 1 else 0

/-- `pRow` is NOT canonical — its low amount limb is `p - 1`, far past `2^16`. -/
theorem pRow_not_canonical : ¬ BurnLimbsCanonical pRow := by
  rintro ⟨hl, -, -, -⟩
  have h := hl B_AMT0 (by simp)
  have e : pRow B_AMT0 = 2013265920 := rfl
  omega

/-- The four chain bodies vanish MOD `p` on `pRow` — the exact check the deployed prover performs.
⚑ The low body is `p` itself over ℤ, which is the whole trick. -/
theorem pRow_chain_holds_mod_p :
    cSub0Body.eval pRow ≡ 0 [ZMOD 2013265921]
    ∧ cSub1Body.eval pRow ≡ 0 [ZMOD 2013265921]
    ∧ cSub2Body.eval pRow ≡ 0 [ZMOD 2013265921]
    ∧ cSub3Body.eval pRow ≡ 0 [ZMOD 2013265921] := by
  refine ⟨Int.modEq_zero_iff_dvd.mpr ⟨1, by decide⟩,
          Int.modEq_zero_iff_dvd.mpr ⟨0, by decide⟩,
          Int.modEq_zero_iff_dvd.mpr ⟨0, by decide⟩,
          Int.modEq_zero_iff_dvd.mpr ⟨0, by decide⟩⟩

/-- The low chain body is `p` over ℤ — NOT zero. This is the gap between the field reading the
prover checks and the ℤ reading `burn_chain_exact` needs. -/
theorem pRow_low_body_is_p : cSub0Body.eval pRow = 2013265921 := rfl

/-- The seven non-chain gates (three borrow booleanity + four disclosure pins) vanish outright. -/
theorem pRow_aux_gates_hold :
    (cBoolBody B_BRW0).eval pRow = 0 ∧ (cBoolBody B_BRW1).eval pRow = 0
    ∧ (cBoolBody B_BRW2).eval pRow = 0 ∧ cWasBurn0Body.eval pRow = 0
    ∧ cWasBurn1Body.eval pRow = 0 ∧ cWasBurn2Body.eval pRow = 0
    ∧ cWasBurn3Body.eval pRow = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The decoded u64s are the GENUINE ones, not a degenerate `0 = 0`: `old = 0`, `new = 1`,
`amount = 2013265920`. ⚠ The ROUND-TRIP out of the limbs is what makes the next two theorems
readable as balances rather than as felts. -/
theorem pRow_decodes :
    u64Of (pRow B_OLD0) (pRow B_OLD1) (pRow B_OLD2) (pRow B_OLD3) = 0
    ∧ u64Of (pRow B_NEW0) (pRow B_NEW1) (pRow B_NEW2) (pRow B_NEW3) = 1
    ∧ u64Of (pRow B_AMT0) (pRow B_AMT1) (pRow B_AMT2) (pRow B_AMT3) = 2013265920 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **The exactness conclusion is FALSE on `pRow`**: `0 ≠ 1 + 2013265920`. -/
theorem pRow_breaks_exactness :
    u64Of (pRow B_OLD0) (pRow B_OLD1) (pRow B_OLD2) (pRow B_OLD3)
      ≠ u64Of (pRow B_NEW0) (pRow B_NEW1) (pRow B_NEW2) (pRow B_NEW3)
        + u64Of (pRow B_AMT0) (pRow B_AMT1) (pRow B_AMT2) (pRow B_AMT3) := by decide

/-- **…and so is the availability conclusion**: the row burns `2013265920` from a balance of `0`. -/
theorem pRow_breaks_no_underflow :
    ¬ (u64Of (pRow B_AMT0) (pRow B_AMT1) (pRow B_AMT2) (pRow B_AMT3)
        ≤ u64Of (pRow B_OLD0) (pRow B_OLD1) (pRow B_OLD2) (pRow B_OLD3)) := by decide

/-- ⚑ **`burnLimbsCanonical_is_load_bearing` — THE FLOOR, PROVED FALSE.** There EXISTS an assignment
satisfying every chain gate mod `p` and every auxiliary gate outright, which is NOT canonical and
which violates BOTH ℤ-conclusions the canonical theorems reach. So `BurnLimbsCanonical` cannot be
dropped from `burn_chain_exact_of_modEq` or from `burn_no_underflow`, and no range-free
strengthening of either exists. This is what makes the missing `rangeTableDef 16` a REAL residual
rather than a stylistic one. -/
theorem burnLimbsCanonical_is_load_bearing :
    ∃ a : Assignment,
      (cSub0Body.eval a ≡ 0 [ZMOD 2013265921] ∧ cSub1Body.eval a ≡ 0 [ZMOD 2013265921]
        ∧ cSub2Body.eval a ≡ 0 [ZMOD 2013265921] ∧ cSub3Body.eval a ≡ 0 [ZMOD 2013265921])
      ∧ ((cBoolBody B_BRW0).eval a = 0 ∧ (cBoolBody B_BRW1).eval a = 0
        ∧ (cBoolBody B_BRW2).eval a = 0 ∧ cWasBurn0Body.eval a = 0
        ∧ cWasBurn1Body.eval a = 0 ∧ cWasBurn2Body.eval a = 0 ∧ cWasBurn3Body.eval a = 0)
      ∧ ¬ BurnLimbsCanonical a
      ∧ u64Of (a B_OLD0) (a B_OLD1) (a B_OLD2) (a B_OLD3)
          ≠ u64Of (a B_NEW0) (a B_NEW1) (a B_NEW2) (a B_NEW3)
            + u64Of (a B_AMT0) (a B_AMT1) (a B_AMT2) (a B_AMT3)
      ∧ ¬ (u64Of (a B_AMT0) (a B_AMT1) (a B_AMT2) (a B_AMT3)
            ≤ u64Of (a B_OLD0) (a B_OLD1) (a B_OLD2) (a B_OLD3)) :=
  ⟨pRow, pRow_chain_holds_mod_p, pRow_aux_gates_hold, pRow_not_canonical,
    pRow_breaks_exactness, pRow_breaks_no_underflow⟩

/-- Continuity: agrees ⇒ 0; differs ⇒ ≠ 0. -/
theorem cont_accepts_chained :
    (contWindowBody 3).eval ⟨fun _ => 5, fun _ => 5, fun _ => 0, fun _ => 0⟩ = 0 := by decide

theorem cont_rejects_stash :
    (contWindowBody 3).eval ⟨fun _ => 5, fun i => if i = 3 then 9 else 5, fun _ => 0, fun _ => 0⟩
      ≠ 0 := by decide

/-! ## §6 — Shape pins. -/

#guard revokeCapabilityDesc.traceWidth == 12
#guard revokeCapabilityDesc.piCount == 12
#guard revokeCapabilityDesc.constraints.length == 24
#guard burnDesc.traceWidth == 27
#guard burnDesc.piCount == 24
#guard burnDesc.constraints.length == 62

#assert_axioms cont_zero_iff
#assert_axioms cSub0_zero_iff
#assert_axioms cSub1_zero_iff
#assert_axioms cSub2_zero_iff
#assert_axioms cSub3_zero_iff
#assert_axioms cBool_zero_iff
#assert_axioms cWasBurn0_zero_iff
#assert_axioms chainBody_abs_lt_p
#assert_axioms burn_chain_exact
#assert_axioms burn_chain_exact_of_modEq
#assert_axioms burn_no_underflow
#assert_axioms borrowBurnRow_exact
#assert_axioms forgedBorrow_rejects
#assert_axioms underflowingBurn_rejects
#assert_axioms pRow_not_canonical
#assert_axioms pRow_chain_holds_mod_p
#assert_axioms pRow_low_body_is_p
#assert_axioms pRow_aux_gates_hold
#assert_axioms pRow_decodes
#assert_axioms pRow_breaks_exactness
#assert_axioms pRow_breaks_no_underflow
#assert_axioms burnLimbsCanonical_is_load_bearing

end Dregg2.Circuit.Emit.EffectActionBindingEmit

#assert_axioms two_felts_cannot_carry_a_u64
#assert_axioms four_limbs_carry_u64_exactly
#assert_axioms amount_limb_fits_felt
