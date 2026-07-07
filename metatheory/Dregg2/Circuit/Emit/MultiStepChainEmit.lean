/-
# Dregg2.Circuit.Emit.MultiStepChainEmit — the emit-from-Lean descriptor for the MULTI-STEP
derivation-chaining COMPOSITION layer (family `multi_step`).

## What this file IS

The `multi_step` family composes K single-step derivations into one authorization by an
accumulated Merkle–Damgård hash CHAIN. The chaining semantics are the authoritative producer
(`circuit/src/multi_step_air.rs::MultiStepWitness::compute_accumulated_hashes` +
`circuit/src/dsl/derivation.rs::generate_multi_step_trace_dsl`):

    prev₀ = initial_state_root
    accᵢ  = hash_2_to_1(prevᵢ, derived_hashᵢ)          -- MS1, the per-step absorb
    prevᵢ₊₁ = accᵢ                                       -- MS2, chain continuity
    final_accumulated_hash = acc_last                    -- MS3, the published tail

⚠ THE ASSURANCE-TWIN POSTURE (honest scope). In the DEPLOYED tree these chaining columns are
WITNESS-COMPUTED but ENFORCED BY NOTHING: `MultiStepStarkAir::eval_constraints` returns `ZERO`
and `boundary_constraints` returns `[]` (`circuit/src/multi_step_air.rs:195-211`). This descriptor
is the ENFORCED twin of that producer — exactly the `AccumulatorOpenEmit` posture (a Lean
assurance-layer emit that trace-FORCES what a deployed producer only fills). It maps the chain
onto IR-v2 primitives:

  * MS1 `accᵢ = hash_2_to_1(prevᵢ, derivedᵢ)` — an **arity-2 `Poseidon2Chip` lookup** (`hash_2_to_1`
    seeds `state[0]=prev, state[1]=derived, state[4]=2`; `poseidon2.rs:365`), `out0 = ACC`.
  * MS2 `prevᵢ₊₁ = accᵢ` — a two-row **`windowGate` on the transition**: `nxt[PREV] − loc[ACC] = 0`
    (the cross-row cumulative primitive, `descriptor_ir2.rs:2222`).
  * MS3 first `prev₀ = pi[INITIAL]` / last `acc_last = pi[FINAL]` — two boundary **`PiBinding`s**.

## Residuals (NAMED, not laundered)

  * the single-step per-derivation constraints C1–C28 (Datalog body membership, head binding,
    GTE/LT range proofs, …) are the SIBLING `derivation` family (the dossier's emit_plan itself
    splits them into a separate `DerivationEmit.lean`); `DERIVED` here is that circuit's published
    `derived_hash` column, taken as a free input at the chain layer.
  * MS4 conclusion-decode (`conclusion = [pred_last == ALLOW]`) needs an aux inverse column to
    force the iff; NOT emitted here.
  * POLICY_ROOT (a multi-block rate-4 sponge fold of the rule structure hashes) — a chained
    multi-permute chip fold; NOT emitted here.

## Axiom hygiene

Definitional descriptor + a byte-pinned `#guard` on its wire string + one genuinely-proven,
non-vacuous semantic lemma (`continuity_zero_iff`, TRUE iff the chain links, FALSE otherwise),
`#assert_axioms`-clean (pure `omega`). NEW file; imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Circuit.Emit.MultiStepChainEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId chipLookupTuple WindowExpr WindowConstraint
   CHIP_RATE CHIP_OUT_LANES emitVmJson2)

set_option autoImplicit false

/-! ## §1 — The trace column layout (one logical step per row). -/

/-- The accumulated hash entering this step (`prevᵢ`; row 0 = `initial_state_root`). -/
def PREV : Nat := 0
/-- This step's per-derivation `derived_hash` (the single-step circuit's published output). -/
def DERIVED : Nat := 1
/-- The accumulated hash leaving this step: `accᵢ = hash_2_to_1(PREV, DERIVED)` (chip out0). -/
def ACC : Nat := 2
/-- The seven exposed permutation lane columns 1..7 of the arity-2 chip lookup (out0 = `ACC`). -/
def LANES : List Nat := [3, 4, 5, 6, 7, 8, 9]

/-- Total main-trace width: 3 chain columns + 7 chip lanes. -/
def CHAIN_WIDTH : Nat := 10

/-- The public root pinned on the first row (`prev₀ = initial_state_root`). -/
def INITIAL_PI : Nat := 0
/-- The public accumulated hash pinned on the last row (`acc_last = final_accumulated_hash`). -/
def FINAL_PI : Nat := 1

/-! ## §2 — The constraint list (per-step absorb · chain continuity · boundary pins). -/

/-- MS1 — the per-step `hash_2_to_1` absorb: an arity-2 `Poseidon2Chip` lookup over `[PREV, DERIVED]`
binding out0 to `ACC`. -/
def ms1Absorb : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2, chipLookupTuple [.var PREV, .var DERIVED] ACC LANES⟩

/-- The chain-continuity window body: `nxt[PREV] − loc[ACC]` — the next step's entering hash equals
this step's leaving hash. -/
def contBody : WindowExpr := .add (.nxt PREV) (.mul (.const (-1)) (.loc ACC))

/-- MS2 — chain continuity as a two-row `windowGate` asserted on the transition (every row but the
last, where there is no next step). -/
def ms2Continuity : VmConstraint2 := .windowGate ⟨contBody, true⟩

/-- MS3a — the first-row boundary pin: `prev₀ = pi[INITIAL_STATE_ROOT]`. -/
def initPin : VmConstraint2 := .base (.piBinding VmRow.first PREV INITIAL_PI)

/-- MS3b — the last-row boundary pin: `acc_last = pi[FINAL_ACCUMULATED_HASH]`. -/
def finalPin : VmConstraint2 := .base (.piBinding VmRow.last ACC FINAL_PI)

/-- **`multiStepChainDesc`** — the accumulated-hash-chain composition descriptor. Constraints: the
per-step arity-2 chip absorb, the transition continuity window, and the two boundary pins. The chip
table (`TID_P2`) is IMPLICITLY present (Presence-detected from the lookup), so `tables` is empty. -/
def multiStepChainDesc : EffectVmDescriptor2 :=
  { name        := "multi-step-accumulated-hash-chain::poseidon2-v1"
  , traceWidth  := CHAIN_WIDTH
  , piCount     := 2
  , tables      := []
  , constraints := [ms1Absorb, ms2Continuity, initPin, finalPin]
  , hashSites   := []
  , ranges      := [] }

/-! ## §3 — The byte-pinned wire golden (the Rust decoder ingests THIS string).

THE EQUALITY-GATE ANCHOR: this exact string is embedded verbatim in
`circuit-prove/tests/multi_step_emit_gate.rs` (`GOLDEN_JSON`), decoded there via
`parse_vm_descriptor2`, asserted equal to an independent Rust-built descriptor, and proven through
the REAL `prove_vm_descriptor2` / `verify_vm_descriptor2`. A drift on either side breaks THIS
`#guard` (Lean) or the Rust `assert_eq!(decoded, hand_built)`. -/

#guard emitVmJson2 multiStepChainDesc ==
  "{\"name\":\"multi-step-accumulated-hash-chain::poseidon2-v1\",\"ir\":2,\"trace_width\":10,\"public_input_count\":2,\"tables\":[],\"constraints\":[{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":2},{\"t\":\"var\",\"v\":0},{\"t\":\"var\",\"v\":1},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":2},{\"t\":\"var\",\"v\":3},{\"t\":\"var\",\"v\":4},{\"t\":\"var\",\"v\":5},{\"t\":\"var\",\"v\":6},{\"t\":\"var\",\"v\":7},{\"t\":\"var\",\"v\":8},{\"t\":\"var\",\"v\":9}]},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":2}}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":0,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":2,\"pi_index\":1}],\"hash_sites\":[],\"ranges\":[]}"

/-! ## §4 — A genuinely-proven, non-vacuous semantic lemma (the continuity window teeth).

The window body is zero EXACTLY when the chain links (`nxt[PREV] = loc[ACC]`) — TRUE when the next
step's entering hash equals this step's leaving hash, FALSE otherwise. This is the Lean face of the
chain-continuity the emitted `windowGate` enforces on every transition row in the Rust Ir2 main AIR
(`descriptor_ir2.rs:2222`, the `when_transition().assert_zero(..)` arm). -/

theorem continuity_zero_iff (env : VmRowEnv) :
    contBody.eval env = 0 ↔ env.nxt PREV = env.loc ACC := by
  simp only [contBody, WindowExpr.eval]
  constructor <;> intro h <;> omega

-- Non-vacuity witnesses: the window ACCEPTS a linked window and REJECTS an unlinked one.
#guard decide (contBody.eval ⟨fun i => if i = ACC then 7 else 0, fun i => if i = PREV then 7 else 0,
    fun _ => 0⟩ = 0)
#guard decide (¬ (contBody.eval ⟨fun _ => 0, fun i => if i = PREV then 7 else 0, fun _ => 0⟩ = 0))

-- Shape pins.
#guard multiStepChainDesc.traceWidth == CHAIN_WIDTH
#guard multiStepChainDesc.piCount == 2
#guard multiStepChainDesc.constraints.length == 4
#guard (multiStepChainDesc.constraints.filter
          (fun c => match c with | .windowGate _ => true | _ => false)).length == 1
#guard (chipLookupTuple [.var PREV, .var DERIVED] ACC LANES).length
         == CHIP_RATE + 1 + CHIP_OUT_LANES

#assert_axioms continuity_zero_iff

end Dregg2.Circuit.Emit.MultiStepChainEmit
