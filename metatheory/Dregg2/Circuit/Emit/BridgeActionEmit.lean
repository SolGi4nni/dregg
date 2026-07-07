/-
# Dregg2.Circuit.Emit.BridgeActionEmit — emit-from-Lean of the bridge-action BINDING leaf.

## What this file IS

A table-free `EffectVmDescriptor2` that emits, in the IR-v2 grammar, the *binding-only* statement of
`circuit/src/bridge_action_air.rs::BridgeActionAir`: "a 26-column typed row
(8-limb nullifier ‖ 8-limb recipient ‖ 8-limb destination_federation ‖ amount_lo ‖ amount_hi) is
pinned to the 26 public inputs, and replicated identically across the FRI power-of-2 padding".

The hand AIR (`bridge_action_air.rs`) enforces EXACTLY two constraint families — nothing else (no
range decomposition, no in-AIR hashing; the felts are bound directly):

  * `boundary_constraints` (`:304`): `row0[col c] == public_inputs[c]` for every column `c ∈ 0..26`
    (`:317-343`, the 8/8/8/2-limb layout). PI layout is identity (`pi_index == col`).
      → `Base(PiBinding{ row := First, col := c, pi_index := c })`  (the first-row carrier evaluated
        by the IR-v2 main AIR at `descriptor_ir2.rs:2173-2177`).
  * `eval_constraints` (`:281-302`): every column is constant across rows, `next[c] − local[c] == 0`
    for all 26 columns, RLC-folded over `alpha` (the "1 typed row replicated for FRI padding" glue,
    so a prover cannot bind one tuple in row 0 and a different one in a padding row).
      → `WindowGate{ body := Nxt(c) + (−1)·Loc(c), on_transition := true }`  (fired on the transition
        domain by the IR-v2 main AIR at `descriptor_ir2.rs:2222-2224`). The `alpha`-RLC is the
        prover's own random-linear-combination of these per-column zero constraints — one WindowGate
        per column IS that family, term-for-term.

The `BRIDGE_ACTION_PI_COUNT != 26` guard (`:311-316`) and the `encode_hash`/`encode_amount` limb
reduction (`:126-141`) are NOT per-row AIR constraints: the first is subsumed by
`public_input_count = 26` (the general IR-v2 prover fixes the PI count at descriptor level), the
second is OFF-AIR witness/PI encoding done in Rust (the felts are bound directly, not decomposed).
There is therefore NO tooth living in a verifier wrapper to preserve — the whole binding is the two
emitted families.

This descriptor is the byte-identical Lean twin of the already-proven Rust builder
`circuit-prove/src/bridge_leaf_adapter.rs::bridge_action_to_descriptor2` (proven total/always-`Ok`,
folded through `prove_vm_descriptor2_for_config`). The gate
(`circuit-prove/tests/bridge_action_emit_gate.rs`) decodes the byte-pinned `emitVmJson2` string
below, asserts it EQUALS both an independently hand-built descriptor AND
`bridge_action_to_descriptor2()`, proves an HONEST 26-slot witness through the REAL
`prove_vm_descriptor2` / `verify_vm_descriptor2` (ACCEPT), and mutation-canaries a forged PI (→ the
`PiBinding` boundary tooth) and a broken-continuity padding row (→ the `WindowGate` transition tooth)
to real UNSAT.

## Soundness scope (do NOT overclaim)

`BridgeActionAir` is a BINDING-ONLY, deliberately-refused shadow AIR — it does NOT re-prove the
underlying note-spend (Merkle membership + key knowledge); that is `note_spending`'s job, and the
SOUND deployed bridge-mint backing is the note-spend leaf folded to the published `mint_hash`
(`BridgeBindingFromFold.lean` REFUSES folding this AIR as a backing — a prover-chosen tuple). This
file is the law-migration of the binding shadow (descriptor emitted-from-Lean + byte-pinned), NOT a
soundness change to the deployed bridge.

## Axiom hygiene

Definitional descriptor + a byte-pinned `#guard` on its wire string + one genuinely-proven,
non-vacuous semantic lemma (`cont_body_zero_iff`, TRUE iff a column chains, FALSE otherwise).
`#assert_axioms cont_body_zero_iff` (pure `omega`). NEW file; imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Circuit.Emit.BridgeActionEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 WindowExpr WindowConstraint emitVmJson2)

set_option autoImplicit false

/-! ## §1 — Shape constants (mirror `bridge_action_air.rs`). -/

/-- Trace width AND PI count: 8 (nullifier) + 8 (recipient) + 8 (destination_federation) + 2
(amount lo/hi) = 26. Both `BRIDGE_ACTION_WIDTH` and `BRIDGE_ACTION_PI_COUNT`. -/
def BRIDGE_ACTION_WIDTH : Nat := 26

/-! ## §2 — The two constraint families (boundary pins · transition continuity). -/

/-- Family 1 — the 26 boundary pins: `row0[col c] == pi[c]`, `pi_index == col` (identity layout,
preserving the 8/8/8/2-limb slots exactly). `PiBinding{First}` is the term-for-term carrier of the
hand AIR's `boundary_constraints` (all emitted at `row: 0`). -/
def piPins : List VmConstraint2 :=
  (List.range BRIDGE_ACTION_WIDTH).map (fun c => .base (.piBinding VmRow.first c c))

/-- The per-column continuity body: `Nxt(c) + (−1)·Loc(c)` — the two-row twin of the hand AIR's
`next[c] − local[c] == 0` (no subtraction node; `Add(Nxt, Mul(Const(-1), Loc))`). -/
def contBody (c : Nat) : WindowExpr :=
  .add (.nxt c) (.mul (.const (-1)) (.loc c))

/-- Family 2 — the 26 transition pins: each per-column difference is one `on_transition` `WindowGate`
whose body must vanish on rows `0..n−2` (exactly the AIR's `eval_constraints` transition domain). -/
def windowGates : List VmConstraint2 :=
  (List.range BRIDGE_ACTION_WIDTH).map (fun c => .windowGate ⟨contBody c, true⟩)

/-- **`bridgeActionDesc`** — the table-free bridge-action binding descriptor: 26 `PiBinding{First}`
++ 26 `WindowGate`, no tables / hash sites / ranges. The Lean twin of the proven Rust
`bridge_action_to_descriptor2`. -/
def bridgeActionDesc : EffectVmDescriptor2 :=
  { name        := "bridge-action-leaf::bridge_action_air_v1"
  , traceWidth  := BRIDGE_ACTION_WIDTH
  , piCount     := BRIDGE_ACTION_WIDTH
  , tables      := []
  , constraints := piPins ++ windowGates
  , hashSites   := []
  , ranges      := [] }

/-! ## §3 — The byte-pinned wire golden (the Rust decoder ingests THIS string).

THE EQUALITY-GATE ANCHOR: this exact string is embedded verbatim in
`circuit-prove/tests/bridge_action_emit_gate.rs` (`GOLDEN_JSON`), decoded there via
`parse_vm_descriptor2`, asserted equal to both a hand-built twin AND the proven
`bridge_action_to_descriptor2()`, and proven. A drift on either side breaks THIS `#guard` (Lean) or
the Rust `assert_eq!(decoded, hand_built)`. -/

#guard emitVmJson2 bridgeActionDesc ==
  "{\"name\":\"bridge-action-leaf::bridge_action_air_v1\",\"ir\":2,\"trace_width\":26,\"public_input_count\":26,\"tables\":[],\"constraints\":[{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":0,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":1,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":2,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":3,\"pi_index\":3},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":4,\"pi_index\":4},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":5,\"pi_index\":5},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":6,\"pi_index\":6},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":7,\"pi_index\":7},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":8,\"pi_index\":8},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":9,\"pi_index\":9},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":10,\"pi_index\":10},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":11,\"pi_index\":11},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":12,\"pi_index\":12},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":13,\"pi_index\":13},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":14,\"pi_index\":14},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":15,\"pi_index\":15},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":16,\"pi_index\":16},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":17,\"pi_index\":17},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":18,\"pi_index\":18},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":19,\"pi_index\":19},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":20,\"pi_index\":20},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":21,\"pi_index\":21},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":22,\"pi_index\":22},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":23,\"pi_index\":23},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":24,\"pi_index\":24},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":25,\"pi_index\":25},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":0}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":1}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":2}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":3}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":4}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":5}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":6}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":7}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":8},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":8}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":9},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":9}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":10},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":10}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":11},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":11}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":12},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":12}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":13},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":13}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":14},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":14}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":15},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":15}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":16},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":16}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":17},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":17}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":18},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":18}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":19},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":19}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":20},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":20}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":21},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":21}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":22},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":22}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":23},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":23}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":24},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":24}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":25},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":25}}}}],\"hash_sites\":[],\"ranges\":[]}"

/-! ## §4 — A genuinely-proven, non-vacuous semantic lemma (the continuity tooth).

The per-column continuity body vanishes EXACTLY when that column chains across the window
(`nxt c = loc c`) — TRUE when they agree, FALSE when they do not. This is the Lean face of the
"every column constant across rows" glue the emitted `WindowGate` enforces on the transition domain
in the Rust IR-v2 main AIR (`descriptor_ir2.rs:2222-2224`). -/

theorem cont_body_zero_iff (env : VmRowEnv) (c : Nat) :
    (contBody c).eval env = 0 ↔ env.nxt c = env.loc c := by
  simp only [contBody, WindowExpr.eval]
  constructor <;> intro h <;> omega

/-! ### Non-vacuity witnesses: the gate ACCEPTS a chained window and REJECTS an unchained one. -/

/-- A chained window: `nxt` and `loc` agree on every column. -/
def envChained : VmRowEnv := { loc := fun _ => 7, nxt := fun _ => 7, pub := fun _ => 0 }
/-- An UNchained window: column 0 differs across the two rows. -/
def envBroken : VmRowEnv :=
  { loc := fun _ => 7, nxt := fun i => if i = 0 then 8 else 7, pub := fun _ => 0 }

#guard decide ((contBody 0).eval envChained = 0)
#guard decide (¬ ((contBody 0).eval envBroken = 0))

/-! ### Shape pins. -/

#guard bridgeActionDesc.traceWidth == BRIDGE_ACTION_WIDTH
#guard bridgeActionDesc.piCount == BRIDGE_ACTION_WIDTH
#guard bridgeActionDesc.tables.length == 0
#guard bridgeActionDesc.hashSites.length == 0
#guard bridgeActionDesc.ranges.length == 0
#guard bridgeActionDesc.constraints.length == 2 * BRIDGE_ACTION_WIDTH
#guard piPins.length == BRIDGE_ACTION_WIDTH
#guard windowGates.length == BRIDGE_ACTION_WIDTH

#assert_axioms cont_body_zero_iff

end Dregg2.Circuit.Emit.BridgeActionEmit
