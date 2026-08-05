/-
# Dregg2.Circuit.Emit.BilateralAggregationCompact — E8: the byte-safe STRENGTHENING proof for the
bilateral-aggregation expected-block delete (width 87 → 52), staged for the bundled regen cutover.

## What this file IS (the E8 soundness core, S2/E1 pattern: prove now, regen later)

The DEPLOYED `bilateralAggDescriptor` (v2, width 87, 70 constraints) spends **35 of its 38 gates on
`sched[13+k] == expected[49+k]` where BOTH blocks are prover-filled from the same
`AggregationInnerRowV2`** (`circuit/src/bilateral_aggregation_air.rs:332-408`): no PI, boundary, or
lookup pins the expected block externally, so any trace satisfies CG-3 by copying — the block is a
tautological self-check carrying 35 dead committed columns. Meanwhile the middle rows'
turn-identity columns are UNCONSTRAINED in-AIR (CG-2 binds first/last only) — `gapTrace` (§8)
EXHIBITS a v2-accepted bundle whose middle cell carries a forged turn identity.

THIS module authors the compacted descriptor `bilateralAggDescriptorV3` (width **52**, 48
constraints: the expected block and its 35 gates DELETED; 13 NEW `windowGate`s pin the identity
slots constant across every transition, which + the first-row PI bindings forces EVERY row onto the
published turn identity) and proves the two halves of the strengthening, against the DEPLOYED
acceptance predicate `Satisfied2`:

* **`expand_satisfies` (the compaction bridge — v3 accepts a SUBSET of v2).** Any trace satisfying
  v3 maps (PI-preserving, schedule block unchanged, expected block := the canonical schedule copy,
  accumulators recolumned 84/85/86 → 49/50/51) to a trace satisfying the FULL `Satisfied2` of the
  ORIGINAL v2 descriptor. Nothing v3 accepts lacks a v2-accepted twin with the same outer PI.
* **`contract_preserves` (every honest witness survives).** Any v2-satisfying trace whose identity
  slots are row-constant (`IdentityConstant` — what the deployed trace builder
  `build_aggregation_trace_v2` produces by construction: all cells share the one turn, padding rows
  mirror the first row's identity slots) contracts to a v3-satisfying trace. Inhabited concretely:
  the Rung-1 honest `witTrace` contracts to `witV3` (`witV3_satisfies`).
* **STRICT strengthening:** `gapTrace_satisfies` (v2 ACCEPTS the middle-row identity forgery) +
  `gapTrace_contract_not_v3` (v3 REJECTS it) + `gap_no_v3_preimage` (no v3-accepted trace expands
  to it — `contractT ∘ expandT = id`). The positive face: `compact_identity_every_row` — under v3,
  EVERY row's 13 identity slots equal the outer PI (v2 proves this for first/last only).
* **The crown carries over:** `compact_refines` (BundleAggregated via the Rung-1 bridge) and
  `compact_unique_agent` (UniqueAgent via the Rung-2 discharge) hold for v3 traces through the
  bridge — the no-double-spend teeth restated on the compact trace's own columns.

## What this file is NOT (byte-safe: NO regen)

The deployed descriptor JSON (`circuit/descriptors/dregg-bilateral-aggregation-v2.json`), its VK,
and the Rust twin are UNTOUCHED — v2 remains the shipped AIR. `bilateralAggDescriptorV3` exists in
Lean only, its wire shape `#guard`-pinned here so the flag-day step is a mechanical re-emit + VK
re-pin with the soundness already machine-checked. The cutover recipe is staged in HORIZONLOG.md
(E8 entry): emit v3 JSON, drop `expected_counts`/`expected_roots` from `AggregationInnerRowV2` +
`build_aggregation_trace_v2`, re-pin the emit gate, and fix the two overstated doc claims in
`bilateral_aggregation_air.rs` (the "per-row PI slots" header — bindings are first/last-only in v2
— and the CG-5 `edge_fp` "~124-bit" collision claim — a 1-felt fingerprint is ~31-bit; the off-AIR
multiset re-derivation is what closes it).

## Field-faithful denotation

Every gate is pinned only `≡ 0 [ZMOD p]` (`p = 2013265921`, BabyBear). The bridges are exact at
that resolution (constraint-for-constraint congruence transfer, no canonicality needed); the ℤ
readings (`compact_identity_every_row`, the crown corollaries) thread the explicit canonicality
envelope `AggCTraceCanon` (the v3 recolumning of Rung-1's `AggTraceCanon`), inhabited by `witV3`.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem; the descriptor family
is crypto-free (no tables/hash-sites/ranges/map-ops on either side). NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.BilateralAggregationEmit
import Dregg2.Circuit.Emit.BilateralAggregationRung2

namespace Dregg2.Circuit.Emit.BilateralAggregationCompact

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
  (VmConstraint VmRowEnv VmRow holdsVm_boundaryFirst_true holdsVm_boundaryLast_true
   holdsVm_piFirst_true holdsVm_piLast_true)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmitBilateralAgg
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff not_modEq_zero_of_canon eqToModEq)
open Dregg2.Circuit.Emit.BilateralAggregationRefine
  (rowAt isAgentAt consistentAt cumAt nActiveAt AggTraceCanon BundleAggregated bilateralAgg_refines
   eq_of_modEq_of_canon witTrace wr0 wr1 wpub witTrace_satisfies witTrace_canon hash0
   memLog_agg mapLog_agg mem_A mem_B mem_turn_hash mem_turn_effects mem_turn_nonce mem_turn_prev
   mem_firstCumSeed mem_firstNSeed mem_lastCumIsOne mem_lastNEqPi mem_boolIsAgent
   mem_boolConsistent mem_cumAgentTransition mem_cumActiveTransition)
open Dregg2.Circuit.Emit.BilateralAggregationRung2 (UniqueAgent bilateralAgg_rung2)
open WindowExpr (loc nxt)

set_option autoImplicit false

/-! ## §1 — The compacted (v3) layout: schedule block unchanged, expected block DELETED. -/

namespace AggC

/-- The turn-identity prefix of the schedule block: cols `[0, 13)` (4 turn-hash + 4 effects-hash +
nonce + 4 previous-receipt). The 13 slots the new per-row window gates pin. -/
def IDENTITY_LEN : Nat := 13

/-- Running cumulative of `IS_AGENT_CELL` — was col 84, now directly after the schedule block. -/
def IS_AGENT_CUMULATIVE_COL : Nat := Sched.WIDTH
/-- Per-row "this row's checks passed" boolean — was col 85. -/
def CONSISTENT_INDICATOR_COL : Nat := IS_AGENT_CUMULATIVE_COL + 1
/-- Running active-row counter — was col 86. -/
def N_CELLS_ACTIVE_COL : Nat := CONSISTENT_INDICATOR_COL + 1
/-- Total main width: 49 + 3 = **52** (was 87; the 35 expected cols are gone). -/
def WIDTH : Nat := N_CELLS_ACTIVE_COL + 1

end AggC

-- The identity prefix is exactly the schedule block below the counts.
#guard AggC.IDENTITY_LEN == Sched.COUNTS_BASE
#guard AggC.WIDTH == 52

/-! ## §2 — The v3 constraint builders. `turnIdBindings` is REUSED verbatim (identity cols < 13 are
untouched by the recolumning); the CG-4/boundary family is recolumned; the identity-carry window
gates are NEW (the strengthening). -/

/-- Identity-slot constancy: `next[c] = local[c]` on every transition — one gate per identity slot.
Together with the first-row PI bindings this pins EVERY row's identity slots to the outer PI (the
middle-row gap v2 leaves open). -/
def identityCarry (c : Nat) : VmConstraint2 :=
  .windowGate
    { onTransition := true
    , body := .add (nxt c) (.mul (.const (-1)) (loc c)) }

/-- The 13 identity-carry gates. -/
def identityCarryAll : List VmConstraint2 :=
  (List.range AggC.IDENTITY_LEN).map identityCarry

/-- The padding gate `(1 - consistent)·is_agent = 0`, recolumned. -/
def paddingGateC : VmConstraint2 :=
  .base (.gate (.mul (.add (.const 1) (.mul (.const (-1)) (.var AggC.CONSISTENT_INDICATOR_COL)))
                     (.var (Agg.schCol Sched.IS_AGENT_CELL))))

/-- The cumulative `is_agent` transition, recolumned. -/
def cumAgentTransitionC : VmConstraint2 :=
  .windowGate
    { onTransition := true
    , body :=
        .add (nxt AggC.IS_AGENT_CUMULATIVE_COL)
          (.add (.mul (.const (-1)) (loc AggC.IS_AGENT_CUMULATIVE_COL))
                (.mul (.const (-1)) (nxt (Agg.schCol Sched.IS_AGENT_CELL)))) }

/-- The active-row-counter transition, recolumned. -/
def cumActiveTransitionC : VmConstraint2 :=
  .windowGate
    { onTransition := true
    , body :=
        .add (nxt AggC.N_CELLS_ACTIVE_COL)
          (.add (.mul (.const (-1)) (loc AggC.N_CELLS_ACTIVE_COL))
                (.mul (.const (-1)) (nxt AggC.CONSISTENT_INDICATOR_COL))) }

/-- Row-0 boundary `cum == is_agent`, recolumned. -/
def firstCumSeedC : VmConstraint2 :=
  .base (.boundary .first
    (.add (.var AggC.IS_AGENT_CUMULATIVE_COL)
          (.mul (.const (-1)) (.var (Agg.schCol Sched.IS_AGENT_CELL)))))

/-- Row-0 boundary `n == consistent`, recolumned. -/
def firstNSeedC : VmConstraint2 :=
  .base (.boundary .first
    (.add (.var AggC.N_CELLS_ACTIVE_COL)
          (.mul (.const (-1)) (.var AggC.CONSISTENT_INDICATOR_COL))))

/-- Last-row boundary `cum == 1`, recolumned. -/
def lastCumIsOneC : VmConstraint2 :=
  .base (.boundary .last
    (.add (.var AggC.IS_AGENT_CUMULATIVE_COL) (.const (-1))))

/-- Last-row binding `n == pi[N_CELLS]`, recolumned. -/
def lastNEqPiC : VmConstraint2 :=
  .base (.piBinding .last AggC.N_CELLS_ACTIVE_COL OuterPi.N_CELLS)

/-- The full v3 constraint list: CG-2 (unchanged, boundary rows) + the NEW identity carries +
CG-4 (recolumned) + boundaries (recolumned). The 35 CG-3 self-check gates are GONE. -/
def aggConstraintsC : List VmConstraint2 :=
  turnIdBindings .first ++ turnIdBindings .last
  ++ identityCarryAll
  ++ [ boolGate (Agg.schCol Sched.IS_AGENT_CELL)
     , boolGate AggC.CONSISTENT_INDICATOR_COL
     , paddingGateC
     , cumAgentTransitionC
     , cumActiveTransitionC ]
  ++ [ firstCumSeedC, firstNSeedC, lastCumIsOneC, lastNEqPiC ]

/-- **The compacted bilateral-aggregation descriptor (v3)** — width 52, the same fixed 23-felt
outer PI, crypto-free. STAGED: proven here, byte-pinned below, NOT yet emitted to
`circuit/descriptors/` (the flag-day step of the bundled regen window). -/
def bilateralAggDescriptorV3 : EffectVmDescriptor2 :=
  { name        := "dregg-bilateral-aggregation-v3"
  , traceWidth  := AggC.WIDTH
  , piCount     := OuterPi.COUNT
  , tables      := []
  , constraints := aggConstraintsC
  , hashSites   := []
  , ranges      := [] }

-- Shape tripwires: 26 CG-2 + 13 identity carries + 5 CG-4 + 4 boundaries = 48 constraints
-- (v2 has 70); 15 window gates (13 identity + 2 cumulative).
#guard aggConstraintsC.length == 48
#guard (aggConstraintsC.filter (fun c => match c with | .windowGate _ => true | _ => false)).length == 15
#guard bilateralAggDescriptorV3.traceWidth == 52
#guard bilateralAggDescriptorV3.piCount == 23
#guard (emitVmJson2 bilateralAggDescriptorV3).startsWith
  "{\"name\":\"dregg-bilateral-aggregation-v3\",\"ir\":2,\"trace_width\":52,\"public_input_count\":23"
-- The FULL byte-pin of the STAGED v3 wire string (the flag-day file content of
-- `circuit/descriptors/dregg-bilateral-aggregation-v3.json`, pinned before it exists).
#guard emitVmJson2 bilateralAggDescriptorV3 ==
  "{\"name\":\"dregg-bilateral-aggregation-v3\",\"ir\":2,\"trace_width\":52,\"public_input_count\":23,\"challenges\":0,\"tables\":[],\"constraints\":[{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":0,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":1,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":2,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":3,\"pi_index\":3},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":4,\"pi_index\":4},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":5,\"pi_index\":5},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":6,\"pi_index\":6},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":7,\"pi_index\":7},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":8,\"pi_index\":8},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":9,\"pi_index\":9},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":10,\"pi_index\":10},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":11,\"pi_index\":11},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":12,\"pi_index\":12},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":0,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":1,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":2,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":3,\"pi_index\":3},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":4,\"pi_index\":4},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":5,\"pi_index\":5},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":6,\"pi_index\":6},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":7,\"pi_index\":7},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":8,\"pi_index\":8},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":9,\"pi_index\":9},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":10,\"pi_index\":10},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":11,\"pi_index\":11},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":12,\"pi_index\":12},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":0}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":1}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":2}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":3}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":4}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":5}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":6}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":7}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":8},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":8}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":9},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":9}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":10},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":10}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":11},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":11}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":12},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":12}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":48},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":48},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":50},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":50},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":50}}},\"r\":{\"t\":\"var\",\"v\":48}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":49},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":49}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":48}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":51},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":51}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":50}}}}},{\"t\":\"boundary\",\"row\":\"first\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":49},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":48}}}},{\"t\":\"boundary\",\"row\":\"first\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":51},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":50}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":49},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":51,\"pi_index\":21}],\"hash_sites\":[],\"ranges\":[]}"

/-! ## §3 — The column maps between the two layouts.

`expandRow` sends a compact row to a v2 row: schedule block unchanged, the expected block
`[49, 84)` filled with the row's OWN carried counts/roots `[13, 48)` (the canonical satisfying
assignment of the tautological CG-3 self-check — the formal face of "nothing pins the expected
block"), accumulators moved up. `contractRow` is its retraction. -/

/-- Compact → v2: `c < 49` schedule (unchanged) · `49 ≤ c < 84` expected := schedule copy ·
`84 ≤ c` accumulators (from 35 lower). (The column binder is ascribed `Nat` so the branch
conditions are syntactically `Nat`-typed — `omega` does not see through the `Var` alias.) -/
def expandRow (w : Assignment) : Assignment := fun c : Nat =>
  if c < 49 then w c
  else if c < 84 then w (13 + (c - 49))
  else w (c - 35)

/-- v2 → compact: `c < 49` schedule (unchanged) · `49 ≤ c` accumulators (from 35 higher; the
expected block is simply dropped). -/
def contractRow (w : Assignment) : Assignment := fun c : Nat =>
  if c < 49 then w c else w (c + 35)

theorem expandRow_sched {c : Nat} (hc : c < 49) (w : Assignment) : expandRow w c = w c := by
  simp only [expandRow]; rw [if_pos hc]

theorem expandRow_exp {c : Nat} (h1 : 49 ≤ c) (h2 : c < 84) (w : Assignment) :
    expandRow w c = w (13 + (c - 49)) := by
  simp only [expandRow]
  rw [if_neg (by omega : ¬ (c < 49)), if_pos h2]

theorem expandRow_cum (w : Assignment) :
    expandRow w Agg.IS_AGENT_CUMULATIVE_COL = w AggC.IS_AGENT_CUMULATIVE_COL := rfl

theorem expandRow_ind (w : Assignment) :
    expandRow w Agg.CONSISTENT_INDICATOR_COL = w AggC.CONSISTENT_INDICATOR_COL := rfl

theorem expandRow_n (w : Assignment) :
    expandRow w Agg.N_CELLS_ACTIVE_COL = w AggC.N_CELLS_ACTIVE_COL := rfl

theorem contractRow_sched {c : Nat} (hc : c < 49) (w : Assignment) : contractRow w c = w c := by
  simp only [contractRow]; rw [if_pos hc]

theorem contractRow_cum (w : Assignment) :
    contractRow w AggC.IS_AGENT_CUMULATIVE_COL = w Agg.IS_AGENT_CUMULATIVE_COL := rfl

theorem contractRow_ind (w : Assignment) :
    contractRow w AggC.CONSISTENT_INDICATOR_COL = w Agg.CONSISTENT_INDICATOR_COL := rfl

theorem contractRow_n (w : Assignment) :
    contractRow w AggC.N_CELLS_ACTIVE_COL = w Agg.N_CELLS_ACTIVE_COL := rfl

theorem contract_expand_at (w : Assignment) (c : Nat) : contractRow (expandRow w) c = w c := by
  by_cases h : c < 49
  · rw [contractRow_sched h, expandRow_sched h]
  · have e1 : contractRow (expandRow w) c = expandRow w (c + 35) := by
      simp only [contractRow]; rw [if_neg h]
    rw [e1]
    simp only [expandRow]
    rw [if_neg (by omega : ¬ (c + 35 < 49)), if_neg (by omega : ¬ (c + 35 < 84)),
        show c + 35 - 35 = c from by omega]

/-- The contraction retracts the expansion EXACTLY (`contractRow ∘ expandRow = id`) — the
expansion is injective, so v3's accept set embeds into v2's. -/
theorem contract_expand (w : Assignment) : contractRow (expandRow w) = w :=
  funext fun c => contract_expand_at w c

theorem expandRow_zero : expandRow zeroAsg = zeroAsg := by
  funext c; simp only [expandRow, zeroAsg]; split_ifs <;> rfl

theorem contractRow_zero : contractRow zeroAsg = zeroAsg := by
  funext c; simp only [contractRow, zeroAsg]; split_ifs <;> rfl

/-- Lift a row map to whole traces (PI and aux tables untouched — the outer PI is IDENTICAL across
the cutover; only the main-trace columns move). -/
def expandT (t : VmTrace) : VmTrace :=
  { rows := t.rows.map expandRow, pub := t.pub, tf := t.tf, chal := t.chal }
def contractT (t : VmTrace) : VmTrace :=
  { rows := t.rows.map contractRow, pub := t.pub, tf := t.tf, chal := t.chal }

theorem contractT_expandT (t : VmTrace) : contractT (expandT t) = t := by
  cases t with
  | mk rows pub tf chal =>
      simp only [contractT, expandT, List.map_map]
      congr 1
      have h : contractRow ∘ expandRow = id := by funext w; exact contract_expand w
      rw [h, List.map_id]

/-- `getD` commutes with a zero-fixed row map (rows in range map through; the off-end default is a
fixed point). -/
theorem getD_map_fixed (f : Assignment → Assignment) (hf : f zeroAsg = zeroAsg) :
    ∀ (l : List Assignment) (i : Nat), (l.map f).getD i zeroAsg = f (l.getD i zeroAsg)
  | [], i => by simp [hf]
  | _ :: _, 0 => by simp
  | _ :: l, (i + 1) => by
      simpa [List.getD_cons_succ] using getD_map_fixed f hf l i

theorem loc_expandT (t : VmTrace) (i : Nat) :
    (envAt (expandT t) i).loc = expandRow ((envAt t i).loc) :=
  getD_map_fixed expandRow expandRow_zero t.rows i

theorem nxt_expandT (t : VmTrace) (i : Nat) :
    (envAt (expandT t) i).nxt = expandRow ((envAt t i).nxt) :=
  getD_map_fixed expandRow expandRow_zero t.rows (i + 1)

theorem loc_contractT (t : VmTrace) (i : Nat) :
    (envAt (contractT t) i).loc = contractRow ((envAt t i).loc) :=
  getD_map_fixed contractRow contractRow_zero t.rows i

theorem nxt_contractT (t : VmTrace) (i : Nat) :
    (envAt (contractT t) i).nxt = contractRow ((envAt t i).nxt) :=
  getD_map_fixed contractRow contractRow_zero t.rows (i + 1)

/-! ## §4 — Crypto-free bookkeeping for the v3 descriptor (mirrors Rung-1's for v2). -/

theorem memOpsOf_aggV3 : memOpsOf bilateralAggDescriptorV3 = [] := rfl
theorem mapOpsOf_aggV3 : mapOpsOf bilateralAggDescriptorV3 = [] := rfl
theorem memLog_aggV3 (t : VmTrace) : memLog bilateralAggDescriptorV3 t = [] := by
  simp [memLog, memOpsOf_aggV3]
theorem mapLog_aggV3 (t : VmTrace) : mapLog bilateralAggDescriptorV3 t = [] := by
  simp [mapLog, mapOpsOf_aggV3]

/-! ## §5 — Generic per-constraint transfer glue + generic extraction (any descriptor). -/

/-- A gate whose body evaluates to LITERAL zero holds on any row (`0 ≡ 0`). -/
theorem gate_of_eval_zero {env : VmRowEnv} {isF isL : Bool} {g : EmittedExpr}
    (he : g.eval env.loc = 0) : VmConstraint.holdsVm env isF isL (.gate g) := by
  cases isL
  · show g.eval env.loc ≡ 0 [ZMOD 2013265921]
    rw [he]
  · trivial

/-- Transfer a gate across environments whose bodies evaluate equal. -/
theorem gateBody_transfer {env env2 : VmRowEnv} {isF isL : Bool} {g g' : EmittedExpr}
    (he : g'.eval env2.loc = g.eval env.loc)
    (h : VmConstraint.holdsVm env isF isL (.gate g)) :
    VmConstraint.holdsVm env2 isF isL (.gate g') := by
  cases isL
  · show g'.eval env2.loc ≡ 0 [ZMOD 2013265921]
    rw [he]; exact h
  · trivial

/-- Transfer a boundary across environments whose bodies evaluate equal. -/
theorem boundary_transfer {env env2 : VmRowEnv} {isF isL : Bool} {row : VmRow} {b b' : EmittedExpr}
    (he : b'.eval env2.loc = b.eval env.loc)
    (h : VmConstraint.holdsVm env isF isL (.boundary row b)) :
    VmConstraint.holdsVm env2 isF isL (.boundary row b') := by
  cases row <;> (intro hf; rw [he]; exact h hf)

/-- Transfer a PI binding across environments agreeing on the (possibly recolumned) bound cell. -/
theorem piBind_transfer {env env2 : VmRowEnv} {isF isL : Bool} {row : VmRow} {col col' k : Nat}
    (hloc : env2.loc col' = env.loc col) (hpub : env2.pub = env.pub)
    (h : VmConstraint.holdsVm env isF isL (.piBinding row col k)) :
    VmConstraint.holdsVm env2 isF isL (.piBinding row col' k) := by
  cases row <;> (intro hf; rw [hloc, hpub]; exact h hf)

section Generic
variable {hash : List ℤ → ℤ} {d : EffectVmDescriptor2}
variable {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- Generic form of Rung-1's `window_forces` (any descriptor). -/
theorem window_forcesD (hsat : Satisfied2 hash d minit mfin maddrs t) {i : Nat}
    (hi : i < t.rows.length) (hnl : i + 1 ≠ t.rows.length)
    {w : WindowConstraint} (hw : VmConstraint2.windowGate w ∈ d.constraints)
    (honT : w.onTransition = true) :
    w.body.eval (envAt t i) ≡ 0 [ZMOD 2013265921] := by
  have hrc := hsat.rowConstraints i hi _ hw
  have hlf : (i + 1 == t.rows.length) = false := by simpa using hnl
  simp only [VmConstraint2.holdsAt, WindowConstraint.holdsAt, honT, if_true] at hrc
  exact hrc hlf

/-- Generic form of Rung-1's `piFirst_forces` (any descriptor). -/
theorem piFirst_forcesD (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hpos : 0 < t.rows.length) {col k : Nat}
    (hb : VmConstraint2.base (.piBinding .first col k) ∈ d.constraints) :
    (envAt t 0).loc col ≡ t.pub k [ZMOD 2013265921] := by
  have hrc := hsat.rowConstraints 0 hpos _ hb
  exact (holdsVm_piFirst_true (envAt t 0) (0 + 1 == t.rows.length) col k).mp hrc

/-- Generic form of Rung-1's `boundaryLast_forces` (any descriptor). -/
theorem boundaryLast_forcesD (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hpos : 0 < t.rows.length) {b : EmittedExpr}
    (hb : VmConstraint2.base (.boundary .last b) ∈ d.constraints) :
    b.eval (envAt t (t.rows.length - 1)).loc ≡ 0 [ZMOD 2013265921] := by
  have hlt : t.rows.length - 1 < t.rows.length := Nat.sub_lt hpos Nat.one_pos
  have hrc := hsat.rowConstraints (t.rows.length - 1) hlt _ hb
  have hlast_true : (t.rows.length - 1 + 1 == t.rows.length) = true := by
    rw [Nat.sub_add_cancel hpos]; exact beq_self_eq_true _
  rw [hlast_true] at hrc
  exact (holdsVm_boundaryLast_true (envAt t (t.rows.length - 1)) (t.rows.length - 1 == 0) b).mp hrc

end Generic

/-! ## §6 — Membership + shape lemmas for the two constraint lists. -/

/-- Every CG-2 binding is a `piBinding` on an identity slot (< 13). -/
theorem turnIdBindings_shape {row : VmRow} {c : VmConstraint2} (h : c ∈ turnIdBindings row) :
    ∃ col k, col < 13 ∧ c = cg2PiBind row col k := by
  unfold turnIdBindings at h
  rcases List.mem_append.mp h with h1 | h1
  · rcases List.mem_append.mp h1 with h2 | h2
    · rcases List.mem_append.mp h2 with h3 | h3
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h3
        have hi' := List.mem_range.mp hi
        refine ⟨_, _, ?_, rfl⟩
        simp only [Agg.schCol, Agg.SCHED_BASE, Sched.TURN_HASH_BASE, OuterPi.TURN_HASH_LEN] at hi' ⊢
        omega
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h3
        have hi' := List.mem_range.mp hi
        refine ⟨_, _, ?_, rfl⟩
        simp only [Agg.schCol, Agg.SCHED_BASE, Sched.EFFECTS_HASH_GLOBAL_BASE,
          OuterPi.EFFECTS_HASH_GLOBAL_LEN] at hi' ⊢
        omega
    · rw [List.mem_singleton] at h2
      subst h2
      refine ⟨_, _, ?_, rfl⟩
      simp only [Agg.schCol, Agg.SCHED_BASE, Sched.ACTOR_NONCE]
      omega
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h1
    have hi' := List.mem_range.mp hi
    refine ⟨_, _, ?_, rfl⟩
    simp only [Agg.schCol, Agg.SCHED_BASE, Sched.PREVIOUS_RECEIPT_HASH_BASE,
      OuterPi.PREVIOUS_RECEIPT_HASH_LEN] at hi' ⊢
    omega

/-- Every CG-3 replay gate is `sched[a] − expected[b]` with `13 ≤ a < 48`, `b = a + 36`. -/
theorem scheduleReplay_shape {c : VmConstraint2} (h : c ∈ scheduleReplay) :
    ∃ a b, 13 ≤ a ∧ a < 48 ∧ b = a + 36 ∧ c = cg3Eq a b := by
  unfold scheduleReplay at h
  rcases List.mem_append.mp h with h1 | h1
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h1
    have hk' := List.mem_range.mp hk
    refine ⟨_, _, ?_, ?_, ?_, rfl⟩ <;>
      · simp only [Agg.schCol, Agg.SCHED_BASE, Sched.COUNTS_BASE, Sched.COUNTS_LEN,
          Agg.EXPECTED_COUNTS_BASE, Sched.WIDTH] at hk' ⊢
        omega
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h1
    have hk' := List.mem_range.mp hk
    refine ⟨_, _, ?_, ?_, ?_, rfl⟩ <;>
      · simp only [Agg.schCol, Agg.SCHED_BASE, Sched.ROOTS_BASE, Sched.ROOTS_LEN,
          Agg.EXPECTED_ROOTS_BASE, Agg.EXPECTED_COUNTS_BASE, Agg.EXPECTED_COUNTS_LEN,
          Sched.WIDTH] at hk' ⊢
        omega

/-- Each identity slot's first/last binding is genuinely in `turnIdBindings` (the slot and PI
indices coincide on the identity prefix). -/
theorem mem_identity_bind (row : VmRow) (c : Nat) (hc : c < 13) :
    VmConstraint2.base (.piBinding row c c) ∈ turnIdBindings row := by
  rcases Nat.lt_or_ge c 4 with h4 | h4
  · have h := mem_turn_hash row c (by simpa [OuterPi.TURN_HASH_LEN] using h4)
    simpa [cg2PiBind, Agg.schCol, Agg.SCHED_BASE, Sched.TURN_HASH_BASE,
      OuterPi.TURN_HASH_BASE] using h
  · rcases Nat.lt_or_ge c 8 with h8 | h8
    · have h := mem_turn_effects row (c - 4)
        (by simp only [OuterPi.EFFECTS_HASH_GLOBAL_LEN]; omega)
      simpa [cg2PiBind, Agg.schCol, Agg.SCHED_BASE, Sched.EFFECTS_HASH_GLOBAL_BASE,
        OuterPi.EFFECTS_HASH_GLOBAL_BASE, show 4 + (c - 4) = c from by omega] using h
    · rcases Nat.lt_or_ge c 9 with h9 | h9
      · have hc8 : c = 8 := by omega
        subst hc8
        have h := mem_turn_nonce row
        simpa [cg2PiBind, Agg.schCol, Agg.SCHED_BASE, Sched.ACTOR_NONCE,
          OuterPi.ACTOR_NONCE] using h
      · have h := mem_turn_prev row (c - 9)
          (by simp only [OuterPi.PREVIOUS_RECEIPT_HASH_LEN]; omega)
        simpa [cg2PiBind, Agg.schCol, Agg.SCHED_BASE, Sched.PREVIOUS_RECEIPT_HASH_BASE,
          OuterPi.PREVIOUS_RECEIPT_HASH_BASE, show 9 + (c - 9) = c from by omega] using h

-- v3 membership: the list is ((((A ++ B) ++ Carry) ++ CG4) ++ Bnd).

theorem memC_turnFirst {c : VmConstraint2} (h : c ∈ turnIdBindings .first) :
    c ∈ bilateralAggDescriptorV3.constraints := by
  show c ∈ aggConstraintsC; unfold aggConstraintsC
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ h)))

theorem memC_turnLast {c : VmConstraint2} (h : c ∈ turnIdBindings .last) :
    c ∈ bilateralAggDescriptorV3.constraints := by
  show c ∈ aggConstraintsC; unfold aggConstraintsC
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ h)))

theorem memC_identityCarry {j : Nat} (hj : j < 13) :
    identityCarry j ∈ bilateralAggDescriptorV3.constraints := by
  show _ ∈ aggConstraintsC; unfold aggConstraintsC
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
  unfold identityCarryAll
  exact List.mem_map_of_mem (List.mem_range.mpr (by simpa [AggC.IDENTITY_LEN] using hj))

theorem memC_boolAgent : boolGate (Agg.schCol Sched.IS_AGENT_CELL)
    ∈ bilateralAggDescriptorV3.constraints := by
  show _ ∈ aggConstraintsC; unfold aggConstraintsC
  exact List.mem_append_left _ (List.mem_append_right _ (by simp [List.mem_cons]))

theorem memC_boolConsistent : boolGate AggC.CONSISTENT_INDICATOR_COL
    ∈ bilateralAggDescriptorV3.constraints := by
  show _ ∈ aggConstraintsC; unfold aggConstraintsC
  exact List.mem_append_left _ (List.mem_append_right _ (by simp [List.mem_cons]))

theorem memC_padding : paddingGateC ∈ bilateralAggDescriptorV3.constraints := by
  show _ ∈ aggConstraintsC; unfold aggConstraintsC
  exact List.mem_append_left _ (List.mem_append_right _ (by simp [List.mem_cons]))

theorem memC_cumAgent : cumAgentTransitionC ∈ bilateralAggDescriptorV3.constraints := by
  show _ ∈ aggConstraintsC; unfold aggConstraintsC
  exact List.mem_append_left _ (List.mem_append_right _ (by simp [List.mem_cons]))

theorem memC_cumActive : cumActiveTransitionC ∈ bilateralAggDescriptorV3.constraints := by
  show _ ∈ aggConstraintsC; unfold aggConstraintsC
  exact List.mem_append_left _ (List.mem_append_right _ (by simp [List.mem_cons]))

theorem memC_firstCumSeed : firstCumSeedC ∈ bilateralAggDescriptorV3.constraints := by
  show _ ∈ aggConstraintsC; unfold aggConstraintsC
  exact List.mem_append_right _ (by simp [List.mem_cons])

theorem memC_firstNSeed : firstNSeedC ∈ bilateralAggDescriptorV3.constraints := by
  show _ ∈ aggConstraintsC; unfold aggConstraintsC
  exact List.mem_append_right _ (by simp [List.mem_cons])

theorem memC_lastCum : lastCumIsOneC ∈ bilateralAggDescriptorV3.constraints := by
  show _ ∈ aggConstraintsC; unfold aggConstraintsC
  exact List.mem_append_right _ (by simp [List.mem_cons])

theorem memC_lastNEqPi : lastNEqPiC ∈ bilateralAggDescriptorV3.constraints := by
  show _ ∈ aggConstraintsC; unfold aggConstraintsC
  exact List.mem_append_right _ (by simp [List.mem_cons])

-- v2 membership for the one item Rung-1 §3 did not cover.
theorem memV2_padding : paddingGate ∈ bilateralAggDescriptor.constraints := by
  show _ ∈ aggConstraints; unfold aggConstraints
  exact List.mem_append_left _ (List.mem_append_right _ (by simp [List.mem_cons]))

/-! ## §7 — THE COMPACTION BRIDGE (direction A): v3 accepts a SUBSET of v2.

Any v3-satisfying trace expands (same outer PI) to a FULL `Satisfied2` witness of the DEPLOYED v2
descriptor. This is the byte-safe soundness half: deleting the expected block + adding the identity
carries cannot admit anything v2 refuses. -/

theorem expand_satisfies
    {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash bilateralAggDescriptorV3 minit mfin maddrs t) :
    Satisfied2 hash bilateralAggDescriptor minit mfin maddrs (expandT t) := by
  have hlen : (expandT t).rows.length = t.rows.length := by simp [expandT]
  refine
    { rowConstraints := ?_
      rowHashes := by intro i _; trivial
      rowRanges := by
        intro i _ r hr
        simp only [bilateralAggDescriptor, List.not_mem_nil] at hr
      memAddrsNodup := hsat.memAddrsNodup
      memClosed := by rw [memLog_agg]; simp
      memDisciplined := by rw [memLog_agg]; trivial
      memBalanced := by
        have hb := hsat.memBalanced
        rw [memLog_aggV3] at hb
        rw [memLog_agg]; exact hb
      memTableFaithful := by
        have hb := hsat.memTableFaithful
        rw [memLog_aggV3] at hb
        show t.tf .memory = _
        rw [memLog_agg]; exact hb
      mapTableFaithful := by
        have hb := hsat.mapTableFaithful
        rw [mapLog_aggV3] at hb
        show t.tf .mapOps = _
        rw [mapLog_agg]; exact hb }
  intro i hi c hc
  rw [hlen] at hi ⊢
  have hpub : (envAt (expandT t) i).pub = (envAt t i).pub := rfl
  have hc' : c ∈ aggConstraints := hc
  unfold aggConstraints at hc'
  rcases List.mem_append.mp hc' with h1 | hBnd
  · rcases List.mem_append.mp h1 with h2 | hCg4
    · rcases List.mem_append.mp h2 with h3 | hRep
      · rcases List.mem_append.mp h3 with hA | hB
        · -- CG-2 first-row bindings: identical constraint in v3 (identity cols untouched).
          obtain ⟨col, k, hcol, rfl⟩ := turnIdBindings_shape hA
          have h3' := hsat.rowConstraints i hi _ (memC_turnFirst hA)
          simp only [cg2PiBind, VmConstraint2.holdsAt] at h3' ⊢
          exact piBind_transfer
            (by rw [loc_expandT]; exact expandRow_sched (by omega) _) hpub h3'
        · -- CG-2 last-row bindings: identical constraint in v3.
          obtain ⟨col, k, hcol, rfl⟩ := turnIdBindings_shape hB
          have h3' := hsat.rowConstraints i hi _ (memC_turnLast hB)
          simp only [cg2PiBind, VmConstraint2.holdsAt] at h3' ⊢
          exact piBind_transfer
            (by rw [loc_expandT]; exact expandRow_sched (by omega) _) hpub h3'
      · -- CG-3 replay gates: the expansion fills expected := schedule, so the body is LITERALLY 0.
        obtain ⟨a, b, ha1, ha2, hb, rfl⟩ := scheduleReplay_shape hRep
        simp only [cg3Eq, colEqCol, VmConstraint2.holdsAt]
        apply gate_of_eval_zero
        simp only [EmittedExpr.eval]
        rw [loc_expandT,
            expandRow_sched (c := a) (by omega) ((envAt t i).loc),
            expandRow_exp (c := b) (by omega) (by omega) ((envAt t i).loc),
            show 13 + (b - 49) = a from by omega]
        ring
    · -- CG-4: recolumned twins.
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hCg4
      rcases hCg4 with rfl | rfl | rfl | rfl | rfl
      · -- boolGate is_agent (col 48, unchanged)
        have h3' := hsat.rowConstraints i hi _ memC_boolAgent
        simp only [boolGate, VmConstraint2.holdsAt] at h3' ⊢
        refine gateBody_transfer ?_ h3'
        simp only [EmittedExpr.eval]
        rw [loc_expandT,
            expandRow_sched (c := Agg.schCol Sched.IS_AGENT_CELL) (by decide) ((envAt t i).loc)]
      · -- boolGate consistent (85 ← 50)
        have h3' := hsat.rowConstraints i hi _ memC_boolConsistent
        simp only [boolGate, VmConstraint2.holdsAt] at h3' ⊢
        refine gateBody_transfer ?_ h3'
        simp only [EmittedExpr.eval]
        rw [loc_expandT, expandRow_ind]
      · -- paddingGate
        have h3' := hsat.rowConstraints i hi _ memC_padding
        simp only [paddingGate, paddingGateC, VmConstraint2.holdsAt] at h3' ⊢
        refine gateBody_transfer ?_ h3'
        simp only [EmittedExpr.eval]
        rw [loc_expandT, expandRow_ind,
            expandRow_sched (c := Agg.schCol Sched.IS_AGENT_CELL) (by decide) ((envAt t i).loc)]
      · -- cumAgentTransition (window, 84 ← 49)
        have h3' := hsat.rowConstraints i hi _ memC_cumAgent
        simp only [cumAgentTransitionC, VmConstraint2.holdsAt] at h3'
        simp only [cumAgentTransition, VmConstraint2.holdsAt]
        intro hL
        have hb := h3' hL
        simp only [WindowExpr.eval] at hb ⊢
        rw [loc_expandT, nxt_expandT, expandRow_cum, expandRow_cum,
            expandRow_sched (c := Agg.schCol Sched.IS_AGENT_CELL) (by decide) ((envAt t i).nxt)]
        exact hb
      · -- cumActiveTransition (window, 86/85 ← 51/50)
        have h3' := hsat.rowConstraints i hi _ memC_cumActive
        simp only [cumActiveTransitionC, VmConstraint2.holdsAt] at h3'
        simp only [cumActiveTransition, VmConstraint2.holdsAt]
        intro hL
        have hb := h3' hL
        simp only [WindowExpr.eval] at hb ⊢
        rw [loc_expandT, nxt_expandT, expandRow_n, expandRow_n, expandRow_ind]
        exact hb
  · -- Boundaries: recolumned twins.
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hBnd
    rcases hBnd with rfl | rfl | rfl | rfl
    · -- firstCumSeed
      have h3' := hsat.rowConstraints i hi _ memC_firstCumSeed
      simp only [firstCumSeed, firstCumSeedC, VmConstraint2.holdsAt] at h3' ⊢
      refine boundary_transfer ?_ h3'
      simp only [EmittedExpr.eval]
      rw [loc_expandT, expandRow_cum,
          expandRow_sched (c := Agg.schCol Sched.IS_AGENT_CELL) (by decide) ((envAt t i).loc)]
    · -- firstNSeed
      have h3' := hsat.rowConstraints i hi _ memC_firstNSeed
      simp only [firstNSeed, firstNSeedC, VmConstraint2.holdsAt] at h3' ⊢
      refine boundary_transfer ?_ h3'
      simp only [EmittedExpr.eval]
      rw [loc_expandT, expandRow_n, expandRow_ind]
    · -- lastCumIsOne
      have h3' := hsat.rowConstraints i hi _ memC_lastCum
      simp only [lastCumIsOne, lastCumIsOneC, VmConstraint2.holdsAt] at h3' ⊢
      refine boundary_transfer ?_ h3'
      simp only [EmittedExpr.eval]
      rw [loc_expandT, expandRow_cum]
    · -- lastNEqPi
      have h3' := hsat.rowConstraints i hi _ memC_lastNEqPi
      simp only [lastNEqPi, lastNEqPiC, VmConstraint2.holdsAt] at h3' ⊢
      exact piBind_transfer (by rw [loc_expandT]; exact expandRow_n _) hpub h3'

/-! ## §8 — HONEST-WITNESS PRESERVATION (direction B) + the STRICTNESS teeth. -/

/-- The identity slots are row-constant — what the DEPLOYED trace builder
`build_aggregation_trace_v2` produces by construction: every active cell carries the bundle's one
shared turn identity, and padding rows mirror the first row's identity slots (that mirroring exists
in the Rust precisely so the v2 last-row CG-2 binding holds; under v3 it is what the identity-carry
gates check IN-CIRCUIT). -/
def IdentityConstant (t : VmTrace) : Prop :=
  ∀ i, i + 1 < t.rows.length → ∀ c : Nat, c < 13 → rowAt t (i + 1) c = rowAt t i c

/-- **Every honest v2 witness contracts to a v3 witness.** The deleted CG-3 gates constrained
nothing (both sides prover-filled); the only NEW obligation is the identity carry, supplied by
`IdentityConstant`. -/
theorem contract_preserves
    {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash bilateralAggDescriptor minit mfin maddrs t)
    (hid : IdentityConstant t) :
    Satisfied2 hash bilateralAggDescriptorV3 minit mfin maddrs (contractT t) := by
  have hlen : (contractT t).rows.length = t.rows.length := by simp [contractT]
  refine
    { rowConstraints := ?_
      rowHashes := by intro i _; trivial
      rowRanges := by
        intro i _ r hr
        simp only [bilateralAggDescriptorV3, List.not_mem_nil] at hr
      memAddrsNodup := hsat.memAddrsNodup
      memClosed := by rw [memLog_aggV3]; simp
      memDisciplined := by rw [memLog_aggV3]; trivial
      memBalanced := by
        have hb := hsat.memBalanced
        rw [memLog_agg] at hb
        rw [memLog_aggV3]; exact hb
      memTableFaithful := by
        have hb := hsat.memTableFaithful
        rw [memLog_agg] at hb
        show t.tf .memory = _
        rw [memLog_aggV3]; exact hb
      mapTableFaithful := by
        have hb := hsat.mapTableFaithful
        rw [mapLog_agg] at hb
        show t.tf .mapOps = _
        rw [mapLog_aggV3]; exact hb }
  intro i hi c hc
  rw [hlen] at hi ⊢
  have hpub : (envAt (contractT t) i).pub = (envAt t i).pub := rfl
  have hc' : c ∈ aggConstraintsC := hc
  unfold aggConstraintsC at hc'
  rcases List.mem_append.mp hc' with h1 | hBnd
  · rcases List.mem_append.mp h1 with h2 | hCg4
    · rcases List.mem_append.mp h2 with h3 | hCarry
      · rcases List.mem_append.mp h3 with hA | hB
        · -- CG-2 first-row bindings: identical constraint in v2.
          obtain ⟨col, k, hcol, rfl⟩ := turnIdBindings_shape hA
          have h2' := hsat.rowConstraints i hi _ (mem_A hA)
          simp only [cg2PiBind, VmConstraint2.holdsAt] at h2' ⊢
          exact piBind_transfer
            (by rw [loc_contractT]; exact contractRow_sched (by omega) _) hpub h2'
        · -- CG-2 last-row bindings: identical constraint in v2.
          obtain ⟨col, k, hcol, rfl⟩ := turnIdBindings_shape hB
          have h2' := hsat.rowConstraints i hi _ (mem_B hB)
          simp only [cg2PiBind, VmConstraint2.holdsAt] at h2' ⊢
          exact piBind_transfer
            (by rw [loc_contractT]; exact contractRow_sched (by omega) _) hpub h2'
      · -- The NEW identity carries: discharged by IdentityConstant.
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hCarry
        have hj13 : j < 13 := by simpa [AggC.IDENTITY_LEN] using List.mem_range.mp hj
        simp only [identityCarry, VmConstraint2.holdsAt]
        intro hL
        have hne : i + 1 ≠ t.rows.length := by
          intro h; rw [h] at hL; simp at hL
        have hi1 : i + 1 < t.rows.length := by omega
        simp only [WindowExpr.eval]
        rw [loc_contractT, nxt_contractT,
            contractRow_sched (c := j) (by omega) ((envAt t i).nxt),
            contractRow_sched (c := j) (by omega) ((envAt t i).loc),
            show (envAt t i).nxt j = (envAt t i).loc j from hid i hi1 j hj13]
        exact eqToModEq (by ring)
    · -- CG-4: recolumned twins.
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hCg4
      rcases hCg4 with rfl | rfl | rfl | rfl | rfl
      · have h2' := hsat.rowConstraints i hi _ mem_boolIsAgent
        simp only [boolGate, VmConstraint2.holdsAt] at h2' ⊢
        refine gateBody_transfer ?_ h2'
        simp only [EmittedExpr.eval]
        rw [loc_contractT,
            contractRow_sched (c := Agg.schCol Sched.IS_AGENT_CELL) (by decide) ((envAt t i).loc)]
      · have h2' := hsat.rowConstraints i hi _ mem_boolConsistent
        simp only [boolGate, VmConstraint2.holdsAt] at h2' ⊢
        refine gateBody_transfer ?_ h2'
        simp only [EmittedExpr.eval]
        rw [loc_contractT, contractRow_ind]
      · have h2' := hsat.rowConstraints i hi _ memV2_padding
        simp only [paddingGate, paddingGateC, VmConstraint2.holdsAt] at h2' ⊢
        refine gateBody_transfer ?_ h2'
        simp only [EmittedExpr.eval]
        rw [loc_contractT, contractRow_ind,
            contractRow_sched (c := Agg.schCol Sched.IS_AGENT_CELL) (by decide) ((envAt t i).loc)]
      · have h2' := hsat.rowConstraints i hi _ mem_cumAgentTransition
        simp only [cumAgentTransition, VmConstraint2.holdsAt] at h2'
        simp only [cumAgentTransitionC, VmConstraint2.holdsAt]
        intro hL
        have hb := h2' hL
        simp only [WindowExpr.eval] at hb ⊢
        rw [loc_contractT, nxt_contractT, contractRow_cum, contractRow_cum,
            contractRow_sched (c := Agg.schCol Sched.IS_AGENT_CELL) (by decide) ((envAt t i).nxt)]
        exact hb
      · have h2' := hsat.rowConstraints i hi _ mem_cumActiveTransition
        simp only [cumActiveTransition, VmConstraint2.holdsAt] at h2'
        simp only [cumActiveTransitionC, VmConstraint2.holdsAt]
        intro hL
        have hb := h2' hL
        simp only [WindowExpr.eval] at hb ⊢
        rw [loc_contractT, nxt_contractT, contractRow_n, contractRow_n, contractRow_ind]
        exact hb
  · -- Boundaries: recolumned twins.
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hBnd
    rcases hBnd with rfl | rfl | rfl | rfl
    · have h2' := hsat.rowConstraints i hi _ mem_firstCumSeed
      simp only [firstCumSeed, firstCumSeedC, VmConstraint2.holdsAt] at h2' ⊢
      refine boundary_transfer ?_ h2'
      simp only [EmittedExpr.eval]
      rw [loc_contractT, contractRow_cum,
          contractRow_sched (c := Agg.schCol Sched.IS_AGENT_CELL) (by decide) ((envAt t i).loc)]
    · have h2' := hsat.rowConstraints i hi _ mem_firstNSeed
      simp only [firstNSeed, firstNSeedC, VmConstraint2.holdsAt] at h2' ⊢
      refine boundary_transfer ?_ h2'
      simp only [EmittedExpr.eval]
      rw [loc_contractT, contractRow_n, contractRow_ind]
    · have h2' := hsat.rowConstraints i hi _ mem_lastCumIsOne
      simp only [lastCumIsOne, lastCumIsOneC, VmConstraint2.holdsAt] at h2' ⊢
      refine boundary_transfer ?_ h2'
      simp only [EmittedExpr.eval]
      rw [loc_contractT, contractRow_cum]
    · have h2' := hsat.rowConstraints i hi _ mem_lastNEqPi
      simp only [lastNEqPi, lastNEqPiC, VmConstraint2.holdsAt] at h2' ⊢
      exact piBind_transfer (by rw [loc_contractT]; exact contractRow_n _) hpub h2'

/-! ### The honest witness survives: Rung-1's `witTrace` contracts to a v3 witness. -/

/-- The honest 2-cell bundle carries a constant (all-zero) turn identity. -/
theorem witTrace_identityConstant : IdentityConstant witTrace := by
  intro i hi c hc
  have hi0 : i = 0 := by
    have hlen : witTrace.rows.length = 2 := rfl
    omega
  subst hi0
  show wr1 c = wr0 c
  interval_cases c <;> decide

/-- The compact image of the honest witness. -/
def witV3 : VmTrace := contractT witTrace

/-- **The v3 accept set is inhabited** — by the image of the genuine Rung-1 witness, THROUGH the
preservation bridge (exercising direction B end-to-end). -/
theorem witV3_satisfies :
    Satisfied2 hash0 bilateralAggDescriptorV3 (fun _ => 0) (fun _ => (0, 0)) [] witV3 :=
  contract_preserves witTrace_satisfies witTrace_identityConstant

/-! ### The gap tooth: v2 ACCEPTS a middle-row identity forgery; v3 REFUSES it. -/

/-- Gap cell 0: honest non-agent cell (`consistent = 1`, `n = 1`), identity all `0`. -/
def g0 : Assignment := fun j => if j = 85 then 1 else if j = 86 then 1 else 0
/-- Gap cell 1 (the MIDDLE cell): carries a FORGED `turn_hash[0] = 7` — disagreeing with the
published outer PI — plus honest accounting (`consistent = 1`, `n = 2`). v2 constrains NOTHING
about this row's identity slots. -/
def g1 : Assignment :=
  fun j => if j = 0 then 7 else if j = 85 then 1 else if j = 86 then 2 else 0
/-- Gap cell 2 (the last cell): the agent cell (`is_agent = 1`, `cum = 1`, `n = 3`), identity `0`
(matching the outer PI, so the last-row CG-2 binding is satisfied). -/
def g2 : Assignment :=
  fun j => if j = 48 then 1 else if j = 84 then 1 else if j = 85 then 1 else if j = 86 then 3 else 0
/-- Published outer PI: `n_cells = 3`, turn identity all `0`. -/
def gpub : Assignment := fun j => if j = 21 then 3 else 0
/-- The 3-cell gap bundle: honest ends, forged middle. -/
def gapTrace : VmTrace := { rows := [g0, g1, g2], pub := gpub, tf := fun _ => [] }

/-- **v2 ACCEPTS the forgery** — the middle row's turn-identity columns are unconstrained
(CG-2 binds first/last only; CG-3 is the self-check, satisfied by `0 = 0`), so the bundle
`Satisfied2`s the deployed descriptor while its middle cell claims a DIFFERENT turn. -/
theorem gapTrace_satisfies :
    Satisfied2 hash0 bilateralAggDescriptor (fun _ => 0) (fun _ => (0, 0)) [] gapTrace where
  rowConstraints := by
    intro i hi c hc
    have hi3 : i < 3 := hi
    rw [show gapTrace.rows.length = 3 from rfl]
    simp only [bilateralAggDescriptor] at hc
    interval_cases i <;>
      fin_cases hc <;>
      simp only [cg2PiBind, cg3Eq, colEqCol, boolGate, paddingGate, cumAgentTransition,
        cumActiveTransition, firstCumSeed, firstNSeed, lastCumIsOne, lastNEqPi,
        VmConstraint2.holdsAt, VmConstraint.holdsVm, WindowConstraint.holdsAt,
        gapTrace, envAt, gpub, EmittedExpr.eval, WindowExpr.eval,
        Nat.reduceAdd, Nat.reduceBEq, reduceIte, reduceCtorEq] <;>
      decide
  rowHashes := by intro i _; trivial
  rowRanges := by intro i _ r hr; simp only [bilateralAggDescriptor, List.not_mem_nil] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by rw [memLog_agg]; simp
  memDisciplined := by rw [memLog_agg]; trivial
  memBalanced := by rw [memLog_agg]; exact memCheck_nil _ _
  memTableFaithful := by rw [memLog_agg]; rfl
  mapTableFaithful := by rw [mapLog_agg]; rfl

/-- The forgery is REAL: the middle cell's carried `turn_hash[0]` differs from the published one. -/
theorem gapTrace_forged : rowAt gapTrace 1 0 = 7 ∧ gapTrace.pub 0 = 0 := ⟨rfl, rfl⟩

/-- **v3 REFUSES the forgery** — the identity-carry window gate on slot 0 fires on the row-0
transition: `7 − 0 ≢ 0 [ZMOD p]`. The middle-row identity gap is CLOSED in-circuit. -/
theorem gapTrace_contract_not_v3 :
    ¬ Satisfied2 hash0 bilateralAggDescriptorV3 (fun _ => 0) (fun _ => (0, 0)) []
        (contractT gapTrace) := by
  intro h
  have hstep := window_forcesD h (i := 0) (by decide) (by decide)
    (memC_identityCarry (j := 0) (by omega)) rfl
  simp only [WindowExpr.eval] at hstep
  have h7 : (envAt (contractT gapTrace) 0).nxt 0
      + (-1) * (envAt (contractT gapTrace) 0).loc 0 = 7 := by decide
  rw [h7] at hstep
  obtain ⟨k, hk⟩ := hstep.dvd
  omega

/-- **No v3-accepted trace expands to the forged bundle** (the expansion is injective —
`contractT ∘ expandT = id` — so the strengthening is STRICT: v3's accept set embeds into v2's and
misses `gapTrace`). -/
theorem gap_no_v3_preimage (s : VmTrace) (hs : expandT s = gapTrace) :
    ¬ Satisfied2 hash0 bilateralAggDescriptorV3 (fun _ => 0) (fun _ => (0, 0)) [] s := by
  have hsc : s = contractT gapTrace := by rw [← hs, contractT_expandT]
  rw [hsc]
  exact gapTrace_contract_not_v3

/-- The single-agent boundary still bites in v3 (the compact descriptor is not vacuous): the
all-zero one-row bundle fails `Satisfied2`. -/
def badTraceC : VmTrace := { rows := [zeroAsg], pub := zeroAsg, tf := fun _ => [] }

theorem badTraceC_not_satisfied :
    ¬ Satisfied2 hash0 bilateralAggDescriptorV3 (fun _ => 0) (fun _ => (0, 0)) [] badTraceC := by
  intro h
  have hb := boundaryLast_forcesD h (by decide) memC_lastCum
  simp only [EmittedExpr.eval] at hb
  have h1 : (envAt badTraceC (badTraceC.rows.length - 1)).loc AggC.IS_AGENT_CUMULATIVE_COL
      + (-1) = -1 := by decide
  rw [h1] at hb
  obtain ⟨k, hk⟩ := hb.dvd
  omega

/-! ## §9 — The POSITIVE strengthening content + the crown, carried through the bridge. -/

/-- **Under v3, EVERY row carries the published turn identity** (mod `p`): the first-row binding
seeds it, the identity-carry chain propagates it. v2 could only say this for the first/last rows. -/
theorem identity_chain
    {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash bilateralAggDescriptorV3 minit mfin maddrs t)
    {c : Nat} (hc : c < 13) :
    ∀ j, j < t.rows.length → rowAt t j c ≡ t.pub c [ZMOD 2013265921] := by
  intro j
  induction j with
  | zero =>
      intro hj
      exact piFirst_forcesD hsat hj (memC_turnFirst (mem_identity_bind .first c hc))
  | succ n ih =>
      intro hj
      have hn : n < t.rows.length := by omega
      have hstep := window_forcesD hsat hn (by omega) (memC_identityCarry hc) rfl
      simp only [WindowExpr.eval] at hstep
      have h1 : (envAt t n).nxt c ≡ (envAt t n).loc c [ZMOD 2013265921] :=
        (gate_modEq_iff (by ring)).mp hstep
      have h1' : rowAt t (n + 1) c ≡ rowAt t n c [ZMOD 2013265921] := h1
      exact h1'.trans (ih hn)

/-- **The v3 canonicality envelope** — the recolumning of Rung-1's `AggTraceCanon` (the deployed
range-check invariant + last-row booleanity of the two contribution columns, whose gates the
transition-zerofier lowering drops on the last row). Inhabited by `witV3` (`witV3_canon`). -/
structure AggCTraceCanon (t : VmTrace) : Prop where
  cells : ∀ i c, 0 ≤ rowAt t i c ∧ rowAt t i c < 2013265921
  pubs : ∀ k, 0 ≤ t.pub k ∧ t.pub k < 2013265921
  lastAgentBool :
    isAgentAt t (t.rows.length - 1) = 0 ∨ isAgentAt t (t.rows.length - 1) = 1
  lastConsistentBool :
    rowAt t (t.rows.length - 1) AggC.CONSISTENT_INDICATOR_COL = 0
    ∨ rowAt t (t.rows.length - 1) AggC.CONSISTENT_INDICATOR_COL = 1

theorem rowAt_expandT (t : VmTrace) (i : Nat) :
    rowAt (expandT t) i = expandRow (rowAt t i) :=
  loc_expandT t i

/-- The agent flag lives below col 49, so the expansion preserves it. -/
theorem isAgentAt_expandT (t : VmTrace) (j : Nat) :
    isAgentAt (expandT t) j = isAgentAt t j := by
  show rowAt (expandT t) j _ = rowAt t j _
  rw [rowAt_expandT]
  exact expandRow_sched (by decide) _

/-- The v3 envelope transports to the v2 envelope of the expanded trace (every expanded cell IS a
compact cell). -/
theorem canon_expandT {t : VmTrace} (h : AggCTraceCanon t) : AggTraceCanon (expandT t) where
  cells := by
    intro i c
    rw [rowAt_expandT]
    simp only [expandRow]
    split_ifs <;> exact h.cells i _
  pubs := h.pubs
  lastAgentBool := by
    have hlen : (expandT t).rows.length = t.rows.length := by simp [expandT]
    rw [hlen, isAgentAt_expandT]
    exact h.lastAgentBool
  lastConsistentBool := by
    have hlen : (expandT t).rows.length = t.rows.length := by simp [expandT]
    simp only [consistentAt]
    rw [hlen, rowAt_expandT, expandRow_ind]
    exact h.lastConsistentBool

/-- The honest compact witness inhabits the envelope (the hypothesis set of every corollary below
is jointly satisfiable). -/
theorem witV3_canon : AggCTraceCanon witV3 := by
  have hcells : ∀ i c, 0 ≤ rowAt witV3 i c ∧ rowAt witV3 i c < 2013265921 := by
    intro i c
    have h : rowAt witV3 i = contractRow (rowAt witTrace i) := loc_contractT witTrace i
    rw [h]
    simp only [contractRow]
    split_ifs <;> exact witTrace_canon.cells i _
  refine ⟨hcells, witTrace_canon.pubs, ?_, ?_⟩
  · right; decide
  · right; decide

/-- **The Rung-1 crown carries through the bridge**: a v3-satisfying canonical bundle IS a genuine
`BundleAggregated` (of its v2 expansion — same outer PI, same schedule block, accumulators
recolumned). -/
theorem compact_refines
    {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash bilateralAggDescriptorV3 minit mfin maddrs t)
    (hne : t.rows ≠ []) (hcanon : AggCTraceCanon t)
    (hsize : (t.rows.length : ℤ) < 2013265921) :
    BundleAggregated (expandT t) := by
  have hlen : (expandT t).rows.length = t.rows.length := by simp [expandT]
  refine bilateralAgg_refines (expand_satisfies hsat) ?_ (canon_expandT hcanon)
    (by rw [hlen]; exact hsize)
  intro h
  exact hne (by simpa [expandT, List.map_eq_nil_iff] using h)

/-- **The Rung-2 crown carries through the bridge, restated on the COMPACT trace's own columns**:
a v3-satisfying canonical bundle seats EXACTLY ONE agent cell — no cross-federation double-spend. -/
theorem compact_unique_agent
    {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash bilateralAggDescriptorV3 minit mfin maddrs t)
    (hne : t.rows ≠ []) (hcanon : AggCTraceCanon t)
    (hsize : (t.rows.length : ℤ) < 2013265921) :
    UniqueAgent t := by
  have hlen : (expandT t).rows.length = t.rows.length := by simp [expandT]
  have h2 : UniqueAgent (expandT t) := by
    refine bilateralAgg_rung2 (expand_satisfies hsat) ?_ (canon_expandT hcanon)
      (by rw [hlen]; exact hsize)
    intro h
    exact hne (by simpa [expandT, List.map_eq_nil_iff] using h)
  refine ⟨?_, ?_⟩
  · obtain ⟨j, hj, hA⟩ := h2.exists_agent
    exact ⟨j, by rwa [hlen] at hj, by rwa [isAgentAt_expandT] at hA⟩
  · intro a b ha hb hAa hAb
    exact h2.unique_agent a b (by rwa [hlen]) (by rwa [hlen])
      (by rwa [isAgentAt_expandT]) (by rwa [isAgentAt_expandT])

/-- **The strengthened per-row identity, exact over ℤ**: under the envelope, EVERY cell of a
v3-satisfying bundle carries the published turn identity — the property whose v2 ABSENCE is
`gapTrace`. -/
theorem compact_identity_every_row
    {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash bilateralAggDescriptorV3 minit mfin maddrs t)
    (hcanon : AggCTraceCanon t)
    {c : Nat} (hc : c < 13) :
    ∀ j, j < t.rows.length → rowAt t j c = t.pub c := by
  intro j hj
  exact eq_of_modEq_of_canon (identity_chain hsat hc j hj)
    (hcanon.cells j c).1 (hcanon.cells j c).2 (hcanon.pubs c).1 (hcanon.pubs c).2

/-- The discharge FIRES on the honest compact witness: `witV3` seats exactly one agent. -/
theorem witV3_unique_agent : UniqueAgent witV3 := by
  refine compact_unique_agent witV3_satisfies ?_ witV3_canon (by decide)
  intro h
  exact absurd (congrArg List.length h) (by decide)

/-! ## §10 — Axiom tripwires. -/

#assert_axioms expand_satisfies
#assert_axioms contract_preserves
#assert_axioms contract_expand
#assert_axioms contractT_expandT
#assert_axioms witV3_satisfies
#assert_axioms gapTrace_satisfies
#assert_axioms gapTrace_contract_not_v3
#assert_axioms gap_no_v3_preimage
#assert_axioms badTraceC_not_satisfied
#assert_axioms identity_chain
#assert_axioms compact_refines
#assert_axioms compact_unique_agent
#assert_axioms compact_identity_every_row
#assert_axioms witV3_unique_agent

end Dregg2.Circuit.Emit.BilateralAggregationCompact
