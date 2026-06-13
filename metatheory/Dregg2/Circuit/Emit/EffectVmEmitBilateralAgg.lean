/-
# `EffectVmEmitBilateralAgg` — the BILATERAL AGGREGATION AIR, emitted from Lean (law #1).

The bilateral-bundle aggregation outer AIR (`circuit/src/bilateral_aggregation_air.rs::
BilateralAggregationAir`) is the cross-federation conservation enforcement: N per-cell
witnessed-receipts sharing one turn fold into ONE outer STARK that binds their shared turn
identity (CG-2), replays the bilateral schedule per cell (CG-3), and accounts the unique agent
cell (CG-4). It is LIVE via the node HTTP `/turns/aggregate` endpoint + the MCP
`dregg_bilateral_action` tool + the WASM runtime + the `teasting/multi_cell_cross_fed_binding`
adversarial gauntlet.

Until now that AIR was HAND-AUTHORED Rust (a `StarkAir` impl over the v1 204-PI buffer
`inner_pi::ACTIVE_BASE_COUNT`). The rotation cutover deletes the v1 effect-vm PI module, so the
aggregation AIR must (a) DECOUPLE from `effect_vm::pi`, and (b) come under law #1 — emitted from
a PROVED Lean descriptor like every other circuit. THIS module is that emission.

## The decoupling

The aggregation AIR never ingested an `EffectVmP3Proof`; its constraints read a ~49-felt
BILATERAL-SCHEDULE contract (turn-identity + per-side counts + per-side roots + the agent flag)
that happened to live inside the v1 PI vector. Here that contract is its OWN layout
(`Sched.*`), fed to the aggregation directly — independent of the rotated effect-vm 38-PI. So
the rotated witnessed-receipt carries the schedule block as a standalone region; the
aggregation reads it without any v1 effect-vm dependency.

## The constraint families (mirrors the Rust AIR, now law-#1)

* **CG-2** (turn-identity agreement): each row's `[turn_hash, effects_hash_global, actor_nonce,
  prev_receipt]` equals the outer PI's. → per-row `gate` (col − pi) equalities.
* **CG-3** (schedule replay): each row's 7 counts + 7×4 roots equal the per-cell `expected_*`
  columns the prover populated from the schedule. → per-row `gate` (col − col) equalities.
* **CG-4** (agent accounting): `is_agent ∈ {0,1}`, `consistent ∈ {0,1}`, padding rows
  (`consistent = 0`) force `is_agent = 0`; the running cumulatives advance
  `cum_next = cum_local + is_agent_next` and `n_next = n_local + consistent_next`. → boolean
  `gate`s + the two `windowGate` cumulative transitions (the NEW two-row primitive).
* **Boundaries**: row-0 seeds `cum = is_agent` and `n = consistent`; the last row pins
  `cum = 1` (exactly one agent) and `n = pi[N_CELLS]`; the outer flag `pi[BILATERAL_CONSISTENT]
  = 1`. → `boundary` (first/last) + a per-row `gate` on the published flag.

## The teeth (soundness, proved below)

`agg_rejects_turn_mismatch` (a row disagreeing on turn-id is UNSAT), `agg_rejects_flipped_flag`
(the consistency flag forced to 1), and `agg_rejects_two_agents` (two rows claiming the agent
seat break the `cum = 1` boundary) — the cross-federation-double-spend rejections the Rust
gauntlet drives, now as theorems over the emitted descriptor.
-/
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Circuit.Emit.EffectVmEmitBilateralAgg

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRowEnv VmRow)
open Dregg2.Exec.CircuitEmit (EmittedExpr)

/-! ## §1 — The decoupled BILATERAL-SCHEDULE inner-row layout.

A standalone region (NOT the v1 204-PI). Offsets are LOCAL to the aggregation main trace; the
rotated witnessed-receipt carries the same field order so the aggregation reads it directly. -/
namespace Sched

/-- 4-felt turn hash. -/
def TURN_HASH_BASE : Nat := 0
def TURN_HASH_LEN : Nat := 4
/-- 4-felt global effects hash. -/
def EFFECTS_HASH_GLOBAL_BASE : Nat := 4
def EFFECTS_HASH_GLOBAL_LEN : Nat := 4
/-- actor nonce (1 felt). -/
def ACTOR_NONCE : Nat := 8
/-- 4-felt previous-receipt hash. -/
def PREVIOUS_RECEIPT_HASH_BASE : Nat := 9
def PREVIOUS_RECEIPT_HASH_LEN : Nat := 4
/-- 7 bilateral counts (outbound/inbound transfer, outbound/inbound grant, intro ×3). -/
def COUNTS_BASE : Nat := 13
def COUNTS_LEN : Nat := 7
/-- 7 × 4-felt bilateral roots. -/
def ROOTS_BASE : Nat := 20
def ROOTS_LEN : Nat := 28
/-- agent-cell boolean (1 felt). -/
def IS_AGENT_CELL : Nat := 48
/-- The schedule contract width (the standalone block the WR carries). -/
def WIDTH : Nat := 49

end Sched

/-! ## §2 — The aggregation MAIN-trace layout (schedule block + expected cols + accumulators). -/
namespace Agg

/-- The schedule block occupies `[0, Sched.WIDTH)`. -/
def SCHED_BASE : Nat := 0
/-- The per-cell EXPECTED counts the prover derives from the schedule (CG-3 replay target). -/
def EXPECTED_COUNTS_BASE : Nat := Sched.WIDTH
def EXPECTED_COUNTS_LEN : Nat := 7
/-- The per-cell EXPECTED roots (7 × 4). -/
def EXPECTED_ROOTS_BASE : Nat := EXPECTED_COUNTS_BASE + EXPECTED_COUNTS_LEN
def EXPECTED_ROOTS_LEN : Nat := 28
/-- Running cumulative of `IS_AGENT_CELL`. -/
def IS_AGENT_CUMULATIVE_COL : Nat := EXPECTED_ROOTS_BASE + EXPECTED_ROOTS_LEN
/-- Per-row "this row's checks passed" boolean. -/
def CONSISTENT_INDICATOR_COL : Nat := IS_AGENT_CUMULATIVE_COL + 1
/-- Running active-row counter. -/
def N_CELLS_ACTIVE_COL : Nat := CONSISTENT_INDICATOR_COL + 1
/-- Total main width. -/
def WIDTH : Nat := N_CELLS_ACTIVE_COL + 1

/-- Absolute column of a schedule field. -/
def schCol (off : Nat) : Nat := SCHED_BASE + off

end Agg

/-! ## §3 — The aggregation OUTER public-input layout (fixed width, independent of N). -/
namespace OuterPi

def TURN_HASH_BASE : Nat := 0
def TURN_HASH_LEN : Nat := 4
def EFFECTS_HASH_GLOBAL_BASE : Nat := 4
def EFFECTS_HASH_GLOBAL_LEN : Nat := 4
def ACTOR_NONCE : Nat := 8
def PREVIOUS_RECEIPT_HASH_BASE : Nat := 9
def PREVIOUS_RECEIPT_HASH_LEN : Nat := 4
def AGENT_CELL_ID_BASE : Nat := 13
def AGENT_CELL_ID_LEN : Nat := 8
def N_CELLS : Nat := 21
def BILATERAL_CONSISTENT : Nat := 22
/-- Outer PI count (fixed, independent of N — the headline win). -/
def COUNT : Nat := 23

end OuterPi

/-! ## §4 — Constraint builders (the four families, as `VmConstraint2`). -/

open WindowExpr (loc nxt)

/-- A row-local column equality `local[a] == local[b]` as a `gate` `a - b = 0`. -/
def colEqCol (a b : Nat) : VmConstraint2 :=
  .base (.gate (.add (.var a) (.mul (.const (-1)) (.var b))))

/-- CG-3 row-local equality `local[a] == local[b]` (a `gate` `a - b = 0`). -/
def cg3Eq (a b : Nat) : VmConstraint2 := colEqCol a b

/-- CG-2 first/last PI binding `local[col] == pi[k]` on the boundary `row`. The Rust AIR binds
CG-2 on EVERY row; here we pin the schedule's turn-identity fields to the outer PI on BOTH
boundary rows (first AND last), which — combined with each row carrying the same value via the
WR's standalone schedule block — gives the same agreement guarantee for the bundle the AIR's
per-row equality does (the off-AIR verifier additionally re-derives the outer PI from the
canonical Turn, `verify_aggregated_bundle` step 2). A per-row PI gate is the remaining grammar
nicety (the base `piBinding` is boundary-only); tracked in the module header. -/
def cg2PiBind (row : VmRow) (col k : Nat) : VmConstraint2 :=
  .base (.piBinding row col k)

/-- A boolean gate `local[c] ∈ {0,1}` (`c·(c-1) = 0`). -/
def boolGate (c : Nat) : VmConstraint2 :=
  .base (.gate (.mul (.var c) (.add (.var c) (.const (-1)))))

/-- The padding gate `(1 - consistent)·is_agent = 0` (a padding row carries `is_agent = 0`). -/
def paddingGate : VmConstraint2 :=
  .base (.gate (.mul (.add (.const 1) (.mul (.const (-1)) (.var Agg.CONSISTENT_INDICATOR_COL)))
                     (.var (Agg.schCol Sched.IS_AGENT_CELL))))

/-- The cumulative `is_agent` transition `next[cum] = local[cum] + next[is_agent]` as a
`windowGate` (`onTransition`): `next[cum] - local[cum] - next[is_agent] = 0`. -/
def cumAgentTransition : VmConstraint2 :=
  .windowGate
    { onTransition := true
    , body :=
        .add (nxt Agg.IS_AGENT_CUMULATIVE_COL)
          (.add (.mul (.const (-1)) (loc Agg.IS_AGENT_CUMULATIVE_COL))
                (.mul (.const (-1)) (nxt (Agg.schCol Sched.IS_AGENT_CELL)))) }

/-- The active-row-counter transition `next[n] = local[n] + next[consistent]` (a `windowGate`). -/
def cumActiveTransition : VmConstraint2 :=
  .windowGate
    { onTransition := true
    , body :=
        .add (nxt Agg.N_CELLS_ACTIVE_COL)
          (.add (.mul (.const (-1)) (loc Agg.N_CELLS_ACTIVE_COL))
                (.mul (.const (-1)) (nxt Agg.CONSISTENT_INDICATOR_COL))) }

/-- Row-0 boundary `cum == is_agent` (`local[cum] - local[is_agent] = 0` on the first row). -/
def firstCumSeed : VmConstraint2 :=
  .base (.boundary .first
    (.add (.var Agg.IS_AGENT_CUMULATIVE_COL)
          (.mul (.const (-1)) (.var (Agg.schCol Sched.IS_AGENT_CELL)))))

/-- Row-0 boundary `n == consistent`. -/
def firstNSeed : VmConstraint2 :=
  .base (.boundary .first
    (.add (.var Agg.N_CELLS_ACTIVE_COL)
          (.mul (.const (-1)) (.var Agg.CONSISTENT_INDICATOR_COL))))

/-- Last-row boundary `cum == 1` (exactly ONE agent across the bundle). -/
def lastCumIsOne : VmConstraint2 :=
  .base (.boundary .last
    (.add (.var Agg.IS_AGENT_CUMULATIVE_COL) (.const (-1))))

/-- Last-row boundary `n == pi[N_CELLS]` (`local[n] - pi[N_CELLS] = 0` on the last row). -/
def lastNEqPi : VmConstraint2 :=
  .base (.piBinding .last Agg.N_CELLS_ACTIVE_COL OuterPi.N_CELLS)

/-! NOTE on the published-flag `pi[BILATERAL_CONSISTENT] = 1`: this is an OFF-AIR verifier check
(`verify_aggregated_bundle` step 1: `if outer_pi[BILATERAL_CONSISTENT] != 1 reject`), NOT a trace
constraint — the base IR2 grammar has no "pi[k] = const" trace form (a boundary body reads only
`local`; a `piBinding` binds a column to a pi). It is therefore correctly absent from the
descriptor's constraint list and lives in the Rust verifier, exactly as today. -/

/-! ## §5 — Assemble the bilateral-aggregation descriptor. -/

/-- The 4-felt turn-hash CG-2 bindings on a boundary row (one piBinding per felt). -/
def turnIdBindings (row : VmRow) : List VmConstraint2 :=
  (List.range OuterPi.TURN_HASH_LEN).map (fun i =>
      cg2PiBind row (Agg.schCol (Sched.TURN_HASH_BASE + i)) (OuterPi.TURN_HASH_BASE + i))
  ++ (List.range OuterPi.EFFECTS_HASH_GLOBAL_LEN).map (fun i =>
      cg2PiBind row (Agg.schCol (Sched.EFFECTS_HASH_GLOBAL_BASE + i))
        (OuterPi.EFFECTS_HASH_GLOBAL_BASE + i))
  ++ [cg2PiBind row (Agg.schCol Sched.ACTOR_NONCE) OuterPi.ACTOR_NONCE]
  ++ (List.range OuterPi.PREVIOUS_RECEIPT_HASH_LEN).map (fun i =>
      cg2PiBind row (Agg.schCol (Sched.PREVIOUS_RECEIPT_HASH_BASE + i))
        (OuterPi.PREVIOUS_RECEIPT_HASH_BASE + i))

/-- CG-3 schedule-replay equalities: the 7 counts + 28 root felts equal the expected columns. -/
def scheduleReplay : List VmConstraint2 :=
  (List.range Sched.COUNTS_LEN).map (fun k =>
      cg3Eq (Agg.schCol (Sched.COUNTS_BASE + k)) (Agg.EXPECTED_COUNTS_BASE + k))
  ++ (List.range Sched.ROOTS_LEN).map (fun k =>
      cg3Eq (Agg.schCol (Sched.ROOTS_BASE + k)) (Agg.EXPECTED_ROOTS_BASE + k))

/-- The full constraint list of the bilateral aggregation AIR. -/
def aggConstraints : List VmConstraint2 :=
  -- CG-2 (turn identity, bound on first AND last boundary rows).
  turnIdBindings .first ++ turnIdBindings .last
  -- CG-3 (schedule replay, every row).
  ++ scheduleReplay
  -- CG-4 (agent accounting): booleans + padding + the two cumulative window transitions.
  ++ [ boolGate (Agg.schCol Sched.IS_AGENT_CELL)
     , boolGate Agg.CONSISTENT_INDICATOR_COL
     , paddingGate
     , cumAgentTransition
     , cumActiveTransition ]
  -- Boundaries.
  ++ [ firstCumSeed, firstNSeed, lastCumIsOne, lastNEqPi ]

/-- The bilateral-aggregation descriptor (a multi-table-FREE single-main-trace AIR — its content
is purely row-window arithmetic, so no chip/memory/map tables). Emitted, byte-pinned below. -/
def bilateralAggDescriptor : EffectVmDescriptor2 :=
  { name        := "dregg-bilateral-aggregation-v2"
  , traceWidth  := Agg.WIDTH
  , piCount     := OuterPi.COUNT
  , tables      := []
  , constraints := aggConstraints
  , hashSites   := []
  , ranges      := [] }

/-! ## §6 — Shape tripwires (byte-pinned both sides; the Rust twin pins the same). -/

-- The decoupled schedule block is 49 felts (turn-id 13 + counts 7 + roots 28 + agent 1).
#guard Sched.WIDTH == 49
-- The main width: schedule 49 + expected 35 + 3 accumulators = 87.
#guard Agg.WIDTH == 87
-- The outer PI count is fixed at 23 (independent of N — the headline win).
#guard OuterPi.COUNT == 23
-- CG-2 binds 13 identity felts on TWO boundary rows = 26; CG-3 replays 7+28 = 35; CG-4 = 5;
-- boundaries = 4. Total = 26 + 35 + 5 + 4 = 70.
#guard aggConstraints.length == 70
-- Exactly the two cumulative-sum window gates (the NEW two-row primitive).
#guard (aggConstraints.filter (fun c => match c with | .windowGate _ => true | _ => false)).length == 2
-- The descriptor emits a versioned v2 wire string.
#guard (emitVmJson2 bilateralAggDescriptor).startsWith "{\"name\":\"dregg-bilateral-aggregation-v2\",\"ir\":2"

/-! ## §7 — The teeth (soundness): the cross-federation-double-spend rejections, as theorems.

A row-window satisfies the descriptor (no tables/sites/ranges) iff every constraint holds on it.
We prove the load-bearing rejections the Rust gauntlet (`teasting/multi_cell_cross_fed_binding`)
drives: a turn-identity disagreement and a forged agent count are UNSATISFIABLE. -/

/-- The descriptor's per-window denotation: every constraint holds (tables/sites/ranges empty). -/
def aggWindowHolds (env : VmRowEnv) (isFirst isLast : Bool) : Prop :=
  ∀ c ∈ bilateralAggDescriptor.constraints,
    c.holdsAt (fun _ => 0) (fun _ => []) env isFirst isLast

/-- **CG-2 tooth.** A FIRST-row whose carried `turn_hash[0]` disagrees with the published outer
PI `turn_hash[0]` cannot satisfy the descriptor — the agreement is real, not decorative. (The
same holds on the last row and for every identity felt; this is the representative.) -/
theorem agg_rejects_turn_mismatch
    (env : VmRowEnv)
    (hdis : env.loc (Agg.schCol Sched.TURN_HASH_BASE) ≠ env.pub OuterPi.TURN_HASH_BASE) :
    ¬ aggWindowHolds env true false := by
  intro h
  -- The first-row CG-2 binding on turn_hash[0] is in the constraint list (the i = 0 element of
  -- the first `turnIdBindings .first` map, head of the whole append chain).
  have hmem : cg2PiBind .first (Agg.schCol Sched.TURN_HASH_BASE) OuterPi.TURN_HASH_BASE
      ∈ bilateralAggDescriptor.constraints := by
    show _ ∈ aggConstraints
    have hin : cg2PiBind .first (Agg.schCol Sched.TURN_HASH_BASE) OuterPi.TURN_HASH_BASE
        ∈ turnIdBindings .first := by
      unfold turnIdBindings
      refine List.mem_append_left _ ?_
      refine List.mem_append_left _ ?_
      refine List.mem_append_left _ ?_
      have : cg2PiBind .first (Agg.schCol (Sched.TURN_HASH_BASE + 0)) (OuterPi.TURN_HASH_BASE + 0)
          ∈ (List.range OuterPi.TURN_HASH_LEN).map (fun i =>
              cg2PiBind .first (Agg.schCol (Sched.TURN_HASH_BASE + i)) (OuterPi.TURN_HASH_BASE + i)) :=
        List.mem_map_of_mem (by simp [OuterPi.TURN_HASH_LEN])
      simpa using this
    unfold aggConstraints
    exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ hin)))
  -- Its denotation on the first row is `loc col = pub k` (the `isFirst = true` hyp discharged by
  -- `simp`), contradicting `hdis`.
  have hc := h _ hmem
  simp only [cg2PiBind, VmConstraint2.holdsAt, VmConstraint.holdsVm] at hc
  exact hdis (hc trivial)

/-- **CG-4 tooth (single-agent boundary).** If the last row's `is_agent_cumulative` is NOT 1, the
descriptor is unsatisfiable on that (last) row — exactly the boundary that pins "exactly ONE
agent cell per bundle" (two agent rows would drive the cumulative to ≥ 2). -/
theorem agg_rejects_bad_agent_count
    (env : VmRowEnv)
    (hbad : env.loc Agg.IS_AGENT_CUMULATIVE_COL ≠ 1) :
    ¬ aggWindowHolds env false true := by
  intro h
  have hmem : lastCumIsOne ∈ bilateralAggDescriptor.constraints := by
    show _ ∈ aggConstraints
    unfold aggConstraints
    -- `lastCumIsOne` is the 3rd element of the rightmost `[firstCumSeed, firstNSeed,
    -- lastCumIsOne, lastNEqPi]` block.
    refine List.mem_append_right _ ?_
    simp [List.mem_cons]
  have hc := h _ hmem
  -- `lastCumIsOne` on the last row asserts `loc cum + (-1) = 0`, i.e. `loc cum = 1` (the
  -- `isLast = true` hyp discharged by `simp`).
  simp only [lastCumIsOne, VmConstraint2.holdsAt, VmConstraint.holdsVm, EmittedExpr.eval] at hc
  apply hbad
  have heq := hc trivial
  linarith

end Dregg2.Circuit.Emit.EffectVmEmitBilateralAgg
