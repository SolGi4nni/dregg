/-
# Dregg2.Circuit.Emit.BilateralAggregationEmit — the emit-from-Lean byte-pin + a fresh CG-3 tooth
for the BILATERAL-BUNDLE AGGREGATION outer AIR (law #1).

## What this file IS (additive closure of the emit-from-Lean loop for `bilateral_aggregation`)

The aggregation descriptor itself is AUTHORED and PROVED in `EffectVmEmitBilateralAgg.lean`
(`bilateralAggDescriptor` — the DECOUPLED width-87 / PI-23 outer AIR: CG-2 turn-identity
`pi_binding`s on the first AND last rows, CG-3 schedule-replay `gate` equalities, CG-4 agent
accounting = two boolean `gate`s + the padding `gate` + the two cumulative-sum `windowGate`s, and
the four boundaries). That module only `startsWith`-pins its wire string. THIS module FULLY
BYTE-PINS `emitVmJson2 bilateralAggDescriptor` against the exact golden the Rust side
`include_str!`s (`circuit/descriptors/dregg-bilateral-aggregation-v2.json`) and the gate test
embeds (`circuit-prove/tests/bilateral_aggregation_emit_gate.rs`, `GOLDEN_JSON`), closing
`Lean-emit ≡ golden ≡ Rust-decode` airtight — a drift on any side breaks THIS `#guard`, that Rust
`assert_eq!(decoded, hand_built)`, or the byte-pinned `include_str!`.

## The fresh, non-vacuous tooth (CG-3 schedule replay)

`agg_rejects_count_mismatch`: a row whose carried bilateral `counts[0]` (`Sched.COUNTS_BASE`)
disagrees with the prover-populated `expected_counts[0]` (`Agg.EXPECTED_COUNTS_BASE`) column CANNOT
satisfy the descriptor on a transition row — the schedule replay is REAL, not decorative. This is
the in-descriptor face of the gate test's schedule-mismatch mutation canary. FIELD-FAITHFUL: the
descriptor denotation is `≡ 0 [ZMOD p]` (`p = 2013265921`, BabyBear), so the tooth carries the
DEPLOYED range-check canonicality (`0 ≤ cell < p` on both columns) — under it a disagreement
cannot wrap around the modulus. Both directions are witnessed (`cg3_body_zero_iff` over ℤ and
`cg3_body_modEq_zero_iff` over the field — the gate body vanishes IFF the columns agree; TRUE when
equal, FALSE when not), so the tooth is genuinely non-vacuous. It is a DIFFERENT constraint family from
the existing `agg_rejects_turn_mismatch` (CG-2 identity) / `agg_rejects_bad_agent_count` (CG-4
boundary) teeth — the schedule-replay leg those two do not cover.

## Axiom hygiene

Definitional re-pin (`#guard`) on the already-proved descriptor's wire string + one
genuinely-proven, non-vacuous semantic lemma. `#assert_axioms cg3_body_zero_iff ⊆ {}` (pure
`omega`). NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitBilateralAgg

namespace Dregg2.Circuit.Emit.BilateralAggregationEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRowEnv VmRow)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmitBilateralAgg
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff not_modEq_zero_of_canon)

set_option autoImplicit false

/-! ## §1 — The FULL byte-pin: the Rust decoder ingests THIS exact string. -/

#guard emitVmJson2 bilateralAggDescriptor ==
  "{\"name\":\"dregg-bilateral-aggregation-v2\",\"ir\":2,\"trace_width\":87,\"public_input_count\":23,\"tables\":[],\"constraints\":[{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":0,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":1,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":2,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":3,\"pi_index\":3},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":4,\"pi_index\":4},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":5,\"pi_index\":5},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":6,\"pi_index\":6},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":7,\"pi_index\":7},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":8,\"pi_index\":8},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":9,\"pi_index\":9},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":10,\"pi_index\":10},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":11,\"pi_index\":11},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":12,\"pi_index\":12},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":0,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":1,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":2,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":3,\"pi_index\":3},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":4,\"pi_index\":4},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":5,\"pi_index\":5},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":6,\"pi_index\":6},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":7,\"pi_index\":7},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":8,\"pi_index\":8},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":9,\"pi_index\":9},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":10,\"pi_index\":10},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":11,\"pi_index\":11},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":12,\"pi_index\":12},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":49}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":50}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":51}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":52}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":53}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":54}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":55}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":56}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":57}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":58}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":59}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":24},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":60}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":61}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":26},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":62}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":27},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":63}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":28},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":64}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":29},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":65}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":30},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":66}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":31},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":67}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":68}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":33},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":69}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":34},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":70}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":35},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":71}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":36},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":72}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":73}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":74}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":39},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":75}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":40},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":76}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":41},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":77}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":78}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":79}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":80}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":81}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":46},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":82}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":47},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":83}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":48},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":48},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":85},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":85},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":85}}},\"r\":{\"t\":\"var\",\"v\":48}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":84},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":84}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":48}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":86},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":86}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":85}}}}},{\"t\":\"boundary\",\"row\":\"first\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":84},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":48}}}},{\"t\":\"boundary\",\"row\":\"first\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":86},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":85}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":84},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":86,\"pi_index\":21}],\"hash_sites\":[],\"ranges\":[]}"

/-! ## §2 — Shape tripwires (the Rust gate asserts the SAME shape on the decoded twin). -/

#guard bilateralAggDescriptor.name == "dregg-bilateral-aggregation-v2"
#guard bilateralAggDescriptor.traceWidth == 87
#guard bilateralAggDescriptor.piCount == 23
#guard bilateralAggDescriptor.constraints.length == 70
#guard (bilateralAggDescriptor.constraints.filter
          (fun c => match c with | .windowGate _ => true | _ => false)).length == 2

/-! ## §3 — The CG-3 schedule-replay tooth (genuinely proven, non-vacuous). -/

/-- The CG-3 replay gate body `local[a] - local[b]` — the body of `cg3Eq a b`. -/
def cg3Body (a b : Nat) : EmittedExpr := .add (.var a) (.mul (.const (-1)) (.var b))

/-- The replay gate vanishes EXACTLY when the carried column equals the expected column. -/
theorem cg3_body_zero_iff (asg : Assignment) (a b : Nat) :
    (cg3Body a b).eval asg = 0 ↔ asg a = asg b := by
  simp only [cg3Body, EmittedExpr.eval]
  constructor <;> intro h <;> omega

/-- FIELD-FAITHFUL face: the replay gate vanishes mod `p` EXACTLY when the two columns are
congruent mod `p` — the deployed field constraint says exactly "the columns agree in the field". -/
theorem cg3_body_modEq_zero_iff (asg : Assignment) (a b : Nat) :
    ((cg3Body a b).eval asg ≡ 0 [ZMOD 2013265921]) ↔ (asg a ≡ asg b [ZMOD 2013265921]) := by
  simp only [cg3Body, EmittedExpr.eval]
  exact gate_modEq_iff (by ring)

-- Non-vacuity witnesses: the replay gate ACCEPTS agreeing columns, REJECTS disagreeing ones.
#guard decide ((cg3Body 13 49).eval (fun i => if i = 13 ∨ i = 49 then 5 else 0) = 0)
#guard decide (¬ ((cg3Body 13 49).eval (fun i => if i = 13 then 5 else 0) = 0))

/-- The descriptor's per-window denotation: every constraint holds (no tables/sites/ranges). -/
def aggWindowHolds (env : VmRowEnv) (isFirst isLast : Bool) : Prop :=
  ∀ c ∈ bilateralAggDescriptor.constraints,
    c.holdsAt (fun _ => 0) (fun _ => []) env isFirst isLast

/-- **CG-3 tooth.** A TRANSITION row whose carried `counts[0]` disagrees with the prover-populated
`expected_counts[0]` column cannot satisfy the descriptor — the schedule replay binds them.
FIELD-FAITHFUL: needs the deployed range-check canonicality on both columns (`0 ≤ cell < p`), so a
mismatch cannot pass the field gate by wrap-around (`p ∤ residual`). -/
theorem agg_rejects_count_mismatch
    (env : VmRowEnv)
    (hcanonSch : 0 ≤ env.loc (Agg.schCol Sched.COUNTS_BASE)
      ∧ env.loc (Agg.schCol Sched.COUNTS_BASE) < 2013265921)
    (hcanonExp : 0 ≤ env.loc Agg.EXPECTED_COUNTS_BASE
      ∧ env.loc Agg.EXPECTED_COUNTS_BASE < 2013265921)
    (hdis : env.loc (Agg.schCol Sched.COUNTS_BASE) ≠ env.loc Agg.EXPECTED_COUNTS_BASE) :
    ¬ aggWindowHolds env false false := by
  intro h
  have hmem : cg3Eq (Agg.schCol Sched.COUNTS_BASE) Agg.EXPECTED_COUNTS_BASE
      ∈ bilateralAggDescriptor.constraints := by
    show _ ∈ aggConstraints
    have hin : cg3Eq (Agg.schCol Sched.COUNTS_BASE) Agg.EXPECTED_COUNTS_BASE ∈ scheduleReplay := by
      unfold scheduleReplay
      refine List.mem_append_left _ ?_
      have : cg3Eq (Agg.schCol (Sched.COUNTS_BASE + 0)) (Agg.EXPECTED_COUNTS_BASE + 0)
          ∈ (List.range Sched.COUNTS_LEN).map (fun k =>
              cg3Eq (Agg.schCol (Sched.COUNTS_BASE + k)) (Agg.EXPECTED_COUNTS_BASE + k)) :=
        List.mem_map_of_mem (by simp [Sched.COUNTS_LEN])
      simpa using this
    unfold aggConstraints
    -- `scheduleReplay` is the 3rd (left-assoc) append: `(((first ++ last) ++ replay) ++ cg4) ++ bnd`.
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hin))
  have hc := h _ hmem
  simp only [cg3Eq, colEqCol, VmConstraint2.holdsAt, VmConstraint.holdsVm, EmittedExpr.eval] at hc
  exact not_modEq_zero_of_canon (by ring) hcanonSch hcanonExp hdis hc

#assert_axioms cg3_body_zero_iff

end Dregg2.Circuit.Emit.BilateralAggregationEmit
