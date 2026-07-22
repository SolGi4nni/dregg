/-
# Market.PrivateBookBfvExactPublicConsumer -- fixed q0/N8 exact-public LogUp proof

This module is the first direct consumer of DescriptorIR2's verifier-committed
`exactPublicRows` semantics.  It deliberately proves the fixed, public q0/N=8
known-answer transform from `PrivateBookBfvButterflyAir`; it is not a hiding
carrier and confers no authority on a prover-private BFV trace.

The twelve logical butterfly rows are not padded to sixteen.  They are split at
the natural stage boundary into three independent four-row descriptors.  Four
is already a valid power-of-two STARK height, so every committed row is real and
every lookup fires exactly once.  Each descriptor carries two complete public
multisets:

* four canonical schedule rows, one per butterfly; and
* sixteen tagged read/write rows, four per butterfly.

The shared tags force each public residue onto the corresponding schedule row;
the Lean-authored radix equations force the remaining product, quotient, and
carry columns.  Duplicate, omission, and manifest-substitution examples below
fail the exact multiset relation.  Production N=4096 still needs a scalable
committed-table implementation: this fixed KAT is intentionally bounded and
public-only.
-/

import Market.PrivateBookBfvButterflyFaithful

namespace Market.PrivateBookBfvExactPublicConsumer

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.DecideSatisfied2
open Market.PrivateBookBfvButterflyAir

set_option autoImplicit false

/-! ## 1. Exact public manifests for one four-row stage -/

/-- Convert a nonnegative, canonical BFV row fragment to the descriptor's
canonical natural-number JSON representation. -/
def natRow (row : List Int) : List Nat := row.map Int.toNat

/-- The four honest butterfly assignments at one q0/N=8 stage. -/
def stageAssignments (stage : Nat) : List Assignment :=
  (List.range (N / 2)).map (honestRow stage)

/-- The schedule lookup tuple actually queried by each stage row. -/
def scheduleManifest (stage : Nat) : List (List Nat) :=
  (stageAssignments stage).map fun row =>
    natRow (scheduleTuple.map (fun expr => expr.eval row))

/-- The four tagged bus tuples queried by one butterfly row, in the same order
as `busLookups`: read-left, read-right, write-left, write-right. -/
def rowBusManifest (row : Assignment) : List (List Nat) :=
  [ natRow (busItem READ_LEFT_TAG LEFT_INPUT row)
  , natRow (busItem READ_RIGHT_TAG RIGHT_INPUT row)
  , natRow (busItem WRITE_LEFT_TAG LEFT_OUTPUT row)
  , natRow (busItem WRITE_RIGHT_TAG RIGHT_OUTPUT row) ]

/-- The complete sixteen-entry read/write multiset for one stage. -/
def busManifest (stage : Nat) : List (List Nat) :=
  (stageAssignments stage).flatMap rowBusManifest

#guard (stageAssignments 0).length == 4
#guard (stageAssignments 1).length == 4
#guard (stageAssignments 2).length == 4
#guard (scheduleManifest 0).length == 4
#guard (busManifest 0).length == 16

/-- One fixed-stage relation.  The descriptor contains the complete table
contents; nothing is supplied by the prover except the four main rows whose
lookups and arithmetic are proved. -/
def stageDescriptorWith
    (stage : Nat) (scheduleRows busRows : List (List Nat)) : EffectVmDescriptor2 :=
  { name := "private-book-bfv-odd-ntt-butterfly-q0-n8-stage" ++ toString stage ++
      "::exact-public-48-v1"
  , traceWidth := TRACE_WIDTH
  , piCount := 0
  , tables :=
      [ ⟨.custom SCHEDULE_TID, "bfv_ntt_q0_n8_stage" ++ toString stage ++ "_schedule",
          17, .exactPublicRows scheduleRows⟩
      , ⟨.custom BUS_TID, "bfv_ntt_q0_n8_stage" ++ toString stage ++ "_bus",
          4, .exactPublicRows busRows⟩ ]
  , constraints := arithmeticConstraints ++ [scheduleLookup] ++ busLookups
  , hashSites := []
  , ranges := limbRanges ++ scheduleRanges ++ carryRanges }

def stageDescriptor (stage : Nat) : EffectVmDescriptor2 :=
  stageDescriptorWith stage (scheduleManifest stage) (busManifest stage)

def stage0Descriptor : EffectVmDescriptor2 := stageDescriptor 0
def stage1Descriptor : EffectVmDescriptor2 := stageDescriptor 1
def stage2Descriptor : EffectVmDescriptor2 := stageDescriptor 2

#guard stage0Descriptor.constraints.length == 67
#guard stage0Descriptor.ranges.length == 48
#guard (emitVmJson2 stage0Descriptor).contains "exact_public_rows"
#guard (emitVmJson2 stage0Descriptor).contains "stage0_schedule"
#guard (emitVmJson2 stage1Descriptor).contains "stage1_schedule"
#guard (emitVmJson2 stage2Descriptor).contains "stage2_schedule"

/-! ## 2. Executable Lean denotation and both-polarity teeth -/

def stageTraceWithRows (stage : Nat) (rows : List Assignment) : VmTrace :=
  { rows := rows
  , pub := zeroAsg
  , tf := fun table =>
      if table = .custom SCHEDULE_TID then exactPublicTable (scheduleManifest stage)
      else if table = .custom BUS_TID then exactPublicTable (busManifest stage)
      else [] }

def stageTrace (stage : Nat) : VmTrace :=
  stageTraceWithRows stage (stageAssignments stage)

/-- Existing DescriptorIR2 row/range/lookup denotation for one stage. -/
def stageAirGate (stage : Nat) : Bool :=
  decideSatisfied2 trivialMapDec (fun _ => 0) (stageDescriptor stage)
    (fun _ => 0) (fun _ => (0, 0)) [] (stageTrace stage)

def ScheduleBalanced (stage : Nat) : Prop :=
  (lookupLog (stageDescriptor stage) (stageTrace stage) (.custom SCHEDULE_TID)).Perm
    (exactPublicTable (scheduleManifest stage))

def BusBalanced (stage : Nat) : Prop :=
  (lookupLog (stageDescriptor stage) (stageTrace stage) (.custom BUS_TID)).Perm
    (exactPublicTable (busManifest stage))

/-- Executable form of the two complete lookup-log equalities.  The descriptor
has exactly these two public tables; `stageTrace` installs their literal
contents, while these two decisions pin their complete query multiplicities. -/
def stagePublicGate (stage : Nat) : Bool :=
  decide ((lookupLog (stageDescriptor stage) (stageTrace stage) (.custom SCHEDULE_TID)).Perm
      (exactPublicTable (scheduleManifest stage))) &&
    decide ((lookupLog (stageDescriptor stage) (stageTrace stage) (.custom BUS_TID)).Perm
      (exactPublicTable (busManifest stage)))

/-- The trace's two table images are definitionally the two descriptor-carried
manifests; no prover-supplied table survives in the semantic object. -/
theorem stage_tables_are_descriptor_contents (stage : Nat) :
    PublicTablesFaithful (stageDescriptor stage) (stageTrace stage) := by
  intro td htd
  change td ∈
    [ ⟨.custom SCHEDULE_TID, "bfv_ntt_q0_n8_stage" ++ toString stage ++ "_schedule",
        17, .exactPublicRows (scheduleManifest stage)⟩
    , ⟨.custom BUS_TID, "bfv_ntt_q0_n8_stage" ++ toString stage ++ "_bus",
        4, .exactPublicRows (busManifest stage)⟩ ] at htd
  have hcases :
      td = ⟨.custom SCHEDULE_TID,
          "bfv_ntt_q0_n8_stage" ++ toString stage ++ "_schedule", 17,
          .exactPublicRows (scheduleManifest stage)⟩ ∨
        td = ⟨.custom BUS_TID,
          "bfv_ntt_q0_n8_stage" ++ toString stage ++ "_bus", 4,
          .exactPublicRows (busManifest stage)⟩ := by
    simpa using htd
  rcases hcases with rfl | rfl
  ·
    simp [TableDef.publicContentsFaithful, stageTrace, stageTraceWithRows,
      SCHEDULE_TID, BUS_TID]
  ·
    simp [TableDef.publicContentsFaithful, stageTrace, stageTraceWithRows,
      SCHEDULE_TID, BUS_TID]

/-- The generic public-table definition reduces to precisely the schedule and
bus multisets named above. -/
theorem public_lookup_balanced_iff (stage : Nat) :
    PublicLookupBalanced (stageDescriptor stage) (stageTrace stage) ↔
      ScheduleBalanced stage ∧ BusBalanced stage := by
  constructor
  · intro h
    constructor
    · exact h
        ⟨.custom SCHEDULE_TID,
          "bfv_ntt_q0_n8_stage" ++ toString stage ++ "_schedule", 17,
          .exactPublicRows (scheduleManifest stage)⟩
        (by simp [stageDescriptor, stageDescriptorWith])
    · exact h
        ⟨.custom BUS_TID,
          "bfv_ntt_q0_n8_stage" ++ toString stage ++ "_bus", 4,
          .exactPublicRows (busManifest stage)⟩
        (by simp [stageDescriptor, stageDescriptorWith])
  · rintro ⟨hschedule, hbus⟩ td htd
    change td ∈
      [ ⟨.custom SCHEDULE_TID, "bfv_ntt_q0_n8_stage" ++ toString stage ++ "_schedule",
          17, .exactPublicRows (scheduleManifest stage)⟩
      , ⟨.custom BUS_TID, "bfv_ntt_q0_n8_stage" ++ toString stage ++ "_bus",
          4, .exactPublicRows (busManifest stage)⟩ ] at htd
    have hcases :
        td = ⟨.custom SCHEDULE_TID,
            "bfv_ntt_q0_n8_stage" ++ toString stage ++ "_schedule", 17,
            .exactPublicRows (scheduleManifest stage)⟩ ∨
          td = ⟨.custom BUS_TID,
            "bfv_ntt_q0_n8_stage" ++ toString stage ++ "_bus", 4,
            .exactPublicRows (busManifest stage)⟩ := by
      simpa using htd
    rcases hcases with rfl | rfl
    ·
      exact hschedule
    ·
      exact hbus

/-- For this two-table descriptor, the executable pair of permutation checks
is exactly `PublicLookupBalanced`, not an adjacent native-only predicate. -/
theorem stagePublicGate_iff (stage : Nat) :
    stagePublicGate stage = true ↔
      PublicLookupBalanced (stageDescriptor stage) (stageTrace stage) := by
  rw [public_lookup_balanced_iff]
  simp [stagePublicGate, ScheduleBalanced, BusBalanced]

def duplicateStage0Rows : List Assignment :=
  match stageAssignments 0 with
  | first :: _ :: rest => first :: first :: rest
  | rows => rows

def omittedStage0Rows : List Assignment := (stageAssignments 0).eraseIdx 1

def substitutedSchedule0 : List (List Nat) :=
  match scheduleManifest 0 with
  | first :: rest =>
      match first with
      | value :: tail => ((value + 1) :: tail) :: rest
      | [] => [] :: rest
  | [] => []

def substitutedStage0Descriptor : EffectVmDescriptor2 :=
  stageDescriptorWith 0 substitutedSchedule0 (busManifest 0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem honest_three_stage_bundle_accepts :
    stageAirGate 0 = true ∧ stagePublicGate 0 = true ∧
    stageAirGate 1 = true ∧ stagePublicGate 1 = true ∧
    stageAirGate 2 = true ∧ stagePublicGate 2 = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem duplicate_omission_refused :
    ¬ (lookupLog stage0Descriptor (stageTraceWithRows 0 duplicateStage0Rows)
        (.custom SCHEDULE_TID)).Perm (exactPublicTable (scheduleManifest 0)) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem omitted_row_refused :
    ¬ (lookupLog stage0Descriptor (stageTraceWithRows 0 omittedStage0Rows)
        (.custom SCHEDULE_TID)).Perm (exactPublicTable (scheduleManifest 0)) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem descriptor_manifest_substitution_refused :
    ¬ (lookupLog substitutedStage0Descriptor (stageTrace 0)
        (.custom SCHEDULE_TID)).Perm (exactPublicTable substitutedSchedule0) := by
  decide

/-! ## 3. Exact no-padding geometry -/

/-- The fixed public tooth proves all twelve logical rows as three real
power-of-two instances; there are no dummy rows and no selector left to trust. -/
theorem no_padding_three_stage_geometry :
    (stageAssignments 0).length = 4 ∧
    (stageAssignments 1).length = 4 ∧
    (stageAssignments 2).length = 4 ∧
    (stageAssignments 0).length + (stageAssignments 1).length +
      (stageAssignments 2).length = scheduleTable.length := by
  decide

#assert_axioms honest_three_stage_bundle_accepts
#assert_axioms stage_tables_are_descriptor_contents
#assert_axioms public_lookup_balanced_iff
#assert_axioms stagePublicGate_iff
#assert_axioms duplicate_omission_refused
#assert_axioms omitted_row_refused
#assert_axioms descriptor_manifest_substitution_refused
#assert_axioms no_padding_three_stage_geometry

end Market.PrivateBookBfvExactPublicConsumer
