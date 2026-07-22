/-
# Market.PrivateBookBfvButterflyFaithful -- faithful committed NTT bus semantics

`PrivateBookBfvButterflyAir` emits real lookup constraints, but generic IR2
lookup denotation is membership-only: a prover-supplied custom table may carry
extra or duplicated rows.  That is enough for range/fixed-chip tables whose
contents are independently faithful, but not enough to conclude that every
butterfly output occurs exactly once as the next stage's input.

This module supplies that missing semantic carrier.  At every transform
boundary, one committed table slice must be a permutation of BOTH:

* the source image (the preceding stage's two outputs per butterfly); and
* the sink image (the following stage's two inputs per butterfly).

Consequently the two images are permutations of each other.  Boundary zero is
the ingress image and boundary `logN` is the egress image; the same definition
therefore scales without a special case from the executable q0/N8 tooth to the
production 12-stage, N=4096 family.

The executable faithful gate additionally pins the custom schedule table to
the canonical Lean table.  Two hostile witnesses demonstrate why this layer is
load-bearing: appending an unused duplicate to either custom table still passes
the old membership-only AIR, while the faithful gate refuses it.

This is the Lean semantic closure for the committed LogUp table.  The Rust IR2
consumer still has to implement this table-exactness carrier (or an equivalent
grand-product/multiset argument) before the production descriptor may consume
the theorem as deployed evidence.
-/
import Market.PrivateBookBfvButterflyAir

namespace Market.PrivateBookBfvButterflyFaithful

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.DecideSatisfied2
open Market.PrivateBookBfvNttFamily
open Market.PrivateBookBfvButterflyAir

set_option autoImplicit false

/-! ## 1. Generic committed boundary-table semantics -/

def rowTag (row : List Int) : Int := row.getD 0 0

/-- The committed rows whose tag lies in boundary `b`'s half-open interval
`[b*n, (b+1)*n)`.  Every bus row starts with this tag followed by the three
radix limbs. -/
def boundaryTableN (n boundary : Nat) (table : Table) : Table :=
  table.filter fun row =>
    decide (Int.ofNat (boundary * n) ≤ rowTag row ∧
      rowTag row < Int.ofNat ((boundary + 1) * n))

/-- At boundary zero, the source is transform ingress.  Every later boundary
is sourced by the preceding stage's writes. -/
def sourceImage (rows : List Assignment) (boundary : Nat) : Table :=
  if boundary = 0 then stageReads rows 0 else stageWrites rows (boundary - 1)

/-- At the final boundary, the sink is transform egress.  Every earlier
boundary is consumed by that stage's reads. -/
def sinkImage (logN : Nat) (rows : List Assignment) (boundary : Nat) : Table :=
  if boundary = logN then stageWrites rows (logN - 1) else stageReads rows boundary

/-- One committed multiset slice is simultaneously the exact source and sink
image at each boundary.  `List.Perm` is the correct semantic equality: LogUp
commits multisets, not a prover-chosen row order. -/
def BusTableFaithfulN (n logN : Nat) (busTid : TableId) (trace : VmTrace) : Prop :=
  ∀ boundary ∈ List.range (logN + 1),
    (sourceImage trace.rows boundary).Perm (boundaryTableN n boundary (trace.tf busTid)) ∧
    (sinkImage logN trace.rows boundary).Perm
      (boundaryTableN n boundary (trace.tf busTid))

/-- Executable decision of exactly `BusTableFaithfulN`. -/
def busTableFaithfulGateN (n logN : Nat) (busTid : TableId) (trace : VmTrace) : Bool :=
  (List.range (logN + 1)).all fun boundary =>
    decide
      ((sourceImage trace.rows boundary).Perm
        (boundaryTableN n boundary (trace.tf busTid)) ∧
       (sinkImage logN trace.rows boundary).Perm
        (boundaryTableN n boundary (trace.tf busTid)))

theorem busTableFaithfulGateN_iff (n logN : Nat) (busTid : TableId) (trace : VmTrace) :
    busTableFaithfulGateN n logN busTid trace = true ↔
      BusTableFaithfulN n logN busTid trace := by
  simp only [busTableFaithfulGateN, BusTableFaithfulN, List.all_eq_true,
    decide_eq_true_eq]

/-- The common committed table eliminates the internal-stage substitution:
the preceding outputs and following inputs are the same multiset.  This theorem
is generic in `n` and `logN`; production instantiates `n=4096, logN=12`. -/
theorem BusTableFaithfulN.internalStagePerm
    {n logN : Nat} {busTid : TableId} {trace : VmTrace}
    (h : BusTableFaithfulN n logN busTid trace)
    (stage : Nat) (hstage : stage + 1 < logN) :
    (stageWrites trace.rows stage).Perm (stageReads trace.rows (stage + 1)) := by
  have hlast : stage + 1 ≠ logN := by omega
  have hboundary :
      (sourceImage trace.rows (stage + 1)).Perm
          (boundaryTableN n (stage + 1) (trace.tf busTid)) ∧
        (sinkImage logN trace.rows (stage + 1)).Perm
          (boundaryTableN n (stage + 1) (trace.tf busTid)) :=
    h (stage + 1) (by
      simp only [List.mem_range]
      omega)
  have hnonzero : stage + 1 ≠ 0 := by omega
  simp only [sourceImage, hnonzero, if_false, Nat.add_sub_cancel,
    sinkImage, hlast, if_false] at hboundary
  exact hboundary.1.trans hboundary.2.symm

/-! The production statement is not a new algorithm or an extrapolated row
count.  It is this same generic relation instantiated at the geometry already
proved by `PrivateBookBfvNttFamily`. -/

def ProductionBusTableFaithful (busTid : TableId) (trace : VmTrace) : Prop :=
  BusTableFaithfulN DEGREE LOG_DEGREE busTid trace

theorem production_internal_stage_permutation
    {busTid : TableId} {trace : VmTrace}
    (h : ProductionBusTableFaithful busTid trace)
    (stage : Nat) (hstage : stage + 1 < LOG_DEGREE) :
    (stageWrites trace.rows stage).Perm (stageReads trace.rows (stage + 1)) :=
  h.internalStagePerm stage hstage

/-! ## 2. q0/N8 faithful carrier and executable gate -/

def ScheduleTableFaithful (scheduleTid : TableId) (expected : Table)
    (trace : VmTrace) : Prop :=
  trace.tf scheduleTid = expected

def BusTableFaithful (trace : VmTrace) : Prop :=
  BusTableFaithfulN N LOG_N (.custom BUS_TID) trace

def busTableFaithfulGate (trace : VmTrace) : Bool :=
  busTableFaithfulGateN N LOG_N (.custom BUS_TID) trace

theorem busTableFaithfulGate_iff (trace : VmTrace) :
    busTableFaithfulGate trace = true ↔ BusTableFaithful trace :=
  busTableFaithfulGateN_iff N LOG_N (.custom BUS_TID) trace

def scheduleTableFaithfulGate (trace : VmTrace) : Bool :=
  decide (trace.tf (.custom SCHEDULE_TID) = scheduleTable)

def airGate (trace : VmTrace) : Bool :=
  decideSatisfied2 trivialMapDec (fun _ => 0) butterflyDescriptor
    (fun _ => 0) (fun _ => (0, 0)) [] trace

/-- The strengthened executable accept set: the original AIR, the exact
canonical schedule table, and the faithful committed bus multiset. -/
def faithfulButterflyGate (trace : VmTrace) : Bool :=
  airGate trace && scheduleTableFaithfulGate trace && busTableFaithfulGate trace

def traceWithTables (rows : List Assignment) (schedule bus : Table) : VmTrace :=
  { rows := rows
  , pub := zeroAsg
  , tf := fun table =>
      match table with
      | .custom tid =>
          if tid = SCHEDULE_TID then schedule
          else if tid = BUS_TID then bus
          else []
      | _ => [] }

def honestTrace : VmTrace := traceWithTables honestRows scheduleTable busTable

/-- Membership-only lookups cannot see an unused duplicate. -/
def duplicateBusTrace : VmTrace :=
  traceWithTables honestRows scheduleTable (busTable ++ [busRow 0 0])

/-- Nor can membership-only schedule lookups see an unused duplicate. -/
def duplicateScheduleTrace : VmTrace :=
  traceWithTables honestRows (scheduleTable ++ [scheduleRow 0 0]) busTable

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem honest_faithful_gate_accepts : faithfulButterflyGate honestTrace = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem membership_only_air_accepts_duplicate_bus : airGate duplicateBusTrace = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem faithful_gate_refuses_duplicate_bus :
    faithfulButterflyGate duplicateBusTrace = false := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem membership_only_air_accepts_duplicate_schedule :
    airGate duplicateScheduleTrace = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem faithful_gate_refuses_duplicate_schedule :
    faithfulButterflyGate duplicateScheduleTrace = false := by
  decide

theorem faithful_gate_implies_schedule
    {trace : VmTrace} (h : faithfulButterflyGate trace = true) :
    ScheduleTableFaithful (.custom SCHEDULE_TID) scheduleTable trace := by
  simp only [faithfulButterflyGate, Bool.and_eq_true,
    scheduleTableFaithfulGate, decide_eq_true_eq] at h
  exact h.1.2

theorem faithful_gate_implies_bus
    {trace : VmTrace} (h : faithfulButterflyGate trace = true) :
    BusTableFaithful trace := by
  simp only [faithfulButterflyGate, Bool.and_eq_true] at h
  exact (busTableFaithfulGate_iff trace).mp h.2

theorem faithful_gate_internal_stage_permutation
    {trace : VmTrace} (h : faithfulButterflyGate trace = true)
    (stage : Nat) (hstage : stage + 1 < LOG_N) :
    (stageWrites trace.rows stage).Perm (stageReads trace.rows (stage + 1)) :=
  (faithful_gate_implies_bus h).internalStagePerm stage hstage

theorem faithful_gate_implies_permutation_gate
    {trace : VmTrace} (h : faithfulButterflyGate trace = true) :
    permutationBusGate trace.rows = true := by
  rw [permutationBusGate, List.all_eq_true]
  intro stage hmem
  rw [decide_eq_true_eq]
  apply faithful_gate_internal_stage_permutation h stage
  simp only [List.mem_range] at hmem
  omega

#assert_all_clean [
  Market.PrivateBookBfvButterflyFaithful.busTableFaithfulGateN_iff,
  Market.PrivateBookBfvButterflyFaithful.BusTableFaithfulN.internalStagePerm,
  Market.PrivateBookBfvButterflyFaithful.production_internal_stage_permutation,
  Market.PrivateBookBfvButterflyFaithful.busTableFaithfulGate_iff,
  Market.PrivateBookBfvButterflyFaithful.honest_faithful_gate_accepts,
  Market.PrivateBookBfvButterflyFaithful.membership_only_air_accepts_duplicate_bus,
  Market.PrivateBookBfvButterflyFaithful.faithful_gate_refuses_duplicate_bus,
  Market.PrivateBookBfvButterflyFaithful.membership_only_air_accepts_duplicate_schedule,
  Market.PrivateBookBfvButterflyFaithful.faithful_gate_refuses_duplicate_schedule,
  Market.PrivateBookBfvButterflyFaithful.faithful_gate_implies_schedule,
  Market.PrivateBookBfvButterflyFaithful.faithful_gate_implies_bus,
  Market.PrivateBookBfvButterflyFaithful.faithful_gate_internal_stage_permutation,
  Market.PrivateBookBfvButterflyFaithful.faithful_gate_implies_permutation_gate]

end Market.PrivateBookBfvButterflyFaithful
