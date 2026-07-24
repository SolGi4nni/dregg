/-
# Dregg2.Verify.RangeFamilyFaithfulBatch — extending the range-table-faithfulness route to a
REPRESENTATIVE BATCH of lookup-bearing by-name descriptors (the named residual from
`RangeFamilyFaithfulRoute`).

## What this closes

`RangeFamilyFaithfulRoute` routed the ONE Gabbay public descriptor's soundness through a per-width
range-family faithfulness conjunct (`RangeFamilyFaithful`, pins `{(rangeTidW 15, 15), (.range, 30)}`),
so a FORGED `.range`/width-tagged range table is inadmissible for it: the honest-interval obligation
moved from a free witness lever (`Lookup.holdsAt` membership against the free `t.tf .range` field)
into a structural conjunct of the soundness statement. That file NAMED the residual:

  > The 43 lookup-bearing by-name descriptors' soundness statements each still route through bare
  > `Satisfied2` or the SCALAR honest-range premise (`t.tf .range = rangeRows N`); porting them to
  > the family conjunct is the same two-line pattern.

This file ports a representative batch of SIX such descriptors, spanning TWO range-width families the
committed `RangeFamilyFaithful` did not cover on its own:

  * the **29-bit predicate-arithmetic** family — `predicateGtDesc`, `predicateGeDesc`,
    `predicateLeDesc`, `predicateLtDesc`, `predicateInRangeDesc` (by-name `predicate-arith-gt/‑ge/‑le/
    ‑lt`, `predicate-arith-inrange`): each carries its diff-range tooth against `.range = rangeRows 29`
    (`DIFF_BITS`), a width the committed `WIDE_RANGE_WIDTHS = [15, 30]` set does NOT contain;
  * the **30-bit presentation-freshness** descriptor — `presentationFreshnessDesc` (by-name
    `presentation-freshness`): two freshness-limb range teeth at `.range = rangeRows 30`
    (`FRESH_BITS`), the SAME shared width the committed carrier pins, so it also routes directly from
    the committed `RangeFamilyFaithful` (`presentation_sound_from_committed`).

Each descriptor already has a machine-checked SAT_IMPLIES_SEM soundness theorem
(`predicate«Op»_sat_imp_sem`, `presentation_satisfied2_fresh`) carrying the honest-range table as an
EXPLICIT SCALAR hypothesis `hrange : t.tf .range = rangeRows «BITS»`. This file does NOT re-author any
AIR or re-prove any refinement: it defines, per descriptor, a `«Op»SatisfiedFamily` predicate carrying
the honest-range table as the reusable per-width FAMILY conjunct `RangeFamilyFaithfulOn`, and routes
the existing soundness theorem through it (`«op»_sound_family`) — mirroring
`RangeFamilyFaithfulRoute.statement_sound_family`. The forged-range lever is then closed structurally:
`«op»_forgedRange_inadmissible` shows any trace whose `.range` differs from the honest interval CANNOT
inhabit the family predicate. Non-vacuity (`«op»_family_nonvacuous`) reuses each descriptor's existing
honest satisfying witness, so the family predicate rejects forgeries rather than everything.

## The reusable generalization (`RangeFamilyFaithfulOn`)

`RangeFamilyFaithful` fixes its pins to `[15, 30]` via `rangeTidW`. The predicate family's teeth ride
`.range` at width 29, which that set does not reach. `RangeFamilyFaithfulOn pins t` generalizes to an
EXPLICIT `(table-id, width)` pin set — quantifying `∀ (tid, n) ∈ pins, t.tf tid = rangeRows n` — so a
descriptor at ANY width (29 here; 48-wide BFV, 16-bit note-spend, etc. for future lanes) routes
through the same carrier. `RangeFamilyFaithful.toOn` shows the committed carrier SUBSUMES this batch
carrier on the shared 30-bit width, connecting the two routes.

## Severity — MODELING GAP, not a live vuln (per descriptor, as in the committed route)

The deployed circuit ENFORCES range-table faithfulness on the wire: `circuit/src/descriptor_ir2.rs`
`Ir2Air::ByteTable` fixes `value = row index` (the table cannot lie about its rows) and
`verify_vm_descriptor2` refuses any range instance whose committed degree differs from the deployed
`BYTE_TABLE_HEIGHT` (test `ir2_oversized_byte_table_refuses`). The honest-table obligation is
discharged BY CONSTRUCTION at Rust assembly. So — for every descriptor here — this is a Lean MODELING
GAP (the abstract accept-set is looser than the deployed one), NOT an exploit against
`verify_vm_descriptor2`. Routing the premise into the family carrier moves it to the emit boundary; it
does not delete it.

## Which of the 43 remain

DONE (6): `predicate-arith-gt`, `predicate-arith` (ge), `predicate-arith-le`, `predicate-arith-lt`,
`predicate-arith-inrange`, `presentation-freshness`. REMAINING lookup-bearing residual includes: the
BFV NTT butterflies (`private-book-bfv-odd-*ntt-butterfly-*`, wide range teeth), the exact-nullifier
rotated-state weld (`rangeTid 15/16` — a 16-bit family, `ExactNullifierAafiRotatedState*`), the
faithful note-spend range teeth (`faithful-note-spend-*`), and the Poseidon2-CHIP-lookup-bearing
membership descriptors (`blinded-membership*`, `attested-fact-membership`, `merkle-membership-*`) whose
lookups are CHIP tables not range tables (a distinct `ChipTableSound` obligation, out of scope here).
Each range-bearing residual is the same two-line port once its soundness theorem carries a scalar or
bare honest-range premise; a descriptor whose range family is not `[15, 30]` uses `RangeFamilyFaithfulOn`
at its own `(tid, width)` pins (no change to the shared `WIDE_RANGE_WIDTHS`).

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. NEW file; imports read-only; no base
`Satisfied2` change (RED-UMBRELLA avoided — soundness STATEMENTS are routed, not the base carrier).
-/
import Dregg2.Verify.RangeFamilyFaithfulRoute
import Dregg2.Circuit.Emit.PredicatesGtRefine
import Dregg2.Circuit.Emit.PredicatesArithmeticRefine
import Dregg2.Circuit.Emit.PredicatesLeRefine
import Dregg2.Circuit.Emit.PredicatesLtRefine
import Dregg2.Circuit.Emit.PredicatesInRangeRefine
import Dregg2.Circuit.Emit.PresentationRefine

namespace Dregg2.Verify.RangeFamilyFaithfulBatch

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitV2 (WIDE_RANGE_WIDTHS rangeTidW rangeTablesWide_range)
open Dregg2.Verify.RangeFamilyFaithfulRoute (RangeFamilyFaithful)

set_option autoImplicit false

/-! ## §1 — the reusable per-descriptor range-family carrier over an EXPLICIT pin set. -/

/-- **`RangeFamilyFaithfulOn pins t`** — the per-descriptor range-table faithfulness conjunct over an
explicit set of `(table-id, width)` pins: at every pin `(tid, n)`, the trace's range table `t.tf tid`
is the genuine honest interval `rangeRows n`. Generalizes `RangeFamilyFaithful` (whose pins are fixed
to `rangeTidW` at `{15, 30}`) to ARBITRARY widths — so a descriptor whose range teeth ride a width
the committed `[15, 30]` set does not cover (the predicate family's 29-bit `.range` teeth) routes
through the same carrier. This is the conjunct the per-descriptor SOUNDNESS statements quantify over,
moving the honest-range obligation from a free `t.tf` lever into a structural premise. -/
def RangeFamilyFaithfulOn (pins : List (TableId × Nat)) (t : VmTrace) : Prop :=
  ∀ p ∈ pins, t.tf p.1 = rangeRows p.2

/-- Project a single honest-interval pin out of the family carrier. -/
theorem RangeFamilyFaithfulOn.pin {pins : List (TableId × Nat)} {t : VmTrace}
    (h : RangeFamilyFaithfulOn pins t) {tid : TableId} {n : Nat}
    (hmem : (tid, n) ∈ pins) : t.tf tid = rangeRows n :=
  h (tid, n) hmem

/-- **The committed carrier subsumes this batch carrier on the shared 30-bit width.** The committed
`RangeFamilyFaithful` (pins `{(rangeTidW 15, 15), (.range, 30)}`) guarantees the honest 30-bit `.range`
interval, i.e. the singleton batch pin `(.range, BAL_LIMB_BITS)`. This connects the batch route back to
the committed Gabbay route: anything routed through `RangeFamilyFaithful` is routed through this. -/
theorem RangeFamilyFaithful.toOn {t : VmTrace} (h : RangeFamilyFaithful t) :
    RangeFamilyFaithfulOn [(TableId.range, BAL_LIMB_BITS)] t := by
  intro p hp
  rcases List.mem_singleton.mp hp with rfl
  exact rangeTablesWide_range (tf := t.tf) h

/-! ## §2 — the 29-bit predicate-arithmetic family: `>` `≥` `≤` `<` `InRange`.

Each `predicate«Op»Desc` carries its diff-range tooth against `.range = rangeRows DIFF_BITS`
(`DIFF_BITS = 29`), and already has a machine-checked SAT_IMPLIES_SEM theorem `predicate«Op»_sat_imp_sem`
taking that honest-range table as an explicit SCALAR hypothesis. We route it through the family
conjunct at the single 29-bit pin `[(.range, 29)]`. -/

open Dregg2.Circuit.Emit.PredicatesGtRefine in
open Dregg2.Circuit.Emit.PredicatesGtEmit in
/-- `predicateGtDesc`'s soundness hypotheses with the honest 29-bit range table carried as the
family conjunct rather than the free `t.tf .range` lever. -/
def GtSatisfiedFamily (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) : Prop :=
  RangeFamilyFaithfulOn [(TableId.range, DIFF_BITS)] t ∧ 2 ≤ t.rows.length ∧ GtCanon t ∧
    Satisfied2 hash predicateGtDesc minit mfin maddrs t

/-- **Soundness, routed through the family conjunct** (mirrors `statement_sound_family`). -/
theorem gt_sound_family {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace} (h : GtSatisfiedFamily hash minit mfin maddrs t) :
    Dregg2.Circuit.Emit.PredicatesGtRefine.ArithGtSem (envAt t 0) :=
  Dregg2.Circuit.Emit.PredicatesGtRefine.predicateGt_sat_imp_sem
    (h.1.pin (List.mem_singleton.mpr rfl)) h.2.1 h.2.2.1 h.2.2.2

/-- **A forged range table is inadmissible.** Any trace whose `.range` differs from the honest 29-bit
interval cannot inhabit the family predicate — the free lever the scalar carrier left open is closed. -/
theorem gt_forgedRange_inadmissible {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hforge : t.tf .range ≠ rangeRows Dregg2.Circuit.Emit.PredicatesGtEmit.DIFF_BITS) :
    ¬ GtSatisfiedFamily hash minit mfin maddrs t :=
  fun h => hforge (h.1.pin (List.mem_singleton.mpr rfl))

/-- **Non-vacuity.** The existing honest `>` witness inhabits the family predicate. -/
theorem gt_family_nonvacuous :
    GtSatisfiedFamily Dregg2.Circuit.Emit.PredicatesGtRefine.hash0 (fun _ => 0) (fun _ => (0, 0)) []
      Dregg2.Circuit.Emit.PredicatesGtRefine.gtWitnessTrace :=
  ⟨fun p hp => by rcases List.mem_singleton.mp hp with rfl
                  exact Dregg2.Circuit.Emit.PredicatesGtRefine.gtWitnessTf_range,
   by decide, Dregg2.Circuit.Emit.PredicatesGtRefine.gtWitness_canon,
   Dregg2.Circuit.Emit.PredicatesGtRefine.gtWitness_satisfies⟩

open Dregg2.Circuit.Emit.PredicatesArithmeticRefine in
open Dregg2.Circuit.Emit.PredicatesArithmeticEmit in
/-- `predicateGeDesc`'s soundness hypotheses with the honest 29-bit range table as the family conjunct. -/
def GeSatisfiedFamily (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) : Prop :=
  RangeFamilyFaithfulOn [(TableId.range, DIFF_BITS)] t ∧ 2 ≤ t.rows.length ∧ GeCanon t ∧
    Satisfied2 hash predicateGeDesc minit mfin maddrs t

/-- Soundness, routed through the family conjunct. (`predicateGe_sat_imp_sem` takes `hsat` before
`hcanon`.) -/
theorem ge_sound_family {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace} (h : GeSatisfiedFamily hash minit mfin maddrs t) :
    Dregg2.Circuit.Emit.PredicatesArithmeticRefine.ArithGeSem (envAt t 0) :=
  Dregg2.Circuit.Emit.PredicatesArithmeticRefine.predicateGe_sat_imp_sem
    (h.1.pin (List.mem_singleton.mpr rfl)) h.2.1 h.2.2.2 h.2.2.1

theorem ge_forgedRange_inadmissible {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hforge : t.tf .range ≠ rangeRows Dregg2.Circuit.Emit.PredicatesArithmeticEmit.DIFF_BITS) :
    ¬ GeSatisfiedFamily hash minit mfin maddrs t :=
  fun h => hforge (h.1.pin (List.mem_singleton.mpr rfl))

theorem ge_family_nonvacuous :
    GeSatisfiedFamily Dregg2.Circuit.Emit.PredicatesArithmeticRefine.hash0 (fun _ => 0)
      (fun _ => (0, 0)) [] Dregg2.Circuit.Emit.PredicatesArithmeticRefine.geWitnessTrace :=
  ⟨fun p hp => by rcases List.mem_singleton.mp hp with rfl
                  exact Dregg2.Circuit.Emit.PredicatesArithmeticRefine.geWitnessTf_range,
   by decide, Dregg2.Circuit.Emit.PredicatesArithmeticRefine.geWitness_canon,
   Dregg2.Circuit.Emit.PredicatesArithmeticRefine.geWitness_satisfies⟩

open Dregg2.Circuit.Emit.PredicatesLeRefine in
open Dregg2.Circuit.Emit.PredicatesLeEmit in
/-- `predicateLeDesc`'s soundness hypotheses with the honest 29-bit range table as the family conjunct. -/
def LeSatisfiedFamily (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) : Prop :=
  RangeFamilyFaithfulOn [(TableId.range, DIFF_BITS)] t ∧ 2 ≤ t.rows.length ∧ LeCanon t ∧
    Satisfied2 hash predicateLeDesc minit mfin maddrs t

theorem le_sound_family {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace} (h : LeSatisfiedFamily hash minit mfin maddrs t) :
    Dregg2.Circuit.Emit.PredicatesLeRefine.ArithLeSem (envAt t 0) :=
  Dregg2.Circuit.Emit.PredicatesLeRefine.predicateLe_sat_imp_sem
    (h.1.pin (List.mem_singleton.mpr rfl)) h.2.1 h.2.2.1 h.2.2.2

theorem le_forgedRange_inadmissible {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hforge : t.tf .range ≠ rangeRows Dregg2.Circuit.Emit.PredicatesLeEmit.DIFF_BITS) :
    ¬ LeSatisfiedFamily hash minit mfin maddrs t :=
  fun h => hforge (h.1.pin (List.mem_singleton.mpr rfl))

theorem le_family_nonvacuous :
    LeSatisfiedFamily Dregg2.Circuit.Emit.PredicatesLeRefine.hash0 (fun _ => 0) (fun _ => (0, 0)) []
      Dregg2.Circuit.Emit.PredicatesLeRefine.leWitnessTrace :=
  ⟨fun p hp => by rcases List.mem_singleton.mp hp with rfl
                  exact Dregg2.Circuit.Emit.PredicatesLeRefine.leWitnessTf_range,
   by decide, Dregg2.Circuit.Emit.PredicatesLeRefine.leWitness_canon,
   Dregg2.Circuit.Emit.PredicatesLeRefine.leWitness_satisfies⟩

open Dregg2.Circuit.Emit.PredicatesLtRefine in
open Dregg2.Circuit.Emit.PredicatesLtEmit in
/-- `predicateLtDesc`'s soundness hypotheses with the honest 29-bit range table as the family conjunct. -/
def LtSatisfiedFamily (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) : Prop :=
  RangeFamilyFaithfulOn [(TableId.range, DIFF_BITS)] t ∧ 2 ≤ t.rows.length ∧ LtCanon t ∧
    Satisfied2 hash predicateLtDesc minit mfin maddrs t

theorem lt_sound_family {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace} (h : LtSatisfiedFamily hash minit mfin maddrs t) :
    Dregg2.Circuit.Emit.PredicatesLtRefine.ArithLtSem (envAt t 0) :=
  Dregg2.Circuit.Emit.PredicatesLtRefine.predicateLt_sat_imp_sem
    (h.1.pin (List.mem_singleton.mpr rfl)) h.2.1 h.2.2.1 h.2.2.2

theorem lt_forgedRange_inadmissible {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hforge : t.tf .range ≠ rangeRows Dregg2.Circuit.Emit.PredicatesLtEmit.DIFF_BITS) :
    ¬ LtSatisfiedFamily hash minit mfin maddrs t :=
  fun h => hforge (h.1.pin (List.mem_singleton.mpr rfl))

theorem lt_family_nonvacuous :
    LtSatisfiedFamily Dregg2.Circuit.Emit.PredicatesLtRefine.hash0 (fun _ => 0) (fun _ => (0, 0)) []
      Dregg2.Circuit.Emit.PredicatesLtRefine.ltWitnessTrace :=
  ⟨fun p hp => by rcases List.mem_singleton.mp hp with rfl
                  exact Dregg2.Circuit.Emit.PredicatesLtRefine.ltWitnessTf_range,
   by decide, Dregg2.Circuit.Emit.PredicatesLtRefine.ltWitness_canon,
   Dregg2.Circuit.Emit.PredicatesLtRefine.ltWitness_satisfies⟩

open Dregg2.Circuit.Emit.PredicatesInRangeRefine in
open Dregg2.Circuit.Emit.PredicatesInRangeEmit in
/-- `predicateInRangeDesc`'s soundness hypotheses with the honest 29-bit range table as the family
conjunct. (Two range teeth `lo, hi`, both against the same `.range = rangeRows 29` — a single pin
covers both.) -/
def InRangeSatisfiedFamily (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) : Prop :=
  RangeFamilyFaithfulOn [(TableId.range, DIFF_BITS)] t ∧ 2 ≤ t.rows.length ∧ InRangeCanon t ∧
    Satisfied2 hash predicateInRangeDesc minit mfin maddrs t

theorem inRange_sound_family {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace} (h : InRangeSatisfiedFamily hash minit mfin maddrs t) :
    Dregg2.Circuit.Emit.PredicatesInRangeRefine.ArithInRangeSem (envAt t 0) :=
  Dregg2.Circuit.Emit.PredicatesInRangeRefine.predicateInRange_sat_imp_sem
    (h.1.pin (List.mem_singleton.mpr rfl)) h.2.1 h.2.2.2 h.2.2.1

theorem inRange_forgedRange_inadmissible {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hforge : t.tf .range ≠ rangeRows Dregg2.Circuit.Emit.PredicatesInRangeEmit.DIFF_BITS) :
    ¬ InRangeSatisfiedFamily hash minit mfin maddrs t :=
  fun h => hforge (h.1.pin (List.mem_singleton.mpr rfl))

theorem inRange_family_nonvacuous :
    InRangeSatisfiedFamily Dregg2.Circuit.Emit.PredicatesInRangeRefine.hash0 (fun _ => 0)
      (fun _ => (0, 0)) [] Dregg2.Circuit.Emit.PredicatesInRangeRefine.inWitnessTrace :=
  ⟨fun p hp => by rcases List.mem_singleton.mp hp with rfl
                  exact Dregg2.Circuit.Emit.PredicatesInRangeRefine.inWitnessTf_range,
   by decide, Dregg2.Circuit.Emit.PredicatesInRangeRefine.inWitness_canon,
   Dregg2.Circuit.Emit.PredicatesInRangeRefine.inWitness_satisfies⟩

/-! ## §3 — the 30-bit presentation-freshness descriptor.

`presentationFreshnessDesc` carries two freshness-limb range teeth against `.range = rangeRows 30`
(`FRESH_BITS = BAL_LIMB_BITS`). Because it pins the SAME shared width the committed `RangeFamilyFaithful`
guarantees, it routes BOTH through the batch carrier at `[(.range, 30)]` AND directly from the committed
carrier (`presentation_sound_from_committed`). -/

open Dregg2.Circuit.Emit.PresentationRefine in
open Dregg2.Circuit.Emit.PresentationEmit in
/-- `presentationFreshnessDesc`'s soundness hypotheses with the honest 30-bit range table as the
family conjunct. -/
def PresSatisfiedFamily (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) : Prop :=
  RangeFamilyFaithfulOn [(TableId.range, FRESH_BITS)] t ∧ 1 < t.rows.length ∧ PresCanon (envAt t 0) ∧
    Satisfied2 hash presentationFreshnessDesc minit mfin maddrs t

theorem pres_sound_family {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace} (h : PresSatisfiedFamily hash minit mfin maddrs t) :
    Dregg2.Circuit.Emit.PresentationRefine.PresentationFresh (envAt t 0) :=
  Dregg2.Circuit.Emit.PresentationRefine.presentation_satisfied2_fresh hash minit mfin maddrs t
    (h.1.pin (List.mem_singleton.mpr rfl)) h.2.1 h.2.2.2 h.2.2.1

theorem pres_forgedRange_inadmissible {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hforge : t.tf .range ≠ rangeRows Dregg2.Circuit.Emit.PresentationEmit.FRESH_BITS) :
    ¬ PresSatisfiedFamily hash minit mfin maddrs t :=
  fun h => hforge (h.1.pin (List.mem_singleton.mpr rfl))

/-- **The committed carrier drives presentation soundness directly.** Because `FRESH_BITS = BAL_LIMB_BITS
= 30`, the committed `RangeFamilyFaithful` (via `.toOn`) supplies the exact 30-bit `.range` pin
`presentation_satisfied2_fresh` needs — the batch route and the committed Gabbay route meet on the
shared width. -/
theorem presentation_sound_from_committed {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hfam : RangeFamilyFaithful t) (hlen : 1 < t.rows.length)
    (hsat : Satisfied2 hash Dregg2.Circuit.Emit.PresentationEmit.presentationFreshnessDesc
      minit mfin maddrs t)
    (hcanon : Dregg2.Circuit.Emit.PresentationRefine.PresCanon (envAt t 0)) :
    Dregg2.Circuit.Emit.PresentationRefine.PresentationFresh (envAt t 0) :=
  Dregg2.Circuit.Emit.PresentationRefine.presentation_satisfied2_fresh hash minit mfin maddrs t
    (by exact (RangeFamilyFaithful.toOn hfam).pin (List.mem_singleton.mpr rfl)) hlen hsat hcanon

theorem pres_family_nonvacuous :
    PresSatisfiedFamily (fun _ => 0) (fun _ => 0) (fun _ => (0, 0)) []
      Dregg2.Circuit.Emit.PresentationRefine.honestTrace :=
  ⟨fun p hp => by rcases List.mem_singleton.mp hp with rfl
                  exact Dregg2.Circuit.Emit.PresentationRefine.honestTrace_range,
   by decide, Dregg2.Circuit.Emit.PresentationRefine.honest_canon,
   Dregg2.Circuit.Emit.PresentationRefine.honest_satisfies⟩

/-! ## §4 — axiom hygiene. -/

#assert_axioms RangeFamilyFaithfulOn.pin
#assert_axioms RangeFamilyFaithful.toOn
#assert_axioms gt_sound_family
#assert_axioms gt_forgedRange_inadmissible
#assert_axioms gt_family_nonvacuous
#assert_axioms ge_sound_family
#assert_axioms ge_family_nonvacuous
#assert_axioms le_sound_family
#assert_axioms le_family_nonvacuous
#assert_axioms lt_sound_family
#assert_axioms lt_family_nonvacuous
#assert_axioms inRange_sound_family
#assert_axioms inRange_family_nonvacuous
#assert_axioms pres_sound_family
#assert_axioms presentation_sound_from_committed
#assert_axioms pres_family_nonvacuous

end Dregg2.Verify.RangeFamilyFaithfulBatch
