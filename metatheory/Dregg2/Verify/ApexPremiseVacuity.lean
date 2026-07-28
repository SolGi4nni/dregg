/-
# `Dregg2.Verify.ApexPremiseVacuity` — the two APEX theorems of the assurance case have
UNSATISFIABLE premises, and this file proves it in the kernel.

`AssuranceCase.deployed_system_secure` (the composed A∧B∧C∧D∧E capstone) and
`AssuranceCase.unfoolability_guarantee` (guarantee E) both carry the FIVE commitment-floor
hypotheses

    hCmb       : compressInjective cmb
    hCompress  : compressInjective compress
    hCompressN : compressNInjective compressN
    hLeaf      : cellLeafInjective CH
    hRest      : RestHashIffFrame RH

Every one of the first four is FALSE at deployed BabyBear width (the tree already proves this:
`HashFloorHonesty.compressInjective_false_of_finite_range`,
`…compressNInjective_false_of_finite_range`,
`StateCommitFloorRegrounded.cellLeafInjective_false_babyBear`). The FIFTH is worse and is what this
file is centred on: `RestFrameCardinalityFloor.restHashIffFrame_false_by_cardinality` refutes
`RestHashIffFrame RH` for **EVERY** `RH : RecordKernelState → ℤ`, at **EVERY** width, by Cantor —
`bal : CellId → AssetId → ℤ` is a function space, so no countable-codomain hash separates it.

⚑ CONSEQUENCE, stated exactly. The two apexes are not "vacuous at deployed parameters"; they are
vacuous at ALL parameters. There is no assignment of `CH RH cmb compress compressN` — deployed,
toy, or hypothetical — under which their hypothesis list is inhabited. `apexCommitFloor_unsatisfiable`
below is the crisp form: the apex's own binder list, taken as a bundle, is refuted outright, so any
application of either theorem has `False` in scope and its conclusion carries no information.

⚑ AND IT PROPAGATES. `CircuitSoundness.CommitSurface` carries the SAME five as FIELDS
(`cmbInj`/`compInj`/`compNInj`/`leafInj`/`restFrame`), so that structure has no inhabitant either —
which is why `AssuranceCaseGrounded.deployed_system_secure_grounded{,_v2}` (which takes both
`S : CommitSurface` AND the five binders, and is advertised as the capstone resting on "strictly the
crypto floor + honest-prover realizer data") is vacuous twice over.

## What this file is NOT

It is not a repair. §4 records the one part of guarantee E that survives floor-free (the
whole-history ATTESTATION, `light_client_verifies_whole_history`, which takes none of the five) and
the part that does not (the CRITICAL-3 conservation-from-verification closure, whose derivation runs
`root_tooth_pins_kernel → recStateCommit_binds_kernel` and therefore consumes all five). Naming that
split is the honest content available today; restoring the conservation leg needs a rest-hash over
FINITE SUPPORT, which is a commitment-shape decision, not a proof.

## Anti-vacuity discipline

Every refutation here is exhibited at BOTH poles (§3), so none of it is a `P → P` shape:
* the deployed-width hypothesis HOLDS at a BabyBear-reduced compress — and there `compressInjective`
  is FALSE (`bbCompress_bounded` + the refutation firing);
* the deployed-width hypothesis FAILS at an unbounded pairing — and there `compressInjective` is
  genuinely TRUE (`pairCompress_injective`, `pairCompress_not_babyBear_bounded`). So the width
  hypothesis is LOAD-BEARING, not decorative.
* `RestHashIffFrame` has no satisfying pole at all (that is the finding), so §3.3 exhibits both poles
  of its REPAIR-SHAPED per-pair weakening instead — satisfiable on the diagonal, refutable at a named
  pair — which is what a finitely-supported rest-view would have to deliver.

No `sorry`, no `axiom`, no `native_decide`.
-/
import Dregg2.Circuit.RestFrameCardinalityFloor
import Dregg2.Circuit.HashFloorHonesty
import Dregg2.Circuit.StateCommitFloorRegrounded
import Dregg2.Circuit.RecursiveAggregation

namespace Dregg2.Verify.ApexPremiseVacuity

open Dregg2.Circuit.StateCommit
  (compressInjective compressNInjective cellLeafInjective RestHashIffFrame kS0)
open Dregg2.Circuit.RestFrameCardinalityFloor (restHashIffFrame_false_by_cardinality balFam)
open Dregg2.Circuit.HashFloorHonesty
  (compressInjective_false_of_finite_range compressNInjective_false_of_finite_range)
open Dregg2.Circuit.StateCommitFloorRegrounded
  (cellLeafInjective_false_babyBear finite_range_of_field_window)
open Dregg2.Exec (CellId Value RecordKernelState)

set_option autoImplicit false

/-- The deployed BabyBear prime `p = 2³¹ − 2²⁷ + 1`. Every Poseidon2 image the deployed
`recStateCommit` produces lands in `[0, p)`. -/
def babyBearP : ℤ := 2013265921

theorem babyBearP_pos : (0 : ℤ) < babyBearP := by norm_num [babyBearP]

/-! ## §1 — the apex's premise bundle, named, and refuted UNCONDITIONALLY. -/

/-- **`ApexCommitFloor`** — EXACTLY the five commitment-floor hypotheses that
`AssuranceCase.unfoolability_guarantee` and `AssuranceCase.deployed_system_secure` carry (in the same
order they appear in those binder lists). Named so the refutation below is visibly about the apex's
own premises and not about a lookalike. -/
def ApexCommitFloor (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ) : Prop :=
  compressInjective cmb ∧ compressInjective compress ∧ compressNInjective compressN
    ∧ cellLeafInjective CH ∧ RestHashIffFrame RH

/-- **⚑ THE HEADLINE — the apex premise bundle is UNSATISFIABLE, at every width.**

Not "at deployed parameters": for EVERY choice of the five commitment functions. The fifth
conjunct alone kills it — `RestHashIffFrame RH` demands `RH : RecordKernelState → ℤ` separate
kernels differing in `bal : CellId → AssetId → ℤ`, a function space of size ≥ `2^ℵ₀`, and `ℤ` is
countable (`restHashIffFrame_false_by_cardinality`, by Cantor). -/
theorem apexCommitFloor_unsatisfiable
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ) :
    ¬ ApexCommitFloor CH RH cmb compress compressN := fun h =>
  restHashIffFrame_false_by_cardinality RH h.2.2.2.2

/-! ### ⚑ WHAT THAT MEANS — the apex proves anything. `ApexCommitFloor` is EXACTLY the binder list
`deployed_system_secure` / `unfoolability_guarantee` take, so `apexCommitFloor_unsatisfiable` says
those binders are jointly contradictory: any application of either theorem would have `False` in
scope, hence an arbitrary `Q`. The conclusions they reach therefore carry no more information than
`False → Q`.

(Stated in prose, not as a theorem, ON PURPOSE: a declaration `(hRest : RestHashIffFrame RH) → Q`
would itself be a refuted-floor CARRIER under `#floor_ratchet`'s position rule — writing the
observation down must not add a gated declaration to the tree it is auditing. `¬ F` above IS the
statement; `absurd` does the rest at any use site.) -/

/-! ## §2 — the FOUR width-refuted legs, INDEPENDENTLY.

§1 rests entirely on `hRest`. If the rest-hash is ever repaired to a finitely-supported view (the
named structural fix), the apex is STILL vacuous at deployed parameters through any one of the other
four. Each is discharged here from the deployed range bound alone, so the finding survives that
repair and does not have to be re-derived. -/

/-- A BabyBear-valued 2-to-1 compression has finite range (as a map on the pair). -/
theorem compress_range_finite (h : ℤ → ℤ → ℤ)
    (hb : ∀ a b, 0 ≤ h a b ∧ h a b < babyBearP) :
    (Set.range (fun p : ℤ × ℤ => h p.1 p.2)).Finite :=
  finite_range_of_field_window (fun p : ℤ × ℤ => h p.1 p.2) babyBearP (fun p => hb p.1 p.2)

/-- **LEG 1/4 — `compressInjective` is FALSE at deployed BabyBear width.** The `cmb` and `compress`
binders of both apexes. Two field elements do not fit in one. -/
theorem compressInjective_false_babyBear (h : ℤ → ℤ → ℤ)
    (hb : ∀ a b, 0 ≤ h a b ∧ h a b < babyBearP) : ¬ compressInjective h :=
  compressInjective_false_of_finite_range h (compress_range_finite h hb)

/-- **LEG 2/4 — `compressNInjective` is FALSE at deployed BabyBear width.** The `compressN` binder;
the sponge runs the infinite `List ℤ` into one felt. -/
theorem compressNInjective_false_babyBear (h : List ℤ → ℤ)
    (hb : ∀ xs, 0 ≤ h xs ∧ h xs < babyBearP) : ¬ compressNInjective h :=
  compressNInjective_false_of_finite_range h
    (finite_range_of_field_window h babyBearP hb)

/-- **LEG 3/4 — `cellLeafInjective` is FALSE at deployed BabyBear width.** The `CH` binder; `Value`
is infinite and a leaf is one felt. (A thin re-pin of the tree's own tooth, at `babyBearP`.) -/
theorem cellLeafInjective_false_babyBear' (CH : CellId → Value → ℤ) (c : CellId)
    (hb : ∀ v, 0 ≤ CH c v ∧ CH c v < babyBearP) : ¬ cellLeafInjective CH :=
  cellLeafInjective_false_babyBear CH c hb

/-- **LEG 4/4 — the rest-hash, which needs NO width hypothesis.** Re-pinned here beside the other
three so the asymmetry is visible in one place: the first three are refuted BY THE WIDTH and would
survive a widening; this one is refuted by the DOMAIN and would not. -/
theorem restHashIffFrame_false_at_any_width (RH : RecordKernelState → ℤ) :
    ¬ RestHashIffFrame RH := restHashIffFrame_false_by_cardinality RH

/-- The apex binder list MINUS the rest-hash leg — i.e. what would remain if `RestHashIffFrame` were
repaired to a finitely-supported rest-view (the named structural fix). -/
def ApexCommitFloorSansRest (CH : CellId → Value → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ) : Prop :=
  compressInjective cmb ∧ compressInjective compress ∧ compressNInjective compressN
    ∧ cellLeafInjective CH

/-- **⚑ THE DEPLOYED-PARAMETER STATEMENT, INDEPENDENT of the cardinality leg.** Even granting a
repaired rest-hash, the REMAINING four apex hypotheses are still jointly contradictory at deployed
BabyBear width — through `compress` alone. So the two findings do not share a cause: repairing
either one leaves the apex vacuous, and both must land. -/
theorem apexCommitFloorSansRest_false_at_babyBear
    (CH : CellId → Value → ℤ) (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (hbc : ∀ a b, 0 ≤ compress a b ∧ compress a b < babyBearP) :
    ¬ ApexCommitFloorSansRest CH cmb compress compressN := fun h =>
  compressInjective_false_babyBear compress hbc h.2.1

/-! ## §3 — ANTI-VACUITY: both poles of every hypothesis used above.

A refutation conditioned on a hypothesis that nothing satisfies would be the same disease one level
up. So: the width hypothesis HOLDS somewhere (§3.1) and FAILS somewhere (§3.2), and at the place it
fails the refuted floor is genuinely TRUE — which is what makes it load-bearing rather than
decorative. -/

/-! ### §3.1 — the POSITIVE pole: a BabyBear-reduced compress satisfies the width hypothesis. -/

/-- A deployed-SHAPED 2-to-1 compression: an arithmetic mix reduced into the BabyBear window. Nothing
about Poseidon2's algebra is used or needed — the refutation's whole hypothesis is "lands in one
felt", which is a property of the reduction, not of the permutation. -/
def bbCompress : ℤ → ℤ → ℤ := fun a b => (a * 31 + b) % babyBearP

/-- The width hypothesis FIRES on it. -/
theorem bbCompress_bounded : ∀ a b, 0 ≤ bbCompress a b ∧ bbCompress a b < babyBearP := by
  intro a b
  refine ⟨Int.emod_nonneg _ (by norm_num [babyBearP]), Int.emod_lt_of_pos _ babyBearP_pos⟩

/-- **POSITIVE POLE (the refutation is not idle).** At the deployed-shaped compression the floor is
FALSE — this is the refutation actually firing on an instance, not an abstract `¬ P`. -/
theorem bbCompress_not_compressInjective : ¬ compressInjective bbCompress :=
  compressInjective_false_babyBear bbCompress bbCompress_bounded

/-- …and CONCRETELY, with the collision exhibited rather than counted: `bbCompress 0 0 = 0` and
`bbCompress 0 p = 0` while `0 ≠ p`. A reader who does not want the pigeonhole gets the pair. -/
theorem bbCompress_explicit_collision :
    bbCompress 0 0 = bbCompress 0 babyBearP ∧ (0 : ℤ) ≠ babyBearP := by
  refine ⟨by norm_num [bbCompress, babyBearP], by norm_num [babyBearP]⟩

/-! ### §3.2 — the NEGATIVE pole: an UNBOUNDED pairing where the floor genuinely HOLDS. -/

/-- A genuine injective pairing `ℤ → ℤ → ℤ` — the toy "hash" into ALL of `ℤ`, which is the only kind
of thing that ever satisfied these floors. -/
def pairCompress : ℤ → ℤ → ℤ := fun a b => (Encodable.encode ((a, b) : ℤ × ℤ) : ℤ)

/-- **NEGATIVE POLE (the floor is SATISFIABLE, so it is not `False` by construction).** The unbounded
pairing IS `compressInjective`. This is what makes the width hypothesis load-bearing: drop it and the
refutation is simply untrue. -/
theorem pairCompress_injective : compressInjective pairCompress := by
  intro a b c d h
  have h' : Encodable.encode ((a, b) : ℤ × ℤ) = Encodable.encode ((c, d) : ℤ × ℤ) := by
    simpa [pairCompress, Nat.cast_inj] using h
  have hp : ((a, b) : ℤ × ℤ) = (c, d) := Encodable.encode_injective h'
  exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩

/-- **…and it is NOT BabyBear-bounded** — proved from the two poles themselves, no arithmetic on
`Encodable.encode` required: a bounded injective 2-to-1 map cannot exist. So the two poles are
genuinely distinct instances and the hypothesis DISCRIMINATES. -/
theorem pairCompress_not_babyBear_bounded :
    ¬ (∀ a b : ℤ, 0 ≤ pairCompress a b ∧ pairCompress a b < babyBearP) := fun hb =>
  compressInjective_false_babyBear pairCompress hb pairCompress_injective

/-! ### §3.3 — the rest-hash has NO positive pole; its REPAIR-SHAPED weakening has both.

`RestHashIffFrame` is refuted for every `RH`, so there is nothing to exhibit on the positive side —
and that absence IS the finding. What a finitely-supported rest-view would have to deliver is the
PER-PAIR separation the binding proof actually consumes: at the two kernels a given seam compares,
equal rest-hashes force equal ledgers. That predicate is satisfiable AND refutable, so the repair
target is a real discriminator rather than another universal nobody can meet. -/

/-- **`RestSeparatesAt RH k k'`** — the per-PAIR leg of `RestHashIffFrame`'s forward direction,
restricted to the `bal` conjunct (the one the cardinality refutation attacks). This is the shape a
finitely-supported rest-hash can actually satisfy: a claim about TWO named kernels, not a universal
injection out of a function space. -/
def RestSeparatesAt (RH : RecordKernelState → ℤ) (k k' : RecordKernelState) : Prop :=
  RH k = RH k' → k'.bal = k.bal

/-- **REPAIR-SHAPE, POSITIVE POLE.** The per-pair predicate is SATISFIED on the diagonal, for every
rest-hash — including the deployed one. (Not a strong fact; the point is that it is inhabited at all,
which `RestHashIffFrame` is not.) -/
theorem restSeparatesAt_satisfiable (RH : RecordKernelState → ℤ) (k : RecordKernelState) :
    RestSeparatesAt RH k k := fun _ => rfl

/-- **REPAIR-SHAPE, NEGATIVE POLE (it BITES).** At a constant rest-hash, the per-pair predicate FAILS
on the two ledgers `balFam ∅` and `balFam Set.univ` — which differ in `bal` at cell `0` (one holds a
unit of every asset, the other holds none). So the repair target discriminates: it is not `True`. -/
theorem restSeparatesAt_refutable :
    ¬ RestSeparatesAt (fun _ => (0 : ℤ)) (balFam ∅) (balFam Set.univ) := by
  intro h
  have hbal : (balFam Set.univ).bal = (balFam ∅).bal := h rfl
  have h0 : (balFam Set.univ).bal 0 0 = (balFam ∅).bal 0 0 := by rw [hbal]
  rw [Dregg2.Circuit.RestFrameCardinalityFloor.balFam_bal_mem (Set.mem_univ 0) 0] at h0
  rw [Dregg2.Circuit.RestFrameCardinalityFloor.balFam_bal_notMem
        (by simp : (0 : Nat) ∉ (∅ : Set Nat)) 0] at h0
  exact absurd h0 (by norm_num)

/-! ## §4 — WHAT SURVIVES: the floor-free half of guarantee E, separated from the vacuous half.

`unfoolability_guarantee` is a CONJUNCTION. Its first conjunct
(`RecursiveAggregation.light_client_verifies_whole_history`) takes NONE of the five refuted floors —
only `EngineSound` and `verify agg.root = true`. Its second conjunct
(`conserves_from_verification`, the CRITICAL-3 closure) takes ALL FIVE, via
`root_tooth_pins_kernel → recStateCommit_binds_kernel`.

So conjoining them made a theorem STRICTLY WEAKER at every parameter than one of its own halves: the
attestation content, which is real, became unreachable because it was welded to content that is not.
This section states the surviving half on its own, and re-pins the tree's existing firing witness so
it is visibly non-vacuous. It does NOT restore the conservation leg — see the header. -/

section Surviving

open Dregg2.Circuit.RecursiveAggregation
open Dregg2.Distributed.HistoryAggregation (ChainStep)

variable {AProof : Type} (verify : AProof → Bool)
variable (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
variable (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)

/-- **`unfoolability_attestation_floor_free` — the half of guarantee E that is NOT vacuous.**
A light client checking ONLY `verify agg.root = true` learns `AggregateAttests`: every turn executed
correctly, the chain is correctly ordered (no reorder/drop/insert), the public final root is the
genuine fold, the genesis root is the chain's start, and `numTurns` is the real count.

⚑ SAID AT CURRENT RESOLUTION, because the name matters: this carries NO commitment-floor hypothesis,
so unlike `unfoolability_guarantee` it has instances. It also does NOT deliver conservation over the
history — that is exactly the conjunct the five refuted floors were paying for, and it is not
available at any parameters until the rest-hash is repaired. This is the floor-free residue, not a
replacement apex. -/
theorem unfoolability_attestation_floor_free
    (agg : Aggregate AProof) (g : Dregg2.Exec.RecChainedState) (steps : List ChainStep)
    (es : EngineSound AProof verify CH RH cmb compress compressN agg g steps)
    (hroot : verify agg.root = true) :
    AggregateAttests AProof CH RH cmb compress compressN agg g steps :=
  light_client_verifies_whole_history AProof verify CH RH cmb compress compressN agg g steps es hroot

end Surviving

/-- **THE FIRING EXHIBIT for the surviving half.** The floor-free attestation FIRES on the tree's
real honest 1-step chain (the `teethGenesis` executor run), delivering a genuine `AggregateAttests`.
So §4's theorem is inhabited — the contrast with §1 is a contrast between a theorem with instances
and one without. -/
theorem unfoolability_attestation_fires :
    Dregg2.Circuit.RecursiveAggregation.AggregateAttests
      Dregg2.Circuit.RecursiveAggregation.RealProof
      Dregg2.Circuit.RecursiveAggregation.zCH Dregg2.Circuit.RecursiveAggregation.zRH
      Dregg2.Circuit.RecursiveAggregation.zcmb Dregg2.Circuit.RecursiveAggregation.zcompress
      Dregg2.Circuit.RecursiveAggregation.zcompressN
      Dregg2.Circuit.RecursiveAggregation.realAggregate
      Dregg2.Exec.ConsensusExec.teethGenesis
      Dregg2.Circuit.RecursiveAggregation.realSteps :=
  unfoolability_attestation_floor_free
    Dregg2.Circuit.RecursiveAggregation.acceptAll
    Dregg2.Circuit.RecursiveAggregation.zCH Dregg2.Circuit.RecursiveAggregation.zRH
    Dregg2.Circuit.RecursiveAggregation.zcmb Dregg2.Circuit.RecursiveAggregation.zcompress
    Dregg2.Circuit.RecursiveAggregation.zcompressN
    Dregg2.Circuit.RecursiveAggregation.realAggregate
    Dregg2.Exec.ConsensusExec.teethGenesis
    Dregg2.Circuit.RecursiveAggregation.realSteps
    Dregg2.Circuit.RecursiveAggregation.real_engine_sound rfl

/-- **⚑ AND THE FIRING WITNESS COULD NEVER HAVE COVERED THE APEX.** The tree's registered non-vacuity
`fires` companion for `unfoolability_guarantee`
(`RecursiveAggregation.light_client_fires_on_real_chain`, the row in
`circuit/tests/security_property_nonvacuity_gate.rs`) instantiates the commitment portal at the
CONSTANT-ZERO hashes `zcmb`/`zcompress`/`zcompressN`/`zCH`. A constant is maximally non-injective, so
that instance REFUTES the apex's own `hCmb`/`hCompress` premises. The registered witness therefore
fires a strictly weaker theorem (`light_client_verifies_whole_history`) at an instance where the apex
itself is inapplicable — which is why a green gate said nothing about the apex. -/
theorem registered_fires_instance_refutes_apex_premises :
    ¬ compressInjective Dregg2.Circuit.RecursiveAggregation.zcmb := by
  intro h
  have := (h 0 0 0 1 rfl).2
  exact absurd this (by norm_num)

/-! ## §5 — the SATISFIABILITY companion is a tautology schema.

`Metatheory.Adversary.Instances.apex_accept_satisfiable_of_floor` — the row that
`security_property_nonvacuity_gate.rs`'s ACCEPT-SATISFIABILITY ledger registers for
`assuranceApexDynamics` (i.e. for `deployed_system_secure`) — has body `⟨c, hacc⟩`: it TAKES
`accept c` and returns `∃ d, accept d`. That is the schema below, at `p := accept`. It is true for
every predicate whatsoever, including an empty one, so it carries ZERO information about whether the
apex's accept-set is inhabited — which is the exact hole the ledger exists to close. -/

/-- **The schema `apex_accept_satisfiable_of_floor` instantiates.** `P → ∃ _, P`, for any predicate
and any point. A "satisfiability companion" of this shape cannot distinguish an inhabited accept-set
from an empty one; it re-packages its own hypothesis. -/
theorem satisfiability_companion_schema {α : Type} (p : α → Prop) (c : α) (h : p c) :
    ∃ d : α, p d := ⟨c, h⟩

/-- **…and it is satisfied by an EMPTY predicate.** The schema is derivable with `p := fun _ => False`
— the hypothesis is then unobtainable and the theorem still elaborates. So registering such a
companion is compatible with the accept-set being empty, which is precisely the vacuous-governance
case the ledger was built to exclude. -/
theorem satisfiability_companion_schema_admits_empty {α : Type} (c : α) :
    (fun _ : α => False) c → ∃ d : α, (fun _ : α => False) d :=
  satisfiability_companion_schema (fun _ => False) c

#assert_axioms apexCommitFloor_unsatisfiable
#assert_axioms apexCommitFloorSansRest_false_at_babyBear
#assert_axioms compressInjective_false_babyBear
#assert_axioms compressNInjective_false_babyBear
#assert_axioms cellLeafInjective_false_babyBear'
#assert_axioms restHashIffFrame_false_at_any_width
#assert_axioms bbCompress_not_compressInjective
#assert_axioms bbCompress_explicit_collision
#assert_axioms pairCompress_injective
#assert_axioms pairCompress_not_babyBear_bounded
#assert_axioms restSeparatesAt_satisfiable
#assert_axioms restSeparatesAt_refutable
#assert_axioms unfoolability_attestation_floor_free
#assert_axioms unfoolability_attestation_fires
#assert_axioms registered_fires_instance_refutes_apex_premises
#assert_axioms satisfiability_companion_schema

end Dregg2.Verify.ApexPremiseVacuity
