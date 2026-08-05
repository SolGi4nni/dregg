/-
# Dregg2.Circuit.Emit.HomomorphicDigestEmit — the SIS homomorphic-digest FOLD STEP, emitted (law #1)

THIS IS LEAN-AUTHORED AIR. This module is the sole author of the algebra for the
`dregg-homomorphic-digest-step-n4` descriptor; Rust may only parse the emitted IR2 bytes and
supply witnesses. No Rust-side constraint exists for this family.

## What it is

The recursion prover's scan-state digest update (`docs/reference/SIS-DIGEST-PARAMS.md`,
`Dregg2/Crypto/HomomorphicDigest.lean` + `HomomorphicDigestPositioned.lean`) is a MONOID fold
`dig' = dig + A·encode(turn)` over `ℤ_q` with `q = BabyBear = 2013265921`. Because `q` IS the AIR's
field modulus, field arithmetic IS the digest's ring arithmetic — no non-native reduction, no
carries: one windowGate per digest coordinate is the whole fold step. This descriptor is the
FOLD-STEP ACCEPTOR (not evaluator — the producer supplies the witness): rows are turns; each
transition folds one turn's contribution into the running digest accumulator.

## Rows / columns / PIs (POC: n = 4 digest coords, m = 4 encode coords, traceWidth 12, piCount 8)

* `dig[k] = col k` (k < 4) — the running digest accumulator.
* `enc[j] = col 4+j` (j < 4) — this row's encode witness (the turn's `encode(turn)` coordinates).
* `contrib[k] = col 8+k` (k < 4) — this row's claimed `A·enc` matrix-vector product.
* PI 0..3 — the INITIAL digest (bound to the first row's `dig`); PI 4..7 — the FINAL digest
  (bound to the last row's `dig`). PI-bound (not zero-pinned) so an IVC chunk can continue a
  previous chunk's digest; a genesis chunk passes the zero digest as PI 0..3.
* Row 0 is the SEED row: it carries the initial digest and its own `enc`/`contrib` lanes are NOT
  accumulated (the accumulate gate fires on transitions, folding the NEXT row's contribution).
  A trace of `1 + t` rows folds exactly `t` turns; a 1-row trace folds none (initial = final).

## Constraints

1. Per k < 4 a `.gate`: `contrib[k] − Σ_{j<4} A k j · enc[j] = 0` — the witness column IS the
   genuine matrix-vector product (A entries are emitted `.const`s).
2. Per k < 4 a `.windowGate` (on-transition): `nxt[dig k] − loc[dig k] − nxt[contrib k] = 0` —
   the accumulate step, verbatim the BilateralAggregation cumulative-sum shape.
3. Per k < 4 a `.boundary .last` twin of gate 1 (LAST-ROW REPAIR, MerkleMembership's
   `gLastRowBoundaries` pattern): `.gate`s are transition-guarded (`when_transition()`), so
   without the repair the LAST row's `contrib` — the one the final transition folds — would be
   unconstrained and the final digest forgeable.
4. `.piBinding first dig[k] ↦ PI k` and `.piBinding last dig[k] ↦ PI 4+k`.

## Soundness in this file

* `step_refines` — FIELD-FAITHFUL per-step iff (the `cg3_body_modEq_zero_iff` shape): the fold-step
  bodies vanish mod `p` at a two-row window IFF the folded row's `contrib` is the genuine `A·enc`
  AND `dig' ≡ dig + A·enc` coordinate-wise mod `p` — i.e. the constraints accept EXACTLY the
  monoid fold step, over the deployed field.
* `step_rejects_wrong_accumulate` — the descriptor-level tooth: a transition window whose claimed
  `dig'` disagrees (mod `p`) with `dig + contrib` cannot satisfy the descriptor. At `q = BabyBear`
  the mod-`p` disagreement IS the spec-level disagreement (the digest lives in `ℤ_q`), so no
  canonicality side-conditions are needed or smuggled.
* `step_accepts_correct` — the completeness face: an honest window satisfies EVERY descriptor
  constraint on a mid-trace transition window.
* Concrete non-vacuity witnesses (`#guard`): an honest step's bodies all vanish; a tampered
  `dig'₀` is rejected in the FIELD.

## Deferred / follow-ups (the honest seams)

* Registry wiring (`EmitByName` + `scripts/emit_descriptors.py` golden) is the DEFERRED
  integrator step — this module is not yet reachable by name.
* n = 4 is a POC width. The SIS doc's deployable position-indexed figure is ≈ 9–48 digest felts;
  the clone to that width is mechanical (same three blocks, wider).
* `A` here is a small distinct-constant placeholder (`A k j = 1 + 4k + j`). A deployed `A` must be
  transparently sampled (nothing-up-my-sleeve); the MSIS floor is about A's distribution, and
  nothing cryptographic is claimed for THIS matrix.
* The multi-step refinement — whole-trace satisfaction ⟹ `HomomorphicDigest.digest` /
  `HomomorphicDigestPositioned` over the folded history — is a follow-up; THIS file proves the
  per-step acceptance is exactly the fold step.

## Axiom hygiene

`#assert_axioms ⊆ {propext, Classical.choice, Quot.sound}` on every keystone. NEW file; imports
read-only.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.Emit.EffectVmEmitTransfer

namespace Dregg2.Circuit.Emit.HomomorphicDigestEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff)

set_option autoImplicit false

/-! ## §0 — Layout: the POC parameters, columns, and the fixed public matrix. -/

/-- POC digest width (`n` in the SIS doc; deployable ≈ 9–48). -/
def N_DIG : Nat := 4
/-- POC encode width (`m_block` in the SIS doc). -/
def N_ENC : Nat := 4

/-- Column of running-digest coordinate `k` (k < 4). -/
def digCol (k : Nat) : Nat := k
/-- Column of this row's encode-witness coordinate `j` (j < 4). -/
def encCol (j : Nat) : Nat := 4 + j
/-- Column of this row's claimed `A·enc` coordinate `k` (k < 4). -/
def contribCol (k : Nat) : Nat := 8 + k

/-- The fixed public POC matrix: small distinct constants `A k j = 1 + 4k + j ∈ {1..16}`
(meaningful for `k, j < 4`). A PLACEHOLDER for a transparently-sampled deployed matrix — no
cryptographic claim attaches to these entries. -/
def A (k j : Nat) : ℤ := 1 + 4 * (k : ℤ) + (j : ℤ)

/-! ## §1 — The emitted bodies. -/

/-- `Σ_{j<4} A k j · enc[j]` as the emitted expression (nested `.add`s, `A` entries `.const`). -/
def rowDotExpr (k : Nat) : EmittedExpr :=
  .add (.add (.add (.mul (.const (A k 0)) (.var (encCol 0)))
                   (.mul (.const (A k 1)) (.var (encCol 1))))
             (.mul (.const (A k 2)) (.var (encCol 2))))
       (.mul (.const (A k 3)) (.var (encCol 3)))

/-- The `A·enc` witness-gate body: `contrib[k] − Σ_j A k j · enc[j]`. -/
def contribBody (k : Nat) : EmittedExpr :=
  .add (.var (contribCol k)) (.mul (.const (-1)) (rowDotExpr k))

/-- The SPEC-side dot product `Σ_{j<4} A k j · enc[j]` over an assignment. -/
def dotRow (k : Nat) (asg : Assignment) : ℤ :=
  A k 0 * asg (encCol 0) + A k 1 * asg (encCol 1) + A k 2 * asg (encCol 2) + A k 3 * asg (encCol 3)

/-- The accumulate windowGate body (BilateralAggregation's cumulative-sum shape):
`nxt[dig k] + (−1)·loc[dig k] + (−1)·nxt[contrib k]`. -/
def accumBody (k : Nat) : WindowExpr :=
  .add (.nxt (digCol k))
       (.add (.mul (.const (-1)) (.loc (digCol k)))
             (.mul (.const (-1)) (.nxt (contribCol k))))

/-! ## §2 — The constraints and the descriptor. -/

/-- The per-row `A·enc` witness gate for coordinate `k`. -/
def contribGate (k : Nat) : VmConstraint2 := .base (.gate (contribBody k))

/-- The on-transition accumulate gate for coordinate `k`: `dig' = dig + contrib'`. -/
def accumGate (k : Nat) : VmConstraint2 := .windowGate ⟨accumBody k, true⟩

/-- LAST-ROW REPAIR: the `A·enc` witness gate re-asserted on the last row (`.gate` is
transition-guarded, so without this twin the final fold's `contrib` would be unconstrained). -/
def lastRepair (k : Nat) : VmConstraint2 := .base (.boundary .last (contribBody k))

/-- Bind first-row `dig[k]` to PI `k` (the initial digest). -/
def initialPin (k : Nat) : VmConstraint2 := .base (.piBinding .first (digCol k) k)

/-- Bind last-row `dig[k]` to PI `4+k` (the final digest). -/
def finalPin (k : Nat) : VmConstraint2 := .base (.piBinding .last (digCol k) (4 + k))

/-- The four `A·enc` witness gates. -/
def contribGates : List VmConstraint2 :=
  [contribGate 0, contribGate 1, contribGate 2, contribGate 3]
/-- The four accumulate windowGates. -/
def accumGates : List VmConstraint2 :=
  [accumGate 0, accumGate 1, accumGate 2, accumGate 3]
/-- The four last-row repairs. -/
def lastRepairs : List VmConstraint2 :=
  [lastRepair 0, lastRepair 1, lastRepair 2, lastRepair 3]
/-- The four initial-digest PI pins. -/
def initialPins : List VmConstraint2 :=
  [initialPin 0, initialPin 1, initialPin 2, initialPin 3]
/-- The four final-digest PI pins. -/
def finalPins : List VmConstraint2 :=
  [finalPin 0, finalPin 1, finalPin 2, finalPin 3]

/-- The complete fold-step constraint block. -/
def homDigestStepConstraints : List VmConstraint2 :=
  contribGates ++ accumGates ++ lastRepairs ++ initialPins ++ finalPins

/-- The SIS homomorphic-digest FOLD-STEP descriptor (n = 4 POC, `q = BabyBear`). -/
def homDigestStepDesc : EffectVmDescriptor2 :=
  { name        := "dregg-homomorphic-digest-step-n4::v1"
  , traceWidth  := 12
  , piCount     := 8
  , tables      := []
  , constraints := homDigestStepConstraints
  , hashSites   := []
  , ranges      := [] }

-- Non-vacuous structural pins. The exact emitted-byte pin follows the literal golden below.
#guard homDigestStepDesc.traceWidth == 12
#guard homDigestStepDesc.piCount == 8
#guard homDigestStepDesc.constraints.length == 20
#guard homDigestStepDesc.tables.length == 0
#guard (homDigestStepDesc.constraints.filter
          (fun c => match c with | .windowGate _ => true | _ => false)).length == 4

/-- Exact emitted-wire golden. Generated once from `emitVmJson2 homDigestStepDesc` and pasted
verbatim; the Rust side will `include_str!` these bytes when the registry wiring lands. -/
def HOM_DIGEST_STEP_GOLDEN : String :=
  "{\"name\":\"dregg-homomorphic-digest-step-n4::v1\",\"ir\":2,\"trace_width\":12,\"public_input_count\":8,\"challenges\":0,\"tables\":[],\"constraints\":[{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":4}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"var\",\"v\":5}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":3},\"r\":{\"t\":\"var\",\"v\":6}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":7}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":5},\"r\":{\"t\":\"var\",\"v\":4}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":6},\"r\":{\"t\":\"var\",\"v\":5}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":7},\"r\":{\"t\":\"var\",\"v\":6}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":8},\"r\":{\"t\":\"var\",\"v\":7}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":9},\"r\":{\"t\":\"var\",\"v\":4}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":10},\"r\":{\"t\":\"var\",\"v\":5}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":11},\"r\":{\"t\":\"var\",\"v\":6}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":12},\"r\":{\"t\":\"var\",\"v\":7}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":13},\"r\":{\"t\":\"var\",\"v\":4}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":14},\"r\":{\"t\":\"var\",\"v\":5}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":15},\"r\":{\"t\":\"var\",\"v\":6}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":16},\"r\":{\"t\":\"var\",\"v\":7}}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":0},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":0}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":8}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":1}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":9}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":2},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":2}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":10}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":3},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":3}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"nxt\",\"c\":11}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":4}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"var\",\"v\":5}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":3},\"r\":{\"t\":\"var\",\"v\":6}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":7}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":5},\"r\":{\"t\":\"var\",\"v\":4}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":6},\"r\":{\"t\":\"var\",\"v\":5}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":7},\"r\":{\"t\":\"var\",\"v\":6}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":8},\"r\":{\"t\":\"var\",\"v\":7}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":9},\"r\":{\"t\":\"var\",\"v\":4}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":10},\"r\":{\"t\":\"var\",\"v\":5}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":11},\"r\":{\"t\":\"var\",\"v\":6}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":12},\"r\":{\"t\":\"var\",\"v\":7}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":13},\"r\":{\"t\":\"var\",\"v\":4}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":14},\"r\":{\"t\":\"var\",\"v\":5}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":15},\"r\":{\"t\":\"var\",\"v\":6}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":16},\"r\":{\"t\":\"var\",\"v\":7}}}}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":0,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":1,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":2,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":3,\"pi_index\":3},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":0,\"pi_index\":4},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":1,\"pi_index\":5},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":2,\"pi_index\":6},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":3,\"pi_index\":7}],\"hash_sites\":[],\"ranges\":[]}"

#guard emitVmJson2 homDigestStepDesc == HOM_DIGEST_STEP_GOLDEN

/-- The complete constraint-block shape, pinned. -/
theorem descriptor_has_complete_shape :
    homDigestStepDesc.constraints =
      contribGates ++ accumGates ++ lastRepairs ++ initialPins ++ finalPins := rfl

/-! ## §3 — FIELD-FAITHFUL per-step refinement (`cg3_body_modEq_zero_iff` shape). -/

/-- The `A·enc` witness gate vanishes mod `p` EXACTLY when the `contrib` column carries the
genuine matrix-vector product mod `p`. -/
theorem contrib_body_modEq_zero_iff (asg : Assignment) (k : Nat) :
    ((contribBody k).eval asg ≡ 0 [ZMOD 2013265921]) ↔
      (asg (contribCol k) ≡ dotRow k asg [ZMOD 2013265921]) := by
  simp only [contribBody, rowDotExpr, EmittedExpr.eval]
  exact gate_modEq_iff (by simp only [dotRow]; ring)

/-- The accumulate gate vanishes mod `p` EXACTLY when the next digest coordinate is the current
one plus the next row's contribution mod `p` — the monoid fold step, in the field. -/
theorem accum_body_modEq_zero_iff (env : VmRowEnv) (k : Nat) :
    ((accumBody k).eval env ≡ 0 [ZMOD 2013265921]) ↔
      (env.nxt (digCol k) ≡ env.loc (digCol k) + env.nxt (contribCol k) [ZMOD 2013265921]) := by
  simp only [accumBody, WindowExpr.eval]
  exact gate_modEq_iff (by ring)

/-- The FOLD-STEP body bundle at a two-row window: the four accumulate windowGate bodies (on the
window) + the four `A·enc` gate bodies on the NEXT row — the row being folded (in the whole-trace
denotation that row's own window asserts them: as its `.gate` on a transition row, as the
`.boundary .last` repair on the last row). -/
def foldStepHolds (env : VmRowEnv) : Prop :=
  (∀ k, k < 4 → ((accumBody k).eval env ≡ 0 [ZMOD 2013265921])) ∧
  (∀ k, k < 4 → ((contribBody k).eval env.nxt ≡ 0 [ZMOD 2013265921]))

/-- **THE PER-STEP REFINEMENT (field-faithful, both directions).** The fold-step bodies vanish
mod `p` IFF, coordinate-wise: the folded row's `contrib` witness IS the genuine `A·enc` (mod `p`),
and the digest update IS the monoid fold `dig' ≡ dig + A·enc` (mod `p`). Because `q = BabyBear`
is the digest's ring modulus, the mod-`p` statement IS the spec statement — the acceptor accepts
exactly the SIS fold step, with the witness column pinned. -/
theorem step_refines (env : VmRowEnv) :
    foldStepHolds env ↔
      ∀ k, k < 4 →
        (env.nxt (contribCol k) ≡ dotRow k env.nxt [ZMOD 2013265921]) ∧
        (env.nxt (digCol k) ≡ env.loc (digCol k) + dotRow k env.nxt [ZMOD 2013265921]) := by
  constructor
  · rintro ⟨hacc, hwit⟩ k hk
    have h1 := (contrib_body_modEq_zero_iff env.nxt k).mp (hwit k hk)
    have h2 := (accum_body_modEq_zero_iff env k).mp (hacc k hk)
    exact ⟨h1, h2.trans (Int.ModEq.add_left _ h1)⟩
  · intro h
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · exact (accum_body_modEq_zero_iff env k).mpr
        ((h k hk).2.trans (Int.ModEq.add_left _ (h k hk).1.symm))
    · exact (contrib_body_modEq_zero_iff env.nxt k).mpr (h k hk).1

/-! ## §4 — Descriptor-level teeth: the emitted object itself accepts/rejects. -/

/-- The descriptor's per-window denotation (no tables / hash sites / ranges): every constraint
holds on the window. -/
def stepWindowHolds (env : VmRowEnv) (isFirst isLast : Bool) : Prop :=
  ∀ c ∈ homDigestStepDesc.constraints,
    c.holdsAt (fun _ => 0) (fun _ => []) env isFirst isLast

/-- The accumulate gate for coordinate `k < 4` is IN the descriptor. -/
theorem accumGate_mem (k : Nat) (hk : k < 4) :
    accumGate k ∈ homDigestStepDesc.constraints := by
  show accumGate k ∈ contribGates ++ accumGates ++ lastRepairs ++ initialPins ++ finalPins
  have h4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  have hmem : accumGate k ∈ accumGates := by
    rcases h4 with rfl | rfl | rfl | rfl <;> simp [accumGates]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ hmem)))

/-- **NEGATIVE TOOTH (descriptor-level, field-faithful).** A transition window whose claimed next
digest coordinate disagrees mod `p` with `dig + contrib` CANNOT satisfy the descriptor: the
accumulate gate is real, not decorative. At `q = BabyBear` the mod-`p` disagreement IS the
spec-level disagreement (the digest lives in `ℤ_q`), so no canonicality hypotheses are needed. -/
theorem step_rejects_wrong_accumulate (env : VmRowEnv) (k : Nat) (hk : k < 4)
    (hbad : ¬ (env.nxt (digCol k)
      ≡ env.loc (digCol k) + env.nxt (contribCol k) [ZMOD 2013265921])) :
    ¬ stepWindowHolds env false false := by
  intro h
  have hc := h _ (accumGate_mem k hk)
  simp only [accumGate, VmConstraint2.holdsAt, WindowConstraint.holdsAt] at hc
  exact hbad ((accum_body_modEq_zero_iff env k).mp (hc trivial))

/-- **POSITIVE TOOTH (descriptor-level completeness).** An honest mid-trace transition window —
current row's `contrib` genuine, next digest the genuine fold — satisfies EVERY constraint of the
descriptor (boundary/PI forms are off-row here; the folded row's own witness gate is asserted by
ITS window, per `foldStepHolds`). The acceptor does not over-constrain the honest prover. -/
theorem step_accepts_correct (env : VmRowEnv)
    (hloc : ∀ k, k < 4 → (env.loc (contribCol k) ≡ dotRow k env.loc [ZMOD 2013265921]))
    (hacc : ∀ k, k < 4 → (env.nxt (digCol k)
      ≡ env.loc (digCol k) + env.nxt (contribCol k) [ZMOD 2013265921])) :
    stepWindowHolds env false false := by
  intro c hc
  rw [descriptor_has_complete_shape] at hc
  simp only [contribGates, accumGates, lastRepairs, initialPins, finalPins,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with ((((rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)) |
    (rfl | rfl | rfl | rfl)) | (rfl | rfl | rfl | rfl)) | (rfl | rfl | rfl | rfl)
  all_goals first
    | exact fun (h : false = true) => nomatch h
    | exact (contrib_body_modEq_zero_iff env.loc _).mpr (hloc _ (by omega))
    | exact fun _ => (accum_body_modEq_zero_iff env _).mpr (hacc _ (by omega))

/-! ## §5 — Concrete witness rows (non-vacuity, both directions).

Honest window: `loc.dig = (100, 200, 300, 400)`; the folded row has `enc = (1, 1, 1, 1)`, so the
genuine contributions are the `A` row sums `(10, 26, 42, 58)` and the honest next digest is
`(110, 226, 342, 458)`. -/

/-- Honest current row: digest `(100, 200, 300, 400)`, all witness lanes zero. -/
def okLoc : Assignment := fun i =>
  if i = 0 then 100 else if i = 1 then 200 else if i = 2 then 300 else if i = 3 then 400 else 0

/-- Honest next row: digest `(110, 226, 342, 458)`, `enc = (1,1,1,1)`, `contrib = (10,26,42,58)`. -/
def okNxt : Assignment := fun i =>
  if i = 0 then 110 else if i = 1 then 226 else if i = 2 then 342 else if i = 3 then 458
  else if i = 4 then 1 else if i = 5 then 1 else if i = 6 then 1 else if i = 7 then 1
  else if i = 8 then 10 else if i = 9 then 26 else if i = 10 then 42 else if i = 11 then 58 else 0

/-- The honest two-row window. -/
def okEnv : VmRowEnv := { loc := okLoc, nxt := okNxt, pub := fun _ => 0 }

/-- The tampered next row: `dig'₀` forged `110 → 111` (everything else honest). -/
def badNxt : Assignment := fun i => if i = 0 then 111 else okNxt i

/-- The tampered window. -/
def badEnv : VmRowEnv := { loc := okLoc, nxt := badNxt, pub := fun _ => 0 }

-- ACCEPTS: every fold-step body vanishes on the honest window (over ℤ, hence mod p).
#guard decide ((accumBody 0).eval okEnv = 0 ∧ (accumBody 1).eval okEnv = 0 ∧
               (accumBody 2).eval okEnv = 0 ∧ (accumBody 3).eval okEnv = 0)
#guard decide ((contribBody 0).eval okNxt = 0 ∧ (contribBody 1).eval okNxt = 0 ∧
               (contribBody 2).eval okNxt = 0 ∧ (contribBody 3).eval okNxt = 0)

-- REJECTS: the forged `dig'₀` breaks the accumulate gate IN THE FIELD (not merely over ℤ).
#guard decide (¬ ((accumBody 0).eval badEnv ≡ 0 [ZMOD 2013265921]))

/-! ## §6 — Axiom hygiene. -/

#assert_axioms descriptor_has_complete_shape
#assert_axioms contrib_body_modEq_zero_iff
#assert_axioms accum_body_modEq_zero_iff
#assert_axioms step_refines
#assert_axioms accumGate_mem
#assert_axioms step_rejects_wrong_accumulate
#assert_axioms step_accepts_correct

end Dregg2.Circuit.Emit.HomomorphicDigestEmit
