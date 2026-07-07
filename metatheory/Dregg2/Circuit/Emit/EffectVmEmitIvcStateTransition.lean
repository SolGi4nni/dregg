/-
# `EffectVmEmitIvcStateTransition` — the IVC hash-chain STATE-TRANSITION AIR, emitted from Lean (law #1).

The IVC (incrementally-verifiable-computation) hash chain accumulates a sequence of fold-step
state roots into ONE published `accumulated_hash`. The deployed crypto content is the REAL STARK
`StateTransitionAir` (`circuit/src/ivc.rs::StateTransitionAir`, AIR name `dregg-state-transition-v1`,
`ivc.rs:585-683`), width 4 = `[step, old_hash, new_root, new_hash]`. Its ONE `eval_constraints`
tooth is the per-row hash-chain step

  `new_hash == extend_accumulated_hash(old_hash, new_root, step)`
             `== hash_many([IVC_DOMAIN_TAG, old_hash, new_root, step])`   (`ivc.rs:231-242,617-620`)

together with FOUR boundary constraints (`ivc.rs:644-682`):

  * row 0:   `step == 1`                                        (`ivc.rs:653-658`)
  * row 0:   `old_hash == initial_accumulated_hash(initial_root)` (`ivc.rs:660-664`, the SEED)
  * last row: `step == step_count`  (= `pi[2]`)                 (`ivc.rs:669-673`)
  * last row: `new_hash == accumulated_hash` (= `pi[3]`)        (`ivc.rs:675-679`, the PUBLISHED pin)

## The arity-4 chip lookup IS the per-row hash.

For EXACTLY four input felts, `hash_many([a,b,c,d])` seeds `state[0..4] = inputs`, sets the
length tag `state[4] = 4`, runs ONE permutation, and returns `state[0]` — byte-identical to
`hash_4_to_1` / the deployed arity-4 Poseidon2 chip absorb (`poseidon2.rs:349-393`,
`descriptor_ir2.rs::chip_absorb_all_lanes` with `arity = 4`). So the per-row step is a REAL
in-circuit arity-4 chip lookup: `(4, [IVC_DOMAIN_TAG, old_hash, new_root, step] padded to
CHIP_RATE, new_hash :: lanes)`. This is the exact `Poseidon2Chip` mapping the ~15 hash-carrying
families (and `MerkleMembershipEmit`) ride.

## The named gate (`FITS_WITH_NAMED_GATE`): the first-row SEED.

The hand AIR's row-0 `old_hash == initial_accumulated_hash(initial_root)` binds a column to a
Poseidon2 HASH-OF-A-PUBLIC-INPUT, gated to the FIRST row only. IR-v2's `Lookup` carries no
`isFirst`/guard (`DescriptorIR2.lean:185,447` — every lookup fires on every row), so a first-row-
gated hash lookup is not expressible without an IR2 change. The AVOIDABLE restructure (the same
posture `EffectVmEmitBundleFold` takes for `acc_in[0] = pi[initial]`): PUBLISH the initial
accumulated hash as the seed public input `pi[0]` and bind it with a first-row `piBinding`. The
`initial_root → initial_accumulated_hash = Poseidon2(IVC_DOMAIN_TAG, initial_root, 0)` step becomes
an OFF-DESCRIPTOR carrier the caller / executor establishes (DECO-leaf posture) — a
ONE-permutation seed leaf, NAMED here, not proven in-descriptor. Every OTHER constraint is emitted
in full.

## Faithful omission (matches the hand AIR): NO step-increment / continuity gate.

`StateTransitionAir` DELIBERATELY drops the two-row `next.step = step+1` / `next.old_hash =
new_hash` transitions (`ivc.rs:622-641`): the STARK's single vanishing polynomial covers the
last→first wrap and the trace pads by DUPLICATING the last row, so an explicit transition gate
would fire on the padded copies (where `next` is an identical clone, NOT the successor) and reject
honest traces. Sequential ordering is instead argued from the boundaries + Poseidon2 preimage
resistance (`step` is a hash input, so each position's digest is unique). We emit EXACTLY the hand
AIR's enforced set — adding a `windowGate` continuity would be UNSOUND against the deployed padding,
not "strictly stronger".

## The teeth (soundness, proved below)

`ivc_rejects_tampered_published_hash` (a last row whose `new_hash` disagrees with the published
`accumulated_hash` is UNSAT — the analogue of `BundleFold`'s tampered-final rejection),
`ivc_rejects_tampered_seed` (a first row whose `old_hash` disagrees with the published seed is
UNSAT), and `ivc_step_is_hashed` (against a sound chip table the `new_hash` column IS the genuine
`hash([IVC_DOMAIN_TAG, old_hash, new_root, step])`), axiom-clean.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Tactics

namespace Dregg2.Circuit.Emit.EffectVmEmitIvcStateTransition

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRowEnv)
open Dregg2.Exec.CircuitEmit (EmittedExpr)

/-! ## §1 — The state-transition trace + PI layout (mirrors the Rust `st_col::*` / PI order). -/
namespace Ivc

/-- The fold-step index (`ivc.rs::st_col::STEP = 0`). -/
def STEP_COL : Nat := 0
/-- The accumulated hash BEFORE this step (`st_col::OLD_HASH = 1`). -/
def OLD_HASH_COL : Nat := 1
/-- This step's new state root (`st_col::NEW_ROOT = 2`). -/
def NEW_ROOT_COL : Nat := 2
/-- The accumulated hash AFTER this step (`st_col::NEW_HASH = 3`). -/
def NEW_HASH_COL : Nat := 3
/-- The 7 exposed chip lanes 1..7 for the per-row arity-4 compress ride cols 4..10 (out0 stays
`NEW_HASH_COL`; the lanes are matched to the chip row, NOT folded — the commitment stays 1-felt). -/
def LANE1_COL : Nat := 4
/-- Total trace width: 4 chain cols + 7 lane cols. -/
def WIDTH : Nat := 4 + (CHIP_OUT_LANES - 1)

/-- Public input: the initial (seed) accumulated hash `initial_accumulated_hash(initial_root)` —
the NAMED-GATE carrier the caller establishes off-descriptor (the row-0 seed the hand AIR hashed
in-boundary from `pi[initial_root]`; here published pre-hashed). -/
def PI_INITIAL_HASH : Nat := 0
/-- Public input: the final state root (declared for layout parity with the hand AIR's
`pi[1] = final_root`; NOT referenced by any constraint — the hand AIR does not bind it either). -/
def PI_FINAL_ROOT : Nat := 1
/-- Public input: the fold-step count (`pi[2]`), pinned to the last row's `step`. -/
def PI_STEP_COUNT : Nat := 2
/-- Public input: the published accumulated hash (`pi[3]`), the soundness anchor. -/
def PI_ACC_HASH : Nat := 3
/-- Public input count (mirrors the hand AIR's 4-PI interface). -/
def PI_COUNT : Nat := 4

end Ivc

/-- The IVC domain-separation tag `0x49564300` (`ivc.rs:179`), the arity-4 absorb's first input. -/
def IVC_DOMAIN_TAG : ℤ := 1230390016

/-! ## §2 — Constraint builders. -/

/-- The per-row hash step as an arity-4 chip lookup: `new_hash = Poseidon2(4, [IVC_DOMAIN_TAG,
old_hash, new_root, step])` — mirrors `ivc.rs:617-620`. (`chipLookupTuple` renders `(4, ins padded
to CHIP_RATE, new_hash :: lanes)`; the deployed chip table is the REAL permutation with the arity
tag at `state[4]`, so out0 IS `hash_4_to_1 = hash_many` of the four felts = `extend_accumulated_hash`.) -/
def perRowHash : VmConstraint2 :=
  .lookup
    { table := .poseidon2
    , tuple := chipLookupTuple
        [.const IVC_DOMAIN_TAG, .var Ivc.OLD_HASH_COL, .var Ivc.NEW_ROOT_COL, .var Ivc.STEP_COL]
        Ivc.NEW_HASH_COL (siteLaneCols Ivc.LANE1_COL) }

/-- First-row boundary `step == 1`, i.e. the polynomial `step − 1` vanishes on row 0
(`ivc.rs:653-658`). -/
def firstStepIsOne : VmConstraint2 :=
  .base (.boundary .first (.add (.var Ivc.STEP_COL) (.const (-1))))

/-- First-row boundary `old_hash == pi[initial_hash]` (the NAMED-GATE seed pin — the restructured
`ivc.rs:660-664`; the `initial_root → seed` Poseidon2 is the off-descriptor carrier). -/
def firstSeedBind : VmConstraint2 :=
  .base (.piBinding .first Ivc.OLD_HASH_COL Ivc.PI_INITIAL_HASH)

/-- Last-row boundary `step == pi[step_count]` (`ivc.rs:669-673`). -/
def lastStepBind : VmConstraint2 :=
  .base (.piBinding .last Ivc.STEP_COL Ivc.PI_STEP_COUNT)

/-- Last-row boundary `new_hash == pi[accumulated_hash]` (`ivc.rs:675-679`) — the
soundness-load-bearing published-hash pin (the analogue of `BundleFold`'s tampered-final tooth). -/
def lastNewHashBind : VmConstraint2 :=
  .base (.piBinding .last Ivc.NEW_HASH_COL Ivc.PI_ACC_HASH)

/-! ## §3 — Assemble the state-transition descriptor. -/

/-- The full constraint list of the state-transition AIR (the hand AIR's ENFORCED set: the per-row
hash + four boundaries, the row-0 seed via the named gate). -/
def ivcConstraints : List VmConstraint2 :=
  [ perRowHash
  , firstStepIsOne
  , firstSeedBind
  , lastStepBind
  , lastNewHashBind ]

/-- The state-transition descriptor: width 11 (4 chain + 7 lane cols), 4 public inputs
`(initial_hash, final_root, step_count, accumulated_hash)`. The Poseidon2 chip AIR the per-row
compress lookup rides is IMPLIED by the `TID_P2` lookup (the prover auto-includes it —
`descriptor_ir2.rs:3539`, `has_chip_lookup`), so `tables` stays empty exactly as
`MerkleMembershipEmit` does. -/
def ivcStateTransitionDescriptor : EffectVmDescriptor2 :=
  { name        := "dregg-ivc-state-transition-v2"
  , traceWidth  := Ivc.WIDTH
  , piCount     := Ivc.PI_COUNT
  , tables      := []
  , constraints := ivcConstraints
  , hashSites   := []
  , ranges      := [] }

/-! ## §4 — Shape tripwires (byte-pinned both sides; the Rust twin pins the same). -/

-- The trace is 4 chain columns (step, old_hash, new_root, new_hash) + 7 chip lane columns.
#guard Ivc.WIDTH == 4 + (CHIP_OUT_LANES - 1)
#guard Ivc.WIDTH == 11
-- Four public inputs: initial-hash seed, final root, step count, accumulated hash.
#guard ivcStateTransitionDescriptor.piCount == 4
-- 5 constraints: 1 chip lookup + 1 first-row boundary + 3 piBindings (1 first, 2 last).
#guard ivcConstraints.length == 5
-- Exactly one chip lookup (the per-row compress), and it is arity-4 (the `hash_4_to_1` shape).
#guard (ivcConstraints.filter (fun c => match c with | .lookup _ => true | _ => false)).length == 1
-- No window gate: the hand AIR omits step-increment/continuity (padding-safe faithful omission).
#guard (ivcConstraints.filter (fun c => match c with | .windowGate _ => true | _ => false)).length == 0
-- Three piBindings (seed + step_count + accumulated_hash).
#guard (ivcConstraints.filter (fun c => match c with
  | .base (.piBinding _ _ _) => true | _ => false)).length == 3
-- The descriptor emits a versioned v2 wire string.
#guard (emitVmJson2 ivcStateTransitionDescriptor).startsWith
  "{\"name\":\"dregg-ivc-state-transition-v2\",\"ir\":2"

-- THE WIRE GOLDEN: the byte-identical string Lean emits; the Rust gate embeds it verbatim and
-- asserts the decode equals an independently hand-built descriptor.
#guard emitVmJson2 ivcStateTransitionDescriptor ==
  "{\"name\":\"dregg-ivc-state-transition-v2\",\"ir\":2,\"trace_width\":11,\"public_input_count\":4,\"tables\":[],\"constraints\":[{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":4},{\"t\":\"const\",\"v\":1230390016},{\"t\":\"var\",\"v\":1},{\"t\":\"var\",\"v\":2},{\"t\":\"var\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":3},{\"t\":\"var\",\"v\":4},{\"t\":\"var\",\"v\":5},{\"t\":\"var\",\"v\":6},{\"t\":\"var\",\"v\":7},{\"t\":\"var\",\"v\":8},{\"t\":\"var\",\"v\":9},{\"t\":\"var\",\"v\":10}]},{\"t\":\"boundary\",\"row\":\"first\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":1,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":0,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":3,\"pi_index\":3}],\"hash_sites\":[],\"ranges\":[]}"

/-! ## §5 — The teeth (soundness): the published-hash + seed rejections + the real-hash strengthening. -/

/-- The descriptor's per-window denotation against a chip `TraceFamily` and a hash. -/
def ivcWindowHolds (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (isFirst isLast : Bool) : Prop :=
  ∀ c ∈ ivcStateTransitionDescriptor.constraints, c.holdsAt hash tf env isFirst isLast

/-- **The published-hash tooth.** A LAST row whose `new_hash` disagrees with the published
`accumulated_hash` (`pi[3]`) cannot satisfy the descriptor — the boundary that binds the fold
output to the caller (the Rust last-row `new_hash == accumulated_hash` boundary). -/
theorem ivc_rejects_tampered_published_hash
    (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (hbad : env.loc Ivc.NEW_HASH_COL ≠ env.pub Ivc.PI_ACC_HASH) :
    ¬ ivcWindowHolds hash tf env false true := by
  intro h
  have hmem : lastNewHashBind ∈ ivcStateTransitionDescriptor.constraints := by
    show _ ∈ ivcConstraints
    simp [ivcConstraints]
  have hc := h _ hmem
  simp only [lastNewHashBind, VmConstraint2.holdsAt, VmConstraint.holdsVm] at hc
  exact hbad (hc trivial)

/-- **The seed tooth (the named-gate anchor).** A FIRST row whose `old_hash` disagrees with the
published seed `pi[initial_hash]` cannot satisfy the descriptor — the restructured row-0 boundary
that pins the accumulated-hash base case to the caller-established seed. -/
theorem ivc_rejects_tampered_seed
    (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (hbad : env.loc Ivc.OLD_HASH_COL ≠ env.pub Ivc.PI_INITIAL_HASH) :
    ¬ ivcWindowHolds hash tf env true false := by
  intro h
  have hmem : firstSeedBind ∈ ivcStateTransitionDescriptor.constraints := by
    show _ ∈ ivcConstraints
    simp [ivcConstraints]
  have hc := h _ hmem
  simp only [firstSeedBind, VmConstraint2.holdsAt, VmConstraint.holdsVm] at hc
  exact hbad (hc trivial)

/-- **The real-hash tooth.** Against a SOUND chip table, the descriptor's per-row lookup ENFORCES
`new_hash = Poseidon2([IVC_DOMAIN_TAG, old_hash, new_root, step])`: the `new_hash` column is the
genuine hash, not a prover-chosen value. This is the deployed `eval_constraints` per-row step, now
an in-circuit constraint (`chip_lookup_sound` forces out0). -/
theorem ivc_step_is_hashed
    (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv) (isFirst isLast : Bool)
    (hSound : ChipTableSound hash (tf .poseidon2))
    (h : ivcWindowHolds hash tf env isFirst isLast) :
    env.loc Ivc.NEW_HASH_COL
      = hash [IVC_DOMAIN_TAG, env.loc Ivc.OLD_HASH_COL, env.loc Ivc.NEW_ROOT_COL,
              env.loc Ivc.STEP_COL] := by
  have hmem : perRowHash ∈ ivcStateTransitionDescriptor.constraints := by
    show _ ∈ ivcConstraints
    simp [ivcConstraints]
  have hc := h _ hmem
  simp only [perRowHash, VmConstraint2.holdsAt, Lookup.holdsAt] at hc
  have hkey := chip_lookup_sound hash (tf .poseidon2) hSound env.loc
    [.const IVC_DOMAIN_TAG, .var Ivc.OLD_HASH_COL, .var Ivc.NEW_ROOT_COL, .var Ivc.STEP_COL]
    Ivc.NEW_HASH_COL (siteLaneCols Ivc.LANE1_COL)
    (by unfold CHIP_RATE; decide) hc
  simpa [EmittedExpr.eval] using hkey

#assert_axioms ivc_rejects_tampered_published_hash
#assert_axioms ivc_rejects_tampered_seed
#assert_axioms ivc_step_is_hashed

end Dregg2.Circuit.Emit.EffectVmEmitIvcStateTransition
