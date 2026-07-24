/-
# Dregg2.Circuit.Emit.GuardedHidingSpanWideBlindEmit — THE hidden-span commitment descriptor:
WIDE BLINDING (5 fresh uniform blinding lanes, |R| = p⁵ ≈ 2^154.5 ≥ 2^128).

**This is Lean-authored AIR.** This module authors the algebra; the descriptor's wire bytes are
byte-pinned by an `emitVmJson2` `#guard`; refinement (`GuardedHidingSpanWideBlindRefine`) is a
`Satisfied2 <emitted-descriptor> ⟹ spec` theorem over the EMITTED object. Rust authors nothing —
it parses the emitted IR2 bytes and supplies witnesses.

Since the felt-width cutover of 2026-07-23 this is the SOLE emitted hidden-span descriptor: the
narrow single-blinding-felt M0 descriptor that used to live in `GuardedHidingSpanEmit` was
DELETED (descriptor + byte golden + `EmitByName` registration), so the ~31-bit-blinding object
is GONE from the emitted set, not merely shadowed.

## THE FINDING this file closes (the blinding-axis felt-width sin)

The original M0 blinded the hidden-span commitment with **ONE** BabyBear
felt (`BLINDING`, column 24; the arity-10 stage-2 tooth `hole_commit = A(MID ‖ [BLINDING, 0])`).
The keyed-ROM hiding bound for a blinded commitment is `Q/|R|`, where `|R|` is the BLINDING SPACE
and `Q` the adversary's query budget: an adversary simply enumerates blindings against the
published `hole_commit`. One BabyBear felt gives `|R| = p ≈ 2^31`, so the M0 hiding is only
~31-bit — **grindable in seconds**. This is the blinding-axis analog of the felt-width law
(`docs/FAITHFUL-COMMITMENT-LAW.md`): one felt of BLINDING is a hiding sin exactly as one felt of
DIGEST is a binding sin. The 8-felt digest work widened every BINDING surface; the blinding — the
HIDING surface — stayed one felt wide.

## The widened scheme (identical to M0 except the blinded tooth)

The stage-2 blinded-commit tooth absorbs **5 fresh uniform blinding lanes** instead of one:

    mid         = A16(span_digest8 ‖ C_T)                     -- unchanged (arity 16)
    hole_commit = A14(mid ‖ [r₀,r₁,r₂,r₃,r₄] ‖ [0])           -- the WIDE-BLIND tooth (arity 14)

`|R| = p⁵` with `p = 2^31 − 2^27 + 1` (BabyBear): `p⁵ ≈ 2^154.5`, so the keyed-ROM hiding bound
`Q/|R| ≤ Q/2^154` is strong. Why 5 lanes and not 4: `p⁴ ≈ 2^123.6` — the "~124-bit" of the digest
convention, but **below the 2^128 hiding floor** the finding names (hiding is a direct `Q/|R|`
enumeration bound, not birthday-halved, so the space itself must clear 2^128). Five lanes clear
it with margin at the cost of one column; the `#guard`s below pin `p^BLIND_LANES ≥ 2^128` so a
future lane-count squeeze fails the build. Arity 14 ≤ `CHIP_RATE = 16`, domain-separated from the
arity-8/10/16 rows by the chip's arity tag (the arity-10 M0 tooth and this arity-14 tooth can
never confuse rows).

Everything else is M0 verbatim: the span digest (arity 8), the stage-1 fold (arity 16), the
three 8-felt PI groups `[C_T, hole_commit, guard_table_commitment]`, all folds absorbing whole
8-lane groups with all 8 output lanes bound via `chipLookupTupleN` — no lane-0 squeeze anywhere.

## HONEST scope — what this construction does and does not buy

This file makes the keyed-ROM hiding bound MEANINGFUL as a construction requirement: with one
blinding felt the bound `Q/|R|` is vacuous at `|R| = 2^31` no matter how good the sponge is; with
`|R| ≥ 2^128` the bound is strong IF the sponge behaves as a keyed ROM. What is PROVEN here (and
in the Refine) is the RELATION and BINDING-as-extraction, exactly as in M0. Hiding-as-ZK itself
("the verifier learns nothing") is NOT proven: it rests on the Poseidon2 keyed-ROM/commitment-
hiding floor + the blinding lanes being fresh-uniform (prover-side discipline) + `HidingFriPcs`,
and inherits the FRI/STARK floor. Do NOT read this file as proven ZK — read it as removing the
CONSTRUCTION-side reason the hiding bound was unmeaningful.

## The guard attestation

The guard obligation `derives span guard = true` is welded strictly below
`mem_language_iff_spans` (`GuardedHidingSpanRefine` §"The WELD"). In the plain refinement
(`GuardedHidingSpanWideBlindRefine`) it rides as the plainly-named hypothesis `hGuard`; the
GROUNDED keystone (`GuardedHidingSpanGuardWeld.guardedHidingSpan_refines_parse_grounded`)
DERIVES it from the emitted table-as-input routing descriptor + the proven DFA encoding weld.

## Axiom hygiene

Definitional descriptor + a byte-pinned `#guard` on its wire string + non-vacuous shape/semantic
lemmas. `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Imports read-only.
-/
import Dregg2.Circuit.Emit.GuardedHidingSpanEmit

namespace Dregg2.Circuit.Emit.GuardedHidingSpanWideBlindEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId Table chipLookupTupleN ChipTableSoundN
   chip_lookup_sound_N CHIP_RATE emitVmJson2)
open Dregg2.Circuit.DeployedCapTree (Digest8 Coll8)
open Dregg2.Circuit.DeployedCapTree.Cap8Scheme (pack8 pack8_inj)
open Dregg2.Circuit.Emit.BlindedMembershipWideEmit (wCols wVal wCols_map wStageIns wStageIns_eval wPermOut)
open Dregg2.Circuit.Emit.GuardedHidingSpanEmit
  (wideFoldPair piCT piHOLE piGUARD GHS_PI_COUNT demoAbsorb dA dB cT0)

set_option autoImplicit false

/-! ## §1 — the trace column layout: M0's, with the one blinding felt widened to 5 lanes.

Every commitment value is an 8-lane `Digest8` group; the ONLY published groups are `C_T`,
`hole_commit`, and the guard identity — identical to M0. The blinding block is now 5 HIDDEN
lanes. -/

/-- The number of fresh uniform blinding lanes. ≥ 4 is the campaign floor (~2^124); 5 clears the
2^128 hiding floor (`p⁵ ≈ 2^154.5`) — pinned by the `#guard`s in §6. -/
def BLIND_LANES : Nat := 5

/-- The blinding vector carrier: 5 BabyBear felts. -/
abbrev Blind5 := Fin 5 → ℤ

/-- The 8 HIDDEN hole-0 span symbol lanes (the private hole data, field-encoded). -/
def gSPAN : Fin 8 → Nat := fun k => k.val
/-- `span_digest8` — the faithful 8-felt Poseidon2 digest of the span lanes (HIDDEN). -/
def gDIGEST : Fin 8 → Nat := fun k => 8 + k.val
/-- `C_T` — the public context commitment the hole is bound against (pinned to PI[0..7]). -/
def gCT : Fin 8 → Nat := fun k => 16 + k.val
/-- The 5 fresh `BLINDING` lanes — HIDDEN, NEVER PI-bound. Their joint space is `p⁵ ≈ 2^154.5`,
which is what makes the keyed-ROM hiding bound `Q/|R|` strong (M0's single felt gave `2^31`,
grindable). -/
def gBLIND : Fin 5 → Nat := fun k => 24 + k.val
/-- The stage-1 wide fold `MID = A16(span_digest8 ‖ C_T)` (HIDDEN interior). -/
def gMID : Fin 8 → Nat := fun k => 29 + k.val
/-- `hole_commit` — the published 8-felt blinded commitment (pinned to PI[8..15]). -/
def gHOLE : Fin 8 → Nat := fun k => 37 + k.val
/-- `guard_table_commitment` — the hole's guard-DFA IDENTITY, public, pinned to PI[16..23]. -/
def gGUARD : Fin 8 → Nat := fun k => 45 + k.val
/-- Total main-trace width: 7 8-lane groups + the 5 blinding lanes. -/
def GHSW_WIDTH : Nat := 53

/-- The 5 blinding columns, in lane order. -/
def bCols : List Nat := (List.finRange 5).map gBLIND

/-- Read the blinding block under an assignment as a `Blind5`. -/
def bVal (a : Assignment) : Blind5 := fun k => a (gBLIND k)

/-- The 5 blinding columns read under `a` ARE `List.ofFn (bVal a)` — the `Blind5` twin of
`wCols_map`. -/
theorem bCols_map (a : Assignment) : bCols.map a = List.ofFn (bVal a) := by
  unfold bCols bVal
  rw [List.map_map, List.ofFn_eq_map]
  rfl

/-! The PI surface is IDENTICAL to M0: `[C_T(8), hole_commit(8), guard_table_commitment(8)]`,
`piCT`/`piHOLE`/`piGUARD`/`GHS_PI_COUNT` reused unchanged. -/

/-! ## §2 — the WIDE-BLIND commit fold model.

`absorb : List ℤ → Digest8` is the wide squeeze. Stage 1 is M0's `wideFoldPair` unchanged;
stage 2 widens the blinding block from `[r, 0]` to `[r₀..r₄, 0]`. -/

/-- Pack an 8-felt leaf with the 5 blinding lanes and the idiom's trailing `0` into the arity-14
stage-2 absorb block `leaf8 ‖ r₀..r₄ ‖ [0]` — the wide-blind analogue of M0's `packCommit`
(`leaf8 ‖ [r, 0]`). -/
def packCommitW (leaf : Digest8) (r : Blind5) : List ℤ :=
  List.ofFn leaf ++ (List.ofFn r ++ [0])

/-- **`holeCommitWideOf`** — the wide-blind hole-commitment: fold the two 8-felt digest slots,
then absorb the running digest with ALL 5 blinding lanes and the trailing `0`. Every input lane in
the preimage, every output lane bound. -/
def holeCommitWideOf (absorb : List ℤ → Digest8) (spanD cT : Digest8) (r : Blind5) : Digest8 :=
  absorb (packCommitW (wideFoldPair absorb spanD cT) r)

/-- `packCommitW` is injective in `(leaf, r)`: the length-8 prefix is the leaf, the next 5 lanes
are the whole blinding vector, the fixed trailing `0` carries no information — `packCommit_inj`
at arity 14. -/
theorem packCommitW_inj {l₁ l₂ : Digest8} {r₁ r₂ : Blind5}
    (h : packCommitW l₁ r₁ = packCommitW l₂ r₂) : l₁ = l₂ ∧ r₁ = r₂ := by
  unfold packCommitW at h
  have hlen : (List.ofFn l₁).length = (List.ofFn l₂).length := by simp
  obtain ⟨hl, hr⟩ := List.append_inj h hlen
  have hlen2 : (List.ofFn r₁).length = (List.ofFn r₂).length := by simp
  obtain ⟨hb, -⟩ := List.append_inj hr hlen2
  exact ⟨List.ofFn_inj.mp hl, List.ofFn_inj.mp hb⟩

/-! ## §3 — the three WIDE lookups (span digest, stage-1 fold, the WIDE-BLIND stage-2 tooth). -/

/-- The 8 input expressions of the span-digest absorb: the 8 hidden span lanes. -/
def spanIns : List EmittedExpr := (wCols gSPAN).map EmittedExpr.var

/-- The span-digest absorb input list evaluates to exactly the 8-felt span lane vector. -/
theorem spanIns_eval (a : Assignment) : spanIns.map (·.eval a) = List.ofFn (wVal a gSPAN) := by
  have hcomp : ((wCols gSPAN).map EmittedExpr.var).map (·.eval a) = (wCols gSPAN).map a := by
    rw [List.map_map]; rfl
  simp only [spanIns, hcomp, wCols_map]

/-- The 14 input expressions of the stage-2 WIDE-BLIND absorb: the 8 `MID` lanes, then the 5
blinding lanes, then the idiom's literal trailing `0`. -/
def commitStage2WideIns : List EmittedExpr :=
  (wCols gMID).map EmittedExpr.var ++ (bCols.map EmittedExpr.var ++ [.const 0])

/-- The stage-2 input list evaluates to exactly `packCommitW MID (bVal a)`. -/
theorem commitStage2WideIns_eval (a : Assignment) :
    commitStage2WideIns.map (·.eval a) = packCommitW (wVal a gMID) (bVal a) := by
  have hcomp : ((wCols gMID).map EmittedExpr.var).map (·.eval a) = (wCols gMID).map a := by
    rw [List.map_map]; rfl
  have hcompb : (bCols.map EmittedExpr.var).map (·.eval a) = bCols.map a := by
    rw [List.map_map]; rfl
  simp only [commitStage2WideIns, List.map_append, hcomp, hcompb, wCols_map, bCols_map,
    List.map_cons, List.map_nil, EmittedExpr.eval, packCommitW]

/-- **span digest**: `span_digest8 = A8(span lanes)` — arity 8, all 8 output lanes bound. -/
def spanDigestLookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2, chipLookupTupleN spanIns (wCols gDIGEST)⟩

/-- **commit stage 1**: `MID = A16(span_digest8 ‖ C_T)` — arity 16, all 8 output lanes bound. -/
def commitStage1Lookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2, chipLookupTupleN (wStageIns gDIGEST gCT) (wCols gMID)⟩

/-- **commit stage 2 (THE WIDE-BLIND TOOTH)**: `hole_commit = A14(MID ‖ r₀..r₄ ‖ 0)` — the
blinded-commit tooth with the FULL 5-lane blinding block in the preimage, all 8 output lanes
bound. arity 14 (domain-separated from M0's arity-10 tooth by the chip's arity tag). -/
def commitStage2WideLookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2, chipLookupTupleN commitStage2WideIns (wCols gHOLE)⟩

/-! ## §4 — the boundary PI pins (identical roles to M0; the blinding lanes are NEVER pinned). -/

/-- `C_T` pins: first-row `C_T` lane `k` = PI `k`. -/
def ctPins : List VmConstraint2 :=
  (List.finRange 8).map fun k => .base (.piBinding VmRow.first (gCT k) (piCT k))
/-- `hole_commit` pins: first-row published blinded lane `k` = PI `8 + k`. -/
def holePins : List VmConstraint2 :=
  (List.finRange 8).map fun k => .base (.piBinding VmRow.first (gHOLE k) (piHOLE k))
/-- `guard_table_commitment` pins: first-row guard-identity lane `k` = PI `16 + k`. -/
def guardPins : List VmConstraint2 :=
  (List.finRange 8).map fun k => .base (.piBinding VmRow.first (gGUARD k) (piGUARD k))

/-! ## §5 — the descriptor. -/

/-- **`guardedHidingSpanWideBlindDesc`** — THE emitted hidden-span descriptor: identical to the
deleted narrow M0 form except the stage-2 blinded tooth absorbs the 5-lane blinding block
(arity 14 vs the deleted arity 10) and the trace carries 4 more (hidden, never-pinned)
columns. -/
def guardedHidingSpanWideBlindDesc : EffectVmDescriptor2 :=
  { name        := "dregg-guarded-hiding-span-m0::wide-blinded-commit-blind5-v1"
  , traceWidth  := GHSW_WIDTH
  , piCount     := GHS_PI_COUNT
  , tables      := []
  , constraints := [spanDigestLookup, commitStage1Lookup, commitStage2WideLookup]
                     ++ ctPins ++ holePins ++ guardPins
  , hashSites   := []
  , ranges      := [] }

/-! ## §6 — the byte-pinned wire golden (the Rust decoder ingests THIS string). -/

#guard emitVmJson2 guardedHidingSpanWideBlindDesc ==
  "{\"name\":\"dregg-guarded-hiding-span-m0::wide-blinded-commit-blind5-v1\",\"ir\":2,\"trace_width\":53,\"public_input_count\":24,\"tables\":[],\"constraints\":[{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":8},{\"t\":\"var\",\"v\":0},{\"t\":\"var\",\"v\":1},{\"t\":\"var\",\"v\":2},{\"t\":\"var\",\"v\":3},{\"t\":\"var\",\"v\":4},{\"t\":\"var\",\"v\":5},{\"t\":\"var\",\"v\":6},{\"t\":\"var\",\"v\":7},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":8},{\"t\":\"var\",\"v\":9},{\"t\":\"var\",\"v\":10},{\"t\":\"var\",\"v\":11},{\"t\":\"var\",\"v\":12},{\"t\":\"var\",\"v\":13},{\"t\":\"var\",\"v\":14},{\"t\":\"var\",\"v\":15}]},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":16},{\"t\":\"var\",\"v\":8},{\"t\":\"var\",\"v\":9},{\"t\":\"var\",\"v\":10},{\"t\":\"var\",\"v\":11},{\"t\":\"var\",\"v\":12},{\"t\":\"var\",\"v\":13},{\"t\":\"var\",\"v\":14},{\"t\":\"var\",\"v\":15},{\"t\":\"var\",\"v\":16},{\"t\":\"var\",\"v\":17},{\"t\":\"var\",\"v\":18},{\"t\":\"var\",\"v\":19},{\"t\":\"var\",\"v\":20},{\"t\":\"var\",\"v\":21},{\"t\":\"var\",\"v\":22},{\"t\":\"var\",\"v\":23},{\"t\":\"var\",\"v\":29},{\"t\":\"var\",\"v\":30},{\"t\":\"var\",\"v\":31},{\"t\":\"var\",\"v\":32},{\"t\":\"var\",\"v\":33},{\"t\":\"var\",\"v\":34},{\"t\":\"var\",\"v\":35},{\"t\":\"var\",\"v\":36}]},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":14},{\"t\":\"var\",\"v\":29},{\"t\":\"var\",\"v\":30},{\"t\":\"var\",\"v\":31},{\"t\":\"var\",\"v\":32},{\"t\":\"var\",\"v\":33},{\"t\":\"var\",\"v\":34},{\"t\":\"var\",\"v\":35},{\"t\":\"var\",\"v\":36},{\"t\":\"var\",\"v\":24},{\"t\":\"var\",\"v\":25},{\"t\":\"var\",\"v\":26},{\"t\":\"var\",\"v\":27},{\"t\":\"var\",\"v\":28},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":37},{\"t\":\"var\",\"v\":38},{\"t\":\"var\",\"v\":39},{\"t\":\"var\",\"v\":40},{\"t\":\"var\",\"v\":41},{\"t\":\"var\",\"v\":42},{\"t\":\"var\",\"v\":43},{\"t\":\"var\",\"v\":44}]},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":16,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":17,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":18,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":19,\"pi_index\":3},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":20,\"pi_index\":4},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":21,\"pi_index\":5},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":22,\"pi_index\":6},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":23,\"pi_index\":7},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":37,\"pi_index\":8},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":38,\"pi_index\":9},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":39,\"pi_index\":10},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":40,\"pi_index\":11},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":41,\"pi_index\":12},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":42,\"pi_index\":13},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":43,\"pi_index\":14},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":44,\"pi_index\":15},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":45,\"pi_index\":16},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":46,\"pi_index\":17},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":47,\"pi_index\":18},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":48,\"pi_index\":19},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":49,\"pi_index\":20},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":50,\"pi_index\":21},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":51,\"pi_index\":22},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":52,\"pi_index\":23}],\"hash_sites\":[],\"ranges\":[]}"

/-! ## §7 — the blinding-space guard (the point of this file, machine-checked).

`|R| = p^BLIND_LANES` for BabyBear `p = 2^31 − 2^27 + 1`. The keyed-ROM hiding bound is `Q/|R|`:
these `#guard`s fail the build if the lane count is ever squeezed back below the hiding floor. -/

/-- The BabyBear prime `2^31 − 2^27 + 1` (the descriptor's field, `circuit/src/faithful8.rs`). -/
def BABYBEAR_P : Nat := 2013265921

-- The campaign floor: at least 4 fresh blinding lanes.
#guard BLIND_LANES ≥ 4
-- THE HIDING GUARD: the blinding space clears 2^128 (in fact p⁵ ≈ 2^154.5 ≥ 2^154).
#guard BABYBEAR_P ^ BLIND_LANES ≥ 2 ^ 128
#guard BABYBEAR_P ^ BLIND_LANES ≥ 2 ^ 154
-- ≥ 2^124 a fortiori (the "~124-bit" campaign convention).
#guard BABYBEAR_P ^ BLIND_LANES ≥ 2 ^ 124
-- Why 4 lanes alone would NOT satisfy the 2^128 floor: p⁴ ≈ 2^123.6 — above 2^123, below 2^124.
#guard BABYBEAR_P ^ 4 ≥ 2 ^ 123
#guard BABYBEAR_P ^ 4 < 2 ^ 124
-- The M0 sin, stated as arithmetic: ONE felt of blinding is < 2^31 — grindable.
#guard BABYBEAR_P ^ 1 < 2 ^ 31

/-! ## §8 — the load-bearing model teeth (non-vacuous; the fold BINDS all lanes). -/

/-- Demo blinding vectors for the discrimination `#guard`s (via M0's `demoAbsorb`). -/
def rA : Blind5 := fun k => if k = 0 then 11 else 0
def rB : Blind5 := fun k => if k = 0 then 12 else 0
/-- `rC` differs from `rA` only at the LAST blinding lane — the discrimination below shows the
NEW lanes are load-bearing in the preimage, not dead padding. -/
def rC : Blind5 := fun k => if k = 4 then 11 else 0

-- The fold discriminates on the SPAN DIGEST.
#guard decide (holeCommitWideOf demoAbsorb dA cT0 rA ≠ holeCommitWideOf demoAbsorb dB cT0 rA)
-- The fold discriminates on the FIRST blinding lane.
#guard decide (holeCommitWideOf demoAbsorb dA cT0 rA ≠ holeCommitWideOf demoAbsorb dA cT0 rB)
-- The fold discriminates on the LAST blinding lane (the widened lanes genuinely enter).
#guard decide (holeCommitWideOf demoAbsorb dA cT0 rA ≠ holeCommitWideOf demoAbsorb dA cT0 rC)
-- The fold discriminates on the CONTEXT `C_T`.
#guard decide (holeCommitWideOf demoAbsorb dA cT0 rA ≠ holeCommitWideOf demoAbsorb dA dB rA)

-- Shape pins.
#guard guardedHidingSpanWideBlindDesc.traceWidth == GHSW_WIDTH
#guard guardedHidingSpanWideBlindDesc.piCount == GHS_PI_COUNT
#guard guardedHidingSpanWideBlindDesc.constraints.length == 27
#guard guardedHidingSpanWideBlindDesc.tables.length == 0
-- span digest: an arity-8 wide absorb, all 8 output lanes bound.
#guard (chipLookupTupleN spanIns (wCols gDIGEST)).length == 1 + CHIP_RATE + 8
#guard (chipLookupTupleN spanIns (wCols gDIGEST)).head? == some (.const 8)
-- commit stage 1: an arity-16 wide absorb, all 8 output lanes bound.
#guard (chipLookupTupleN (wStageIns gDIGEST gCT) (wCols gMID)).length == 1 + CHIP_RATE + 8
#guard (chipLookupTupleN (wStageIns gDIGEST gCT) (wCols gMID)).head? == some (.const 16)
-- commit stage 2 (the WIDE-BLIND tooth): arity 14 = 8 (MID) + 5 (blinding) + 1 (pad 0), all 8 bound.
#guard (chipLookupTupleN commitStage2WideIns (wCols gHOLE)).length == 1 + CHIP_RATE + 8
#guard (chipLookupTupleN commitStage2WideIns (wCols gHOLE)).head? == some (.const 14)
#guard commitStage2WideIns.length == 8 + BLIND_LANES + 1
-- ALL 5 blinding lanes are real trace columns, and NONE is PI-bound (witness, never revealed):
-- no blinding column appears among the pinned column groups.
#guard bCols.length == BLIND_LANES
#guard bCols.all (fun c => c < GHSW_WIDTH)
#guard bCols.all (fun c => !((wCols gCT ++ wCols gHOLE ++ wCols gGUARD).contains c))
-- Every published/absorbed digest value is an 8-LANE group — no lane-0 squeeze anywhere.
#guard (wCols gDIGEST).length == 8
#guard (wCols gHOLE).length == 8
#guard (wCols gCT).length == 8
#guard (wCols gMID).length == 8
#guard (wCols gGUARD).length == 8

#assert_axioms packCommitW_inj
#assert_axioms spanIns_eval
#assert_axioms commitStage2WideIns_eval
#assert_axioms bCols_map

end Dregg2.Circuit.Emit.GuardedHidingSpanWideBlindEmit
