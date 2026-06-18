/-
# Dregg2.Circuit.Emit.EffectVmEmitRotationV3 — THE FULL-COHORT REGEN at the rotated block
(R = 24, CONFIRMED), staged.

`docs/ROTATION-CUTOVER.md` §5 item 1: the staged probes pin the rotated SHAPE; the 26
per-effect descriptors still emit against the 186/14 layout. THIS module re-emits EVERY
cohort member against the rotated 25+…-limb state block — as ONE parametric transformation
(`rotateV3`), so the soundness keystones lift ONCE, for all 26, not per-descriptor:

  * **§1 the appended geometry** — each rotated descriptor carries, PAST its v1 layout
    (every v1 column index, constraint, and theorem untouched): a rotated BEFORE block at
    `d.traceWidth` (32 absorption-ordered limbs · iroot · state_commit · 11 chain carriers
    = 45 columns, the R=24 register geometry PLUS the `commitments_root` map-root limb), a
    rotated AFTER block at `d.traceWidth + 45`, and the WIDENED-CAVEAT region at
    `d.traceWidth + 90` (29-felt manifest · 9 chain carriers · caveat commit = 39 columns).
    Width: `+129`.
  * **§2 col-chained sites** — the chained absorptions reference their carrier COLUMNS
    (`.col`), never `.digest k`, so the site group is POSITION-INDEPENDENT (appendable
    after any descriptor's own sites with no index shift) and graduates to the SAME wire
    bytes as the digest-chained probe (`#guard` byte-identity tripwire below;
    `HashInput.toExpr` resolves `.digest k` to site `k`'s `digestCol`).
  * **§3 the welds** — the rotated blocks are tied to the v1 state blocks where the datum
    EXISTS in the v1 layout (per side): `r0 ↔ BALANCE_LO` and `r1 ↔ NONCE` (the CONFIRMED
    balance/nonce → r0/r1 assignment, ember 2026-06-12), `r2 ↔ BALANCE_HI` (the high
    limb's STAGED home — the single-felt-vs-two-limb encoding refinement is the §5.2
    flag-day line, HORIZONLOG'd), `r3..r10 ↔ fields[0..7]`, `CAP_ROOT ↔ CAP_ROOT`.
    The remaining limbs (cells_root · nullifier/heap roots · lifecycle · epoch ·
    committed_height · iroot · r11..r23) are WITNESS-CARRIED, commitment-bound limbs:
    their per-turn producers are `turn/src/rotation_witness.rs` (cells_root + iroot +
    lifecycle/epoch carriers — ROTATION-CUTOVER §5 items 3-5); nothing here claims they
    are v1-column-derived.
  * **§4 the keystones, ONCE, parametric in `d`** — `go_colOnly_mem` (col-only sites'
    equations survive ANY walk position), `rotV3SitesAt_pin`/`caveatV3SitesAt_pin` (the
    appended chains pin `wireCommitR`/`caveatCommit` of the row's OWN limbs, parametric
    in the block base), `rotateV3_satisfiedVm_v1` (the rotated descriptor still forces
    the FULL v1 denotation — every existing per-effect faithfulness/anti-ghost theorem
    composes unchanged), `graduable_rotateV3` (graduation side conditions lift),
    `rotV3_pins` / `rotV3_publishes` (4 appended PI pins: rotated OLD commit on the
    first row, rotated NEW commit + height + caveat commit on the last), and THE
    END-TO-END `rotV3_binds_published`: two `Satisfied2` witnesses of ANY cohort member's
    rotated form publishing the same rotated commits agree on the WHOLE before block, the
    WHOLE after block, both iroots, the published height, AND the WHOLE caveat manifest —
    under the ONE `Poseidon2SpongeCR` floor, via the parametric `wireCommitR_binds` /
    `caveatCommit_binds`. One theorem, 26 descriptors.
  * **§5 the v3 registry** — `v3Registry`: all 36 cohort members rotated. The 28 `v2Registry`
    members (the 17 graduated cohort + attenuate WITH its phase-B map ops/submask lookup + revoke
    WITH its cap-crown map ops + CUSTOM WITH its recursive-proof-binding op + the dynamic setField
    WITH its mem ops + the 8 per-slot setFields)
    PLUS the 8 LIVE-path effects
    the v2 graduation never covered but the v1 wire DID (STEP 1 / ROTATION-CUTOVER §2c cohort
    widening): grantCap (the bare unattenuated cap-root grant), makeSovereign, createCell,
    factory, spawn, receiptArchive, cellUnseal, emitEvent — each the graduated RUNTIME row
    lifted through the SAME `rotateV3`, so the soundness keystones apply unchanged. Keys
    suffixed `R24`. Driver: `EmitRotationV3.lean` (the Rust staged twin is
    `circuit/descriptors/rotation-v3-staged-registry.tsv`, sha-pinned).
    HONEST RESIDUE: **EMPTY** — every LIVE selector now has a rotated descriptor. `Custom` (8) was
    the last; it GRADUATED via the new accumulator / recursive-proof-binding constraint kind
    (`DescriptorIR2.ProofBind`): the rotated `customV3` carries the `proofBind` op that ties the
    row's `custom_proof_commitment` to a VERIFYING external sub-proof of the named recursion engine
    (the row commits to the verification, rather than trusting it). (`RevokeCapability` (24)
    GRADUATED via the cap-crown `revokeCapabilityVmDescriptor2` — held-membership map-read +
    ZERO-value remove-write — rotated as `revokeCapabilityV3`.)

## Honest boundary notes (do NOT over-read)

  * STAGED beside v1/v2: a new registry constant, NO VK bump, nothing on the live wire.
    The v1 path stays byte-identical; the v2 registry is untouched.
  * The appended blocks are ADDITIVE: the v1 state commitment (GROUP-4) still binds
    everything it bound before (including `BALANCE_HI`, wherever the flip's encoding
    decision lands); the rotated commitment binds the NEW block beside it. The flip
    (§3 steps 1-6 of ROTATION-CUTOVER.md) replaces; this stages.
  * `attenuateV3`/`setFieldDynV3` carry their v2 extras verbatim; their §7/§8 theorems
    re-state through `memOpsOf`/membership transport (`setFieldDynV3_readback_genuine`,
    `attenuateV3_non_amp` below).

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; crypto only as the named
`Poseidon2SpongeCR` hypothesis. No `sorry`, no `native_decide`.
-/
import Dregg2.Circuit.Emit.EffectVmEmitRotationCaveat
-- The LIVE-PATH (non-v2-cohort) effects whose wire descriptors the flag-day must keep
-- reachable once v1 dies (ROTATION-CUTOVER §2c cohort boundary). Each is the GRADUATED
-- RUNTIME row (frozen-frame / passthrough + nonce-tick), lifted through the SAME `rotateV3`.
import Dregg2.Circuit.Emit.EffectVmEmitMakeSovereign
import Dregg2.Circuit.Emit.EffectVmEmitCreateCell
import Dregg2.Circuit.Emit.EffectVmEmitCreateCellFromFactory
import Dregg2.Circuit.Emit.EffectVmEmitSpawn
import Dregg2.Circuit.Emit.EffectVmEmitReceiptArchive
import Dregg2.Circuit.Emit.EffectVmEmitCellUnseal
import Dregg2.Circuit.Emit.EffectVmEmitEmitEvent

namespace Dregg2.Circuit.Emit.EffectVmEmitRotationV3

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitV2
open Dregg2.Circuit.Emit.EffectVmEmitRotationR
open Dregg2.Circuit.Emit.EffectVmEmitRotationCaveat
  (RotCaveatManifest caveatCommit caveatCommit_binds)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Crypto
open Dregg2.Substrate.Heap (refSponge)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §1 — the appended geometry (R = 24, offsets relative to a block base). -/

-- ── THE `commitments_root` FLAG-DAY (NUM_PRE_LIMBS 31→32) ─────────────────────────────────────
-- The deployed rotated block carries a dedicated `commitments_root` limb at in-block offset 27
-- (right after `nullifier_root` at 26; `heap_root` shifts 27→28, `lifecycle` 28→29, `epoch` 29→30,
-- `committed_height` 30→31). The 32-limb pre-iroot list chains as: a 4-wide head + nine 3-wide body
-- groups (limbs 4..30) + ONE arity-2 leftover site (limb 31) + the iroot ALONE last = 12 chained
-- sites (11 chain carriers + the state-commit carrier). This is the R=24 register shape PLUS the
-- one extra committed map-root limb, so the per-block span grows 43→45 (one more chain carrier than
-- the bare R=24 probe). `wireCommitR`/`chunk31` (`EffectVmEmitRotationR`) are length-generic, so the
-- chained-commitment binding lifts unchanged; only the literal site walk + offsets move here.

/-- The per-block span: 32 pre-iroot limbs + iroot + state_commit + 11 chain carriers. -/
def B_SPAN : Nat := 45
/-- iroot offset inside a block. -/
def B_IROOT : Nat := 32
/-- state-commit offset inside a block. -/
def B_STATE_COMMIT : Nat := 33
/-- committed-height offset inside a block (limb 31, after the `commitments_root` shift). -/
def B_COMMITTED_HEIGHT : Nat := 31
/-- cap-root offset inside a block (unshifted — `commitments_root` rides AFTER nullifier_root). -/
def B_CAP_ROOT : Nat := 25
/-- nullifier-root offset inside a block (unshifted, limb 26). -/
def B_NULLIFIER_ROOT_OFF : Nat := 26
/-- commitments-root offset inside a block (limb 27 — the flag-day new committed shielded-set root). -/
def B_COMMITMENTS_ROOT : Nat := 27
/-- The caveat region span: 29 manifest felts + 9 chain carriers + 1 commit. -/
def C_SPAN : Nat := 39
/-- caveat-commit offset inside the caveat region. -/
def C_COMMIT : Nat := 38
/-- The whole appendix width: two rotated blocks + the caveat region. -/
def APPENDIX_SPAN : Nat := 129

-- The map-root offsets ride past the R=24 probe's named columns (cap_root at probe `capRootCol 24`);
-- the `commitments_root` limb is the +1 over the bare R=24 register shape.
#guard B_CAP_ROOT == capRootCol 24
#guard B_COMMITMENTS_ROOT == B_NULLIFIER_ROOT_OFF + 1
#guard B_IROOT == 32                 -- 32 pre-iroot limbs, then iroot
#guard B_STATE_COMMIT == B_IROOT + 1
#guard B_COMMITTED_HEIGHT == 31      -- last pre-iroot limb
#guard B_SPAN == probeWidth 24 + 2   -- +1 limb + +1 leftover chain carrier over the R=24 probe
#guard APPENDIX_SPAN == 2 * B_SPAN + C_SPAN

/-- The pre-iroot limb list of a block at `base` (32 limbs, absorption order: cells_root ·
r0..r23 · cap_root · nullifier_root · **commitments_root** · heap_root · lifecycle · epoch ·
committed height). Literal, so every positional fact is `rfl`. -/
def preLimbsAt (base : Nat) (a : Assignment) : List ℤ :=
  [ a (base + 0), a (base + 1), a (base + 2), a (base + 3), a (base + 4), a (base + 5)
  , a (base + 6), a (base + 7), a (base + 8), a (base + 9), a (base + 10), a (base + 11)
  , a (base + 12), a (base + 13), a (base + 14), a (base + 15), a (base + 16), a (base + 17)
  , a (base + 18), a (base + 19), a (base + 20), a (base + 21), a (base + 22), a (base + 23)
  , a (base + 24), a (base + 25), a (base + 26), a (base + 27), a (base + 28), a (base + 29)
  , a (base + 30), a (base + 31) ]

theorem preLimbsAt_length (base : Nat) (a : Assignment) :
    (preLimbsAt base a).length = 32 := rfl

/-- Read the caveat manifest off a row at region base `base` (positional, 29 felts). -/
def manifestAt (base : Nat) (a : Assignment) : RotCaveatManifest :=
  { count := a (base + 0)
  , e0 := ⟨a (base + 1), a (base + 2), a (base + 3), a (base + 4), a (base + 5),
           a (base + 6), a (base + 7)⟩
  , e1 := ⟨a (base + 8), a (base + 9), a (base + 10), a (base + 11), a (base + 12),
           a (base + 13), a (base + 14)⟩
  , e2 := ⟨a (base + 15), a (base + 16), a (base + 17), a (base + 18), a (base + 19),
           a (base + 20), a (base + 21)⟩
  , e3 := ⟨a (base + 22), a (base + 23), a (base + 24), a (base + 25), a (base + 26),
           a (base + 27), a (base + 28)⟩ }

/-! ## §2 — the col-chained sites (position-independent; graduate to the probe's bytes). -/

/-- The 12 chained absorption sites of a rotated block at `base`: the 4-wide head, nine
3-wide body groups (limbs 4..30), ONE arity-2 leftover site (limb 31 — the `commitments_root`
flag-day's extra limb pushes the body to 28 limbs = 9×3 + 1), then the iroot ALONE last onto the
state-commit carrier. Chaining is by CARRIER COLUMNS (`.col`), which graduates to the SAME wire
bytes as `.digest` chaining while keeping the group position-independent. Chain carriers ride
`base + 34 .. base + 44` (11 carriers); the state-commit carrier is `base + 33`. -/
def rotV3SitesAt (base : Nat) : List VmHashSite :=
  [ ⟨base + 34, [.col (base + 0), .col (base + 1), .col (base + 2), .col (base + 3)], 4⟩
  , ⟨base + 35, [.col (base + 34), .col (base + 4), .col (base + 5), .col (base + 6)], 4⟩
  , ⟨base + 36, [.col (base + 35), .col (base + 7), .col (base + 8), .col (base + 9)], 4⟩
  , ⟨base + 37, [.col (base + 36), .col (base + 10), .col (base + 11), .col (base + 12)], 4⟩
  , ⟨base + 38, [.col (base + 37), .col (base + 13), .col (base + 14), .col (base + 15)], 4⟩
  , ⟨base + 39, [.col (base + 38), .col (base + 16), .col (base + 17), .col (base + 18)], 4⟩
  , ⟨base + 40, [.col (base + 39), .col (base + 19), .col (base + 20), .col (base + 21)], 4⟩
  , ⟨base + 41, [.col (base + 40), .col (base + 22), .col (base + 23), .col (base + 24)], 4⟩
  , ⟨base + 42, [.col (base + 41), .col (base + 25), .col (base + 26), .col (base + 27)], 4⟩
  , ⟨base + 43, [.col (base + 42), .col (base + 28), .col (base + 29), .col (base + 30)], 4⟩
  , ⟨base + 44, [.col (base + 43), .col (base + 31)], 2⟩
  , ⟨base + 33, [.col (base + 44), .col (base + 32)], 2⟩ ]

/-- The 10 chained caveat sites at region base `base` (the `caveatSites` shape, positional):
4-wide head over `[count, e0.tag, e0.dom, e0.key]`, eight (carrier+3) body groups, the
(carrier+1) tail onto the caveat-commit carrier. -/
def caveatV3SitesAt (base : Nat) : List VmHashSite :=
  [ ⟨base + 29, [.col (base + 0), .col (base + 1), .col (base + 2), .col (base + 3)], 4⟩
  , ⟨base + 30, [.col (base + 29), .col (base + 4), .col (base + 5), .col (base + 6)], 4⟩
  , ⟨base + 31, [.col (base + 30), .col (base + 7), .col (base + 8), .col (base + 9)], 4⟩
  , ⟨base + 32, [.col (base + 31), .col (base + 10), .col (base + 11), .col (base + 12)], 4⟩
  , ⟨base + 33, [.col (base + 32), .col (base + 13), .col (base + 14), .col (base + 15)], 4⟩
  , ⟨base + 34, [.col (base + 33), .col (base + 16), .col (base + 17), .col (base + 18)], 4⟩
  , ⟨base + 35, [.col (base + 34), .col (base + 19), .col (base + 20), .col (base + 21)], 4⟩
  , ⟨base + 36, [.col (base + 35), .col (base + 22), .col (base + 23), .col (base + 24)], 4⟩
  , ⟨base + 37, [.col (base + 36), .col (base + 25), .col (base + 26), .col (base + 27)], 4⟩
  , ⟨base + 38, [.col (base + 37), .col (base + 28)], 2⟩ ]

/-- The whole appendix site group for a descriptor of width `w`. The AFTER block rides at
`w + B_SPAN` (= `w + 45`); the caveat region at `w + 2·B_SPAN` (= `w + 90`). -/
def rotV3Appendix (w : Nat) : List VmHashSite :=
  rotV3SitesAt w ++ rotV3SitesAt (w + 45) ++ caveatV3SitesAt (w + 90)

-- Arity discipline: every appendix site is arity 4 or 2 (the chip refuses 3) — checked at
-- a concrete base; the literal arities are base-independent.
#guard (rotV3Appendix 186).all fun s => s.arity == 4 || s.arity == 2
#guard (rotV3Appendix 186).length == 34   -- 12 (before) + 12 (after) + 10 (caveat)

-- **THE BYTE-IDENTITY TRIPWIRE** (32-limb shape): the col-chained 12-site block at base 0
-- graduates to the EXACT wire JSON of its DIGEST-chained twin (the running accumulator referenced
-- as `.digest (k-1)` instead of `.col carrier`). `HashInput.toExpr` resolves `.digest k` to site
-- `k`'s `digestCol`, which IS the chain-carrier column the col-chained form names, so the two emit
-- byte-for-byte. This is the standalone analog of the old R=24-probe cross-check, at the deployed
-- 32-limb geometry (the R-register probe no longer matches the +commitments_root limb shape).
private def rotV3SitesDigestAt0 : List VmHashSite :=
  [ ⟨34, [.col 0, .col 1, .col 2, .col 3], 4⟩
  , ⟨35, [.digest 0, .col 4, .col 5, .col 6], 4⟩
  , ⟨36, [.digest 1, .col 7, .col 8, .col 9], 4⟩
  , ⟨37, [.digest 2, .col 10, .col 11, .col 12], 4⟩
  , ⟨38, [.digest 3, .col 13, .col 14, .col 15], 4⟩
  , ⟨39, [.digest 4, .col 16, .col 17, .col 18], 4⟩
  , ⟨40, [.digest 5, .col 19, .col 20, .col 21], 4⟩
  , ⟨41, [.digest 6, .col 22, .col 23, .col 24], 4⟩
  , ⟨42, [.digest 7, .col 25, .col 26, .col 27], 4⟩
  , ⟨43, [.digest 8, .col 28, .col 29, .col 30], 4⟩
  , ⟨44, [.digest 9, .col 31], 2⟩
  , ⟨33, [.digest 10, .col 32], 2⟩ ]

#guard emitVmJson2 (graduateV1
    { name := "dregg-effectvm-rotation-v3-commitments-tripwire"
    , traceWidth := B_SPAN
    , piCount := 2
    , constraints :=
        [ .piBinding .last B_STATE_COMMIT Dregg2.Circuit.Emit.EffectVmEmitRotation.PUB_COMMIT
        , .piBinding .last B_COMMITTED_HEIGHT
            Dregg2.Circuit.Emit.EffectVmEmitRotation.PUB_HEIGHT ]
    , hashSites := rotV3SitesAt 0
    , ranges := [] })
  == emitVmJson2 (graduateV1
    { name := "dregg-effectvm-rotation-v3-commitments-tripwire"
    , traceWidth := B_SPAN
    , piCount := 2
    , constraints :=
        [ .piBinding .last B_STATE_COMMIT Dregg2.Circuit.Emit.EffectVmEmitRotation.PUB_COMMIT
        , .piBinding .last B_COMMITTED_HEIGHT
            Dregg2.Circuit.Emit.EffectVmEmitRotation.PUB_HEIGHT ]
    , hashSites := rotV3SitesDigestAt0
    , ranges := [] })

/-! ## §3 — the welds and the transformation. -/

/-- The weld gate `loc a = loc b` (an equality as a vanishing polynomial). -/
def colEq (a b : Nat) : VmConstraint :=
  .gate (.add (.var a) (.mul (.const (-1)) (.var b)))

theorem colEq_holds_iff (env : VmRowEnv) (isFirst isLast : Bool) (a b : Nat) :
    (colEq a b).holdsVm env isFirst isLast ↔ env.loc a = env.loc b := by
  simp only [colEq, VmConstraint.holdsVm, EmittedExpr.eval]
  constructor <;> intro h <;> linarith

/-- The per-side welds: rotated block at `base` ↔ v1 state block at `stateBase`
(`STATE_BEFORE_BASE` or `STATE_AFTER_BASE`). r0 ↔ BALANCE_LO · r1 ↔ NONCE (the CONFIRMED
assignment) · r2 ↔ BALANCE_HI (staged home) · r3..r10 ↔ fields[0..7] · CAP_ROOT ↔ CAP_ROOT. -/
def weldsAt (base stateBase : Nat) : List VmConstraint :=
  [ colEq (base + 1) (stateBase + state.BALANCE_LO)
  , colEq (base + 2) (stateBase + state.NONCE)
  , colEq (base + 3) (stateBase + state.BALANCE_HI)
  , colEq (base + 4) (stateBase + state.FIELD_BASE)
  , colEq (base + 5) (stateBase + state.FIELD_BASE + 1)
  , colEq (base + 6) (stateBase + state.FIELD_BASE + 2)
  , colEq (base + 7) (stateBase + state.FIELD_BASE + 3)
  , colEq (base + 8) (stateBase + state.FIELD_BASE + 4)
  , colEq (base + 9) (stateBase + state.FIELD_BASE + 5)
  , colEq (base + 10) (stateBase + state.FIELD_BASE + 6)
  , colEq (base + 11) (stateBase + state.FIELD_BASE + 7)
  , colEq (base + B_CAP_ROOT) (stateBase + state.CAP_ROOT) ]

/-- The four appended PI pins of a rotated descriptor (PI slots `piBase..piBase+3`):
rotated OLD commit (first row) · rotated NEW commit · rotated height · caveat commit (last). -/
def rotPins (w piBase : Nat) : List VmConstraint :=
  [ .piBinding .first (w + B_STATE_COMMIT) piBase
  , .piBinding .last (w + 45 + B_STATE_COMMIT) (piBase + 1)
  , .piBinding .last (w + 45 + B_COMMITTED_HEIGHT) (piBase + 2)
  , .piBinding .last (w + 90 + C_COMMIT) (piBase + 3) ]

/-- **`rotateV3`** — the ONE parametric regen: append the rotated BEFORE/AFTER blocks and
the caveat region past the descriptor's own layout; weld where the v1 block carries the
datum; pin the rotated commits to four appended PI slots. Every v1 column index, constraint,
hash site, and range tooth is UNTOUCHED — the v1 theorems survive verbatim
(`rotateV3_satisfiedVm_v1`). -/
def rotateV3 (d : EffectVmDescriptor) : EffectVmDescriptor :=
  { name        := d.name ++ "-rot24-v3-staged"
  , traceWidth  := d.traceWidth + APPENDIX_SPAN
  , piCount     := d.piCount + 4
  , constraints := d.constraints
      ++ (weldsAt d.traceWidth STATE_BEFORE_BASE
          ++ weldsAt (d.traceWidth + 45) STATE_AFTER_BASE
          ++ rotPins d.traceWidth d.piCount)
  , hashSites   := d.hashSites ++ rotV3Appendix d.traceWidth
  , ranges      := d.ranges }

/-! ## §4 — the keystones, proved ONCE, parametric. -/

/-- A hash-site input that never reads the digest accumulator. -/
def colOnlyInput : HashInput → Bool
  | .col _ => true
  | .zero => true
  | .digest _ => false

/-- A site whose inputs are all accumulator-free. -/
def colOnly (s : VmHashSite) : Bool := s.inputs.all colOnlyInput

/-- A col-only site resolves identically under EVERY accumulator. -/
theorem resolvedInputs_colOnly (env : VmRowEnv) (acc acc' : List ℤ) (s : VmHashSite)
    (h : colOnly s = true) :
    s.resolvedInputs env acc = s.resolvedInputs env acc' := by
  unfold VmHashSite.resolvedInputs
  apply List.map_congr_left
  intro i hi
  have hci := List.all_eq_true.mp h i hi
  cases i with
  | col c => rfl
  | digest k => simp [colOnlyInput] at hci
  | zero => rfl

/-- **The col-only walk lemma**: anywhere in the ordered site walk — after ANY prefix, under
ANY accumulator — a col-only site's equation holds in its accumulator-free form. THIS is what
makes the appendix position-independent: no induction over the host descriptor's own sites is
ever needed. -/
theorem go_colOnly_mem (hash : List ℤ → ℤ) (env : VmRowEnv) :
    ∀ (acc : List ℤ) (sites : List VmHashSite),
      siteHoldsAll.go hash env acc sites →
      ∀ s ∈ sites, colOnly s = true →
        env.loc s.digestCol = hash (s.resolvedInputs env []) := by
  intro acc sites
  induction sites generalizing acc with
  | nil => intro _ s hs _; cases hs
  | cons t ts ih =>
    intro h s hs hcol
    obtain ⟨hd, hgo⟩ := h
    rcases List.mem_cons.mp hs with rfl | hs'
    · rw [hd, resolvedInputs_colOnly env acc [] s hcol]
    · exact ih _ hgo s hs' hcol

/-- The walk restricts to any prefix (the host descriptor's own sites still walk). -/
theorem go_append_left (hash : List ℤ → ℤ) (env : VmRowEnv) :
    ∀ (acc : List ℤ) (P Q : List VmHashSite),
      siteHoldsAll.go hash env acc (P ++ Q) → siteHoldsAll.go hash env acc P := by
  intro acc P
  induction P generalizing acc with
  | nil => intro Q _; trivial
  | cons t ts ih =>
    intro Q h
    obtain ⟨hd, hgo⟩ := h
    exact ⟨hd, ih _ Q hgo⟩

/-- Every rotated-block site is col-only (12 literal cases). -/
theorem rotV3SitesAt_colOnly (base : Nat) : ∀ s ∈ rotV3SitesAt base, colOnly s = true := by
  intro s hs
  simp only [rotV3SitesAt, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Every caveat site is col-only (10 literal cases). -/
theorem caveatV3SitesAt_colOnly (base : Nat) :
    ∀ s ∈ caveatV3SitesAt base, colOnly s = true := by
  intro s hs
  simp only [caveatV3SitesAt, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

set_option maxHeartbeats 6400000 in
/-- **The block pin, parametric in `base`**: the twelve col-chained site equations compose
into the chained rotated commitment — the row's state-commit carrier at `base + 33` IS
`wireCommitR` of the row's OWN 32 limbs and iroot (the `commitments_root` flag-day shape). -/
theorem rotV3SitesAt_pin (hash : List ℤ → ℤ) (env : VmRowEnv) (base : Nat)
    (h : ∀ s ∈ rotV3SitesAt base, env.loc s.digestCol = hash (s.resolvedInputs env [])) :
    env.loc (base + 33)
      = wireCommitR hash (preLimbsAt base env.loc) (env.loc (base + 32)) := by
  have h0 : env.loc (base + 34) = hash [env.loc (base + 0), env.loc (base + 1),
      env.loc (base + 2), env.loc (base + 3)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 34, [.col (base + 0), .col (base + 1), .col (base + 2), .col (base + 3)], 4⟩
        (by simp [rotV3SitesAt])
  have h1 : env.loc (base + 35) = hash [env.loc (base + 34), env.loc (base + 4),
      env.loc (base + 5), env.loc (base + 6)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 35, [.col (base + 34), .col (base + 4), .col (base + 5), .col (base + 6)], 4⟩
        (by simp [rotV3SitesAt])
  have h2 : env.loc (base + 36) = hash [env.loc (base + 35), env.loc (base + 7),
      env.loc (base + 8), env.loc (base + 9)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 36, [.col (base + 35), .col (base + 7), .col (base + 8), .col (base + 9)], 4⟩
        (by simp [rotV3SitesAt])
  have h3 : env.loc (base + 37) = hash [env.loc (base + 36), env.loc (base + 10),
      env.loc (base + 11), env.loc (base + 12)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 37, [.col (base + 36), .col (base + 10), .col (base + 11),
        .col (base + 12)], 4⟩ (by simp [rotV3SitesAt])
  have h4 : env.loc (base + 38) = hash [env.loc (base + 37), env.loc (base + 13),
      env.loc (base + 14), env.loc (base + 15)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 38, [.col (base + 37), .col (base + 13), .col (base + 14),
        .col (base + 15)], 4⟩ (by simp [rotV3SitesAt])
  have h5 : env.loc (base + 39) = hash [env.loc (base + 38), env.loc (base + 16),
      env.loc (base + 17), env.loc (base + 18)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 39, [.col (base + 38), .col (base + 16), .col (base + 17),
        .col (base + 18)], 4⟩ (by simp [rotV3SitesAt])
  have h6 : env.loc (base + 40) = hash [env.loc (base + 39), env.loc (base + 19),
      env.loc (base + 20), env.loc (base + 21)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 40, [.col (base + 39), .col (base + 19), .col (base + 20),
        .col (base + 21)], 4⟩ (by simp [rotV3SitesAt])
  have h7 : env.loc (base + 41) = hash [env.loc (base + 40), env.loc (base + 22),
      env.loc (base + 23), env.loc (base + 24)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 41, [.col (base + 40), .col (base + 22), .col (base + 23),
        .col (base + 24)], 4⟩ (by simp [rotV3SitesAt])
  have h8 : env.loc (base + 42) = hash [env.loc (base + 41), env.loc (base + 25),
      env.loc (base + 26), env.loc (base + 27)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 42, [.col (base + 41), .col (base + 25), .col (base + 26),
        .col (base + 27)], 4⟩ (by simp [rotV3SitesAt])
  have h9 : env.loc (base + 43) = hash [env.loc (base + 42), env.loc (base + 28),
      env.loc (base + 29), env.loc (base + 30)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 43, [.col (base + 42), .col (base + 28), .col (base + 29),
        .col (base + 30)], 4⟩ (by simp [rotV3SitesAt])
  have h10 : env.loc (base + 44) = hash [env.loc (base + 43), env.loc (base + 31)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 44, [.col (base + 43), .col (base + 31)], 2⟩ (by simp [rotV3SitesAt])
  have h11 : env.loc (base + 33) = hash [env.loc (base + 44), env.loc (base + 32)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 33, [.col (base + 44), .col (base + 32)], 2⟩ (by simp [rotV3SitesAt])
  rw [h11, h10, h9, h8, h7, h6, h5, h4, h3, h2, h1, h0]
  rfl

set_option maxHeartbeats 6400000 in
/-- **The caveat pin, parametric in `base`**: the ten col-chained caveat site equations
compose into the chained caveat commitment of the row's OWN manifest block. -/
theorem caveatV3SitesAt_pin (hash : List ℤ → ℤ) (env : VmRowEnv) (base : Nat)
    (h : ∀ s ∈ caveatV3SitesAt base, env.loc s.digestCol = hash (s.resolvedInputs env [])) :
    env.loc (base + 38) = caveatCommit hash (manifestAt base env.loc) := by
  have h0 : env.loc (base + 29) = hash [env.loc (base + 0), env.loc (base + 1),
      env.loc (base + 2), env.loc (base + 3)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 29, [.col (base + 0), .col (base + 1), .col (base + 2), .col (base + 3)], 4⟩
        (by simp [caveatV3SitesAt])
  have h1 : env.loc (base + 30) = hash [env.loc (base + 29), env.loc (base + 4),
      env.loc (base + 5), env.loc (base + 6)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 30, [.col (base + 29), .col (base + 4), .col (base + 5), .col (base + 6)], 4⟩
        (by simp [caveatV3SitesAt])
  have h2 : env.loc (base + 31) = hash [env.loc (base + 30), env.loc (base + 7),
      env.loc (base + 8), env.loc (base + 9)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 31, [.col (base + 30), .col (base + 7), .col (base + 8), .col (base + 9)], 4⟩
        (by simp [caveatV3SitesAt])
  have h3 : env.loc (base + 32) = hash [env.loc (base + 31), env.loc (base + 10),
      env.loc (base + 11), env.loc (base + 12)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 32, [.col (base + 31), .col (base + 10), .col (base + 11),
        .col (base + 12)], 4⟩ (by simp [caveatV3SitesAt])
  have h4 : env.loc (base + 33) = hash [env.loc (base + 32), env.loc (base + 13),
      env.loc (base + 14), env.loc (base + 15)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 33, [.col (base + 32), .col (base + 13), .col (base + 14),
        .col (base + 15)], 4⟩ (by simp [caveatV3SitesAt])
  have h5 : env.loc (base + 34) = hash [env.loc (base + 33), env.loc (base + 16),
      env.loc (base + 17), env.loc (base + 18)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 34, [.col (base + 33), .col (base + 16), .col (base + 17),
        .col (base + 18)], 4⟩ (by simp [caveatV3SitesAt])
  have h6 : env.loc (base + 35) = hash [env.loc (base + 34), env.loc (base + 19),
      env.loc (base + 20), env.loc (base + 21)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 35, [.col (base + 34), .col (base + 19), .col (base + 20),
        .col (base + 21)], 4⟩ (by simp [caveatV3SitesAt])
  have h7 : env.loc (base + 36) = hash [env.loc (base + 35), env.loc (base + 22),
      env.loc (base + 23), env.loc (base + 24)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 36, [.col (base + 35), .col (base + 22), .col (base + 23),
        .col (base + 24)], 4⟩ (by simp [caveatV3SitesAt])
  have h8 : env.loc (base + 37) = hash [env.loc (base + 36), env.loc (base + 25),
      env.loc (base + 26), env.loc (base + 27)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 37, [.col (base + 36), .col (base + 25), .col (base + 26),
        .col (base + 27)], 4⟩ (by simp [caveatV3SitesAt])
  have h9 : env.loc (base + 38) = hash [env.loc (base + 37), env.loc (base + 28)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 38, [.col (base + 37), .col (base + 28)], 2⟩ (by simp [caveatV3SitesAt])
  rw [h9, h8, h7, h6, h5, h4, h3, h2, h1, h0]
  rfl

#assert_axioms go_colOnly_mem
#assert_axioms rotV3SitesAt_pin
#assert_axioms caveatV3SitesAt_pin

/-- **The v1 survival keystone**: a row satisfying the rotated descriptor satisfies the
ORIGINAL descriptor — every existing per-effect faithfulness / anti-ghost / full-state
theorem composes through this unchanged. -/
theorem rotateV3_satisfiedVm_v1 (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (env : VmRowEnv) (isFirst isLast : Bool)
    (h : satisfiedVm hash (rotateV3 d) env isFirst isLast) :
    satisfiedVm hash d env isFirst isLast := by
  obtain ⟨hc, hsites, hr⟩ := h
  exact ⟨fun c hc' => hc c (List.mem_append_left _ hc'),
    go_append_left hash env [] d.hashSites (rotV3Appendix d.traceWidth) hsites, hr⟩

/-- The appendix pins, extracted from a satisfying row: the BEFORE commit carrier, the
AFTER commit carrier, and the caveat commit carrier each carry the genuine chained
commitment of the row's OWN limbs. -/
theorem rotateV3_pins_commits (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (env : VmRowEnv) (isFirst isLast : Bool)
    (h : satisfiedVm hash (rotateV3 d) env isFirst isLast) :
    env.loc (d.traceWidth + 33)
      = wireCommitR hash (preLimbsAt d.traceWidth env.loc) (env.loc (d.traceWidth + 32))
    ∧ env.loc (d.traceWidth + 45 + 33)
      = wireCommitR hash (preLimbsAt (d.traceWidth + 45) env.loc)
          (env.loc (d.traceWidth + 45 + 32))
    ∧ env.loc (d.traceWidth + 90 + 38)
      = caveatCommit hash (manifestAt (d.traceWidth + 90) env.loc) := by
  have hsites := h.2.1
  have heq := go_colOnly_mem hash env [] _ hsites
  have hmem : ∀ s ∈ rotV3Appendix d.traceWidth, s ∈ (rotateV3 d).hashSites :=
    fun s hs => List.mem_append_right _ hs
  refine ⟨?_, ?_, ?_⟩
  · exact rotV3SitesAt_pin hash env d.traceWidth fun s hs =>
      heq s (hmem s (List.mem_append_left _ (List.mem_append_left _ hs)))
        (rotV3SitesAt_colOnly _ s hs)
  · exact rotV3SitesAt_pin hash env (d.traceWidth + 45) fun s hs =>
      heq s (hmem s (List.mem_append_left _ (List.mem_append_right _ hs)))
        (rotV3SitesAt_colOnly _ s hs)
  · exact caveatV3SitesAt_pin hash env (d.traceWidth + 90) fun s hs =>
      heq s (hmem s (List.mem_append_right _ hs)) (caveatV3SitesAt_colOnly _ s hs)

/-- A weld of the rotated descriptor holds on every satisfying row. -/
theorem rotateV3_weld (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (env : VmRowEnv) (isFirst isLast : Bool)
    (h : satisfiedVm hash (rotateV3 d) env isFirst isLast)
    {a b : Nat}
    (hw : colEq a b ∈ weldsAt d.traceWidth STATE_BEFORE_BASE
        ∨ colEq a b ∈ weldsAt (d.traceWidth + 45) STATE_AFTER_BASE) :
    env.loc a = env.loc b := by
  have hc := h.1 (colEq a b) (List.mem_append_right _ (by
    rcases hw with hw | hw
    · exact List.mem_append_left _ (List.mem_append_left _ hw)
    · exact List.mem_append_left _ (List.mem_append_right _ hw)))
  exact (colEq_holds_iff env isFirst isLast a b).mp hc

/-- The CONFIRMED scalar welds, named: on every satisfying row, the rotated blocks' `r0`
carries the v1 balance (low limb) and `r1` the v1 nonce, before AND after; the rotated
`CAP_ROOT` limb carries the v1 cap root. -/
theorem rotateV3_welds_named (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (env : VmRowEnv) (isFirst isLast : Bool)
    (h : satisfiedVm hash (rotateV3 d) env isFirst isLast) :
    env.loc (d.traceWidth + 1) = env.loc (sbCol state.BALANCE_LO)
    ∧ env.loc (d.traceWidth + 2) = env.loc (sbCol state.NONCE)
    ∧ env.loc (d.traceWidth + B_CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
    ∧ env.loc (d.traceWidth + 45 + 1) = env.loc (saCol state.BALANCE_LO)
    ∧ env.loc (d.traceWidth + 45 + 2) = env.loc (saCol state.NONCE)
    ∧ env.loc (d.traceWidth + 45 + B_CAP_ROOT) = env.loc (saCol state.CAP_ROOT) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact rotateV3_weld hash d env isFirst isLast h (Or.inl (by simp [weldsAt, sbCol]))
  · exact rotateV3_weld hash d env isFirst isLast h (Or.inl (by simp [weldsAt, sbCol]))
  · exact rotateV3_weld hash d env isFirst isLast h (Or.inl (by simp [weldsAt, sbCol]))
  · exact rotateV3_weld hash d env isFirst isLast h (Or.inr (by simp [weldsAt, saCol]))
  · exact rotateV3_weld hash d env isFirst isLast h (Or.inr (by simp [weldsAt, saCol]))
  · exact rotateV3_weld hash d env isFirst isLast h (Or.inr (by simp [weldsAt, saCol]))

/-! ### Graduation side conditions lift parametrically. -/

theorem colOnly_siteInputWF (idx : Nat) (s : VmHashSite) (h : colOnly s = true) :
    s.inputs.all (siteInputWF idx) = true := by
  unfold colOnly at h
  rw [List.all_eq_true] at h ⊢
  intro i hi
  have hci := h i hi
  cases i with
  | col c => rfl
  | digest k => simp [colOnlyInput] at hci
  | zero => rfl

theorem sitesWFAux_colOnly :
    ∀ (idx : Nat) (Q : List VmHashSite), (∀ s ∈ Q, colOnly s = true) →
      sitesWFAux idx Q = true := by
  intro idx Q
  induction Q generalizing idx with
  | nil => intro _; rfl
  | cons t ts ih =>
    intro hQ
    show (t.inputs.all (siteInputWF idx) && sitesWFAux (idx + 1) ts) = true
    rw [colOnly_siteInputWF idx t (hQ t List.mem_cons_self),
      ih (idx + 1) (fun s hs => hQ s (List.mem_cons_of_mem t hs))]
    rfl

theorem sitesWFAux_append_colOnly :
    ∀ (idx : Nat) (P Q : List VmHashSite), (∀ s ∈ Q, colOnly s = true) →
      sitesWFAux idx (P ++ Q) = sitesWFAux idx P := by
  intro idx P
  induction P generalizing idx with
  | nil =>
    intro Q hQ
    rw [List.nil_append, sitesWFAux_colOnly idx Q hQ]
    rfl
  | cons t ts ih =>
    intro Q hQ
    show (t.inputs.all (siteInputWF idx) && sitesWFAux (idx + 1) (ts ++ Q))
      = (t.inputs.all (siteInputWF idx) && sitesWFAux (idx + 1) ts)
    rw [ih (idx + 1) Q hQ]

theorem rotV3Appendix_colOnly (w : Nat) : ∀ s ∈ rotV3Appendix w, colOnly s = true := by
  intro s hs
  unfold rotV3Appendix at hs
  rcases List.mem_append.mp hs with hs' | hs'
  · rcases List.mem_append.mp hs' with hs'' | hs''
    · exact rotV3SitesAt_colOnly _ s hs''
    · exact rotV3SitesAt_colOnly _ s hs''
  · exact caveatV3SitesAt_colOnly _ s hs'

/-- The graduation side conditions LIFT: a graduable cohort member's rotated form is
graduable — so `graduateV1_sound`/`_complete`/`_faithful` apply to all 26 with no new
per-descriptor checks. -/
theorem graduable_rotateV3 {d : EffectVmDescriptor} (h : graduable d = true) :
    graduable (rotateV3 d) = true := by
  unfold graduable at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨⟨?_, ?_⟩, h3⟩
  · show sitesWFAux 0 (d.hashSites ++ rotV3Appendix d.traceWidth) = true
    rw [sitesWFAux_append_colOnly 0 d.hashSites _ (rotV3Appendix_colOnly d.traceWidth)]
    exact h1
  · show sitesFit (d.hashSites ++ rotV3Appendix d.traceWidth) = true
    unfold sitesFit at h2 ⊢
    rw [List.all_append, h2, Bool.true_and, List.all_eq_true]
    intro s hs
    unfold rotV3Appendix at hs
    rcases List.mem_append.mp hs with hs' | hs'
    · rcases List.mem_append.mp hs' with hs'' | hs'' <;>
      · simp only [rotV3SitesAt, List.mem_cons, List.not_mem_nil, or_false] at hs''
        rcases hs'' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · simp only [caveatV3SitesAt, List.mem_cons, List.not_mem_nil, or_false] at hs'
      rcases hs' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

#assert_axioms rotateV3_satisfiedVm_v1
#assert_axioms rotateV3_pins_commits
#assert_axioms rotateV3_welds_named
#assert_axioms graduable_rotateV3

/-! ### The Satisfied2-level keystones (one composition each, parametric in `d`). -/

/-- The graduated rotated descriptor of a cohort member. -/
def v3Of (d : EffectVmDescriptor) : EffectVmDescriptor2 := graduateV1 (rotateV3 d)

/-- A `Satisfied2` witness of the rotated graduation yields the FULL v1 denotation of the
ORIGINAL descriptor on every row — the per-effect soundness chains lift to v3 by THIS one
composition. -/
theorem rotV3_sound_v1 (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hchip : ChipTableSound hash (t.tf .poseidon2))
    (hrange : t.tf .range = rangeRows BAL_LIMB_BITS)
    (hgrad : graduable d = true)
    (hsat : Satisfied2 hash (v3Of d) minit mfin maddrs t) :
    ∀ i, i < t.rows.length →
      satisfiedVm hash d (envAt t i) (i == 0) (i + 1 == t.rows.length) := by
  intro i hi
  exact rotateV3_satisfiedVm_v1 hash d _ _ _
    (graduateV1_sound hash (rotateV3 d) minit mfin maddrs t hchip hrange
      (graduable_rotateV3 hgrad) hsat i hi)

/-- Every row of a `Satisfied2` witness pins all three rotated commitments. -/
theorem rotV3_pins (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hchip : ChipTableSound hash (t.tf .poseidon2))
    (hrange : t.tf .range = rangeRows BAL_LIMB_BITS)
    (hgrad : graduable d = true)
    (hsat : Satisfied2 hash (v3Of d) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    (envAt t i).loc (d.traceWidth + 33)
      = wireCommitR hash (preLimbsAt d.traceWidth (envAt t i).loc)
          ((envAt t i).loc (d.traceWidth + 32))
    ∧ (envAt t i).loc (d.traceWidth + 45 + 33)
      = wireCommitR hash (preLimbsAt (d.traceWidth + 45) (envAt t i).loc)
          ((envAt t i).loc (d.traceWidth + 45 + 32))
    ∧ (envAt t i).loc (d.traceWidth + 90 + 38)
      = caveatCommit hash (manifestAt (d.traceWidth + 90) (envAt t i).loc) :=
  rotateV3_pins_commits hash d _ _ _
    (graduateV1_sound hash (rotateV3 d) minit mfin maddrs t hchip hrange
      (graduable_rotateV3 hgrad) hsat i hi)

/-- The rotated descriptor PUBLISHES: first row → rotated OLD commit on PI `d.piCount`;
last row → rotated NEW commit, rotated height, caveat commit on `d.piCount + 1..3`. -/
theorem rotV3_publishes (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hchip : ChipTableSound hash (t.tf .poseidon2))
    (hrange : t.tf .range = rangeRows BAL_LIMB_BITS)
    (hgrad : graduable d = true)
    (hsat : Satisfied2 hash (v3Of d) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    ((i == 0) = true →
      (envAt t i).loc (d.traceWidth + B_STATE_COMMIT) = (envAt t i).pub d.piCount)
    ∧ ((i + 1 == t.rows.length) = true →
      (envAt t i).loc (d.traceWidth + 45 + B_STATE_COMMIT) = (envAt t i).pub (d.piCount + 1)
      ∧ (envAt t i).loc (d.traceWidth + 45 + B_COMMITTED_HEIGHT)
          = (envAt t i).pub (d.piCount + 2)
      ∧ (envAt t i).loc (d.traceWidth + 90 + C_COMMIT) = (envAt t i).pub (d.piCount + 3)) := by
  have h := graduateV1_sound hash (rotateV3 d) minit mfin maddrs t hchip hrange
    (graduable_rotateV3 hgrad) hsat i hi
  have hmem : ∀ c ∈ rotPins d.traceWidth d.piCount, c ∈ (rotateV3 d).constraints :=
    fun c hc => List.mem_append_right _ (List.mem_append_right _ hc)
  have h0 := h.1 _ (hmem (.piBinding .first (d.traceWidth + B_STATE_COMMIT) d.piCount)
    (by simp [rotPins]))
  have h1 := h.1 _ (hmem (.piBinding .last (d.traceWidth + 45 + B_STATE_COMMIT)
    (d.piCount + 1)) (by simp [rotPins]))
  have h2 := h.1 _ (hmem (.piBinding .last (d.traceWidth + 45 + B_COMMITTED_HEIGHT)
    (d.piCount + 2)) (by simp [rotPins]))
  have h3 := h.1 _ (hmem (.piBinding .last (d.traceWidth + 90 + C_COMMIT) (d.piCount + 3))
    (by simp [rotPins]))
  simp only [VmConstraint.holdsVm] at h0 h1 h2 h3
  exact ⟨h0, fun hl => ⟨h1 hl, h2 hl, h3 hl⟩⟩

set_option maxHeartbeats 1600000 in
/-- **THE END-TO-END KEYSTONE — once, for all 26.** Two `Satisfied2` witnesses of ANY cohort
member's rotated graduation publishing the SAME rotated OLD commit, the SAME rotated NEW
commit, and the SAME caveat commit agree on the WHOLE rotated before block, the WHOLE after
block (all 24 registers — balance/nonce included by the welds — every map root, lifecycle,
epoch, height), BOTH iroots, the published height, AND the WHOLE caveat manifest (every
entry's type tag, DOMAIN TAG, KEY, params) — under the ONE CR floor, via the PARAMETRIC
`wireCommitR_binds` / `caveatCommit_binds`. -/
theorem rotV3_binds_published (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (d : EffectVmDescriptor)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (minit' : ℤ → ℤ) (mfin' : ℤ → ℤ × Nat) (maddrs' : List ℤ) (t' : VmTrace)
    (hchip : ChipTableSound hash (t.tf .poseidon2))
    (hrange : t.tf .range = rangeRows BAL_LIMB_BITS)
    (hchip' : ChipTableSound hash (t'.tf .poseidon2))
    (hrange' : t'.tf .range = rangeRows BAL_LIMB_BITS)
    (hgrad : graduable d = true)
    (hsat : Satisfied2 hash (v3Of d) minit mfin maddrs t)
    (hsat' : Satisfied2 hash (v3Of d) minit' mfin' maddrs' t')
    (i j : Nat) (hi : i < t.rows.length) (hj : j < t'.rows.length)
    (hfirst : (i == 0) = true) (hfirst' : (j == 0) = true)
    (k l : Nat) (hk : k < t.rows.length) (hl : l < t'.rows.length)
    (hlast : (k + 1 == t.rows.length) = true) (hlast' : (l + 1 == t'.rows.length) = true)
    (hpubOld : (envAt t i).pub d.piCount = (envAt t' j).pub d.piCount)
    (hpubNew : (envAt t k).pub (d.piCount + 1) = (envAt t' l).pub (d.piCount + 1))
    (hpubCav : (envAt t k).pub (d.piCount + 3) = (envAt t' l).pub (d.piCount + 3)) :
    (preLimbsAt d.traceWidth (envAt t i).loc = preLimbsAt d.traceWidth (envAt t' j).loc
      ∧ (envAt t i).loc (d.traceWidth + 32) = (envAt t' j).loc (d.traceWidth + 32))
    ∧ (preLimbsAt (d.traceWidth + 45) (envAt t k).loc
        = preLimbsAt (d.traceWidth + 45) (envAt t' l).loc
      ∧ (envAt t k).loc (d.traceWidth + 45 + 32) = (envAt t' l).loc (d.traceWidth + 45 + 32)
      ∧ (envAt t k).pub (d.piCount + 2) = (envAt t' l).pub (d.piCount + 2))
    ∧ manifestAt (d.traceWidth + 90) (envAt t k).loc
        = manifestAt (d.traceWidth + 90) (envAt t' l).loc := by
  have hp := rotV3_pins hash d minit mfin maddrs t hchip hrange hgrad hsat
  have hp' := rotV3_pins hash d minit' mfin' maddrs' t' hchip' hrange' hgrad hsat'
  have hq := rotV3_publishes hash d minit mfin maddrs t hchip hrange hgrad hsat
  have hq' := rotV3_publishes hash d minit' mfin' maddrs' t' hchip' hrange' hgrad hsat'
  refine ⟨?_, ?_, ?_⟩
  · -- the before block, via the first-row pins
    have hc := (hq i hi).1 hfirst
    have hc' := (hq' j hj).1 hfirst'
    have hwire : wireCommitR hash (preLimbsAt d.traceWidth (envAt t i).loc)
        ((envAt t i).loc (d.traceWidth + 32))
        = wireCommitR hash (preLimbsAt d.traceWidth (envAt t' j).loc)
            ((envAt t' j).loc (d.traceWidth + 32)) := by
      rw [← (hp i hi).1, ← (hp' j hj).1]
      show (envAt t i).loc (d.traceWidth + B_STATE_COMMIT)
        = (envAt t' j).loc (d.traceWidth + B_STATE_COMMIT)
      rw [hc, hc', hpubOld]
    exact wireCommitR_binds hash hCR
      (by rw [preLimbsAt_length, preLimbsAt_length]) hwire
  · -- the after block, via the last-row pins
    obtain ⟨hc, hh, -⟩ := (hq k hk).2 hlast
    obtain ⟨hc', hh', -⟩ := (hq' l hl).2 hlast'
    have hwire : wireCommitR hash (preLimbsAt (d.traceWidth + 45) (envAt t k).loc)
        ((envAt t k).loc (d.traceWidth + 45 + 32))
        = wireCommitR hash (preLimbsAt (d.traceWidth + 45) (envAt t' l).loc)
            ((envAt t' l).loc (d.traceWidth + 45 + 32)) := by
      rw [← (hp k hk).2.1, ← (hp' l hl).2.1]
      show (envAt t k).loc (d.traceWidth + 45 + B_STATE_COMMIT)
        = (envAt t' l).loc (d.traceWidth + 45 + B_STATE_COMMIT)
      rw [hc, hc', hpubNew]
    obtain ⟨hpre, hir⟩ := wireCommitR_binds hash hCR
      (by rw [preLimbsAt_length, preLimbsAt_length]) hwire
    refine ⟨hpre, hir, ?_⟩
    rw [← hh, ← hh']
    exact congrArg (fun L => L.getD 31 0) hpre
  · -- the caveat manifest, via the last-row pin
    obtain ⟨-, -, hk1⟩ := (hq k hk).2 hlast
    obtain ⟨-, -, hk2⟩ := (hq' l hl).2 hlast'
    have hcc : caveatCommit hash (manifestAt (d.traceWidth + 90) (envAt t k).loc)
        = caveatCommit hash (manifestAt (d.traceWidth + 90) (envAt t' l).loc) := by
      rw [← (hp k hk).2.2, ← (hp' l hl).2.2]
      show (envAt t k).loc (d.traceWidth + 90 + C_COMMIT)
        = (envAt t' l).loc (d.traceWidth + 90 + C_COMMIT)
      rw [hk1, hk2, hpubCav]
    exact caveatCommit_binds hash hCR hcc

#assert_axioms rotV3_sound_v1
#assert_axioms rotV3_pins
#assert_axioms rotV3_publishes
#assert_axioms rotV3_binds_published

/-! ## §5 — the v3 registry: all 27 v2-cohort members (+ the 8 widened), rotated. -/

/-- Append v2-native extras (map ops / mem ops / lookups) to a rotated graduation —
the attenuate phase-B leg and the dynamic setField ride through unchanged. -/
def v3OfWith (d : EffectVmDescriptor) (extras : List VmConstraint2) : EffectVmDescriptor2 :=
  { v3Of d with constraints := (v3Of d).constraints ++ extras }

/-- The v1 face of the dynamic setField (its two mem ops are the v2 extras). -/
def setFieldDynV1Face : EffectVmDescriptor :=
  { name        := "dregg-effectvm-setfield-dyn-v2"
  , traceWidth  := EFFECT_VM_WIDTH
  , piCount     := 34
  , constraints := [ .gate gSlotRange, selectorGate EffectVmEmitSetField.SEL_SET_FIELD ]
  , hashSites   := []
  , ranges      := [] }

/-- The rotated attenuate WITH the cap-crown phase-B circuit leg (held-membership map read,
attenuated map write, submask lookup — verbatim from `attenuateVmDescriptor2`). -/
def attenuateV3 : EffectVmDescriptor2 :=
  v3OfWith EffectVmEmitAttenuateA.attenuateVmDescriptor
    [.mapOp heldReadOp, .mapOp keepWriteOp, .lookup submaskLookup]

/-- The rotated REVOKE (sel 24) WITH the cap-crown circuit leg: held-membership map read +
ZERO-value remove-write (NO submask — revoke deletes a slot, it does not narrow rights), verbatim
from `revokeCapabilityVmDescriptor2`. -/
def revokeCapabilityV3 : EffectVmDescriptor2 :=
  v3OfWith EffectVmEmitRevokeCapability.revokeCapabilityVmDescriptor
    [.mapOp heldReadOp, .mapOp removeWriteOp]

/-- The rotated dynamic setField WITH its memory ops (the Blum write→read transport). -/
def setFieldDynV3 : EffectVmDescriptor2 :=
  v3OfWith setFieldDynV1Face [.memOp fieldWriteOp, .memOp fieldReadbackOp]

/-- The rotated CUSTOM (sel 8) WITH the recursive-proof-binding leg: the runtime passthrough face
lifted through `rotateV3`, carrying the `proofBind` op (`customProofBind`) that ties the row's
`custom_proof_commitment` to a verifying external sub-proof — the accumulator constraint the
per-row IR gained. This is THE last rotation-cohort member: with it the HONEST RESIDUE is EMPTY. -/
def customV3 : EffectVmDescriptor2 :=
  v3OfWith customV1Face [.proofBind customProofBind]

/-! ### The note-spend nullifier PI weld (the C4 last-flip-gate close).

The v1 hand-AIR (`circuit/src/effect_vm/air.rs`, D5) carries a per-row GATED cross-binding
`s_notespend · (param0 − PI[NOTESPEND_NULLIFIER])` (offset 198): the spend row's folded
nullifier (`param::NULLIFIER = param0`, column `prmCol 0`) MUST equal the published
`PI[198]` — the weld that forbids the EffectVM from spending a different nullifier than the
one the SCHEMA_NOTE_SPEND binding proof certified (the off-AIR verifier reconstructs PI[198]
from the binding proof's `fields[0]` and `verify_full_turn` step 8 cross-checks the
non-revocation proof's queried item == PI[198]).

That cross-binding tooth lives ONLY in the v1 hand-AIR — `noteSpendVmDescriptor` (the Lean
per-effect descriptor) does NOT bind the nullifier to any PI (its `piCount = 34` is the v1
prefix only). So when the rotated leg retires the hand-AIR, the rotated 38-PI omits the
nullifier and a note-spending turn with a freshness binding CANNOT rotate (it falls back to
v1 — the documented C4 boundary, `verify_full_turn` step 8 REFUSES the rotated leg).

`noteSpendV3` CLOSES that gate: it appends a FIFTH PI pin past the four rotated commit pins
(`rotateV3` produces `piCount = 34 + 4 = 38`), binding the spend row's `param0` (the folded
nullifier) to the new rotated PI slot 38 on the FIRST row. The note-spend turn lays the spend
on row 0 (`generate_effect_vm_trace`'s `Effect::NoteSpend` arm + the trace generator's
`row[PARAM_BASE + param::NULLIFIER]` write are on row 0; `boundaryFirstPins` pins the first
row), so the first-row pin is the rotated analog of the v1 per-row gate. The SOUNDNESS TOOTH
(`noteSpendV3_rejects_nullifier_tamper`): a row whose `param0` differs from the published
PI[38] FAILS the pin and is UNSAT — exactly the v1 `rejects_swap` adversarial test, now at the
rotated boundary. The Rust `verify_full_turn` step 8 reads PI[38] of the rotated leg instead
of refusing, so the no-double-spend cross-check (`queried_item == nullifier`) fires on the
rotated note-spend turn. -/

/-- The rotated nullifier-PI slot: the FIRST slot past the four rotated commit pins
(`rotateV3` appends OLD/NEW commit · height · caveat commit at `piCount..piCount+3`). For the
note-spend cohort member this is `34 + 4 = 38`. -/
def ROT_NULLIFIER_PI : Nat := 38

/-- The folded-nullifier parameter column (`param::NULLIFIER = param0`, `prmCol 0`) — the
spend row's single folded `fold_bytes32_to_bb(nullifier)` felt the v1 hand-AIR cross-binds. -/
def NULLIFIER_PARAM_COL : Nat := prmCol 0

/-- **`rotateV3WithNullifierPin`** — `rotateV3` PLUS the fifth appended PI pin welding the
spend row's folded nullifier (`prmCol 0`) to the rotated PI slot `ROT_NULLIFIER_PI = 38` on
the FIRST row. Every v1 column, constraint, hash site, and the four rotated commit pins are
UNTOUCHED (so `rotateV3`'s keystones — `rotateV3_satisfiedVm_v1`, `rotV3_binds_published`,
`graduable_rotateV3` — all compose verbatim; this only ADDS one PI pin + one PI slot). -/
def rotateV3WithNullifierPin (d : EffectVmDescriptor) : EffectVmDescriptor :=
  let r := rotateV3 d
  { r with
    piCount     := r.piCount + 1
    constraints := r.constraints ++ [.piBinding .first NULLIFIER_PARAM_COL ROT_NULLIFIER_PI] }

/-- The rotated BEFORE-block `nullifier_root` limb column (limb 26 of the before block at
`base = traceWidth`). The deployed nullifier accumulator's PRE root — the openable
sorted-Poseidon2 root the grow-gate opens against. -/
def beforeNullifierRootCol (w : Nat) : Nat := w + 26

/-- The rotated AFTER-block `nullifier_root` limb column (limb 26 of the after block at
`base = traceWidth + 45`). The deployed nullifier accumulator's POST root — the grow-gate's
`newRoot`. -/
def afterNullifierRootCol (w : Nat) : Nat := w + 45 + 26

/-! ## §5.N — the noteSpend KERNEL-SET GROW-GATE (the deployment-real set-insert + double-spend
tooth).

`RotatedKernelRefinementNotesFresh.lean` proves, against a MODELED nullifier tree, that a
non-membership open (`GapOpen`/`opensTo … none`) FORCES `nf ∉ pre.nullifiers` and a set-insert
gate FORCES `post.nullifiers = nf :: pre.nullifiers`. Until now the DEPLOYED rotated descriptor
carried `nullifier_root` (limb 26) as a TURN-INVARIANT witness limb (before == after; no gate),
so `kernel_set_insert_is_not_forced_by_the_live_descriptor` proved a frozen/forged nullifier
root still verifies.

These two `MapOp`s CLOSE that on the live wire — the EXISTING IR-v2 map-ops machinery (the same
the cap-crown attenuate write rides) is the row-level grow-gate the negative test claimed the
per-row IR "cannot express":

  * **`nullifierFreshOp`** (`.absent`) — the in-circuit DOUBLE-SPEND tooth: the published
    nullifier `param0` is NON-MEMBER of the BEFORE nullifier tree (limb 26). Under CR
    (`opensTo_none_of_gap` / the gap bracketing) this is the deployed face of the Lean
    `GapOpen` the `NotesFresh` rung consumes; a double-spend (`nf` already present) has no
    bracketing witness and is UNSAT.
  * **`nullifierInsertOp`** (`.insert`) — the SET-INSERT: the AFTER nullifier root (limb 26 of
    the after block) IS the genuine sorted insert of `param0` into the BEFORE root. Under CR
    (`writesTo_functional`) the after-root column cannot be frozen or forged — it is pinned to
    the real grown tree. This is the deployed face of `gNoteGrow`.

Both gated by the noteSpend selector (`SEL_NOTE_SPEND = 4`), so non-spend / NoOp pad rows (where
the selector is 0) contribute nothing. The published nullifier `param0` (`NULLIFIER_PARAM_COL`)
is ALREADY the spend row's folded nullifier (cross-bound to PI[38] by `rotateV3WithNullifierPin`),
so the gate's key IS the same nullifier the apex reads. -/

/-- The DOUBLE-SPEND tooth (the deployed `GapOpen` face): the published nullifier `param0` is a
NON-MEMBER of the BEFORE nullifier tree (limb 26); the root is unchanged by an absent read. -/
def nullifierFreshOp : MapOp :=
  { guard   := .var EffectVmEmitNoteSpend.SEL_NOTE_SPEND
  , root    := .var (beforeNullifierRootCol EFFECT_VM_WIDTH)
  , key     := .var NULLIFIER_PARAM_COL
  , value   := .const 0
  , newRoot := .var (beforeNullifierRootCol EFFECT_VM_WIDTH)
  , op      := .absent }

/-- The SET-INSERT (the deployed `gNoteGrow` face): the AFTER nullifier root (limb 26 of the
after block) IS the genuine sorted write of `param0` into the BEFORE root. The note value
(`param::NOTE_VALUE_LO`) rides as the leaf value so a spent nullifier carries its note datum. -/
def nullifierInsertOp : MapOp :=
  { guard   := .var EffectVmEmitNoteSpend.SEL_NOTE_SPEND
  , root    := .var (beforeNullifierRootCol EFFECT_VM_WIDTH)
  , key     := .var NULLIFIER_PARAM_COL
  , value   := .var (prmCol EffectVmEmitNoteSpend.param.NOTE_VALUE_LO)
  , newRoot := .var (afterNullifierRootCol EFFECT_VM_WIDTH)
  , op      := .insert }

/-- **`noteSpendV3`** — the rotated note-spend WITH the nullifier PI weld AND the KERNEL-SET
GROW-GATE (the deployment-real set-insert + double-spend tooth). `piCount = 39` (the 38-PI
rotated prefix + the appended nullifier slot). Past the graduated `rotateV3WithNullifierPin`
descriptor, it appends the two map-ops that FORCE the nullifier set-insert on the live wire:
`nullifierFreshOp` (the `.absent` double-spend tooth — `nf ∉ pre`) and `nullifierInsertOp` (the
`.insert` set-insert — `after_root = insert(before_root, nf)`). These repoint limb 26 from a
turn-invariant witness limb into a FORCED, grown, fresh nullifier root. -/
def noteSpendV3 : EffectVmDescriptor2 :=
  let base := graduateV1 (rotateV3WithNullifierPin EffectVmEmitNoteSpend.noteSpendVmDescriptor)
  { base with
    constraints := base.constraints ++ [.mapOp nullifierFreshOp, .mapOp nullifierInsertOp] }

/-- **`noteSpendV3_grow_gate_forces_set_insert` — the live descriptor FORCES the nullifier
set-insert + freshness (the deployment-real tooth).** On a satisfying `noteSpendV3` witness whose
spend selector fires, the two appended map-ops hold: (1) the published nullifier is ABSENT from
the BEFORE nullifier tree (limb 26) — the in-circuit double-spend tooth (`opensTo … none`); and
(2) the AFTER nullifier root IS the genuine sorted insert of that nullifier into the BEFORE root
(`writesTo`). Under CR these are FUNCTIONAL (`opensTo_functional` / `writesTo_functional`), so a
frozen or forged after-root, or a double-spent (present) nullifier, cannot satisfy the descriptor
— exactly the forgery `kernel_set_insert_is_not_forced_by_the_live_descriptor` documented, now
REJECTED. The map-ops are the deployed faces of the `NotesFresh` `GapOpen` (`.absent`) and
`gNoteGrow` (`.insert`). -/
theorem noteSpendV3_grow_gate_forces_set_insert (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash noteSpendV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (hspend : (envAt t i).loc EffectVmEmitNoteSpend.SEL_NOTE_SPEND = 1) :
    -- (1) the double-spend tooth: the published nullifier is absent from the BEFORE tree.
    (opensTo hash ((envAt t i).loc (beforeNullifierRootCol EFFECT_VM_WIDTH))
        ((envAt t i).loc NULLIFIER_PARAM_COL) none)
    -- (2) the set-insert: the AFTER root is the genuine sorted write of the nullifier.
    ∧ writesTo hash ((envAt t i).loc (beforeNullifierRootCol EFFECT_VM_WIDTH))
        ((envAt t i).loc NULLIFIER_PARAM_COL)
        ((envAt t i).loc (prmCol EffectVmEmitNoteSpend.param.NOTE_VALUE_LO))
        ((envAt t i).loc (afterNullifierRootCol EFFECT_VM_WIDTH)) := by
  have hrowc := hsat.rowConstraints i hi
  have hfresh := hrowc (.mapOp nullifierFreshOp) (by simp [noteSpendV3])
  have hins := hrowc (.mapOp nullifierInsertOp) (by simp [noteSpendV3])
  -- the map-op denotations fire under the spend selector (`SEL_NOTE_SPEND = 1`).
  have ha := hfresh hspend
  have hw := hins hspend
  exact ⟨ha.1, hw⟩

/-- The appended pin is the only constraint past `rotateV3`'s, and it targets the new slot. -/
theorem rotateV3WithNullifierPin_constraints (d : EffectVmDescriptor) :
    (rotateV3WithNullifierPin d).constraints
      = (rotateV3 d).constraints
        ++ [.piBinding .first NULLIFIER_PARAM_COL ROT_NULLIFIER_PI] := rfl

/-- The nullifier pin does NOT disturb graduation: the hash sites and ranges are `rotateV3`'s
verbatim (the pin is a CONSTRAINT, and `graduable` reads only sites/ranges). -/
theorem graduable_rotateV3WithNullifierPin {d : EffectVmDescriptor}
    (h : graduable d = true) : graduable (rotateV3WithNullifierPin d) = true := by
  have hr := graduable_rotateV3 h
  unfold rotateV3WithNullifierPin
  unfold graduable at hr ⊢
  -- `rotateV3WithNullifierPin` shares `rotateV3 d`'s hashSites + ranges exactly.
  simpa using hr

/-- **The nullifier weld holds on a satisfying first row**: a row satisfying `noteSpendV3`
carries the spend row's folded nullifier (`prmCol 0`) EQUAL to the published rotated PI[38].
This is the rotated re-statement of the v1 D5 cross-binding (`param0 == PI[NOTESPEND_NULLIFIER]`),
now a first-row pin of the rotated descriptor. -/
theorem noteSpendV3_pins_nullifier (hash : List ℤ → ℤ)
    (env : VmRowEnv) (isLast : Bool)
    (h : satisfiedVm hash (rotateV3WithNullifierPin
      EffectVmEmitNoteSpend.noteSpendVmDescriptor) env true isLast) :
    env.loc NULLIFIER_PARAM_COL = env.pub ROT_NULLIFIER_PI := by
  have hpin := h.1 (.piBinding .first NULLIFIER_PARAM_COL ROT_NULLIFIER_PI)
    (by rw [rotateV3WithNullifierPin_constraints]; exact List.mem_append_right _ List.mem_cons_self)
  simpa only [VmConstraint.holdsVm] using hpin rfl

/-- **ANTI-GHOST (nullifier tamper ⇒ UNSAT)** — the C4 soundness tooth. A first row whose
folded nullifier `param0` does NOT equal the published rotated PI[38] does NOT satisfy
`noteSpendV3`: the appended pin REJECTS it. This is the rotated boundary's analog of the v1
`test_notespend_nullifier_cross_binding_rejects_swap` ("prove N, spend M" ⇒ STARK rejects):
the rotated leg can no longer publish a nullifier different from the one the spend row carries,
so the off-row freshness cross-check (`verify_full_turn` step 8) binds THIS turn's nullifier. -/
theorem noteSpendV3_rejects_nullifier_tamper (hash : List ℤ → ℤ)
    (env : VmRowEnv) (isLast : Bool)
    (htamper : env.loc NULLIFIER_PARAM_COL ≠ env.pub ROT_NULLIFIER_PI) :
    ¬ satisfiedVm hash (rotateV3WithNullifierPin
      EffectVmEmitNoteSpend.noteSpendVmDescriptor) env true isLast :=
  fun h => htamper (noteSpendV3_pins_nullifier hash env isLast h)

/-- The v1 denotation still survives the added pin (the per-effect noteSpend faithfulness /
anti-ghost theorems compose through, exactly as for bare `rotateV3`). -/
theorem noteSpendV3_satisfiedVm_v1 (hash : List ℤ → ℤ)
    (env : VmRowEnv) (isFirst isLast : Bool)
    (h : satisfiedVm hash (rotateV3WithNullifierPin
      EffectVmEmitNoteSpend.noteSpendVmDescriptor) env isFirst isLast) :
    satisfiedVm hash EffectVmEmitNoteSpend.noteSpendVmDescriptor env isFirst isLast := by
  apply rotateV3_satisfiedVm_v1 hash EffectVmEmitNoteSpend.noteSpendVmDescriptor env isFirst isLast
  -- `rotateV3WithNullifierPin` = `rotateV3` with one extra constraint + the same sites; a
  -- satisfier of the former satisfies the latter (constraints are a superset, sites identical).
  obtain ⟨hc, hsites, hr⟩ := h
  refine ⟨fun c hc' => hc c ?_, hsites, hr⟩
  rw [rotateV3WithNullifierPin_constraints]
  exact List.mem_append_left _ hc'

#assert_axioms graduable_rotateV3WithNullifierPin
#assert_axioms noteSpendV3_pins_nullifier
#assert_axioms noteSpendV3_rejects_nullifier_tamper
#assert_axioms noteSpendV3_satisfiedVm_v1

-- The nullifier pin lands at PI slot 38 (one past the four rotated commit pins 34..37) and
-- the rotated note-spend publishes 39 PIs.
#guard ROT_NULLIFIER_PI == 34 + 4
#guard NULLIFIER_PARAM_COL == 68          -- PARAM_BASE (54+14) + param::NULLIFIER (0)
#guard noteSpendV3.piCount == 39
#guard (rotateV3WithNullifierPin EffectVmEmitNoteSpend.noteSpendVmDescriptor).piCount == 39
-- Graduation survives the appended pin.
#guard graduable (rotateV3WithNullifierPin EffectVmEmitNoteSpend.noteSpendVmDescriptor)
-- The rotated commit pins are UNDISTURBED at 34..37 (the fifth pin is strictly appended);
-- `noteSpendV3` carries the four rotated commit pins PLUS one more PI pin (the nullifier weld)
-- PLUS the two KERNEL-SET grow-gate map-ops (`nullifierFreshOp` `.absent` + `nullifierInsertOp`
-- `.insert` — the deployment-real set-insert + double-spend tooth) = +3 constraints in total.
#guard noteSpendV3.constraints.length == (v3Of EffectVmEmitNoteSpend.noteSpendVmDescriptor).constraints.length + 1 + 2
-- The grow-gate map-ops ARE present on `noteSpendV3` (the live wire now carries the set-insert).
#guard (mapOpsOf noteSpendV3).length == 2
-- BOTH POLARITIES of the soundness tooth, executable on the toy environment: a row whose
-- param0 equals PI[38] PASSES the pin; a tampered one FAILS it. (`decEnv` toy: param col 68
-- carries `n`, PI 38 carries `p`.)
#guard (let env : VmRowEnv := ⟨fun c => if c == 68 then 5 else 0, fun _ => 0, fun k => if k == 38 then 5 else 0⟩;
        decide (env.loc NULLIFIER_PARAM_COL = env.pub ROT_NULLIFIER_PI))   -- match ⇒ pin holds
#guard (let env : VmRowEnv := ⟨fun c => if c == 68 then 5 else 0, fun _ => 0, fun k => if k == 38 then 9 else 0⟩;
        decide (env.loc NULLIFIER_PARAM_COL ≠ env.pub ROT_NULLIFIER_PI))   -- mismatch ⇒ pin REJECTS

/-! ## §5.NC — the noteCreate KERNEL-SET GROW-GATE (the deployment-real COMMITMENTS set-insert).

The `commitments_root` flag-day limb (in-block offset `B_COMMITMENTS_ROOT = 27`, the NEW committed
shielded-set root the widening NUM_PRE_LIMBS 31→32 added) gives the note COMMITMENT set a committed
home. Before the widening there was NO `commitments_root` limb at all, so
`kernel_set_insert_is_not_forced_by_the_live_descriptor` proved a noteCreate turn whose commitments
set was NOT grown still verified — the ONE remaining named residual of the kernel-set family.

This `MapOp` CLOSES it on the live wire, CLONING the noteSpend grow-gate onto limb 27. `NoteCreate`
is append-only (`NoteCreateASpec` has NO guard — `noteCreateAdmit = True`), so unlike noteSpend there
is NO freshness `.absent` tooth: just the SET-INSERT. The inserted KEY is the published note
commitment `param0` (`generate_effect_vm_trace`'s `Effect::NoteCreate` arm lays
`param0 = commitment`), cross-bound to a published PI slot by `rotateV3WithCommitmentKeyPin` so the
apex reads the SAME commitment the gate forces:

  * **`commitmentsInsertOp`** (`.insert`) — the SET-INSERT (the deployed `gNoteGrow` face): the
    AFTER commitments root (limb 27 of the after block) IS the genuine sorted insert of `param0`
    into the BEFORE root. Under CR (`writesTo_functional`) the after-root column cannot be frozen or
    forged — it is pinned to the real grown commitments tree. This is the deployed realization of
    `RotatedKernelRefinementNotes.noteCreate_commitments_forced` against the NOW-LIVE limb 27.

Gated by the noteCreate selector (`SEL_NOTE_CREATE = 5`), so non-create / NoOp pad rows contribute
nothing. The note value (`param::NOTE_VALUE_LO = param1`) rides as the leaf value so a created
commitment carries its note datum. -/

/-- The rotated published-PI slot the note commitment (`param0`) welds to — the FIRST slot past the
four rotated commit pins (`piCount = 34 + 4 = 38`), the same arithmetic as `ROT_NULLIFIER_PI`
(noteCreate and noteSpend never co-occur on one row, so sharing slot 38 is sound). -/
def ROT_COMMITMENT_KEY_PI : Nat := 38

/-- The note-commitment key parameter column (`param0`, `prmCol 0`) — the noteCreate row's
single published note-commitment felt (`Effect::NoteCreate { commitment }` ⇒ `row[PARAM_BASE+0]`). -/
def COMMITMENT_KEY_PARAM_COL : Nat := prmCol 0

/-- The rotated BEFORE-block `commitments_root` limb column (limb 27 of the before block at
`base = traceWidth`). The deployed commitments accumulator's PRE root. -/
def beforeCommitmentsRootCol (w : Nat) : Nat := w + B_COMMITMENTS_ROOT

/-- The rotated AFTER-block `commitments_root` limb column (limb 27 of the after block at
`base = traceWidth + 45`). The deployed commitments accumulator's POST root — the grow-gate's
`newRoot`. -/
def afterCommitmentsRootCol (w : Nat) : Nat := w + 45 + B_COMMITMENTS_ROOT

/-- **`rotateV3WithCommitmentKeyPin`** — `rotateV3` PLUS the fifth appended PI pin welding the note
commitment (`prmCol 0`) to `ROT_COMMITMENT_KEY_PI = 38` on the FIRST row. Structurally identical to
`rotateV3WithNullifierPin`; every v1 column/constraint/site and the four rotated commit pins are
UNTOUCHED. -/
def rotateV3WithCommitmentKeyPin (d : EffectVmDescriptor) : EffectVmDescriptor :=
  let r := rotateV3 d
  { r with
    piCount     := r.piCount + 1
    constraints := r.constraints ++ [.piBinding .first COMMITMENT_KEY_PARAM_COL ROT_COMMITMENT_KEY_PI] }

/-- The SET-INSERT: the AFTER commitments root (limb 27 of the after block) IS the genuine sorted
write of the note commitment (`param0`) into the BEFORE root, with the note value (`param1`) as the
leaf value. Guarded by the noteCreate selector. -/
def commitmentsInsertOp : MapOp :=
  { guard   := .var EffectVmEmitNoteCreate.SEL_NOTE_CREATE
  , root    := .var (beforeCommitmentsRootCol EFFECT_VM_WIDTH)
  , key     := .var COMMITMENT_KEY_PARAM_COL
  , value   := .var (prmCol EffectVmEmitNoteCreate.param.NOTE_VALUE_LO)
  , newRoot := .var (afterCommitmentsRootCol EFFECT_VM_WIDTH)
  , op      := .insert }

/-- **`noteCreateV3`** — the rotated noteCreate WITH the commitment PI weld AND the KERNEL-SET
GROW-GATE (the deployment-real commitments set-insert). `piCount = 39`. Past the graduated
`rotateV3WithCommitmentKeyPin` descriptor it appends the one map-op that FORCES the commitment
set-insert on the live wire (`commitmentsInsertOp .insert`), repointing limb 27 from a turn-invariant
witness limb into a FORCED, grown commitments root. NoteCreate is append-only — there is no `.absent`
freshness tooth (`NoteCreateASpec` has no guard), so the gate is the single insert. -/
def noteCreateV3 : EffectVmDescriptor2 :=
  let base := graduateV1 (rotateV3WithCommitmentKeyPin EffectVmEmitNoteCreate.noteCreateVmDescriptor)
  { base with
    constraints := base.constraints ++ [.mapOp commitmentsInsertOp] }

/-- **`noteCreateV3_grow_gate_forces_set_insert` — the live descriptor FORCES the commitment
set-insert (the deployment-real tooth).** On a satisfying `noteCreateV3` witness whose create
selector fires, the appended map-op holds: the AFTER commitments root (limb 27 of the after block)
IS the genuine sorted insert of the published note commitment (`param0`) into the BEFORE root
(`writesTo`). Under CR this is FUNCTIONAL (`writesTo_functional`), so a frozen or forged after-root
cannot satisfy the descriptor — exactly the forgery
`kernel_set_insert_is_not_forced_by_the_live_descriptor` documented as the noteCreate residual, now
REJECTED. The map-op is the deployed face of
`RotatedKernelRefinementNotes.noteCreate_commitments_forced` against the live limb 27. -/
theorem noteCreateV3_grow_gate_forces_set_insert (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash noteCreateV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (hcreate : (envAt t i).loc EffectVmEmitNoteCreate.SEL_NOTE_CREATE = 1) :
    writesTo hash ((envAt t i).loc (beforeCommitmentsRootCol EFFECT_VM_WIDTH))
        ((envAt t i).loc COMMITMENT_KEY_PARAM_COL)
        ((envAt t i).loc (prmCol EffectVmEmitNoteCreate.param.NOTE_VALUE_LO))
        ((envAt t i).loc (afterCommitmentsRootCol EFFECT_VM_WIDTH)) := by
  have hrowc := hsat.rowConstraints i hi
  have hins := hrowc (.mapOp commitmentsInsertOp) (by simp [noteCreateV3])
  exact hins hcreate

#assert_axioms noteCreateV3_grow_gate_forces_set_insert

-- The commitment pin lands at PI slot 38; the rotated noteCreate publishes 39 PIs and carries the
-- single grow-gate map-op on the new commitments_root limb (27).
#guard ROT_COMMITMENT_KEY_PI == 34 + 4
#guard COMMITMENT_KEY_PARAM_COL == 68
#guard noteCreateV3.piCount == 39
#guard (mapOpsOf noteCreateV3).length == 1
#guard beforeCommitmentsRootCol EFFECT_VM_WIDTH == EFFECT_VM_WIDTH + 27
#guard afterCommitmentsRootCol EFFECT_VM_WIDTH == EFFECT_VM_WIDTH + 45 + 27

/-! ## §5.C — the createCell / factory / spawn KERNEL-SET GROW-GATE (the deployment-real
ACCOUNTS set-insert).

`cells_root` (rotated limb 0) is ALREADY an openable sorted-Poseidon2 root, but — exactly as
limb 26 was for noteSpend before §5.N — the createCell/factory/spawn descriptors carried it as a
TURN-INVARIANT witness limb (before == after; no gate), so
`kernel_set_insert_is_not_forced_by_the_live_descriptor` proved a frozen/forged cells_root still
verifies and the new cell's account-set growth was unwitnessed (`createCell_offrow_unenforced`).

These two `MapOp`s CLOSE that on the live wire, CLONING the noteSpend grow-gate onto limb 0. The
inserted KEY is the new-cell identity `param0` (`Effect::CreateCell { create_hash }` ⇒
`row[PARAM_BASE+0] = create_hash[0]`; the spawn/factory child-id likewise lands in `param0`),
cross-bound to a published PI slot by `rotateV3WithNewCellKeyPin` so the apex reads the SAME key
the gate forces:

  * **`cellsFreshOp`** (`.absent`) — the FRESHNESS tooth: the new-cell key `param0` is a
    NON-MEMBER of the BEFORE cells tree (limb 0). A re-creation of an existing cell id has no
    bracketing witness and is UNSAT (no account-id collision).
  * **`cellsInsertOp`** (`.insert`) — the SET-INSERT: the AFTER cells root (limb 0 of the after
    block) IS the genuine sorted insert of `param0` into the BEFORE root. Under CR
    (`writesTo_functional`) the after-root column cannot be frozen or forged — it is pinned to the
    real grown accounts tree.

The gate is guarded per-effect by the runtime selector (createCell `31`, factory `13`, spawn `32`),
so non-matching / NoOp pad rows contribute nothing. spawn's cap-handoff (the child cap-root MOVE +
delegation snapshot) is ORTHOGONAL to this accounts-set insert — it rides spawn's existing
`gCapMove`/delegation legs and is NOT closed here (the named spawn residual). -/

/-- The rotated published-PI slot the new-cell key (`param0`) welds to — the FIRST slot past the
four rotated commit pins (`piCount = 34 + 4 = 38`), the same arithmetic as `ROT_NULLIFIER_PI`
(these descriptors and noteSpend never co-occur on one row, so sharing slot 38 is sound). -/
def ROT_NEW_CELL_KEY_PI : Nat := 38

/-- The new-cell key parameter column (`param0`, `prmCol 0`) — the create/factory/spawn row's
single folded new-cell identity felt (`create_hash[0]`). -/
def NEW_CELL_KEY_PARAM_COL : Nat := prmCol 0

/-- The rotated BEFORE-block `cells_root` limb column (limb 0 of the before block at
`base = traceWidth`). The deployed accounts accumulator's PRE root — the openable
sorted-Poseidon2 root the grow-gate opens against. -/
def beforeCellsRootCol (w : Nat) : Nat := w + 0

/-- The rotated AFTER-block `cells_root` limb column (limb 0 of the after block at
`base = traceWidth + 45`). The deployed accounts accumulator's POST root — the grow-gate's
`newRoot`. -/
def afterCellsRootCol (w : Nat) : Nat := w + 45 + 0

/-- **`rotateV3WithNewCellKeyPin`** — `rotateV3` PLUS the fifth appended PI pin welding the
new-cell key (column `keyCol`) to `ROT_NEW_CELL_KEY_PI = 38` on the FIRST row. Structurally identical
to `rotateV3WithNullifierPin`; every v1 column/constraint/site and the four rotated commit pins are
UNTOUCHED. `keyCol` is `param0` for createCell/spawn, `param1` (the derived child VK) for factory. -/
def rotateV3WithNewCellKeyPin (keyCol : Nat) (d : EffectVmDescriptor) : EffectVmDescriptor :=
  let r := rotateV3 d
  { r with
    piCount     := r.piCount + 1
    constraints := r.constraints ++ [.piBinding .first keyCol ROT_NEW_CELL_KEY_PI] }

/-- The FRESHNESS tooth (no account-id collision): the new-cell key (column `keyCol`) is a NON-MEMBER
of the BEFORE cells tree (limb 0); the root is unchanged by an absent read. Guarded by the supplied
runtime selector column `sel`. `keyCol` is `param0` for createCell/spawn (the new-cell id) and `param1`
for factory (the derived child VK). -/
def cellsFreshOp (sel keyCol : Nat) : MapOp :=
  { guard   := .var sel
  , root    := .var (beforeCellsRootCol EFFECT_VM_WIDTH)
  , key     := .var keyCol
  , value   := .const 0
  , newRoot := .var (beforeCellsRootCol EFFECT_VM_WIDTH)
  , op      := .absent }

/-- The SET-INSERT: the AFTER cells root (limb 0 of the after block) IS the genuine sorted write of
the new-cell key (`keyCol`) into the BEFORE root. The key rides as its own leaf value (a born-empty
cell). -/
def cellsInsertOp (sel keyCol : Nat) : MapOp :=
  { guard   := .var sel
  , root    := .var (beforeCellsRootCol EFFECT_VM_WIDTH)
  , key     := .var keyCol
  , value   := .var keyCol
  , newRoot := .var (afterCellsRootCol EFFECT_VM_WIDTH)
  , op      := .insert }

/-- The factory's new-cell key column (`param1`, the derived child VK — `CHILD_VK_DERIVED`); factory's
`param0` carries the factory VK, so the child id is `param1`. -/
def FACTORY_CHILD_KEY_PARAM_COL : Nat := prmCol 1

/-- **`createCellV3`** — the rotated createCell WITH the new-cell-key PI weld AND the ACCOUNTS-SET
GROW-GATE. `piCount = 39`. Past the graduated `rotateV3WithNewCellKeyPin` descriptor it appends the
two map-ops that FORCE the accounts set-insert on the live wire (`cellsFreshOp .absent` +
`cellsInsertOp .insert`), repointing limb 0 from a turn-invariant witness limb into a FORCED, grown,
fresh accounts root. -/
def createCellV3 : EffectVmDescriptor2 :=
  let base := graduateV1 (rotateV3WithNewCellKeyPin NEW_CELL_KEY_PARAM_COL
    EffectVmEmitCreateCell.createCellActorVmDescriptor)
  { base with
    constraints := base.constraints
      ++ [.mapOp (cellsFreshOp EffectVmEmitCreateCell.SEL_CREATE_CELL_RT NEW_CELL_KEY_PARAM_COL),
          .mapOp (cellsInsertOp EffectVmEmitCreateCell.SEL_CREATE_CELL_RT NEW_CELL_KEY_PARAM_COL)] }

/-- **`factoryV3`** — the rotated createCellFromFactory WITH the new-cell-key weld + accounts-set
grow-gate (factory selector `13`). Same shape as `createCellV3`. -/
def factoryV3 : EffectVmDescriptor2 :=
  let base := graduateV1 (rotateV3WithNewCellKeyPin FACTORY_CHILD_KEY_PARAM_COL
    EffectVmEmitCreateCellFromFactory.factoryActorVmDescriptor)
  { base with
    constraints := base.constraints
      ++ [.mapOp (cellsFreshOp EffectVmEmitCreateCellFromFactory.SEL_FACTORY_RT
            FACTORY_CHILD_KEY_PARAM_COL),
          .mapOp (cellsInsertOp EffectVmEmitCreateCellFromFactory.SEL_FACTORY_RT
            FACTORY_CHILD_KEY_PARAM_COL)] }

/-- **`spawnV3`** — the rotated spawn WITH the new-cell-key weld + accounts-set grow-gate (spawn
selector `32`). The cap-handoff (child cap-root MOVE + delegation snapshot) is NOT closed here — it
rides spawn's existing `gCapMove`/delegation legs (the named spawn residual). -/
def spawnV3 : EffectVmDescriptor2 :=
  let base := graduateV1 (rotateV3WithNewCellKeyPin NEW_CELL_KEY_PARAM_COL
    EffectVmEmitSpawn.spawnActorVmDescriptor)
  { base with
    constraints := base.constraints
      ++ [.mapOp (cellsFreshOp EffectVmEmitSpawn.SEL_SPAWN_RT NEW_CELL_KEY_PARAM_COL),
          .mapOp (cellsInsertOp EffectVmEmitSpawn.SEL_SPAWN_RT NEW_CELL_KEY_PARAM_COL)] }

/-- **`createCellV3_grow_gate_forces_set_insert` — the live descriptor FORCES the accounts
set-insert + freshness.** On a satisfying `createCellV3` witness whose createCell selector fires, the
two appended map-ops hold: (1) the published new-cell key is ABSENT from the BEFORE cells tree (limb
0) — the no-collision tooth (`opensTo … none`); and (2) the AFTER cells root IS the genuine sorted
insert of that key into the BEFORE root (`writesTo`). Under CR these are FUNCTIONAL, so a frozen or
forged after-root, or a re-created (present) cell id, cannot satisfy the descriptor — exactly the
forgery `kernel_set_insert_is_not_forced_by_the_live_descriptor` documented, now REJECTED. -/
theorem createCellV3_grow_gate_forces_set_insert (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash createCellV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (hcreate : (envAt t i).loc EffectVmEmitCreateCell.SEL_CREATE_CELL_RT = 1) :
    (opensTo hash ((envAt t i).loc (beforeCellsRootCol EFFECT_VM_WIDTH))
        ((envAt t i).loc NEW_CELL_KEY_PARAM_COL) none)
    ∧ writesTo hash ((envAt t i).loc (beforeCellsRootCol EFFECT_VM_WIDTH))
        ((envAt t i).loc NEW_CELL_KEY_PARAM_COL)
        ((envAt t i).loc NEW_CELL_KEY_PARAM_COL)
        ((envAt t i).loc (afterCellsRootCol EFFECT_VM_WIDTH)) := by
  have hrowc := hsat.rowConstraints i hi
  have hfresh := hrowc (.mapOp (cellsFreshOp EffectVmEmitCreateCell.SEL_CREATE_CELL_RT
    NEW_CELL_KEY_PARAM_COL)) (by simp [createCellV3])
  have hins := hrowc (.mapOp (cellsInsertOp EffectVmEmitCreateCell.SEL_CREATE_CELL_RT
    NEW_CELL_KEY_PARAM_COL)) (by simp [createCellV3])
  exact ⟨(hfresh hcreate).1, hins hcreate⟩

/-- **`factoryV3_grow_gate_forces_set_insert`** — `createCellV3`'s tooth for the factory descriptor
(selector `13`). -/
theorem factoryV3_grow_gate_forces_set_insert (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash factoryV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (hfactory : (envAt t i).loc EffectVmEmitCreateCellFromFactory.SEL_FACTORY_RT = 1) :
    (opensTo hash ((envAt t i).loc (beforeCellsRootCol EFFECT_VM_WIDTH))
        ((envAt t i).loc FACTORY_CHILD_KEY_PARAM_COL) none)
    ∧ writesTo hash ((envAt t i).loc (beforeCellsRootCol EFFECT_VM_WIDTH))
        ((envAt t i).loc FACTORY_CHILD_KEY_PARAM_COL)
        ((envAt t i).loc FACTORY_CHILD_KEY_PARAM_COL)
        ((envAt t i).loc (afterCellsRootCol EFFECT_VM_WIDTH)) := by
  have hrowc := hsat.rowConstraints i hi
  have hfresh := hrowc (.mapOp (cellsFreshOp EffectVmEmitCreateCellFromFactory.SEL_FACTORY_RT
    FACTORY_CHILD_KEY_PARAM_COL)) (by simp [factoryV3])
  have hins := hrowc (.mapOp (cellsInsertOp EffectVmEmitCreateCellFromFactory.SEL_FACTORY_RT
    FACTORY_CHILD_KEY_PARAM_COL)) (by simp [factoryV3])
  exact ⟨(hfresh hfactory).1, hins hfactory⟩

/-- **`spawnV3_grow_gate_forces_set_insert`** — `createCellV3`'s tooth for the spawn descriptor
(selector `32`). The accounts set-insert is FORCED; the cap-handoff is the named spawn residual. -/
theorem spawnV3_grow_gate_forces_set_insert (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash spawnV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (hspawn : (envAt t i).loc EffectVmEmitSpawn.SEL_SPAWN_RT = 1) :
    (opensTo hash ((envAt t i).loc (beforeCellsRootCol EFFECT_VM_WIDTH))
        ((envAt t i).loc NEW_CELL_KEY_PARAM_COL) none)
    ∧ writesTo hash ((envAt t i).loc (beforeCellsRootCol EFFECT_VM_WIDTH))
        ((envAt t i).loc NEW_CELL_KEY_PARAM_COL)
        ((envAt t i).loc NEW_CELL_KEY_PARAM_COL)
        ((envAt t i).loc (afterCellsRootCol EFFECT_VM_WIDTH)) := by
  have hrowc := hsat.rowConstraints i hi
  have hfresh := hrowc (.mapOp (cellsFreshOp EffectVmEmitSpawn.SEL_SPAWN_RT
    NEW_CELL_KEY_PARAM_COL)) (by simp [spawnV3])
  have hins := hrowc (.mapOp (cellsInsertOp EffectVmEmitSpawn.SEL_SPAWN_RT
    NEW_CELL_KEY_PARAM_COL)) (by simp [spawnV3])
  exact ⟨(hfresh hspawn).1, hins hspawn⟩

#assert_axioms createCellV3_grow_gate_forces_set_insert
#assert_axioms factoryV3_grow_gate_forces_set_insert
#assert_axioms spawnV3_grow_gate_forces_set_insert

-- The new-cell-key pin lands at PI slot 38; each rotated create-family descriptor publishes 39 PIs.
#guard ROT_NEW_CELL_KEY_PI == 34 + 4
#guard NEW_CELL_KEY_PARAM_COL == 68
#guard createCellV3.piCount == 39
#guard factoryV3.piCount == 39
#guard spawnV3.piCount == 39
-- Each carries the four rotated commit pins + one new-cell-key pin + the two grow-gate map-ops.
#guard createCellV3.constraints.length == (v3Of EffectVmEmitCreateCell.createCellActorVmDescriptor).constraints.length + 1 + 2
#guard (mapOpsOf createCellV3).length == 2
#guard (mapOpsOf factoryV3).length == 2
#guard (mapOpsOf spawnV3).length == 2

/-! ### The SetField + BridgeMint runtime reconcile (the last rotation flip gate, C7).

The model (the end-to-end `effect_vm_rotation_flip` prove) surfaced TWO runtime divergences in
the rotated SetField / BridgeMint descriptors. Both are reconciled here so those turns ROTATE.

**Seam 1 — the nonce tick.** The runtime trace generator (`circuit/src/effect_vm/trace.rs`)
TICKS the per-cell sequence nonce on EVERY non-NoOp row: `Effect::SetField` →
`new_state.nonce += 1`, `Effect::BridgeMint` → `new_state.nonce += 1` (only `Effect::NoOp`
leaves it). `trace_rotated.rs::fill_block` copies that ticked nonce into the rotated `r1` limb
(`row[base+2] = row[state_base + state::NONCE]`, the `weldsAt` r1↔NONCE weld). But the per-effect
descriptors FREEZE it (`EffectVmEmitSetField.gNonceFreeze` / `EffectVmEmitMint.gNonceFix` are
BOTH `after_nonce − before_nonce`), so `after_nonce = before_nonce` is UNSAT on the ticked trace.

**Seam 2 — the value/credit param column.** The runtime puts the EFFECT's payload at `param1`,
not `param0`: `Effect::SetField` writes `param0 = field_index`, `param1 = new_value`
(`trace.rs` + the v1 hand-AIR `air.rs` `new_value = p1`); `Effect::BridgeMint` writes
`param0 = mint_hash`, `param1 = value_lo` and credits `balance += value_lo`. But the per-effect
descriptors read `param0`: `setFieldVmDescriptor`'s write gate reads `prmCol VALUE = prmCol
param.AMOUNT = prmCol 0` (= the runtime's FIELD_INDEX), and `mintVmDescriptor`'s credit reads
`prmCol param.AMOUNT = prmCol 0` (= the runtime's MINT_HASH). So both check the field write /
balance credit against the WRONG column — UNSAT on the honest trace even with the nonce fixed.
(The registry's BridgeMint leg is `mintVmDescriptor`, NOT `EffectVmEmitBridgeMint` — that module
does not build in the shared tree, `EffectVmEmitV2` line 73 — so the param1 fix is applied to the
mint descriptor's credit here rather than swapping descriptors.)

This section builds TICK-faced + param1-corrected variants by REBUILDING each descriptor's
constraint list: the nonce freeze gate becomes the transfer/noteSpend TICK gate
`EffectVmEmitTransfer.gNonce = (after_nonce − before_nonce) − (1 − s_noop)` (the SAME
`−(1 − selector)` term `transferVmDescriptor2R24` / `noteSpendVmDescriptor2R24` carry), and the
field-write / balance-credit gate reads `prmCol 1` (the runtime's NEW_VALUE / value_lo). Every
OTHER gate, transition, boundary pin, hash site, and range tooth is the per-effect descriptor's
verbatim, so `rotateV3`'s parametric keystones (`rotV3_sound_v1`, `rotV3_binds_published`,
`graduable_rotateV3`) compose unchanged (the graduable side conditions read only the unchanged
sites/ranges).

POST-RECONCILE (the source-coherence follow-up): the per-effect `EffectVmEmitSetField` /
`EffectVmEmitMint` SOURCE descriptors have SINCE been corrected to match the runtime themselves
(the SAME three fixes: nonce tick, value/credit at `param1`, setField gated by `sel::SET_FIELD = 2`;
their faithfulness theorems re-proved against the ticked/param1 behaviour, both polarities, on the
active-row premise `IsSetFieldRow` / `IsMintRow` — exactly burn's shape). So these tick-faced
constraint lists now COINCIDE with their source descriptors' (`setFieldTickFace_eq_source` below);
the rebuild is retained so the rotated registry JSON + the `V3_STAGED_REGISTRY_FP` pin are unchanged,
but it is no longer a BYPASS of a buggy source — source and rotated leg agree. The descriptor NAME is
kept (`dregg-effectvm-setfield-v1` / `dregg-effectvm-mint-v1`), exactly as the v1 reconciles kept it.

SOUNDNESS TOOTH (do NOT just make it SAT): the tick gate is ENFORCED — a row whose nonce delta is
NOT the tick (`after_nonce ≠ before_nonce + 1` on a non-NoOp row) FAILS the gate and is UNSAT
(`setFieldTick_rejects_wrong_nonce_delta` / `mintTick_rejects_wrong_nonce_delta`, both polarities
`#guard`'d), and the corrected write/credit gate is ENFORCED — a row whose written field / credited
balance does NOT match `prmCol 1` is UNSAT (`setFieldP1_rejects_wrong_value` /
`mintP1_rejects_wrong_credit`). So the rotated leg binds the per-cell sequence counter AND the
genuine payload column the runtime carries. -/

/-- The runtime's value/credit param column: `param1` (NEW_VALUE for setField, value_lo for
BridgeMint) — NOT `param0` (FIELD_INDEX / MINT_HASH). The v1 hand-AIR (`air.rs`) reads `p1`. -/
def RUNTIME_VALUE_PARAM : Nat := 1

/-- The runtime's SetField SELECTOR column: `sel::SET_FIELD = 2` (the trace generator writes
`row[2] = 1` on the active setField row, `effect_selector` → `trace.rs`). The per-effect
`EffectVmEmitSetField.SEL_SET_FIELD` has SINCE been reconciled to this same value (the source
descriptor was corrected in the cutover — the earlier `54` was `sbCol BALANCE_LO`, NOT a selector).
The corrected write gate gates by THIS column. -/
def SEL_SET_FIELD_COL : Nat := 2

-- The runtime selector column is `sel::SET_FIELD = 2`, distinct from `sbCol BALANCE_LO = 54`.
-- POST-RECONCILE: the per-effect `EffectVmEmitSetField.SEL_SET_FIELD` now AGREES (= 2), and the
-- per-effect value column `VALUE` now reads `param1` (the runtime NEW_VALUE), matching the
-- corrections below — so the rotated tick-face and the source descriptor now COINCIDE (see
-- `setFieldTickFace_eq_source`).
#guard SEL_SET_FIELD_COL == 2
#guard SEL_SET_FIELD_COL ≠ sbCol state.BALANCE_LO
#guard EffectVmEmitSetField.SEL_SET_FIELD == SEL_SET_FIELD_COL   -- source reconciled (was the 54 bug)
#guard EffectVmEmitSetField.VALUE == RUNTIME_VALUE_PARAM         -- source value column reconciled to param1

/-! #### The TICK-faced + param1-corrected SetField (per slot). -/

/-- The field-`slot` WRITE gate reading the RUNTIME value column (`prmCol 1 = NEW_VALUE`),
SELECTOR-GATED by `s_set_field`: `s_set_field · (fields[slot]_after − param1) = 0`.

Two corrections over the per-effect `gFieldWrite` (which is `fields[slot]_after − prmCol 0`,
UNGATED): (1) it reads `param1` (the runtime NEW_VALUE — `air.rs` `new_value = p1`), not `param0`
(FIELD_INDEX); (2) it is gated by `s_set_field`, exactly as the runtime hand-AIR gates every
setField constraint (`air.rs` `c = s_setfield · …`). The gating is LOAD-BEARING for multi-row
traces: the field write PERSISTS into the after-state, so a trailing NoOp PAD row carries
`fields[slot]_after = (the written value)` while its `param1 = 0` — an UNGATED write gate would
fire `written_value − 0 ≠ 0` and the honest 64-row trace would be UNSAT. With the `s_set_field`
factor the gate VANISHES on NoOp rows (`s_set_field = 0`) and binds only the ACTIVE row
(`s_set_field = 1`), matching the runtime. (The freeze gates degenerate naturally on NoOp —
`after − before = frozen − frozen = 0` — so only the write gate needs the factor.) -/
def gFieldWriteP1 (slot : Fin 8) : EmittedExpr :=
  .mul (.var SEL_SET_FIELD_COL)
    (EffectVmEmitTransfer.eSub (EffectVmEmitTransfer.eSA (state.FIELD_BASE + slot.val))
      (EffectVmEmitTransfer.ePrm RUNTIME_VALUE_PARAM))

/-- The setField row gates with (1) the nonce FREEZE gate swapped for the transfer/noteSpend TICK
gate `EffectVmEmitTransfer.gNonce` and (2) the WRITE gate reading the runtime value column
`prmCol 1`. Every OTHER gate (the bal/cap/reserved freezes, the seven other-field passthroughs)
is `EffectVmEmitSetField.setFieldRowGates`'s verbatim. -/
def setFieldRowGatesTick (slot : Fin 8) : List VmConstraint :=
  [ .gate (gFieldWriteP1 slot)
  , .gate EffectVmEmitSetField.gBalLoFreeze
  , .gate EffectVmEmitTransfer.gBalHi
  , .gate EffectVmEmitTransfer.gNonce
  , .gate EffectVmEmitTransfer.gCapPass
  , .gate EffectVmEmitTransfer.gResPass ]
  ++ EffectVmEmitSetField.gOtherFieldsAll slot

/-- **`setFieldTickFace slot`** — `setFieldVmDescriptor slot` with the nonce gate ticked AND the
write gate reading the runtime value column. The name, width, PI count, hash sites, and ranges are
the per-effect descriptor's verbatim; only the constraint list changes those two gates (so
`graduable` — which reads only sites/ranges — is unchanged, and the rotated keystones compose). -/
def setFieldTickFace (slot : Fin 8) : EffectVmDescriptor :=
  { EffectVmEmitSetField.setFieldVmDescriptor slot with
    constraints := setFieldRowGatesTick slot }

/-- The tick-faced setField shares the per-effect descriptor's sites + ranges (both slot-FREE:
`transferHashSites` and the two balance-limb range teeth), so it is graduable (the parametric
`graduable_rotateV3` premise). `graduable` reads only `hashSites`/`ranges`, invisible to the
constraint swap, so this is the constant `transferHashSites`-graduability — `rfl`. -/
theorem graduable_setFieldTickFace (slot : Fin 8) :
    graduable (setFieldTickFace slot) = true := rfl

/-- **SOURCE-COHERENCE: the tick-face now COINCIDES with the (reconciled) source descriptor.** After
the per-effect `EffectVmEmitSetField` source was corrected (nonce tick, value at `param1`, gated by
`sel::SET_FIELD = 2`), its `setFieldRowGates` IS this section's `setFieldRowGatesTick` (gate-for-gate
definitionally — `gFieldWriteP1 = gFieldWrite`, both `.mul (.var 2) (·_after − param1)`; the tick gate
is the same `EffectVmEmitTransfer.gNonce`), so the tick-faced descriptor equals the source descriptor.
The rotated registry routing through `setFieldV3` is therefore NOT a bypass of a buggy source — they
are the same circuit. -/
theorem setFieldTickFace_eq_source (slot : Fin 8) :
    setFieldTickFace slot = EffectVmEmitSetField.setFieldVmDescriptor slot := rfl

/-- **`setFieldV3 slot`** — the rotated tick-faced setField (the registry member). -/
def setFieldV3 (slot : Fin 8) : EffectVmDescriptor2 := v3Of (setFieldTickFace slot)

/-- **The nonce TICK holds on a satisfying non-NoOp setField row.** A row satisfying the rotated
tick-faced setField, with `s_noop = 0`, carries `after_nonce = before_nonce + 1` (the runtime
tick) — the rotated re-statement of the transfer/noteSpend nonce gate, now on setField. -/
theorem setFieldV3_pins_nonce_tick (slot : Fin 8) (hash : List ℤ → ℤ) (env : VmRowEnv)
    (isFirst isLast : Bool) (hnoop : env.loc sel.NOOP = 0)
    (h : satisfiedVm hash (rotateV3 (setFieldTickFace slot)) env isFirst isLast) :
    env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE) + 1 := by
  have hmem : VmConstraint.gate EffectVmEmitTransfer.gNonce ∈ (rotateV3 (setFieldTickFace slot)).constraints := by
    apply List.mem_append_left
    show _ ∈ setFieldRowGatesTick slot
    simp [setFieldRowGatesTick]
  have hg := h.1 _ hmem
  simp only [VmConstraint.holdsVm, EffectVmEmitTransfer.gNonce, EffectVmEmitTransfer.eSub,
    EffectVmEmitTransfer.eSA, EffectVmEmitTransfer.eSB, EffectVmEmitTransfer.eSelNoop,
    EmittedExpr.eval] at hg
  rw [hnoop] at hg
  linarith [hg]

/-- **ANTI-GHOST (wrong nonce delta ⇒ UNSAT)** — the C7 soundness tooth for setField. A non-NoOp
row whose nonce delta is NOT the tick (`after_nonce ≠ before_nonce + 1`) does NOT satisfy the
rotated tick-faced setField: the swapped tick gate REJECTS it. A forged passthrough
(`after = before`) is the special case the FREEZE descriptor wrongly accepted; it is now UNSAT. -/
theorem setFieldTick_rejects_wrong_nonce_delta (slot : Fin 8) (hash : List ℤ → ℤ) (env : VmRowEnv)
    (isFirst isLast : Bool) (hnoop : env.loc sel.NOOP = 0)
    (hwrong : env.loc (saCol state.NONCE) ≠ env.loc (sbCol state.NONCE) + 1) :
    ¬ satisfiedVm hash (rotateV3 (setFieldTickFace slot)) env isFirst isLast :=
  fun h => hwrong (setFieldV3_pins_nonce_tick slot hash env isFirst isLast hnoop h)

/-- **The corrected WRITE binds the runtime value column on the ACTIVE row.** A row satisfying the
rotated param1-corrected setField with `s_set_field = 1` (the active setField row) carries
`fields[slot]_after = param1` (the runtime NEW_VALUE) — the selector-gated write gate, on the
active row, reads the column the trace generator wrote the value to. (On NoOp rows
`s_set_field = 0` the gate vanishes, so the binding is exactly the runtime's gated semantics.) -/
theorem setFieldV3_pins_value (slot : Fin 8) (hash : List ℤ → ℤ) (env : VmRowEnv)
    (isFirst isLast : Bool) (hactive : env.loc SEL_SET_FIELD_COL = 1)
    (h : satisfiedVm hash (rotateV3 (setFieldTickFace slot)) env isFirst isLast) :
    env.loc (saCol (state.FIELD_BASE + slot.val)) = env.loc (prmCol RUNTIME_VALUE_PARAM) := by
  have hmem : VmConstraint.gate (gFieldWriteP1 slot) ∈ (rotateV3 (setFieldTickFace slot)).constraints := by
    apply List.mem_append_left
    show _ ∈ setFieldRowGatesTick slot
    simp [setFieldRowGatesTick]
  have hg := h.1 _ hmem
  simp only [VmConstraint.holdsVm, gFieldWriteP1, EffectVmEmitTransfer.eSub,
    EffectVmEmitTransfer.eSA, EffectVmEmitTransfer.ePrm, EmittedExpr.eval] at hg
  rw [hactive] at hg
  linarith [hg]

/-- **ANTI-GHOST (wrong written value ⇒ UNSAT)** — the C7 param-column soundness tooth for
setField. An ACTIVE setField row (`s_set_field = 1`) whose written field does NOT equal `param1`
(the runtime value column) does NOT satisfy the corrected descriptor: the gated write gate, on the
active row, REJECTS it. -/
theorem setFieldP1_rejects_wrong_value (slot : Fin 8) (hash : List ℤ → ℤ) (env : VmRowEnv)
    (isFirst isLast : Bool) (hactive : env.loc SEL_SET_FIELD_COL = 1)
    (hwrong : env.loc (saCol (state.FIELD_BASE + slot.val)) ≠ env.loc (prmCol RUNTIME_VALUE_PARAM)) :
    ¬ satisfiedVm hash (rotateV3 (setFieldTickFace slot)) env isFirst isLast :=
  fun h => hwrong (setFieldV3_pins_value slot hash env isFirst isLast hactive h)

/-! #### The TICK-faced + param1-corrected BridgeMint (= the `mintVmDescriptor2R24` member). -/

/-- Balance-lo CREDIT body reading the RUNTIME value column (`prmCol 1 = value_lo`):
`new_bal_lo − old_bal_lo − param1` (so `new = old + value_lo`). (The per-effect `gBalLoCredit`
reads `prmCol 0 = MINT_HASH` on a BridgeMint row; the runtime credits `param1 = value_lo`.) -/
def gBalLoCreditP1 : EmittedExpr :=
  .add (EffectVmEmitTransfer.eSub (EffectVmEmitTransfer.eSA state.BALANCE_LO)
          (EffectVmEmitTransfer.eSB state.BALANCE_LO))
    (.mul (.const (-1)) (EffectVmEmitTransfer.ePrm RUNTIME_VALUE_PARAM))

/-- The mint row gates with (1) the nonce FREEZE gate (`gNonceFix`) swapped for the TICK gate and
(2) the balance credit reading the runtime value column `prmCol 1`. The bal-hi/cap/reserved
freezes and 8 field freezes are `EffectVmEmitMint.mintRowGates`'s verbatim. -/
def mintRowGatesTick : List VmConstraint :=
  [ .gate gBalLoCreditP1
  , .gate EffectVmEmitMint.gBalHiFix
  , .gate EffectVmEmitTransfer.gNonce
  , .gate EffectVmEmitMint.gCapFix
  , .gate EffectVmEmitMint.gResFix ]
  ++ EffectVmEmitMint.gFieldFixAll

/-- **`mintTickFace`** — `mintVmDescriptor` (the BridgeMint registry leg) with the nonce gate
ticked AND the credit reading the runtime value column. The transitions + boundary PI pins + hash
sites + ranges are verbatim; only those two row gates change. -/
def mintTickFace : EffectVmDescriptor :=
  { EffectVmEmitMint.mintVmDescriptor with
    constraints := mintRowGatesTick ++ EffectVmEmitTransfer.transitionAll
      ++ EffectVmEmitTransfer.boundaryFirstPins ++ EffectVmEmitTransfer.boundaryLastPins }

/-- The tick-faced mint shares the per-effect descriptor's sites + ranges, so it is graduable. -/
theorem graduable_mintTickFace : graduable mintTickFace = true := rfl

/-- **SOURCE-COHERENCE: the mint tick-face now COINCIDES with the (reconciled) source descriptor.**
After the per-effect `EffectVmEmitMint` source was corrected (nonce tick, credit at `param1`), its
`mintRowGates` IS this section's `mintRowGatesTick` (definitionally — `gBalLoCreditP1 = gBalLoCredit`,
both crediting `param1`; the tick gate is the same `EffectVmEmitTransfer.gNonce`), so the tick-faced
BridgeMint equals the source descriptor. The registry routing through `mintV3` is the same circuit. -/
theorem mintTickFace_eq_source : mintTickFace = EffectVmEmitMint.mintVmDescriptor := rfl

/-- **`mintV3`** — the rotated tick-faced BridgeMint (the `mintVmDescriptor2R24` registry member). -/
def mintV3 : EffectVmDescriptor2 := v3Of mintTickFace

/-- **The nonce TICK holds on a satisfying non-NoOp BridgeMint row.** -/
theorem mintV3_pins_nonce_tick (hash : List ℤ → ℤ) (env : VmRowEnv) (isFirst isLast : Bool)
    (hnoop : env.loc sel.NOOP = 0)
    (h : satisfiedVm hash (rotateV3 mintTickFace) env isFirst isLast) :
    env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE) + 1 := by
  have hmem : VmConstraint.gate EffectVmEmitTransfer.gNonce ∈ (rotateV3 mintTickFace).constraints := by
    apply List.mem_append_left
    show _ ∈ mintTickFace.constraints
    simp [mintTickFace, mintRowGatesTick]
  have hg := h.1 _ hmem
  simp only [VmConstraint.holdsVm, EffectVmEmitTransfer.gNonce, EffectVmEmitTransfer.eSub,
    EffectVmEmitTransfer.eSA, EffectVmEmitTransfer.eSB, EffectVmEmitTransfer.eSelNoop,
    EmittedExpr.eval] at hg
  rw [hnoop] at hg
  linarith [hg]

/-- **ANTI-GHOST (wrong nonce delta ⇒ UNSAT)** — the C7 soundness tooth for BridgeMint. -/
theorem mintTick_rejects_wrong_nonce_delta (hash : List ℤ → ℤ) (env : VmRowEnv)
    (isFirst isLast : Bool) (hnoop : env.loc sel.NOOP = 0)
    (hwrong : env.loc (saCol state.NONCE) ≠ env.loc (sbCol state.NONCE) + 1) :
    ¬ satisfiedVm hash (rotateV3 mintTickFace) env isFirst isLast :=
  fun h => hwrong (mintV3_pins_nonce_tick hash env isFirst isLast hnoop h)

/-- **The corrected CREDIT binds the runtime value column.** A row satisfying the rotated
param1-corrected BridgeMint carries `bal_lo_after = bal_lo_before + param1` (the runtime
value_lo) — the credit gate now reads the column the trace generator credited from. -/
theorem mintV3_pins_credit (hash : List ℤ → ℤ) (env : VmRowEnv) (isFirst isLast : Bool)
    (h : satisfiedVm hash (rotateV3 mintTickFace) env isFirst isLast) :
    env.loc (saCol state.BALANCE_LO)
      = env.loc (sbCol state.BALANCE_LO) + env.loc (prmCol RUNTIME_VALUE_PARAM) := by
  have hmem : VmConstraint.gate gBalLoCreditP1 ∈ (rotateV3 mintTickFace).constraints := by
    apply List.mem_append_left
    show _ ∈ mintTickFace.constraints
    simp [mintTickFace, mintRowGatesTick]
  have hg := h.1 _ hmem
  simp only [VmConstraint.holdsVm, gBalLoCreditP1, EffectVmEmitTransfer.eSub,
    EffectVmEmitTransfer.eSA, EffectVmEmitTransfer.eSB, EffectVmEmitTransfer.ePrm,
    EmittedExpr.eval] at hg
  linarith [hg]

/-- **ANTI-GHOST (wrong credit ⇒ UNSAT)** — the C7 param-column soundness tooth for BridgeMint.
A row whose post-balance is NOT `before + param1` (the runtime value_lo) is UNSAT. -/
theorem mintP1_rejects_wrong_credit (hash : List ℤ → ℤ) (env : VmRowEnv) (isFirst isLast : Bool)
    (hwrong : env.loc (saCol state.BALANCE_LO)
      ≠ env.loc (sbCol state.BALANCE_LO) + env.loc (prmCol RUNTIME_VALUE_PARAM)) :
    ¬ satisfiedVm hash (rotateV3 mintTickFace) env isFirst isLast :=
  fun h => hwrong (mintV3_pins_credit hash env isFirst isLast h)

#assert_axioms graduable_setFieldTickFace
#assert_axioms setFieldTickFace_eq_source
#assert_axioms setFieldV3_pins_nonce_tick
#assert_axioms setFieldTick_rejects_wrong_nonce_delta
#assert_axioms setFieldV3_pins_value
#assert_axioms setFieldP1_rejects_wrong_value
#assert_axioms graduable_mintTickFace
#assert_axioms mintTickFace_eq_source
#assert_axioms mintV3_pins_nonce_tick
#assert_axioms mintTick_rejects_wrong_nonce_delta
#assert_axioms mintV3_pins_credit
#assert_axioms mintP1_rejects_wrong_credit

-- The tick-faced descriptors keep the per-effect width/PI-count/site/range shape (only the
-- nonce gate body changed): graduable, and the rotated form is the standard 311-col / 38-PI member.
#guard graduable (setFieldTickFace 0)
#guard graduable mintTickFace
#guard (setFieldV3 0).traceWidth == EFFECT_VM_WIDTH + APPENDIX_SPAN
#guard mintV3.traceWidth == EFFECT_VM_WIDTH + APPENDIX_SPAN
#guard (setFieldV3 0).piCount == 34 + 4
#guard mintV3.piCount == 34 + 4
-- The swap is a ONE-gate change: the tick-faced constraint list has the SAME length as the
-- per-effect descriptor's (a gate replaced a gate, none added or removed).
#guard (setFieldTickFace 0).constraints.length
        == (EffectVmEmitSetField.setFieldVmDescriptor 0).constraints.length
#guard mintTickFace.constraints.length == EffectVmEmitMint.mintVmDescriptor.constraints.length
-- The tick gate IS the transfer/noteSpend tick gate (the `−(1 − selector)` term): the rotated
-- tick-faced constraint list carries `EffectVmEmitTransfer.gNonce` at the nonce slot, and the
-- freeze-gate body is GONE — the two tick-faced descriptors no longer hold the bare freeze gate
-- the `mismodels_nonce_tick` predicate guarded against. (`setFieldRowGatesTick`'s 4th gate / the
-- mint list's 3rd gate ARE the tick gate; `setField{V3_pins,Tick_rejects}_*` prove its membership +
-- enforcement formally, so this is the lightweight positional witness.)
#guard (setFieldRowGatesTick 0).length == 13   -- 6 head gates + 7 other-field freezes
#guard mintRowGatesTick.length == 13           -- 5 head gates + 8 field freezes
-- BOTH POLARITIES of the NONCE tooth, executable on a toy row (NOOP = col 0; sb NONCE = 56;
-- sa NONCE = STATE_AFTER_BASE(76) + NONCE(2) = 78). A ticked row (after = before + 1, s_noop = 0)
-- HOLDS the tick gate; a forged passthrough (after = before) FAILS it. (Mirrors transfer's
-- `gNonce` adversarial #guards — the `−(1 − selector)` term makes passthrough UNSAT off NoOp.)
#guard (let env : VmRowEnv := ⟨fun c => if c == 56 then 5 else if c == 78 then 6 else 0, fun _ => 0, fun _ => 0⟩;
        decide ((EffectVmEmitTransfer.gNonce).eval env.loc = 0))   -- tick (5→6) ⇒ gate holds
#guard (let env : VmRowEnv := ⟨fun c => if c == 56 then 5 else if c == 78 then 5 else 0, fun _ => 0, fun _ => 0⟩;
        decide ((EffectVmEmitTransfer.gNonce).eval env.loc ≠ 0))   -- passthrough (5→5) ⇒ gate REJECTS
-- The corrected WRITE/CREDIT gates read `prmCol 1` (NEW_VALUE / value_lo = col PARAM_BASE+1 = 69),
-- NOT `prmCol 0` (FIELD_INDEX / MINT_HASH = col 68). Positional witness + both polarities.
#guard prmCol RUNTIME_VALUE_PARAM == 69
-- setField WRITE (selector-gated by s_set_field = col SEL_SET_FIELD_COL = 2): on the ACTIVE row
-- (s_set_field = 1), field0_after (saCol FIELD_BASE = 79) == param1 (69). Match holds; mismatch
-- rejects. On a NoOp row (s_set_field = 0) the gate VANISHES (third guard).
#guard (let env : VmRowEnv := ⟨fun c => if c == 2 then 1 else if c == 79 then 7 else if c == 69 then 7 else 0, fun _ => 0, fun _ => 0⟩;
        decide ((gFieldWriteP1 0).eval env.loc = 0))   -- active + (field0_after == param1) ⇒ holds
#guard (let env : VmRowEnv := ⟨fun c => if c == 2 then 1 else if c == 79 then 7 else if c == 69 then 9 else 0, fun _ => 0, fun _ => 0⟩;
        decide ((gFieldWriteP1 0).eval env.loc ≠ 0))   -- active + (field0_after ≠ param1) ⇒ REJECTS
#guard (let env : VmRowEnv := ⟨fun c => if c == 79 then 7 else if c == 69 then 9 else 0, fun _ => 0, fun _ => 0⟩;
        decide ((gFieldWriteP1 0).eval env.loc = 0))   -- NoOp (s_set_field = 0) ⇒ gate VANISHES
-- mint CREDIT: bal_lo_after (76) == bal_lo_before (54) + param1 (69). Honest credit holds; wrong rejects.
#guard (let env : VmRowEnv := ⟨fun c => if c == 54 then 100 else if c == 76 then 130 else if c == 69 then 30 else 0, fun _ => 0, fun _ => 0⟩;
        decide (gBalLoCreditP1.eval env.loc = 0))   -- 130 == 100 + 30 ⇒ holds
#guard (let env : VmRowEnv := ⟨fun c => if c == 54 then 100 else if c == 76 then 999 else if c == 69 then 30 else 0, fun _ => 0, fun _ => 0⟩;
        decide (gBalLoCreditP1.eval env.loc ≠ 0))   -- 999 ≠ 100 + 30 ⇒ REJECTS

/-! ### The RECORD-FORCING PIN (the deployment-soundness close for the 7 binds-but-unforced effects).

`cellSeal` / `cellUnseal` / `cellDestroy` write the per-cell `lifecycle` side-table; `setPermissions`
/ `setVK` AND the audit writes `refusal` / `receiptArchive` write a record slot folded into the
per-cell `authority_digest` (the `record_digest` — the audit slots `"refusal"`/`"lifecycle"` land in
`fields_root`, which the digest folds, `cell/src/commitment.rs::compute_authority_digest_felt`). The
rotated AFTER block CARRIES those writes (limb 28 = `lifecycle`, limb 24 = `authority_digest`, filled
from the post-state producer witness, `turn/src/rotation_witness.rs`) and the rolled-up commitment
BINDS them — but NOTHING in `rotateV3` FORCES the AFTER limb to equal the CORRECTLY-WRITTEN value. So
a malicious prover can publish an AFTER block whose lifecycle is still the PRE value (frozen, never
sealed) and whose `authority_digest` is the PRE record — the descriptor accepts, the light client is
fooled (the `RotatedKernelRefinement{CellSeal,Lifecycle,PermsVK}` rungs prove the gate that bites this
against a FIX descriptor; THIS wires that gate LIVE).

The forcing is ONE appended last-row PI pin, exactly the `rotateV3WithNullifierPin` shape: the AFTER
block's forced limb is bound to a NEW rotated PI slot (`piCount`, the first past the four commit pins)
carrying the correctly-written post value. The off-circuit verifier RECOMPUTES that PI from the
committed pre-state + the effect (`lifecycle_felt(post)` for the lifecycle effects, the post
`record_digest` for setPerms/setVK), so a frozen / wrong-record AFTER block FAILS the pin and is UNSAT
— the deployment analog of the rungs' `gLifecycleSeal` / `gSlotSet`. Every v1 column, constraint, hash
site, and the four commit pins are UNTOUCHED, so `rotateV3`'s keystones (`rotateV3_satisfiedVm_v1`,
`rotV3_binds_published`, `graduable_rotateV3`) compose verbatim — this only ADDS one PI pin + one PI
slot, exactly as the nullifier weld does. -/

/-- In-block offset of the `lifecycle` limb (limb 29 in `preLimbsAt`, shifted +1 by the
`commitments_root` flag-day): the per-cell lifecycle felt the producer witness carries
(`rotation_witness.rs::lifecycle_felt`, `pre_limbs[29]`). The forced limb for `cellSeal` /
`cellUnseal` / `cellDestroy`. -/
def B_LIFECYCLE : Nat := 29

/-- In-block offset of the `authority_digest` / `record_digest` limb (limb 24 = r23 in `preLimbsAt`):
the single felt folding ALL authority-bearing cell state including the `permissions` / `verification_key`
slots (`trace_rotated.rs::B_AUTHORITY_DIGEST`). The forced limb for `setPermissions` / `setVK`. -/
def B_RECORD_DIGEST : Nat := 24

/-- The rotated AFTER-block base offset (past the v1 layout + the BEFORE block, `B_SPAN = 45`). -/
def AFTER_BLOCK_OFF : Nat := 45

/-- **`rotateV3WithRecordPin off d`** — `rotateV3` PLUS a fifth appended last-row PI pin welding the
AFTER block's limb at in-block offset `off` (`B_LIFECYCLE` or `B_RECORD_DIGEST`) to the new rotated PI
slot `r.piCount` (the first past the four commit pins). The write LANDS in the AFTER state (the
post-state producer witness fills it), so the LAST-row pin is the rotated analog of the rungs' post-root
gate. Every v1 column, constraint, hash site, and the four commit pins are UNTOUCHED (so `rotateV3`'s
keystones compose verbatim; this only ADDS one PI pin + one PI slot). -/
def rotateV3WithRecordPin (off : Nat) (d : EffectVmDescriptor) : EffectVmDescriptor :=
  let r := rotateV3 d
  { r with
    piCount     := r.piCount + 1
    constraints := r.constraints
      ++ [.piBinding .last (d.traceWidth + AFTER_BLOCK_OFF + off) r.piCount] }

/-- The appended record pin is the only constraint past `rotateV3`'s. -/
theorem rotateV3WithRecordPin_constraints (off : Nat) (d : EffectVmDescriptor) :
    (rotateV3WithRecordPin off d).constraints
      = (rotateV3 d).constraints
        ++ [.piBinding .last (d.traceWidth + AFTER_BLOCK_OFF + off) (rotateV3 d).piCount] := rfl

/-- The record pin does NOT disturb graduation (it is a CONSTRAINT; `graduable` reads only
sites/ranges, which are `rotateV3`'s verbatim). -/
theorem graduable_rotateV3WithRecordPin (off : Nat) {d : EffectVmDescriptor}
    (h : graduable d = true) : graduable (rotateV3WithRecordPin off d) = true := by
  have hr := graduable_rotateV3 h
  unfold rotateV3WithRecordPin
  unfold graduable at hr ⊢
  simpa using hr

/-- **The record weld holds on a satisfying LAST row**: a row satisfying `rotateV3WithRecordPin off d`
carries the AFTER block's forced limb EQUAL to the published rotated PI `(rotateV3 d).piCount`. -/
theorem rotateV3WithRecordPin_pins (off : Nat) (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (env : VmRowEnv) (isFirst : Bool)
    (h : satisfiedVm hash (rotateV3WithRecordPin off d) env isFirst true) :
    env.loc (d.traceWidth + AFTER_BLOCK_OFF + off) = env.pub (rotateV3 d).piCount := by
  have hpin := h.1 (.piBinding .last (d.traceWidth + AFTER_BLOCK_OFF + off) (rotateV3 d).piCount)
    (by rw [rotateV3WithRecordPin_constraints]; exact List.mem_append_right _ List.mem_cons_self)
  simpa only [VmConstraint.holdsVm] using hpin rfl

/-- **(forced limb ≠ published value ⇒ UNSAT)** — a LAST row whose AFTER forced limb does NOT equal the
published PI `PI[(rotateV3 d).piCount]` does NOT satisfy `rotateV3WithRecordPin off d`: the appended pin
REJECTS it.

⚠ HONESTY BOUNDARY (do NOT overclaim this as a closed anti-ghost for the WHOLE record-pin family): this
theorem forces only `after_limb == PI[piCount]`, where `PI[piCount]` is a FREE public input. It is a
genuine FORCING gate (a real anti-ghost rejecting a frozen lifecycle / un-written record) ONLY when the
deployed verifier independently ANCHORS `PI[piCount]` to `compute_authority_digest_felt(trusted post-cell)`
(= apply the effect to the cross-checked before-cell, then digest).

CLOSED FOR `setPermissions` AND `setVK` (the record-digest movers, limb `B_RECORD_DIGEST = 24`): the
deployed verifier (`turn/src/executor/proof_verify.rs verify_and_commit_proof_rotated`, step 6b) anchors PI
38 for BOTH leads — it clones the trusted before-cell, applies the kernel effect through the SHARED
`dregg_turn::rotation_witness::apply_effect_to_cell` weld (the SAME projection the cipherclerk producer uses
for its after-cell, so honest proofs are NOT rejected), and overrides
`dpis[38] = compute_authority_digest_felt(post_cell)`. `compute_authority_digest_felt` FOLDS both the cell's
`permissions` and `verification_key.hash`, so a genuine setPermissions / setVK MOVES the AFTER r23 residue and
a forged after-residue disagrees with the anchored PI 38 ⇒ `verify_vm_descriptor2` UNSAT. Tests
(`sdk/tests/sovereign_rotated_c1.rs record_pin_anchor`):
`{rotated_sovereign_set_permissions_proves_and_verifies, rotated_sovereign_forged_after_permissions_is_rejected,
rotated_sovereign_set_vk_proves_and_verifies, rotated_sovereign_forged_after_vk_is_rejected}` — the honest
accept BITES (without the anchor PI 38 stays at the placeholder and the honest proof is rejected), and the
forged-after proof is rejected by the anchor mismatch.

CLOSED FOR THE WHOLE RECORD-PIN FAMILY (the fan-out fixed the 3 bugs the vacuous pin had masked — the
model-finds-the-bug loop; each effect's forged-after tooth BITES, tests in `sdk/tests/sovereign_rotated_c1.rs
record_pin_anchor`, all 7 accept/reject pairs green):

  * RECORD-DIGEST anchor (limb `B_RECORD_DIGEST = 24`, `compute_authority_digest_felt`): `setPermissions`,
    `setVK`, and `refusal`. The refusal fix: the deployed `apply_refusal` now writes the audit commitment into
    the protocol-reserved EXT key `REFUSAL_AUDIT_EXT_KEY` (`≥ STATE_SLOTS`, committed via `fields_root` which
    `compute_authority_digest_felt` folds), matching the Lean SPEC `TurnExecutorFull.refusalField` — was the
    welded `fields[4]` (unfolded), the spec/deployment divergence that left the refusal record UNBOUND.

  * LIFECYCLE anchor (limb `B_LIFECYCLE = 29`, `lifecycle_felt_cell`): `cellSeal`, `cellUnseal`, `cellDestroy`
    (the lifecycle separates Live/Sealed/Destroyed + folds the death-cert for Destroy), AND `receiptArchive`
    (`record_pin_offset` re-routed from the mis-routed `B_RECORD_DIGEST` to `B_LIFECYCLE`). The cellSeal/Unseal/
    Destroy producer/verifier projection divergence (the cipherclerk producer collapsed them to
    `VmEffect::SetPermissions` vs the executor bridge's native variants) was fixed by aligning the producer to
    native projection (+ threading `block_height` into the otherwise-stateless producer for the cellSeal seam).

The verifier (`verify_and_commit_proof_rotated`, step 6b) clones the trusted before-cell, applies the kernel
effect through the SHARED `dregg_turn::rotation_witness::apply_effect_to_cell` weld (the SAME projection the
cipherclerk producer uses for its after-cell, so honest proofs are NOT rejected), and overrides `dpis[38]`
from the trusted post-cell (`compute_authority_digest_felt` for the record-digest class, `lifecycle_felt_cell`
for the lifecycle class) — so a forged after-residue disagrees with the anchored PI 38 ⇒ UNSAT. The record-pin
is now a genuine forcing gate across the family, not a published-value binding. -/
theorem rotateV3WithRecordPin_rejects_wrong_post (off : Nat) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor) (env : VmRowEnv) (isFirst : Bool)
    (hwrong : env.loc (d.traceWidth + AFTER_BLOCK_OFF + off) ≠ env.pub (rotateV3 d).piCount) :
    ¬ satisfiedVm hash (rotateV3WithRecordPin off d) env isFirst true :=
  fun h => hwrong (rotateV3WithRecordPin_pins off hash d env isFirst h)

/-- The v1 denotation survives the added record pin (the per-effect faithfulness / anti-ghost
theorems compose through, exactly as for the nullifier pin). -/
theorem rotateV3WithRecordPin_satisfiedVm_v1 (off : Nat) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor) (env : VmRowEnv) (isFirst isLast : Bool)
    (h : satisfiedVm hash (rotateV3WithRecordPin off d) env isFirst isLast) :
    satisfiedVm hash d env isFirst isLast := by
  apply rotateV3_satisfiedVm_v1 hash d env isFirst isLast
  obtain ⟨hc, hsites, hr⟩ := h
  refine ⟨fun c hc' => hc c ?_, hsites, hr⟩
  rw [rotateV3WithRecordPin_constraints]
  exact List.mem_append_left _ hc'

/-- **`cellSealV3`** — the LIVE rotated cellSeal WITH the lifecycle-forcing pin: the AFTER block's
lifecycle limb (`B_LIFECYCLE`) is welded to PI `38`, the verifier-recomputed `lifecycle_felt(Sealed …)`.
A frozen-lifecycle (un-sealed) AFTER block is now UNSAT (`rotateV3WithRecordPin_rejects_wrong_post`). -/
def cellSealV3 : EffectVmDescriptor2 :=
  graduateV1 (rotateV3WithRecordPin B_LIFECYCLE EffectVmEmitCellSeal.cellSealVmDescriptor)

/-- **`cellUnsealV3`** — the LIVE rotated cellUnseal WITH the lifecycle-forcing pin (post = `Live`). -/
def cellUnsealV3 : EffectVmDescriptor2 :=
  graduateV1 (rotateV3WithRecordPin B_LIFECYCLE EffectVmEmitCellUnseal.cellUnsealVmDescriptor)

/-- **`cellDestroyV3`** — the LIVE rotated cellDestroy WITH the lifecycle-forcing pin (post = `Destroyed
…`; the death-cert is folded into the same per-cell lifecycle felt — the producer's `lifecycle_felt`
binds the Destroyed discriminant + the death-certificate payload, so the one pin forces both legs). -/
def cellDestroyV3 : EffectVmDescriptor2 :=
  graduateV1 (rotateV3WithRecordPin B_LIFECYCLE EffectVmEmitCellDestroy.cellDestroyVmDescriptor)

/-- **`setPermsV3`** — the LIVE rotated setPermissions WITH the record-digest-forcing pin: the AFTER
block's `authority_digest` limb (`B_RECORD_DIGEST` = r23) is welded to PI `38`, the verifier-recomputed
post `record_digest` (which folds the written `permissions := p`). A frozen-record forgery is UNSAT. -/
def setPermsV3 : EffectVmDescriptor2 :=
  graduateV1 (rotateV3WithRecordPin B_RECORD_DIGEST EffectVmEmitSetPermissions.setPermsVmDescriptor)

/-- **`setVKV3`** — the LIVE rotated setVK WITH the record-digest-forcing pin (post `record_digest`
folds the written `verification_key := vk`). -/
def setVKV3 : EffectVmDescriptor2 :=
  graduateV1 (rotateV3WithRecordPin B_RECORD_DIGEST EffectVmEmitSetVK.setVKVmDescriptor)

/-- **`refusalV3`** — the LIVE rotated refusal WITH the record-digest-forcing pin (the deployment
close for the field-NOT-bound audit-write gap). The `.refusalA` arm sets the cell record's `"refusal"`
audit slot to `1` (`TurnExecutorFull.refusalField`, `Spec.CellStateAudit.RefusalSpec`). That named
record slot lands in the deployed cell's `fields_root` (the named-field map — NOT one of the welded
`fields[0..7]` indexed slots), and `compute_authority_digest_felt` FOLDS `fields_root` into the r23
authority residue (`B_RECORD_DIGEST` = limb 24). So the AFTER block's `record_digest` limb MOVES on a
genuine refusal; pinning it to PI `38` forces the write. A FROZEN-audit-slot AFTER block (claiming a
refusal that did not happen) carries the unchanged record digest, FAILS the pin, and is UNSAT
(`rotateV3WithRecordPin_rejects_wrong_post`) — the forgery the deployed commitment did not even bind
before is now BITING. -/
def refusalV3 : EffectVmDescriptor2 :=
  graduateV1 (rotateV3WithRecordPin B_RECORD_DIGEST EffectVmEmitRefusal.refusalVmDescriptor)

/-- **`receiptArchiveV3`** — the LIVE rotated receiptArchive WITH the LIFECYCLE-forcing pin (limb
`B_LIFECYCLE = 29`). The DEPLOYED `apply_receipt_archive` writes the cell LIFECYCLE (`Archived`) via
`c.archive(checkpoint)` — NOT a `fields_root` record slot — so the genuine mover is `lifecycle_felt`
(`rotation_witness.rs::lifecycle_felt`, AFTER limb 29), which folds the archival checkpoint into a
distinct `Archived` felt. Pinning that limb to PI `38` forces it; the verifier anchors PI 38 to
`lifecycle_felt_cell(post_cell)` (the Class-2 path), so a frozen-lifecycle archive forgery (claiming
an archive that did not move the lifecycle) FAILS the pin and is UNSAT
(`rotateV3WithRecordPin_rejects_wrong_post`). This MATCHES the deployed apply (which moves the
lifecycle), where the prior `B_RECORD_DIGEST` route was a MIS-ROUTE (the deployed write does not move
the authority residue). -/
def receiptArchiveV3 : EffectVmDescriptor2 :=
  graduateV1 (rotateV3WithRecordPin B_LIFECYCLE
    EffectVmEmitReceiptArchive.receiptArchiveActorVmDescriptor)

#assert_axioms graduable_rotateV3WithRecordPin
#assert_axioms rotateV3WithRecordPin_pins
#assert_axioms rotateV3WithRecordPin_rejects_wrong_post
#assert_axioms rotateV3WithRecordPin_satisfiedVm_v1

-- The record pin lands at PI slot 38 (one past the four rotated commit pins 34..37); each forced
-- descriptor publishes 39 PIs, and graduation survives the appended pin.
#guard (rotateV3 EffectVmEmitCellSeal.cellSealVmDescriptor).piCount == 38
#guard cellSealV3.piCount == 39
#guard cellUnsealV3.piCount == 39
#guard cellDestroyV3.piCount == 39
#guard setPermsV3.piCount == 39
#guard setVKV3.piCount == 39
#guard refusalV3.piCount == 39
#guard receiptArchiveV3.piCount == 39
#guard graduable (rotateV3WithRecordPin B_RECORD_DIGEST EffectVmEmitRefusal.refusalVmDescriptor)
#guard graduable (rotateV3WithRecordPin B_LIFECYCLE
        EffectVmEmitReceiptArchive.receiptArchiveActorVmDescriptor)
#guard graduable (rotateV3WithRecordPin B_LIFECYCLE EffectVmEmitCellSeal.cellSealVmDescriptor)
#guard graduable (rotateV3WithRecordPin B_LIFECYCLE EffectVmEmitCellUnseal.cellUnsealVmDescriptor)
#guard graduable (rotateV3WithRecordPin B_LIFECYCLE EffectVmEmitCellDestroy.cellDestroyVmDescriptor)
#guard graduable (rotateV3WithRecordPin B_RECORD_DIGEST EffectVmEmitSetPermissions.setPermsVmDescriptor)
#guard graduable (rotateV3WithRecordPin B_RECORD_DIGEST EffectVmEmitSetVK.setVKVmDescriptor)
-- Each forced descriptor carries EXACTLY one constraint past its bare `rotateV3` form (the pin).
#guard cellSealV3.constraints.length
        == (v3Of EffectVmEmitCellSeal.cellSealVmDescriptor).constraints.length + 1
#guard setPermsV3.constraints.length
        == (v3Of EffectVmEmitSetPermissions.setPermsVmDescriptor).constraints.length + 1
-- The forced AFTER limbs are the lifecycle limb (col tw+45+29) and the record-digest limb (col
-- tw+45+24) — the producer-witnessed limbs the commitment binds but `rotateV3` did not force
-- (lifecycle shifted 28→29 by the `commitments_root` flag-day; AFTER block base 43→45).
#guard B_LIFECYCLE == 29
#guard B_RECORD_DIGEST == 24
-- BOTH POLARITIES of the deployment tooth, executable on a toy LAST row (AFTER lifecycle limb at col
-- tw+45+29; with tw = 186 that is col 260; PI 38 carries the recomputed post felt). A row whose AFTER
-- limb equals PI[38] PASSES the pin; a frozen / wrong one FAILS it (the forgery is rejected).
#guard (let off := B_LIFECYCLE; let tw := (186 : Nat);
        let env : VmRowEnv := ⟨fun c => if c == tw + 45 + off then 1 else 0, fun _ => 0, fun k => if k == 38 then 1 else 0⟩;
        decide (env.loc (tw + 45 + off) = env.pub 38))   -- sealed (1) == PI[38] ⇒ pin holds
#guard (let off := B_LIFECYCLE; let tw := (186 : Nat);
        let env : VmRowEnv := ⟨fun c => if c == tw + 45 + off then 0 else 0, fun _ => 0, fun k => if k == 38 then 1 else 0⟩;
        decide (env.loc (tw + 45 + off) ≠ env.pub 38))   -- frozen-Live (0) ≠ sealed PI[38] ⇒ pin REJECTS

/-- **`v3Registry`** — the full 35-member cohort at the rotated block (the 27 v2-graduated members
+ the 8 STEP-1-widened; keys = the v2 keys suffixed `R24`; wire strings via `emitVmJson2`; driver
`EmitRotationV3.lean`). -/
def v3Registry : List (String × EffectVmDescriptor2) :=
  [ ("transferVmDescriptor2R24", v3Of EffectVmEmitTransfer.transferVmDescriptor)
  , ("burnVmDescriptor2R24", v3Of EffectVmEmitBurn.burnVmDescriptor)
  , ("mintVmDescriptor2R24", mintV3)
  , ("noteSpendVmDescriptor2R24", noteSpendV3)
  , ("noteCreateVmDescriptor2R24", noteCreateV3)
  , ("cellSealVmDescriptor2R24", cellSealV3)
  , ("cellDestroyVmDescriptor2R24", cellDestroyV3)
  , ("refusalVmDescriptor2R24", refusalV3)
  , ("setPermsVmDescriptor2R24", setPermsV3)
  , ("setVKVmDescriptor2R24", setVKV3)
  , ("exerciseVmDescriptor2R24", v3Of EffectVmEmitExercise.exerciseVmDescriptor)
  , ("pipelinedSendVmDescriptor2R24", v3Of EffectVmEmitPipelinedSend.pipelinedSendVmDescriptor)
  , ("refreshVmDescriptor2R24", v3Of EffectVmEmitRefreshDelegation.refreshVmDescriptor)
  , ("incrementNonceVmDescriptor2R24",
      v3Of EffectVmEmitIncrementNonce.incrementNonceVmDescriptor)
  , ("revokeVmDescriptor2R24", v3Of EffectVmEmitRevokeDelegation.revokeVmDescriptor)
  , ("introduceVmDescriptor2R24", v3Of EffectVmEmitIntroduce.introduceVmDescriptor)
  , ("attenuateVmDescriptor2R24", attenuateV3)
  , ("revokeCapabilityVmDescriptor2R24", revokeCapabilityV3)
  , ("customVmDescriptor2R24", customV3)
  , ("setFieldDynVmDescriptor2R24", setFieldDynV3)
    -- THE COHORT-WIDENING (ROTATION-CUTOVER §2c, STEP 1): the eight LIVE-path effects that
    -- the v2 graduation never covered but the v1 wire DID — their graduated RUNTIME row
    -- (frozen-frame / passthrough + nonce-tick) lifted through the SAME `rotateV3`, so the
    -- soundness keystones (`rotV3_sound_v1`, `rotV3_binds_published`) apply to them with the
    -- per-member graduability `#guard`s below and no new proof. Deleting v1 no longer bricks
    -- them. GrantCapability rides the BARE attenuate template (`dregg-effectvm-attenuateA-v1`,
    -- the UNATTENUATED cap-root grant — the v1 GRANT_CAP descriptor), distinct from the
    -- ATTENUATE_CAPABILITY phase-B `attenuateV3`.
  , ("grantCapVmDescriptor2R24", v3Of EffectVmEmitAttenuateA.attenuateVmDescriptor)
  , ("makeSovereignVmDescriptor2R24",
      v3Of EffectVmEmitMakeSovereign.makeSovereignRuntimeVmDescriptor)
  , ("createCellVmDescriptor2R24", createCellV3)
  , ("factoryVmDescriptor2R24", factoryV3)
  , ("spawnVmDescriptor2R24", spawnV3)
  , ("receiptArchiveVmDescriptor2R24", receiptArchiveV3)
  , ("cellUnsealVmDescriptor2R24", cellUnsealV3)
  , ("emitEventVmDescriptor2R24", v3Of EffectVmEmitEmitEvent.emitEventVmDescriptor) ]
  ++ (List.finRange 8).map fun slot =>
      (s!"setFieldVmDescriptor2-{slot.val}R24", setFieldV3 slot)

#guard v3Registry.length == 36
-- Every registry entry emits a versioned v2 wire string with the rotated width, the five
-- EPOCH tables, and the four appended PI slots.
#guard v3Registry.all fun (_, d) => (emitVmJson2 d).startsWith "{\"name\":\""
#guard v3Registry.all fun (_, d) => d.traceWidth == EFFECT_VM_WIDTH + APPENDIX_SPAN
#guard v3Registry.all fun (_, d) => d.tables.length == 5
#guard v3Registry.all fun (_, d) => d.hashSites.length == 0 && d.ranges.length == 0
-- The rotated transfer: the v1 graduation's constraints + 24 welds + 4 pins + 34 chip sites.
#guard (v3Of EffectVmEmitTransfer.transferVmDescriptor).constraints.length
        == transferVmDescriptor2.constraints.length + 24 + 4 + 34
#guard (v3Of EffectVmEmitTransfer.transferVmDescriptor).piCount == 34 + 4
-- The graduation side conditions hold on every v1-faced member (per-instance witnesses of
-- the parametric `graduable_rotateV3`; attenuate/setFieldDyn ride `v3OfWith` over faces
-- checked here too).
#guard graduable (rotateV3 EffectVmEmitTransfer.transferVmDescriptor)
#guard graduable (rotateV3 setFieldDynV1Face)
#guard graduable (rotateV3 EffectVmEmitAttenuateA.attenuateVmDescriptor)
#guard graduable (rotateV3 EffectVmEmitRevokeCapability.revokeCapabilityVmDescriptor)
-- The COHORT-WIDENING faces (STEP 1): each graduable, so `rotV3_sound_v1` /
-- `rotV3_binds_published` apply to them with no new proof. (GrantCapability rides the
-- attenuate template already guarded above.)
#guard graduable (rotateV3 EffectVmEmitMakeSovereign.makeSovereignRuntimeVmDescriptor)
#guard graduable (rotateV3 EffectVmEmitCreateCell.createCellActorVmDescriptor)
#guard graduable (rotateV3 EffectVmEmitCreateCellFromFactory.factoryActorVmDescriptor)
#guard graduable (rotateV3 EffectVmEmitSpawn.spawnActorVmDescriptor)
#guard graduable (rotateV3 EffectVmEmitReceiptArchive.receiptArchiveActorVmDescriptor)
#guard graduable (rotateV3 EffectVmEmitCellUnseal.cellUnsealVmDescriptor)
#guard graduable (rotateV3 EffectVmEmitEmitEvent.emitEventVmDescriptor)
-- The extras ride: attenuate carries its 3 phase-B constraints, revoke its 2 cap-crown
-- constraints (held-read + remove-write, no submask), setFieldDyn its 2 mem ops.
#guard attenuateV3.constraints.length
        == (v3Of EffectVmEmitAttenuateA.attenuateVmDescriptor).constraints.length + 3
#guard revokeCapabilityV3.constraints.length
        == (v3Of EffectVmEmitRevokeCapability.revokeCapabilityVmDescriptor).constraints.length + 2
#guard (memOpsOf setFieldDynV3).length == 2
#guard (mapOpsOf setFieldDynV3).length == 0
#guard (mapOpsOf attenuateV3).length == 2
#guard (mapOpsOf revokeCapabilityV3).length == 2
-- The rotated Custom carries EXACTLY its one proof-binding op past the rotated passthrough base
-- (no mem/map ops — the recursive-proof binding is Custom's only NEWLY-EXPRESSIBLE leg).
#guard customV3.constraints.length == (v3Of customV1Face).constraints.length + 1
#guard (proofBindsOf customV3).length == 1
#guard (memOpsOf customV3).length == 0
#guard (mapOpsOf customV3).length == 0
#guard graduable (rotateV3 customV1Face)

/-! ### The extras' theorems, transported (the §7/§8 legs survive the rotation). -/

/-- The extras' op surface is EXACTLY the original's: the rotated graduation contributes
no mem ops (both sides are concrete lists; the kernel decides this by reduction). -/
theorem memOpsOf_setFieldDynV3 : memOpsOf setFieldDynV3 = memOpsOf setFieldDynVmDescriptor2 :=
  rfl

/-- Likewise for the rotated attenuate's map ops (the phase-B read/write pair). -/
theorem mapOpsOf_attenuateV3 : mapOpsOf attenuateV3 = mapOpsOf attenuateVmDescriptor2 := rfl

/-- The rotated dynamic setField's memory log IS the original's (op-for-op): both
descriptors declare the same two mem ops, so the gathered logs coincide definitionally —
the Blum write→read transport transports verbatim. -/
theorem setFieldDynV3_memLog (t : VmTrace) :
    memLog setFieldDynV3 t = memLog setFieldDynVmDescriptor2 t := rfl

/-- **The rotated dynamic write→read transport** — Blum applied, zero hashing, at the
rotated block: on a satisfying one-row active trace the read-back column carries EXACTLY
the written value (the §8 keystone, transported through `setFieldDynV3_memLog`). -/
theorem setFieldDynV3_readback_genuine (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hone : t.rows.length = 1)
    (hactive : (envAt t 0).loc EffectVmEmitSetField.SEL_SET_FIELD = 1)
    (hsat : Satisfied2 hash setFieldDynV3 minit mfin maddrs t) :
    (envAt t 0).loc (prmCol READBACK) = (envAt t 0).loc (prmCol NEW_VAL) := by
  have hcons := satisfied2_mem_consistent hash _ minit mfin maddrs t hsat
  rw [setFieldDynV3_memLog, setFieldDyn_memLog t hone hactive] at hcons
  obtain ⟨_, hr, _⟩ := hcons
  have := hr rfl
  simpa [MemoryChecking.step] using this

/-- **The rotated cap-crown phase-B leg** — `attenuateV2_non_amp`, transported: on an
active attenuate row of a `Satisfied2` witness of the ROTATED attenuate, the held
capability is authenticated against the before cap root, the post root is the genuine
sorted write, and `keep ⊑ held` bitwise. -/
theorem attenuateV3_non_amp (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsub : t.tf (.custom SUBMASK_TID) = subsetTable MASK_BITS)
    (hsat : Satisfied2 hash attenuateV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (hactive : (envAt t i).loc EffectVmEmitAttenuateA.selA.ATTENUATE = 1) :
    opensTo hash ((envAt t i).loc (sbCol state.CAP_ROOT))
        ((envAt t i).loc (prmCol CAP_KEY)) (some ((envAt t i).loc (prmCol HELD_MASK)))
    ∧ writesTo hash ((envAt t i).loc (sbCol state.CAP_ROOT))
        ((envAt t i).loc (prmCol CAP_KEY)) ((envAt t i).loc (prmCol KEEP_MASK))
        ((envAt t i).loc (saCol state.CAP_ROOT))
    ∧ ∃ a b : Nat, (envAt t i).loc (prmCol KEEP_MASK) = (a : ℤ)
        ∧ (envAt t i).loc (prmCol HELD_MASK) = (b : ℤ) ∧ a &&& b = a := by
  have hrowc := hsat.rowConstraints i hi
  have hmem : ∀ c ∈ ([.mapOp heldReadOp, .mapOp keepWriteOp, .lookup submaskLookup] :
      List VmConstraint2), c ∈ attenuateV3.constraints :=
    fun c hc => List.mem_append_right _ hc
  have hread := hrowc (.mapOp heldReadOp) (hmem _ (by simp))
  have hwrite := hrowc (.mapOp keepWriteOp) (hmem _ (by simp))
  have hlook := hrowc (.lookup submaskLookup) (hmem _ (by simp))
  have hr := hread hactive
  have hw := hwrite hactive
  refine ⟨hr.1, hw, ?_⟩
  have hlook' : [(envAt t i).loc (prmCol KEEP_MASK), (envAt t i).loc (prmCol HELD_MASK)]
      ∈ t.tf (.custom SUBMASK_TID) := hlook
  rw [hsub] at hlook'
  obtain ⟨a, b, _, _, hab, hx, hy⟩ := (subsetTable_mem_iff MASK_BITS _ _).mp hlook'
  exact ⟨a, b, hx, hy, hab⟩

/-- The rotated Custom declares EXACTLY the one proof-binding op (the rotated graduation
contributes none; the extras add exactly `customProofBind`). -/
theorem proofBindsOf_customV3 : proofBindsOf customV3 = [customProofBind] := by
  have hbase : proofBindsOf (v3Of customV1Face) = [] := proofBindsOf_graduateV1 (rotateV3 customV1Face)
  unfold proofBindsOf at hbase ⊢
  show ((v3Of customV1Face).constraints ++ [VmConstraint2.proofBind customProofBind]).filterMap
      _ = _
  rw [List.filterMap_append, hbase]
  rfl

/-- **The rotated cap-crown analog for Custom** — `customV2_binds_proof`, transported: on an active
Custom row of a `Satisfied2Custom` witness of the ROTATED Custom, the row's
`custom_proof_commitment` is the public-input commitment of a VERIFYING external sub-proof and its
`custom_program_vk_hash` is that proof's program VK. -/
theorem customV3_binds_proof (hash : List ℤ → ℤ)
    (E : Dregg2.Circuit.DescriptorIR2.ProofEngine)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2Custom hash E customV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (hactive : (envAt t i).loc SEL_CUSTOM = 1) :
    E.boundTo ((envAt t i).loc (prmCol CUSTOM_COMMIT)) ((envAt t i).loc (prmCol CUSTOM_VK)) := by
  have hm : customProofBind ∈ proofBindsOf customV3 := by
    rw [proofBindsOf_customV3]; exact List.mem_cons_self
  have := proofBind_bound hash E customV3 hsat hm i hi (by simpa [customProofBind] using hactive)
  simpa [customProofBind] using this

#assert_axioms setFieldDynV3_memLog
#assert_axioms setFieldDynV3_readback_genuine
#assert_axioms attenuateV3_non_amp
#assert_axioms proofBindsOf_customV3
#assert_axioms customV3_binds_proof
#assert_axioms noteSpendV3_grow_gate_forces_set_insert

-- NON-VACUITY of the bound block, executable (Horner toy sponge): moving the heap-root limb
-- (offset 27) or the iroot moves the chained commitment the appendix pins.
#guard wireCommitR refSponge ((List.range 31).map (fun i => (300 + i : ℤ))) 7
  != wireCommitR refSponge (((List.range 31).map (fun i => (300 + i : ℤ))).set 27 999) 7
#guard wireCommitR refSponge ((List.range 31).map (fun i => (300 + i : ℤ))) 7
  != wireCommitR refSponge ((List.range 31).map (fun i => (300 + i : ℤ))) 8

end Dregg2.Circuit.Emit.EffectVmEmitRotationV3
