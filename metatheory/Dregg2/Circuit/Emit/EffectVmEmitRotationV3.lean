/-
# Dregg2.Circuit.Emit.EffectVmEmitRotationV3 — THE FULL-COHORT REGEN at the rotated block
(R = 24, CONFIRMED), staged.

`docs/ROTATION-CUTOVER.md` §5 item 1: the staged probes pin the rotated SHAPE; the 26
per-effect descriptors still emit against the 186/14 layout. THIS module re-emits EVERY
cohort member against the rotated 25+…-limb state block — as ONE parametric transformation
(`rotateV3`), so the soundness keystones lift ONCE, for all 26, not per-descriptor:

  * **§1 the appended geometry** — each rotated descriptor carries, PAST its v1 layout
    (every v1 column index, constraint, and theorem untouched): a rotated BEFORE block at
    `d.traceWidth` (31 absorption-ordered limbs · iroot · state_commit · 10 chain carriers
    = 43 columns, the `EffectVmEmitRotationR` R=24 geometry verbatim), a rotated AFTER
    block at `d.traceWidth + 43`, and the WIDENED-CAVEAT region at `d.traceWidth + 86`
    (29-felt manifest · 9 chain carriers · caveat commit = 39 columns). Width: `+125`.
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
  * **§5 the v3 registry** — `v3Registry`: all 34 cohort members rotated. The 26 `v2Registry`
    members (the 17 graduated cohort + attenuate WITH its phase-B map ops/submask lookup + the
    dynamic setField WITH its mem ops + the 8 per-slot setFields) PLUS the 8 LIVE-path effects
    the v2 graduation never covered but the v1 wire DID (STEP 1 / ROTATION-CUTOVER §2c cohort
    widening): grantCap (the bare unattenuated cap-root grant), makeSovereign, createCell,
    factory, spawn, receiptArchive, cellUnseal, emitEvent — each the graduated RUNTIME row
    lifted through the SAME `rotateV3`, so the soundness keystones apply unchanged. Keys
    suffixed `R24`. Driver: `EmitRotationV3.lean` (the Rust staged twin is
    `circuit/descriptors/rotation-v3-staged-registry.tsv`, sha-pinned).
    HONEST RESIDUE: two LIVE selectors still have NO rotated descriptor — `RevokeCapability`
    (24; its cap-root advance is being reshaped by the cap-crown lanes, no graduated v1
    descriptor exists) and `Custom` (8; needs an accumulator/recursive proof-binding constraint
    kind the per-row IR does not have). These are precise obstructions, not papered over.

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

/-- The per-block span: 31 pre-iroot limbs + iroot + state_commit + 10 chain carriers. -/
def B_SPAN : Nat := 43
/-- iroot offset inside a block. -/
def B_IROOT : Nat := 31
/-- state-commit offset inside a block. -/
def B_STATE_COMMIT : Nat := 32
/-- committed-height offset inside a block. -/
def B_COMMITTED_HEIGHT : Nat := 30
/-- cap-root offset inside a block. -/
def B_CAP_ROOT : Nat := 25
/-- The caveat region span: 29 manifest felts + 9 chain carriers + 1 commit. -/
def C_SPAN : Nat := 39
/-- caveat-commit offset inside the caveat region. -/
def C_COMMIT : Nat := 38
/-- The whole appendix width: two rotated blocks + the caveat region. -/
def APPENDIX_SPAN : Nat := 125

-- The geometry IS the measured R=24 probe geometry (the staged constants do not move).
#guard B_IROOT == irootCol 24
#guard B_STATE_COMMIT == stateCommitCol 24
#guard B_COMMITTED_HEIGHT == committedHeightCol 24
#guard B_CAP_ROOT == capRootCol 24
#guard B_SPAN == probeWidth 24
#guard APPENDIX_SPAN == 2 * B_SPAN + C_SPAN

/-- The pre-iroot limb list of a block at `base` (31 limbs, absorption order: cells_root ·
r0..r23 · cap/nullifier/heap roots · lifecycle · epoch · committed height). Literal, so every
positional fact is `rfl`. -/
def preLimbsAt (base : Nat) (a : Assignment) : List ℤ :=
  [ a (base + 0), a (base + 1), a (base + 2), a (base + 3), a (base + 4), a (base + 5)
  , a (base + 6), a (base + 7), a (base + 8), a (base + 9), a (base + 10), a (base + 11)
  , a (base + 12), a (base + 13), a (base + 14), a (base + 15), a (base + 16), a (base + 17)
  , a (base + 18), a (base + 19), a (base + 20), a (base + 21), a (base + 22), a (base + 23)
  , a (base + 24), a (base + 25), a (base + 26), a (base + 27), a (base + 28), a (base + 29)
  , a (base + 30) ]

theorem preLimbsAt_length (base : Nat) (a : Assignment) :
    (preLimbsAt base a).length = 31 := rfl

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

/-- The 11 chained absorption sites of a rotated block at `base`: the 4-wide head, nine
3-wide body groups (limbs 4..30 — the EXACT 3-fill of R=24), the iroot ALONE last onto the
state-commit carrier. Chaining is by CARRIER COLUMNS (`.col`), which graduates to the SAME
wire bytes as `.digest` chaining while keeping the group position-independent. -/
def rotV3SitesAt (base : Nat) : List VmHashSite :=
  [ ⟨base + 33, [.col (base + 0), .col (base + 1), .col (base + 2), .col (base + 3)], 4⟩
  , ⟨base + 34, [.col (base + 33), .col (base + 4), .col (base + 5), .col (base + 6)], 4⟩
  , ⟨base + 35, [.col (base + 34), .col (base + 7), .col (base + 8), .col (base + 9)], 4⟩
  , ⟨base + 36, [.col (base + 35), .col (base + 10), .col (base + 11), .col (base + 12)], 4⟩
  , ⟨base + 37, [.col (base + 36), .col (base + 13), .col (base + 14), .col (base + 15)], 4⟩
  , ⟨base + 38, [.col (base + 37), .col (base + 16), .col (base + 17), .col (base + 18)], 4⟩
  , ⟨base + 39, [.col (base + 38), .col (base + 19), .col (base + 20), .col (base + 21)], 4⟩
  , ⟨base + 40, [.col (base + 39), .col (base + 22), .col (base + 23), .col (base + 24)], 4⟩
  , ⟨base + 41, [.col (base + 40), .col (base + 25), .col (base + 26), .col (base + 27)], 4⟩
  , ⟨base + 42, [.col (base + 41), .col (base + 28), .col (base + 29), .col (base + 30)], 4⟩
  , ⟨base + 32, [.col (base + 42), .col (base + 31)], 2⟩ ]

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

/-- The whole appendix site group for a descriptor of width `w`. -/
def rotV3Appendix (w : Nat) : List VmHashSite :=
  rotV3SitesAt w ++ rotV3SitesAt (w + 43) ++ caveatV3SitesAt (w + 86)

-- Arity discipline: every appendix site is arity 4 or 2 (the chip refuses 3) — checked at
-- a concrete base; the literal arities are base-independent.
#guard (rotV3Appendix 186).all fun s => s.arity == 4 || s.arity == 2
#guard (rotV3Appendix 186).length == 32

-- **THE BYTE-IDENTITY TRIPWIRE**: at base 0, the col-chained block graduates to the EXACT
-- wire JSON of the digest-chained R=24 probe (name-aligned) — col-chaining IS the probe's
-- absorption, byte-for-byte.
#guard emitVmJson2 (graduateV1
    { name := (rotationProbeVmDescriptorR 24).name
    , traceWidth := probeWidth 24
    , piCount := 2
    , constraints :=
        [ .piBinding .last (stateCommitCol 24) Dregg2.Circuit.Emit.EffectVmEmitRotation.PUB_COMMIT
        , .piBinding .last (committedHeightCol 24)
            Dregg2.Circuit.Emit.EffectVmEmitRotation.PUB_HEIGHT ]
    , hashSites := rotV3SitesAt 0
    , ranges := [] })
  == emitVmJson2 (rotationProbeVmDescriptorR2 24)

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
  , .piBinding .last (w + 43 + B_STATE_COMMIT) (piBase + 1)
  , .piBinding .last (w + 43 + B_COMMITTED_HEIGHT) (piBase + 2)
  , .piBinding .last (w + 86 + C_COMMIT) (piBase + 3) ]

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
          ++ weldsAt (d.traceWidth + 43) STATE_AFTER_BASE
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

/-- Every rotated-block site is col-only (11 literal cases). -/
theorem rotV3SitesAt_colOnly (base : Nat) : ∀ s ∈ rotV3SitesAt base, colOnly s = true := by
  intro s hs
  simp only [rotV3SitesAt, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Every caveat site is col-only (10 literal cases). -/
theorem caveatV3SitesAt_colOnly (base : Nat) :
    ∀ s ∈ caveatV3SitesAt base, colOnly s = true := by
  intro s hs
  simp only [caveatV3SitesAt, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

set_option maxHeartbeats 6400000 in
/-- **The block pin, parametric in `base`**: the eleven col-chained site equations compose
into the chained rotated commitment — the row's state-commit carrier at `base + 32` IS
`wireCommitR` of the row's OWN 31 limbs and iroot. -/
theorem rotV3SitesAt_pin (hash : List ℤ → ℤ) (env : VmRowEnv) (base : Nat)
    (h : ∀ s ∈ rotV3SitesAt base, env.loc s.digestCol = hash (s.resolvedInputs env [])) :
    env.loc (base + 32)
      = wireCommitR hash (preLimbsAt base env.loc) (env.loc (base + 31)) := by
  have h0 : env.loc (base + 33) = hash [env.loc (base + 0), env.loc (base + 1),
      env.loc (base + 2), env.loc (base + 3)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 33, [.col (base + 0), .col (base + 1), .col (base + 2), .col (base + 3)], 4⟩
        (by simp [rotV3SitesAt])
  have h1 : env.loc (base + 34) = hash [env.loc (base + 33), env.loc (base + 4),
      env.loc (base + 5), env.loc (base + 6)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 34, [.col (base + 33), .col (base + 4), .col (base + 5), .col (base + 6)], 4⟩
        (by simp [rotV3SitesAt])
  have h2 : env.loc (base + 35) = hash [env.loc (base + 34), env.loc (base + 7),
      env.loc (base + 8), env.loc (base + 9)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 35, [.col (base + 34), .col (base + 7), .col (base + 8), .col (base + 9)], 4⟩
        (by simp [rotV3SitesAt])
  have h3 : env.loc (base + 36) = hash [env.loc (base + 35), env.loc (base + 10),
      env.loc (base + 11), env.loc (base + 12)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 36, [.col (base + 35), .col (base + 10), .col (base + 11),
        .col (base + 12)], 4⟩ (by simp [rotV3SitesAt])
  have h4 : env.loc (base + 37) = hash [env.loc (base + 36), env.loc (base + 13),
      env.loc (base + 14), env.loc (base + 15)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 37, [.col (base + 36), .col (base + 13), .col (base + 14),
        .col (base + 15)], 4⟩ (by simp [rotV3SitesAt])
  have h5 : env.loc (base + 38) = hash [env.loc (base + 37), env.loc (base + 16),
      env.loc (base + 17), env.loc (base + 18)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 38, [.col (base + 37), .col (base + 16), .col (base + 17),
        .col (base + 18)], 4⟩ (by simp [rotV3SitesAt])
  have h6 : env.loc (base + 39) = hash [env.loc (base + 38), env.loc (base + 19),
      env.loc (base + 20), env.loc (base + 21)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 39, [.col (base + 38), .col (base + 19), .col (base + 20),
        .col (base + 21)], 4⟩ (by simp [rotV3SitesAt])
  have h7 : env.loc (base + 40) = hash [env.loc (base + 39), env.loc (base + 22),
      env.loc (base + 23), env.loc (base + 24)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 40, [.col (base + 39), .col (base + 22), .col (base + 23),
        .col (base + 24)], 4⟩ (by simp [rotV3SitesAt])
  have h8 : env.loc (base + 41) = hash [env.loc (base + 40), env.loc (base + 25),
      env.loc (base + 26), env.loc (base + 27)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 41, [.col (base + 40), .col (base + 25), .col (base + 26),
        .col (base + 27)], 4⟩ (by simp [rotV3SitesAt])
  have h9 : env.loc (base + 42) = hash [env.loc (base + 41), env.loc (base + 28),
      env.loc (base + 29), env.loc (base + 30)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 42, [.col (base + 41), .col (base + 28), .col (base + 29),
        .col (base + 30)], 4⟩ (by simp [rotV3SitesAt])
  have h10 : env.loc (base + 32) = hash [env.loc (base + 42), env.loc (base + 31)] := by
    simpa [VmHashSite.resolvedInputs, HashInput.resolve] using
      h ⟨base + 32, [.col (base + 42), .col (base + 31)], 2⟩ (by simp [rotV3SitesAt])
  rw [h10, h9, h8, h7, h6, h5, h4, h3, h2, h1, h0]
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
    env.loc (d.traceWidth + 32)
      = wireCommitR hash (preLimbsAt d.traceWidth env.loc) (env.loc (d.traceWidth + 31))
    ∧ env.loc (d.traceWidth + 43 + 32)
      = wireCommitR hash (preLimbsAt (d.traceWidth + 43) env.loc)
          (env.loc (d.traceWidth + 43 + 31))
    ∧ env.loc (d.traceWidth + 86 + 38)
      = caveatCommit hash (manifestAt (d.traceWidth + 86) env.loc) := by
  have hsites := h.2.1
  have heq := go_colOnly_mem hash env [] _ hsites
  have hmem : ∀ s ∈ rotV3Appendix d.traceWidth, s ∈ (rotateV3 d).hashSites :=
    fun s hs => List.mem_append_right _ hs
  refine ⟨?_, ?_, ?_⟩
  · exact rotV3SitesAt_pin hash env d.traceWidth fun s hs =>
      heq s (hmem s (List.mem_append_left _ (List.mem_append_left _ hs)))
        (rotV3SitesAt_colOnly _ s hs)
  · exact rotV3SitesAt_pin hash env (d.traceWidth + 43) fun s hs =>
      heq s (hmem s (List.mem_append_left _ (List.mem_append_right _ hs)))
        (rotV3SitesAt_colOnly _ s hs)
  · exact caveatV3SitesAt_pin hash env (d.traceWidth + 86) fun s hs =>
      heq s (hmem s (List.mem_append_right _ hs)) (caveatV3SitesAt_colOnly _ s hs)

/-- A weld of the rotated descriptor holds on every satisfying row. -/
theorem rotateV3_weld (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (env : VmRowEnv) (isFirst isLast : Bool)
    (h : satisfiedVm hash (rotateV3 d) env isFirst isLast)
    {a b : Nat}
    (hw : colEq a b ∈ weldsAt d.traceWidth STATE_BEFORE_BASE
        ∨ colEq a b ∈ weldsAt (d.traceWidth + 43) STATE_AFTER_BASE) :
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
    ∧ env.loc (d.traceWidth + 43 + 1) = env.loc (saCol state.BALANCE_LO)
    ∧ env.loc (d.traceWidth + 43 + 2) = env.loc (saCol state.NONCE)
    ∧ env.loc (d.traceWidth + 43 + B_CAP_ROOT) = env.loc (saCol state.CAP_ROOT) := by
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
        rcases hs'' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
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
    (envAt t i).loc (d.traceWidth + 32)
      = wireCommitR hash (preLimbsAt d.traceWidth (envAt t i).loc)
          ((envAt t i).loc (d.traceWidth + 31))
    ∧ (envAt t i).loc (d.traceWidth + 43 + 32)
      = wireCommitR hash (preLimbsAt (d.traceWidth + 43) (envAt t i).loc)
          ((envAt t i).loc (d.traceWidth + 43 + 31))
    ∧ (envAt t i).loc (d.traceWidth + 86 + 38)
      = caveatCommit hash (manifestAt (d.traceWidth + 86) (envAt t i).loc) :=
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
      (envAt t i).loc (d.traceWidth + 43 + B_STATE_COMMIT) = (envAt t i).pub (d.piCount + 1)
      ∧ (envAt t i).loc (d.traceWidth + 43 + B_COMMITTED_HEIGHT)
          = (envAt t i).pub (d.piCount + 2)
      ∧ (envAt t i).loc (d.traceWidth + 86 + C_COMMIT) = (envAt t i).pub (d.piCount + 3)) := by
  have h := graduateV1_sound hash (rotateV3 d) minit mfin maddrs t hchip hrange
    (graduable_rotateV3 hgrad) hsat i hi
  have hmem : ∀ c ∈ rotPins d.traceWidth d.piCount, c ∈ (rotateV3 d).constraints :=
    fun c hc => List.mem_append_right _ (List.mem_append_right _ hc)
  have h0 := h.1 _ (hmem (.piBinding .first (d.traceWidth + B_STATE_COMMIT) d.piCount)
    (by simp [rotPins]))
  have h1 := h.1 _ (hmem (.piBinding .last (d.traceWidth + 43 + B_STATE_COMMIT)
    (d.piCount + 1)) (by simp [rotPins]))
  have h2 := h.1 _ (hmem (.piBinding .last (d.traceWidth + 43 + B_COMMITTED_HEIGHT)
    (d.piCount + 2)) (by simp [rotPins]))
  have h3 := h.1 _ (hmem (.piBinding .last (d.traceWidth + 86 + C_COMMIT) (d.piCount + 3))
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
      ∧ (envAt t i).loc (d.traceWidth + 31) = (envAt t' j).loc (d.traceWidth + 31))
    ∧ (preLimbsAt (d.traceWidth + 43) (envAt t k).loc
        = preLimbsAt (d.traceWidth + 43) (envAt t' l).loc
      ∧ (envAt t k).loc (d.traceWidth + 43 + 31) = (envAt t' l).loc (d.traceWidth + 43 + 31)
      ∧ (envAt t k).pub (d.piCount + 2) = (envAt t' l).pub (d.piCount + 2))
    ∧ manifestAt (d.traceWidth + 86) (envAt t k).loc
        = manifestAt (d.traceWidth + 86) (envAt t' l).loc := by
  have hp := rotV3_pins hash d minit mfin maddrs t hchip hrange hgrad hsat
  have hp' := rotV3_pins hash d minit' mfin' maddrs' t' hchip' hrange' hgrad hsat'
  have hq := rotV3_publishes hash d minit mfin maddrs t hchip hrange hgrad hsat
  have hq' := rotV3_publishes hash d minit' mfin' maddrs' t' hchip' hrange' hgrad hsat'
  refine ⟨?_, ?_, ?_⟩
  · -- the before block, via the first-row pins
    have hc := (hq i hi).1 hfirst
    have hc' := (hq' j hj).1 hfirst'
    have hwire : wireCommitR hash (preLimbsAt d.traceWidth (envAt t i).loc)
        ((envAt t i).loc (d.traceWidth + 31))
        = wireCommitR hash (preLimbsAt d.traceWidth (envAt t' j).loc)
            ((envAt t' j).loc (d.traceWidth + 31)) := by
      rw [← (hp i hi).1, ← (hp' j hj).1]
      show (envAt t i).loc (d.traceWidth + B_STATE_COMMIT)
        = (envAt t' j).loc (d.traceWidth + B_STATE_COMMIT)
      rw [hc, hc', hpubOld]
    exact wireCommitR_binds hash hCR
      (by rw [preLimbsAt_length, preLimbsAt_length]) hwire
  · -- the after block, via the last-row pins
    obtain ⟨hc, hh, -⟩ := (hq k hk).2 hlast
    obtain ⟨hc', hh', -⟩ := (hq' l hl).2 hlast'
    have hwire : wireCommitR hash (preLimbsAt (d.traceWidth + 43) (envAt t k).loc)
        ((envAt t k).loc (d.traceWidth + 43 + 31))
        = wireCommitR hash (preLimbsAt (d.traceWidth + 43) (envAt t' l).loc)
            ((envAt t' l).loc (d.traceWidth + 43 + 31)) := by
      rw [← (hp k hk).2.1, ← (hp' l hl).2.1]
      show (envAt t k).loc (d.traceWidth + 43 + B_STATE_COMMIT)
        = (envAt t' l).loc (d.traceWidth + 43 + B_STATE_COMMIT)
      rw [hc, hc', hpubNew]
    obtain ⟨hpre, hir⟩ := wireCommitR_binds hash hCR
      (by rw [preLimbsAt_length, preLimbsAt_length]) hwire
    refine ⟨hpre, hir, ?_⟩
    rw [← hh, ← hh']
    exact congrArg (fun L => L.getD 30 0) hpre
  · -- the caveat manifest, via the last-row pin
    obtain ⟨-, -, hk1⟩ := (hq k hk).2 hlast
    obtain ⟨-, -, hk2⟩ := (hq' l hl).2 hlast'
    have hcc : caveatCommit hash (manifestAt (d.traceWidth + 86) (envAt t k).loc)
        = caveatCommit hash (manifestAt (d.traceWidth + 86) (envAt t' l).loc) := by
      rw [← (hp k hk).2.2, ← (hp' l hl).2.2]
      show (envAt t k).loc (d.traceWidth + 86 + C_COMMIT)
        = (envAt t' l).loc (d.traceWidth + 86 + C_COMMIT)
      rw [hk1, hk2, hpubCav]
    exact caveatCommit_binds hash hCR hcc

#assert_axioms rotV3_sound_v1
#assert_axioms rotV3_pins
#assert_axioms rotV3_publishes
#assert_axioms rotV3_binds_published

/-! ## §5 — the v3 registry: all 26 cohort members, rotated. -/

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

/-- The rotated dynamic setField WITH its memory ops (the Blum write→read transport). -/
def setFieldDynV3 : EffectVmDescriptor2 :=
  v3OfWith setFieldDynV1Face [.memOp fieldWriteOp, .memOp fieldReadbackOp]

/-- **`v3Registry`** — the full 26-member cohort at the rotated block (keys = the v2 keys
suffixed `R24`; wire strings via `emitVmJson2`; driver `EmitRotationV3.lean`). -/
def v3Registry : List (String × EffectVmDescriptor2) :=
  [ ("transferVmDescriptor2R24", v3Of EffectVmEmitTransfer.transferVmDescriptor)
  , ("burnVmDescriptor2R24", v3Of EffectVmEmitBurn.burnVmDescriptor)
  , ("mintVmDescriptor2R24", v3Of EffectVmEmitMint.mintVmDescriptor)
  , ("noteSpendVmDescriptor2R24", v3Of EffectVmEmitNoteSpend.noteSpendVmDescriptor)
  , ("noteCreateVmDescriptor2R24", v3Of EffectVmEmitNoteCreate.noteCreateVmDescriptor)
  , ("cellSealVmDescriptor2R24", v3Of EffectVmEmitCellSeal.cellSealVmDescriptor)
  , ("cellDestroyVmDescriptor2R24", v3Of EffectVmEmitCellDestroy.cellDestroyVmDescriptor)
  , ("refusalVmDescriptor2R24", v3Of EffectVmEmitRefusal.refusalVmDescriptor)
  , ("setPermsVmDescriptor2R24", v3Of EffectVmEmitSetPermissions.setPermsVmDescriptor)
  , ("setVKVmDescriptor2R24", v3Of EffectVmEmitSetVK.setVKVmDescriptor)
  , ("exerciseVmDescriptor2R24", v3Of EffectVmEmitExercise.exerciseVmDescriptor)
  , ("pipelinedSendVmDescriptor2R24", v3Of EffectVmEmitPipelinedSend.pipelinedSendVmDescriptor)
  , ("refreshVmDescriptor2R24", v3Of EffectVmEmitRefreshDelegation.refreshVmDescriptor)
  , ("incrementNonceVmDescriptor2R24",
      v3Of EffectVmEmitIncrementNonce.incrementNonceVmDescriptor)
  , ("revokeVmDescriptor2R24", v3Of EffectVmEmitRevokeDelegation.revokeVmDescriptor)
  , ("introduceVmDescriptor2R24", v3Of EffectVmEmitIntroduce.introduceVmDescriptor)
  , ("attenuateVmDescriptor2R24", attenuateV3)
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
  , ("createCellVmDescriptor2R24", v3Of EffectVmEmitCreateCell.createCellActorVmDescriptor)
  , ("factoryVmDescriptor2R24",
      v3Of EffectVmEmitCreateCellFromFactory.factoryActorVmDescriptor)
  , ("spawnVmDescriptor2R24", v3Of EffectVmEmitSpawn.spawnActorVmDescriptor)
  , ("receiptArchiveVmDescriptor2R24",
      v3Of EffectVmEmitReceiptArchive.receiptArchiveActorVmDescriptor)
  , ("cellUnsealVmDescriptor2R24", v3Of EffectVmEmitCellUnseal.cellUnsealVmDescriptor)
  , ("emitEventVmDescriptor2R24", v3Of EffectVmEmitEmitEvent.emitEventVmDescriptor) ]
  ++ (List.finRange 8).map fun slot =>
      (s!"setFieldVmDescriptor2-{slot.val}R24",
        v3Of (EffectVmEmitSetField.setFieldVmDescriptor slot))

#guard v3Registry.length == 34
-- Every registry entry emits a versioned v2 wire string with the rotated width, the five
-- EPOCH tables, and the four appended PI slots.
#guard v3Registry.all fun (_, d) => (emitVmJson2 d).startsWith "{\"name\":\""
#guard v3Registry.all fun (_, d) => d.traceWidth == EFFECT_VM_WIDTH + APPENDIX_SPAN
#guard v3Registry.all fun (_, d) => d.tables.length == 5
#guard v3Registry.all fun (_, d) => d.hashSites.length == 0 && d.ranges.length == 0
-- The rotated transfer: the v1 graduation's constraints + 24 welds + 4 pins + 32 chip sites.
#guard (v3Of EffectVmEmitTransfer.transferVmDescriptor).constraints.length
        == transferVmDescriptor2.constraints.length + 24 + 4 + 32
#guard (v3Of EffectVmEmitTransfer.transferVmDescriptor).piCount == 34 + 4
-- The graduation side conditions hold on every v1-faced member (per-instance witnesses of
-- the parametric `graduable_rotateV3`; attenuate/setFieldDyn ride `v3OfWith` over faces
-- checked here too).
#guard graduable (rotateV3 EffectVmEmitTransfer.transferVmDescriptor)
#guard graduable (rotateV3 setFieldDynV1Face)
#guard graduable (rotateV3 EffectVmEmitAttenuateA.attenuateVmDescriptor)
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
-- The extras ride: attenuate carries its 3 phase-B constraints, setFieldDyn its 2 mem ops.
#guard attenuateV3.constraints.length
        == (v3Of EffectVmEmitAttenuateA.attenuateVmDescriptor).constraints.length + 3
#guard (memOpsOf setFieldDynV3).length == 2
#guard (mapOpsOf setFieldDynV3).length == 0
#guard (mapOpsOf attenuateV3).length == 2

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

#assert_axioms setFieldDynV3_memLog
#assert_axioms setFieldDynV3_readback_genuine
#assert_axioms attenuateV3_non_amp

-- NON-VACUITY of the bound block, executable (Horner toy sponge): moving the heap-root limb
-- (offset 27) or the iroot moves the chained commitment the appendix pins.
#guard wireCommitR refSponge ((List.range 31).map (fun i => (300 + i : ℤ))) 7
  != wireCommitR refSponge (((List.range 31).map (fun i => (300 + i : ℤ))).set 27 999) 7
#guard wireCommitR refSponge ((List.range 31).map (fun i => (300 + i : ℤ))) 7
  != wireCommitR refSponge ((List.range 31).map (fun i => (300 + i : ℤ))) 8

end Dregg2.Circuit.Emit.EffectVmEmitRotationV3
