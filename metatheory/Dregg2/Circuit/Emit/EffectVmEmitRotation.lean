/-
# Dregg2.Circuit.Emit.EffectVmEmitRotation — the ROTATED STATE BLOCK, emitted (staged).

`Circuit/RotationLayout.lean` pins the rotation's COMMITMENT shape (`RotatedLimbs` — 23 named
limbs, receipt-index root literally last, `rotatedCommit_binds` the anti-ghost keystone). THIS
module propagates that shape onto the WIRE, staged behind the IR-v2 recursion-gated path
(`docs/UNIVERSAL-MAP-ROTATION.md` §2.1/§2.4/§2.6 → the layout flag-day; cutover =
`docs/ROTATION-CUTOVER.md`). The live v1 registry is untouched — nothing here rides the wire
until the flag-day regen.

  * **§1 the rotated state BLOCK** — the 25-slot column block (`BLOCK_SIZE`): the 23
    `RotatedLimbs` limbs in `RotatedLimbs.toList` order at offsets `0..22`, the `IROOT` carrier
    (the receipt-index MMR root limb) at 23, `STATE_COMMIT` at 24. The block IS the absorption
    order (`absorbCols = List.range 24` — positional, nothing hides); `readLimbs_spec` welds the
    column reader to `RotatedLimbs.toList ++ [iroot]` BY `rfl`. NOTE deliberately absent: the
    obsolete 186-wide fan-out is NOT widened to carry this block — `EPOCH-DESIGN.md` makes the
    post-LogUp main table far thinner, so the staged probe trace is the block + chain carriers
    alone; the flag-day regen decides the final main-table packing.
  * **§2 `wireCommit`** — the CHAINED realization of `rotatedCommit`'s abstract sponge:
    9 chip absorptions (7 arity-4 + 2 arity-2 = 24 limbs; the deployed chip pins arity ∈
    {2,4}, and the arity-2 tail keeps the iroot LITERALLY LAST), each a REAL `babyBearD4W16`
    permutation row in the IR-v2 chip table. `wireCommit_binds` re-proves the anti-ghost keystone for the
    CHAINED shape under the same ONE CR floor (peel 8 collisions): equal wire commits force
    equal `RotatedLimbs` AND equal iroot; `wireCommit_binds_log` composes `mroot_injective` so
    the whole receipt log is bound (tamper/truncate/extend/reorder all move the commit);
    `wireCommit_binds_named_field` carries the `FactoryDescriptor.fields` weld.
  * **§3/§4 the PROBE descriptor** — `rotationProbeVmDescriptor2` (graduated IR-v2, the five
    EPOCH tables): the 9 chained hash sites as chip lookups + the two PI pins (published rotated
    commit at `PUB_COMMIT`, the `committedHeight` limb at `PUB_HEIGHT` — the PI-v3 face).
    `rotationProbeV2_pins_commit` (via `graduateV1_sound`) forces `STATE_COMMIT` to the genuine
    chained absorption on EVERY row; `rotationProbe_commit_binds_published` is the end-to-end
    keystone: two satisfying traces publishing the SAME commit agree on the WHOLE rotated block,
    the iroot, and the published height — `committed_height_not_prover_chosen` in wire form.
  * **§5 the staged wire artifacts** — `rotationLayoutManifest` (byte-pinned JSON, the Rust
    drift-guard twin reconstructs it from `circuit/src/effect_vm/columns.rs::rotation`) +
    the probe JSON via `emitVmJson2` (driver: `EmitRotationV3.lean` →
    `circuit/descriptors/rotation-layout-v3-staged.json` /
    `dregg-effectvm-rotation-state-v3-staged.json`).

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; crypto only as the named
`Poseidon2SpongeCR` hypothesis. No `sorry`, no `native_decide`. Staged: no live Rust path
consumes these artifacts until the cutover commit (the Rust consumers are recursion-gated
tests + the drift guards).
-/
import Dregg2.Circuit.RotationLayout
import Dregg2.Circuit.Emit.EffectVmEmitV2

namespace Dregg2.Circuit.Emit.EffectVmEmitRotation

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitV2
open Dregg2.Circuit.RotationLayout
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Lightclient.MMR (mroot mroot_injective demoLog)
open Dregg2.Substrate.Heap (refSponge)

set_option autoImplicit false

/-! ## §1 — the rotated state block: 25 slots, absorption-ordered. -/

/-- The cells-root limb column. -/
def CELLS_ROOT : Nat := 0
/-- The register file base: register `i` at `REG_BASE + i`, `i < NUM_REGISTERS` (= 16). -/
def REG_BASE : Nat := 1
/-- The cap-map root limb column (the map roots ADJACENT AND UNIFORM — `EPOCH-DESIGN.md`). -/
def CAP_ROOT : Nat := 17
/-- The nullifier-map root limb column. -/
def NULLIFIER_ROOT : Nat := 18
/-- The heap-map root limb column (§2.4 — the rotation's `heap_root` limb). -/
def HEAP_ROOT : Nat := 19
/-- The lifecycle scalar limb column. -/
def LIFECYCLE : Nat := 20
/-- The epoch scalar limb column. -/
def EPOCH : Nat := 21
/-- The committed-height scalar limb column (§2.6 — the PI-v3 limb). -/
def COMMITTED_HEIGHT : Nat := 22
/-- The receipt-index MMR root carrier (`iroot = mroot log`), absorbed literally LAST. -/
def IROOT : Nat := 23
/-- The rotated state commitment carrier (the chained absorption's final digest). -/
def STATE_COMMIT : Nat := 24
/-- The rotated state block width: 23 limbs + iroot + state_commit. -/
def BLOCK_SIZE : Nat := 25

/-- The chained-absorption intermediate-digest carriers (8, one per non-final site). -/
def CHAIN_BASE : Nat := 25
/-- Number of chain carriers (9 sites: 7 arity-4 + 2 arity-2; the deployed chip pins
arity ∈ {2, 4}, so the tail rides two arity-2 absorptions — `committedHeight`, then the
iroot LITERALLY LAST, preserving the `CommitBindsMMR` last-limb discipline in wire form). -/
def NUM_CHAIN : Nat := 8
/-- Chain carrier `k`'s column. -/
def chainCol (k : Nat) : Nat := CHAIN_BASE + k
/-- The staged probe trace width: the rotated block + the chain carriers. -/
def PROBE_WIDTH : Nat := 33

/-- A named register's column. -/
def regCol (i : Fin NUM_REGISTERS) : Nat := REG_BASE + i.val

/-- Every register column sits strictly inside the register sub-block (below the map roots). -/
theorem regCol_lt_capRoot (i : Fin NUM_REGISTERS) : regCol i < CAP_ROOT := by
  have := i.isLt
  simp only [regCol, REG_BASE, CAP_ROOT, NUM_REGISTERS] at *
  omega

/-- **The absorption order** — the columns `recStateCommit`'s rotated realization absorbs, in
order. The block layout IS the absorption order (positional: `List.range 24`). -/
def absorbCols : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

theorem absorbCols_is_positional : absorbCols = List.range 24 := by decide

theorem absorbCols_length : absorbCols.length = 24 := by decide

/-- The absorb order names exactly: cells root · the 16 registers · cap/nullifier/heap roots
adjacent · lifecycle · epoch · committed height · iroot LAST. -/
theorem absorbCols_named :
    absorbCols
      = [CELLS_ROOT] ++ ((List.range NUM_REGISTERS).map (REG_BASE + ·))
        ++ [CAP_ROOT, NULLIFIER_ROOT, HEAP_ROOT, LIFECYCLE, EPOCH, COMMITTED_HEIGHT, IROOT] := by
  decide

/-- Read the rotated block off a row into the PROVEN commitment payload (`RotatedLimbs`). -/
def blockLimbs (a : Assignment) : RotatedLimbs :=
  { cellsRoot := a CELLS_ROOT
  , r0 := a 1,  r1 := a 2,  r2 := a 3,  r3 := a 4
  , r4 := a 5,  r5 := a 6,  r6 := a 7,  r7 := a 8
  , r8 := a 9,  r9 := a 10, r10 := a 11, r11 := a 12
  , r12 := a 13, r13 := a 14, r14 := a 15, r15 := a 16
  , capRoot := a CAP_ROOT, nullifierRoot := a NULLIFIER_ROOT, heapRoot := a HEAP_ROOT
  , lifecycle := a LIFECYCLE, epoch := a EPOCH, committedHeight := a COMMITTED_HEIGHT }

/-- **The layout weld**: reading the absorb columns yields EXACTLY `RotatedLimbs.toList ++
[iroot]` — the column layout realizes the proven commitment payload, definitionally. -/
theorem readLimbs_spec (a : Assignment) :
    absorbCols.map a = (blockLimbs a).toList ++ [a IROOT] := rfl

/-- A declared register column reads back the resolved `RotatedLimbs.reg` — the
`FactoryDescriptor.fields` resolution lands on the commitment-carried register. -/
theorem regCol_reads_reg (a : Assignment) (i : Fin NUM_REGISTERS) :
    a (regCol i) = (blockLimbs a).reg i := by
  fin_cases i <;> rfl

/-! ## §2 — `wireCommit`: the 4-ary chained realization of the rotated commitment.

`rotatedCommit` is ONE abstract sponge over `toList ++ [iroot]` (24 limbs). The deployed chip
absorbs at arity ∈ {2, 4} per permutation (`hash_many`'s arity-tag discipline, pinned by the
chip AIR), so the wire realization is the 9-site CHAIN below: 7 arity-4 sites (4 + 3·6 = 22
limbs) + 2 arity-2 sites (`committedHeight`, then the iroot LITERALLY LAST). The anti-ghost
keystone is RE-PROVED for the chained shape — no axiom bridges the two realizations; each
carries its own CR-floor proof. -/

/-- The chained rotated commitment: 9 absorptions, 4 + 3·6 + 1 + 1 = 24 limbs, iroot LAST. -/
def wireCommit (hash : List ℤ → ℤ) (s : RotatedLimbs) (ir : ℤ) : ℤ :=
  hash [hash [hash [hash [hash [hash [hash [hash [hash [s.cellsRoot, s.r0, s.r1, s.r2],
    s.r3, s.r4, s.r5], s.r6, s.r7, s.r8], s.r9, s.r10, s.r11], s.r12, s.r13, s.r14],
    s.r15, s.capRoot, s.nullifierRoot], s.heapRoot, s.lifecycle, s.epoch],
    s.committedHeight], ir]

/-- **THE CHAINED ANTI-GHOST KEYSTONE.** Under the ONE named CR floor, equal wire commits force
equal limb structures AND equal iroots — every register (including the widened `r8..r15`), every
map root (including `heap_root`), the height, and the receipt-index root are bound by the
chained shape exactly as `rotatedCommit_binds` binds the one-shot shape. -/
theorem wireCommit_binds (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {s s' : RotatedLimbs} {ir ir' : ℤ}
    (h : wireCommit hash s ir = wireCommit hash s' ir') : s = s' ∧ ir = ir' := by
  simp only [wireCommit] at h
  have h8 := hCR _ _ h
  simp only [List.cons.injEq, and_true] at h8
  obtain ⟨h7eq, hir⟩ := h8
  have h7 := hCR _ _ h7eq
  simp only [List.cons.injEq, and_true] at h7
  obtain ⟨h6, hch⟩ := h7
  have h6' := hCR _ _ h6
  simp only [List.cons.injEq, and_true] at h6'
  obtain ⟨h5, hhr, hlc, hep⟩ := h6'
  have h5' := hCR _ _ h5
  simp only [List.cons.injEq, and_true] at h5'
  obtain ⟨h4, hr15, hcr, hnr⟩ := h5'
  have h4' := hCR _ _ h4
  simp only [List.cons.injEq, and_true] at h4'
  obtain ⟨h3, hr12, hr13, hr14⟩ := h4'
  have h3' := hCR _ _ h3
  simp only [List.cons.injEq, and_true] at h3'
  obtain ⟨h2, hr9, hr10, hr11⟩ := h3'
  have h2' := hCR _ _ h2
  simp only [List.cons.injEq, and_true] at h2'
  obtain ⟨h1, hr6, hr7, hr8⟩ := h2'
  have h1' := hCR _ _ h1
  simp only [List.cons.injEq, and_true] at h1'
  obtain ⟨h0, hr3, hr4, hr5⟩ := h1'
  have h0' := hCR _ _ h0
  simp only [List.cons.injEq, and_true] at h0'
  obtain ⟨hcl, hr0, hr1, hr2⟩ := h0'
  refine ⟨RotatedLimbs.toList_injective ?_, hir⟩
  simp only [RotatedLimbs.toList]
  rw [hcl, hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13, hr14,
    hr15, hcr, hnr, hhr, hlc, hep, hch]

/-- The `heap_root` tooth, chained form: equal wire commits force equal heap roots. -/
theorem wireCommit_binds_heapRoot (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {s s' : RotatedLimbs} {ir ir' : ℤ}
    (h : wireCommit hash s ir = wireCommit hash s' ir') : s.heapRoot = s'.heapRoot :=
  congrArg RotatedLimbs.heapRoot (wireCommit_binds hash hCR h).1

/-- The widened-register tooth, chained form: EVERY register limb is bound. -/
theorem wireCommit_binds_reg (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {s s' : RotatedLimbs} {ir ir' : ℤ}
    (h : wireCommit hash s ir = wireCommit hash s' ir') (i : Fin NUM_REGISTERS) :
    s.reg i = s'.reg i :=
  congrArg (fun t => RotatedLimbs.reg t i) (wireCommit_binds hash hCR h).1

/-- The named-field weld, chained form: a declared field name's register VALUE is bound by the
wire commitment (`resolve` ∘ `wireCommit_binds_reg`). -/
theorem wireCommit_binds_named_field (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {s s' : RotatedLimbs} {ir ir' : ℤ} {names : List String} {n : String}
    {i : Fin NUM_REGISTERS}
    (_hres : resolve names n = some i)
    (h : wireCommit hash s ir = wireCommit hash s' ir') : s.reg i = s'.reg i :=
  wireCommit_binds_reg hash hCR h i

/-- The log tooth, chained form: with `ir := mroot log`, equal wire commits force EQUAL receipt
logs (tamper / truncate / extend / REORDER all refused via `mroot_injective`). -/
theorem wireCommit_binds_log (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {s s' : RotatedLimbs} {L L' : List ℤ}
    (h : wireCommit hash s (mroot hash L) = wireCommit hash s' (mroot hash L')) : L = L' :=
  mroot_injective hash hCR (wireCommit_binds hash hCR h).2

#assert_axioms wireCommit_binds
#assert_axioms wireCommit_binds_heapRoot
#assert_axioms wireCommit_binds_reg
#assert_axioms wireCommit_binds_named_field
#assert_axioms wireCommit_binds_log

-- NON-VACUITY, both polarities, executable (the Horner toy sponge; deployment = the audited
-- p3 Poseidon2 under the same CR-floor hypothesis). Every tamper class moves the wire commit.
#guard wireCommit refSponge demoLimbs (mroot refSponge demoLog)
  != wireCommit refSponge { demoLimbs with heapRoot := 99 } (mroot refSponge demoLog)
#guard wireCommit refSponge demoLimbs (mroot refSponge demoLog)
  != wireCommit refSponge { demoLimbs with r15 := 999 } (mroot refSponge demoLog)
#guard wireCommit refSponge demoLimbs (mroot refSponge demoLog)
  != wireCommit refSponge { demoLimbs with committedHeight := 43 } (mroot refSponge demoLog)
#guard wireCommit refSponge demoLimbs (mroot refSponge demoLog)
  != wireCommit refSponge { demoLimbs with nullifierRoot := 99 } (mroot refSponge demoLog)
#guard wireCommit refSponge demoLimbs (mroot refSponge demoLog)
  != wireCommit refSponge demoLimbs (mroot refSponge (demoLog ++ [444]))
#guard wireCommit refSponge demoLimbs (mroot refSponge demoLog)
  != wireCommit refSponge demoLimbs (mroot refSponge (demoLog.take 2))
#guard wireCommit refSponge demoLimbs (mroot refSponge demoLog)
  != wireCommit refSponge demoLimbs (mroot refSponge [222, 111, 333])
-- The honest recompute is stable (the positive polarity).
#guard wireCommit refSponge demoLimbs (mroot refSponge demoLog)
  == wireCommit refSponge demoLimbs (mroot refSponge [111, 222, 333])

/-! ## §3 — the 8 chained hash sites (the wire form of `wireCommit`). -/

/-- The rotated absorption as ORDERED hash sites: site `k < 8`'s digest rides chain carrier
`k`; the FINAL site's digest is `STATE_COMMIT`. Digest chaining via `.digest k` (the
`sitesWF` discipline — every reference strictly earlier). -/
def rotationSites : List VmHashSite :=
  [ ⟨chainCol 0, [.col CELLS_ROOT, .col 1, .col 2, .col 3], 4⟩
  , ⟨chainCol 1, [.digest 0, .col 4, .col 5, .col 6], 4⟩
  , ⟨chainCol 2, [.digest 1, .col 7, .col 8, .col 9], 4⟩
  , ⟨chainCol 3, [.digest 2, .col 10, .col 11, .col 12], 4⟩
  , ⟨chainCol 4, [.digest 3, .col 13, .col 14, .col 15], 4⟩
  , ⟨chainCol 5, [.digest 4, .col 16, .col CAP_ROOT, .col NULLIFIER_ROOT], 4⟩
  , ⟨chainCol 6, [.digest 5, .col HEAP_ROOT, .col LIFECYCLE, .col EPOCH], 4⟩
  , ⟨chainCol 7, [.digest 6, .col COMMITTED_HEIGHT], 2⟩
  , ⟨STATE_COMMIT, [.digest 7, .col IROOT], 2⟩ ]

/-- The sites pin the wire commitment: a row satisfying the ordered site walk carries
`STATE_COMMIT = wireCommit` of its OWN limbs and iroot. (The walk's accumulator recomputes
each digest genuinely, so the final conjunct IS the chained commitment, definitionally.) -/
theorem rotationSites_pin (hash : List ℤ → ℤ) (env : VmRowEnv)
    (h : siteHoldsAll hash env rotationSites) :
    env.loc STATE_COMMIT = wireCommit hash (blockLimbs env.loc) (env.loc IROOT) := by
  obtain ⟨-, -, -, -, -, -, -, -, h8, -⟩ := h
  exact h8

#assert_axioms rotationSites_pin

/-! ## §4 — the staged PROBE descriptor (graduated IR-v2). -/

/-- The published-commit PI slot. -/
def PUB_COMMIT : Nat := 0
/-- The published committed-height PI slot (the PI-v3 `COMMITTED_HEIGHT` face, probe-local). -/
def PUB_HEIGHT : Nat := 1

/-- The v1-grammar probe: the 8 chained sites + the two last-row PI pins. -/
def rotationProbeVmDescriptor : EffectVmDescriptor :=
  { name        := "dregg-effectvm-rotation-state-v3-staged"
  , traceWidth  := PROBE_WIDTH
  , piCount     := 2
  , constraints :=
      [ .piBinding .last STATE_COMMIT PUB_COMMIT
      , .piBinding .last COMMITTED_HEIGHT PUB_HEIGHT ]
  , hashSites   := rotationSites
  , ranges      := [] }

/-- **The staged IR-v2 probe** — `graduateV1` of the rotation probe: the 8 sites become chip
lookups (every absorption a REAL permutation row), the five EPOCH tables declared, no legacy
carriers. This is the descriptor `EmitRotationV3.lean` emits for the recursion-gated Rust path. -/
def rotationProbeVmDescriptor2 : EffectVmDescriptor2 :=
  graduateV1 rotationProbeVmDescriptor

#guard graduable rotationProbeVmDescriptor
#guard rotationProbeVmDescriptor2.constraints.length == 2 + 9
#guard rotationProbeVmDescriptor2.tables.length == 5
#guard rotationProbeVmDescriptor2.hashSites.length == 0
#guard (emitVmJson2 rotationProbeVmDescriptor2).startsWith "{\"name\":\""

/-- The probe pins the rotated commitment on EVERY row of a `Satisfied2` witness (sound chip
table, faithful range table): `STATE_COMMIT` is the genuine chained absorption of the row's
own 24 limbs. -/
theorem rotationProbeV2_pins_commit (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hf : Satisfied2Faithful permOut hash rotationProbeVmDescriptor2 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    (envAt t i).loc STATE_COMMIT
      = wireCommit hash (blockLimbs (envAt t i).loc) ((envAt t i).loc IROOT) := by
  have h := satisfied2Faithful_satisfiedVm permOut hash rotationProbeVmDescriptor
    minit mfin maddrs t (by decide) hf i hi
  exact rotationSites_pin hash _ h.2.1

/-- The probe PUBLISHES: on the last row, PI `PUB_COMMIT` carries the rotated commitment and
PI `PUB_HEIGHT` carries the `committedHeight` limb (the `BindsCommittedHeight` shape). -/
theorem rotationProbeV2_publishes (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hf : Satisfied2Faithful permOut hash rotationProbeVmDescriptor2 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hlast : i + 1 = t.rows.length) :
    (envAt t i).loc STATE_COMMIT = (envAt t i).pub PUB_COMMIT
    ∧ (envAt t i).loc COMMITTED_HEIGHT = (envAt t i).pub PUB_HEIGHT := by
  have h := satisfied2Faithful_satisfiedVm permOut hash rotationProbeVmDescriptor
    minit mfin maddrs t (by decide) hf i hi
  have h1 := h.1 (.piBinding .last STATE_COMMIT PUB_COMMIT)
    (by simp [rotationProbeVmDescriptor])
  have h2 := h.1 (.piBinding .last COMMITTED_HEIGHT PUB_HEIGHT)
    (by simp [rotationProbeVmDescriptor])
  simp only [VmConstraint.holdsVm] at h1 h2
  exact ⟨h1 (by simp [hlast]), h2 (by simp [hlast])⟩

/-- **THE END-TO-END STAGED KEYSTONE.** Two `Satisfied2` probe witnesses publishing the SAME
commit agree on the WHOLE rotated block (every register incl. `r8..r15`, every map root incl.
`heap_root`, lifecycle/epoch/height), the receipt-index root, AND the published height — the
anti-ghost + `committed_height_not_prover_chosen` closure, in wire form, under the ONE CR
floor. -/
theorem rotationProbe_commit_binds_published (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (minit' : ℤ → ℤ) (mfin' : ℤ → ℤ × Nat) (maddrs' : List ℤ) (t' : VmTrace)
    (hf : Satisfied2Faithful permOut hash rotationProbeVmDescriptor2 minit mfin maddrs t)
    (hf' : Satisfied2Faithful permOut hash rotationProbeVmDescriptor2 minit' mfin' maddrs' t')
    (i j : Nat) (hi : i < t.rows.length) (hj : j < t'.rows.length)
    (hlast : i + 1 = t.rows.length) (hlast' : j + 1 = t'.rows.length)
    (hpub : (envAt t i).pub PUB_COMMIT = (envAt t' j).pub PUB_COMMIT) :
    blockLimbs (envAt t i).loc = blockLimbs (envAt t' j).loc
    ∧ (envAt t i).loc IROOT = (envAt t' j).loc IROOT
    ∧ (envAt t i).pub PUB_HEIGHT = (envAt t' j).pub PUB_HEIGHT := by
  obtain ⟨hc, hh⟩ := rotationProbeV2_publishes permOut hash minit mfin maddrs t
    hf i hi hlast
  obtain ⟨hc', hh'⟩ := rotationProbeV2_publishes permOut hash minit' mfin' maddrs' t'
    hf' j hj hlast'
  have hp := rotationProbeV2_pins_commit permOut hash minit mfin maddrs t hf i hi
  have hp' := rotationProbeV2_pins_commit permOut hash minit' mfin' maddrs' t' hf' j hj
  have hwire : wireCommit hash (blockLimbs (envAt t i).loc) ((envAt t i).loc IROOT)
      = wireCommit hash (blockLimbs (envAt t' j).loc) ((envAt t' j).loc IROOT) := by
    rw [← hp, ← hp', hc, hc', hpub]
  obtain ⟨hblk, hir⟩ := wireCommit_binds hash hCR hwire
  refine ⟨hblk, hir, ?_⟩
  rw [← hh, ← hh']
  exact congrArg RotatedLimbs.committedHeight hblk

#assert_axioms rotationProbeV2_pins_commit
#assert_axioms rotationProbeV2_publishes
#assert_axioms rotationProbe_commit_binds_published

/-! ## §5 — the staged wire artifacts (manifest + probe JSON). -/

/-- **The rotation layout manifest** — the staged layout as JSON, built FROM the defs (it
cannot drift from the constants this module proves about). The Rust twin
(`columns.rs::rotation` + `rotation_layout_matches_lean` in `effect_vm_descriptors.rs`)
reconstructs the SAME bytes from its constants and compares against the committed file —
both sides pin, neither parses. -/
def rotationLayoutManifest : String :=
  s!"\{\"v\":\"dregg-rotation-layout-v3-staged\",\"block_size\":{BLOCK_SIZE}" ++
  s!",\"cells_root\":{CELLS_ROOT},\"reg_base\":{REG_BASE},\"num_registers\":{NUM_REGISTERS}" ++
  s!",\"cap_root\":{CAP_ROOT},\"nullifier_root\":{NULLIFIER_ROOT},\"heap_root\":{HEAP_ROOT}" ++
  s!",\"lifecycle\":{LIFECYCLE},\"epoch\":{EPOCH},\"committed_height\":{COMMITTED_HEIGHT}" ++
  s!",\"iroot\":{IROOT},\"state_commit\":{STATE_COMMIT},\"chain_base\":{CHAIN_BASE}" ++
  s!",\"num_chain\":{NUM_CHAIN},\"probe_width\":{PROBE_WIDTH},\"chain_arity\":4" ++
  s!",\"pi_v3\":\{\"v2_base_count\":{PiV3.V2_BASE_COUNT}" ++
  s!",\"committed_height\":{PiV3.COMMITTED_HEIGHT},\"rate_bound_tag\":{PiV3.RATE_BOUND_TAG}" ++
  s!",\"challenge_window_tag\":{PiV3.CHALLENGE_WINDOW_TAG}}}"

-- The byte pin (the golden the committed `rotation-layout-v3-staged.json` must equal).
#guard rotationLayoutManifest ==
  "{\"v\":\"dregg-rotation-layout-v3-staged\",\"block_size\":25,\"cells_root\":0,\"reg_base\":1,\"num_registers\":16,\"cap_root\":17,\"nullifier_root\":18,\"heap_root\":19,\"lifecycle\":20,\"epoch\":21,\"committed_height\":22,\"iroot\":23,\"state_commit\":24,\"chain_base\":25,\"num_chain\":8,\"probe_width\":33,\"chain_arity\":4,\"pi_v3\":{\"v2_base_count\":209,\"committed_height\":209,\"rate_bound_tag\":210,\"challenge_window_tag\":211}}"

end Dregg2.Circuit.Emit.EffectVmEmitRotation
