/-
# Dregg2.Circuit.Emit.EffectVmEmitSwissExport — the CapTP sturdy-ref MINT `exportSturdyRefA`, EMITTED
  onto the runnable EffectVM `swiss_root` (digest) column, with the supported per-row faithfulness +
  anti-ghost commitment tooth + the connector to universe-A `swissExportA_full_sound`, and a PRECISE,
  LOUD flag of the IR-blocked guard/list-structure parts.

## The "ONE circuit" thesis for the swiss-table effects — and where the per-row IR STOPS

`exportSturdyRefA sw actor exporter target rights` MINTS a fresh sturdy ref: it GROWS the swiss-table
list `kernel.swiss` by `exportRecord sw exporter target rights`, prepends an authority receipt, and
freezes the 16 non-`swiss` kernel fields. The touched component is the `List SwissRecord` side-table
`swiss` (a `listComponent` over a FULL-list digest `listDigest LE cN`), GATED on a THREE-way guard
`ExportGuard` (AUTHORITY ∧ FRESHNESS ∧ NON-AMPLIFICATION). Its validation
`swissExportA_full_sound ⇒ ExportSpec` is DONE (`Inst/swissExportA.lean`).

The running EffectVM row (`circuit/src/effect_vm_p3_full_air.rs`, the 186-column `EffectVmP3Air`) has a
FIXED 14-column state block: two balance limbs, a nonce, eight content fields, ONE scalar `cap_root`
column (state offset 11, `state.CAP_ROOT`), a `state_commit`, and a `reserved`. The prover absorbs
`cap_root` into the GROUP-4 state-commitment chain (`site2` reads `saCol CAP_ROOT`). There is NO
per-row column for "the swiss-table list", "the swiss number `sw`", "the inserted record", or "the
3-way guard": the row layout is a per-cell SCALAR block, not a side-table with membership/freshness
structure.

So at the row level, the ONLY thing the per-row arithmetic IR can faithfully express of a swiss
effect is a SCALAR DIGEST-COLUMN MOVE: the post `swiss_root` digest is the digest of the post
swiss-list, every OTHER state column frozen, and the moved digest bound into the published
`state_commit` under Poseidon2 collision-resistance. We emit EXACTLY that — reusing the validated
`AttenuateA` `cap_root`-column-move template, with the `cap_root` column REINTERPRETED as carrying the
SWISS-TABLE digest for these `caps`-freezing swiss effects (export touches `caps` nowhere — `caps` is
in its frozen frame — so the `cap_root` state column is free to carry the swiss-table digest in this
swiss AIR variant). `swissExportVmDescriptor` pins the post `swiss_root` to a parameter
`paramSE.SWISS_DIGEST_NEW` (the runnable column the witness fills with `D (post.swiss)`), the move gate
is `new_swiss_root - swissDigestNew = 0`, the frame is frozen, and the GROUP-4 hash sites bind the
moved digest into `state_commit`. We PROVE: satisfying the descriptor pins the digest-column move ↔
the row intent `SwissExportRowIntent`; the commitment binds the WHOLE post-state (digest included), so
a tampered post-`swiss_root` claiming the published `NEW_COMMIT` is UNSAT (the anti-ghost tooth).

## The CONNECTOR — `swissRootProj` to universe-A's `swissExportA_full_sound`

`swissRootProj D k = D k.swiss` reads a whole-list digest `D : List SwissRecord → ℤ` of the swiss
side-table (the SAME measure universe-A's `swissComponent`'s `listDigest LE cN` digests, here packaged
as the single `D`). `unify_swissExport` shows: when universe-A's `ExportSpec` holds (so
`s'.kernel.swiss = exportRecord … :: s.kernel.swiss`), the projected post-`swiss_root` is EXACTLY
`D (exportRecord … :: s.kernel.swiss)` — the column move the descriptor pins. So the runnable
`swiss_root` column transition IS universe-A's `swiss`-digest transition; not a fourth spec.

## ===================  IR-BLOCKED — the precise asks  ===================

The per-row scalar IR CANNOT express (each FLAGGED, never faked):

  * **IR GAP 1 — the 3-way guard `ExportGuard` (AUTHORITY ∧ FRESHNESS ∧ NON-AMPLIFICATION).** These are
    SET-MEMBERSHIP / c-list predicates over `s.kernel.caps`, `s.kernel.swiss`, `heldAuths s.kernel
    exporter`. The EffectVM row has NO cap-graph columns, NO swiss-list columns, NO `findSwiss`/
    `rightsNarrowerOrEqual` gate. Universe-A commits the guard as a single `propBit` column
    (`exportGuardGates`); the per-row EffectVM IR has no `propBit` guard column and no way to RE-DERIVE
    the guard from row data. So the descriptor does NOT enforce the guard in-circuit; the guard's
    enforcement lives in universe-A's `swissExportA_full_sound` (carried). ASK: a `VmConstraint`
    guard-bit form (an extra selector-gated `propBit` column equal to `1`, decoded to the guard Prop
    out-of-band) would internalize the guard's PRESENCE; re-deriving the SET-MEMBERSHIP content
    in-circuit additionally needs a lookup/permutation argument the per-row IR lacks entirely.

  * **IR GAP 2 — the LIST STRUCTURE (which record was inserted, `swiss = exportRecord … :: pre`).** The
    `swiss_root` column carries only the SCALAR digest `D (post.swiss)`. The IR's `VmHashSite` absorbs
    trace COLUMNS only; it has NO site that re-derives `swiss_root` from a per-row SERIALIZATION of the
    `List SwissRecord` (the leaf hash `LE` of each record, folded by `cN`). So the descriptor pins the
    digest-column equality `new_swiss_root = D(post.swiss)` (witness-supplied), and binds THAT into
    `state_commit`, but does NOT prove in-circuit that `swiss_root` IS the genuine list digest, nor that
    the post-list is the pre-list with `exportRecord` consed. That binding lives in universe-A's
    `listLeafInjective LE` + `compressNInjective cN` portals (the realizable Poseidon-CR set). ASK: a
    `VmHashSite` that absorbs the swiss-list rows and outputs `swiss_root` (a Merkle-over-the-list
    gadget) would internalize the list digest; until then it is a NAMED hypothesis (`D`), not an
    in-circuit gate.

  * PER-CELL / PER-ROW. Single-row AIR + its binding into the published `state_commit`. Cross-row
    composition is the turn layer (`TurnEmit`), cited not claimed. `state.RESERVED` is absorbed by no
    hash-site (inherited keystone finding).

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. Poseidon2 CR enters ONLY
as the NAMED hypothesis `Poseidon2SpongeCR hash`; the swiss-list digest enters ONLY as the abstract
`D : List SwissRecord → ℤ` (universe-A's `listComponent` portal, packaged). No `sorry`, no `:= True`,
no `native_decide`, no `rfl`-posing-as-bridge. Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Inst.swissExportA

namespace Dregg2.Circuit.Emit.EffectVmEmitSwissExport

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA ePrm eSub eSelNoop site0 site1 transitionAll boundaryFirstPins)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.EffectCommit2 (Surface2 satisfiedE2 encodeE2 logHashInjective)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Auth)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §0 — Selector + param offsets for the swiss-export effect row.

The running EffectVM lays one selector per effect (`columns.rs::NUM_EFFECTS = 54`); `exportSturdyRefA`
has its own selector index `selSE.SWISS_EXPORT` (the running prover's per-effect selector). The post
swiss-table digest the row pins is carried in a parameter column `paramSE.SWISS_DIGEST_NEW` (the
runnable column the witness generator fills with `D (post.swiss)`). The digest is carried on the
`state.CAP_ROOT` scalar column (REINTERPRETED as the swiss-table digest for these `caps`-freezing swiss
effects — `caps` is in export's frozen frame, so `cap_root` is free to carry the swiss digest here). -/

namespace selSE
/-- The `exportSturdyRefA` effect selector column. -/
def SWISS_EXPORT : Nat := 3
end selSE

namespace paramSE
/-- The post swiss-table digest parameter: the value the witness fills with `D (post.swiss)`. -/
def SWISS_DIGEST_NEW : Nat := 2
end paramSE

/-- The `exportSturdyRefA` selector as an expression. -/
def eSelSwissExport : EmittedExpr := .var selSE.SWISS_EXPORT

/-- The post swiss-digest param as an expression. -/
def eSwissDigestNew : EmittedExpr := .var (prmCol paramSE.SWISS_DIGEST_NEW)

/-! ## §1 — The swiss-export row gates (the SUPPORTED part: a digest-column MOVE + frame freeze).

The swiss effect MOVES the `swiss_root` (carried on the `cap_root` column) to the post swiss-table
digest and FREEZES the rest of the block (balance limbs, nonce, 8 fields, reserved). This is the
SCALAR portion the per-row IR can express; the guard + list-structure are IR-BLOCKED (header). -/

/-- Swiss-root MOVE body: `new_swiss_root - swissDigestNew` (post swiss_root IS the param digest). -/
def gSwissMove : EmittedExpr := eSub (eSA state.CAP_ROOT) eSwissDigestNew

/-- Balance-lo freeze body: `new_bal_lo - old_bal_lo`. -/
def gBalLoFix : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)

/-- Balance-hi freeze body: `new_bal_hi - old_bal_hi`. -/
def gBalHiFix : EmittedExpr := eSub (eSA state.BALANCE_HI) (eSB state.BALANCE_HI)

/-- Nonce freeze body: `new_nonce - old_nonce` (a swiss effect rewrites only the `swiss` list — matches
the universe-A executor, which freezes the kernel cell record). -/
def gNonceFix : EmittedExpr := eSub (eSA state.NONCE) (eSB state.NONCE)

/-- Reserved freeze body: `new_reserved - old_reserved`. -/
def gResFix : EmittedExpr := eSub (eSA state.RESERVED) (eSB state.RESERVED)

/-- Field-`i` freeze body: `field_after[i] - field_before[i]`. -/
def gFieldFix (i : Nat) : EmittedExpr :=
  eSub (eSA (state.FIELD_BASE + i)) (eSB (state.FIELD_BASE + i))

/-- The eight field-freeze gates. -/
def gFieldFixAll : List VmConstraint :=
  (List.range 8).map (fun i => VmConstraint.gate (gFieldFix i))

/-! ## §2 — The emitted descriptor. -/

/-- The `exportSturdyRefA` AIR identity (the fingerprint binding). -/
def swissExportVmAirName : String := "dregg-effectvm-swissExportA-v1"

/-- The swiss-export per-row gates: swiss-root MOVE, balance/nonce/reserved freeze, 8 fields freeze. -/
def swissExportRowGates : List VmConstraint :=
  [ .gate gSwissMove, .gate gBalLoFix, .gate gBalHiFix, .gate gNonceFix
  , .gate gResFix ] ++ gFieldFixAll

/-- Site 2 absorbing the post `swiss_root` (carried on the `cap_root` column; same shape as the
transfer keystone's `site2`, so the moved digest is bound into `state_commit`). -/
def site2 : VmHashSite :=
  { digestCol := auxCol aux_off.STATE_INTER3
  , inputs := [ .col (saCol (state.FIELD_BASE + 5)), .col (saCol (state.FIELD_BASE + 6))
              , .col (saCol (state.FIELD_BASE + 7)), .col (saCol state.CAP_ROOT) ]
  , arity := 4 }

/-- Site 3: `state_commit = H4(inter1, inter2, inter3, 0)` — reading sites 0/1/2. -/
def site3 : VmHashSite :=
  { digestCol := saCol state.STATE_COMMIT
  , inputs := [ .digest 0, .digest 1, .digest 2, .zero ]
  , arity := 4 }

/-- The ordered GROUP-4 hash sites (identical chain to the transfer keystone). -/
def swissExportHashSites : List VmHashSite := [site0, site1, site2, site3]

/-- **`swissExportVmDescriptor`** — the `exportSturdyRefA` effect's SUPPORTED concrete circuit, emitted
through the EffectVM IR: the swiss-root MOVE + frame-freeze gates ++ transition continuity ++ the row-0
boundary pins, with the 4 ordered GROUP-4 hash sites (binding the moved digest). No balance range
checks (no balance move). NOTE: the guard + list-structure are IR-BLOCKED (header), NOT in this
descriptor. -/
def swissExportVmDescriptor : EffectVmDescriptor :=
  { name := swissExportVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := swissExportRowGates ++ transitionAll ++ boundaryFirstPins
  , hashSites := swissExportHashSites
  , ranges := [] }

/-! ## §3 — The swiss-export ROW INTENT (the SUPPORTED faithfulness target).

`SwissExportRowIntent env` is the field-level swiss-digest move the per-row IR supports: post
`swiss_root` IS the supplied post swiss-digest, balance limbs / nonce / reserved / 8 fields FIXED. This
is the EffectVM-row projection of universe-A's `ExportSpec` `swiss` clause (the whole-LIST `swiss`
equality, projected to the swiss-DIGEST column) + the 16-field freeze (projected to the row's frozen
columns). It does NOT carry the guard or the list structure (IR-BLOCKED, header). -/

/-- **`SwissExportRowIntent env`** — the SUPPORTED intent: post `swiss_root` is the digest param, frame
frozen. -/
def SwissExportRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.CAP_ROOT) = env.loc (prmCol paramSE.SWISS_DIGEST_NEW)
  ∧ env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-- The row is a swiss-export row: `s_swissExport = 1`, `s_noop = 0`. -/
def IsSwissExportRow (env : VmRowEnv) : Prop :=
  env.loc selSE.SWISS_EXPORT = 1 ∧ env.loc sel.NOOP = 0

/-! ## §4 — FAITHFULNESS: the emitted per-row gates ⟺ the SUPPORTED intent. -/

/-- **`swissExportRowGates_holds_iff`** — on a swiss-export row, the emitted per-row gates all hold IFF
`SwissExportRowIntent` holds. The gate bodies are the running prover's polynomials (swiss-root move +
frame freeze); they pin EXACTLY the supported digest-move intent. -/
theorem swissExportRowGates_holds_iff (env : VmRowEnv) :
    (∀ c ∈ swissExportRowGates, c.holdsVm env false false) ↔ SwissExportRowIntent env := by
  unfold swissExportRowGates gFieldFixAll SwissExportRowIntent
  constructor
  · intro h
    have hSw := h (.gate gSwissMove) (by simp)
    have hLo := h (.gate gBalLoFix) (by simp)
    have hHi := h (.gate gBalHiFix) (by simp)
    have hNon := h (.gate gNonceFix) (by simp)
    have hRes := h (.gate gResFix) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldFix i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gSwissMove, gBalLoFix, gBalHiFix, gNonceFix, gResFix,
      eSA, eSB, eSwissDigestNew, eSub, EmittedExpr.eval] at hSw hLo hHi hNon hRes
    refine ⟨by linarith [hSw], by linarith [hLo], by linarith [hHi], by linarith [hNon],
      by linarith [hRes], ?_⟩
    intro i hi
    have := hFld i hi
    simp only [VmConstraint.holdsVm, gFieldFix, eSA, eSB, eSub, EmittedExpr.eval] at this
    linarith
  · rintro ⟨hSw, hLo, hHi, hNon, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · simp only [VmConstraint.holdsVm, gSwissMove, eSA, eSwissDigestNew, eSub, EmittedExpr.eval]
      rw [hSw]; ring
    · simp only [VmConstraint.holdsVm, gBalLoFix, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hLo]; ring
    · simp only [VmConstraint.holdsVm, gBalHiFix, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hHi]; ring
    · simp only [VmConstraint.holdsVm, gNonceFix, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hNon]; ring
    · simp only [VmConstraint.holdsVm, gResFix, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hRes]; ring
    · simp only [VmConstraint.holdsVm, gFieldFix, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hFld i hi]; ring

/-- **`swissExportVm_faithful` — THE supported deliverable.** On a swiss-export row, the emitted
descriptor's per-row gates hold IFF the supported swiss-digest intent holds. -/
theorem swissExportVm_faithful (env : VmRowEnv) :
    (∀ c ∈ swissExportRowGates, c.holdsVm env false false) ↔ SwissExportRowIntent env :=
  swissExportRowGates_holds_iff env

/-! ## §5 — ANTI-GHOST (per-row): a wrong swiss-root move fails the emitted descriptor. -/

/-- **Anti-ghost (swiss-root tamper).** A row whose post-`swiss_root` is NOT the supplied post-digest
fails the `gSwissMove` gate (UNSAT). -/
theorem swissExportVm_rejects_wrong_swissRoot (env : VmRowEnv)
    (hwrong : env.loc (saCol state.CAP_ROOT) ≠ env.loc (prmCol paramSE.SWISS_DIGEST_NEW)) :
    ¬ (VmConstraint.gate gSwissMove).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gSwissMove, eSA, eSwissDigestNew, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith

/-- **Anti-ghost (general).** A row whose post-state is NOT the intent move does NOT satisfy the per-row
gates. -/
theorem swissExportVm_rejects_wrong_output (env : VmRowEnv) (hwrong : ¬ SwissExportRowIntent env) :
    ¬ (∀ c ∈ swissExportRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((swissExportVm_faithful env).mp h)

/-! ## §6 — The structured per-cell soundness (the keystone analog). -/

/-- **`SwissRowEncodes env pre post swissDigestNew`** — the row decodes to `(pre, post)` cell states
with the post swiss-digest carried in `paramSE.SWISS_DIGEST_NEW`. (`cap_root` column carries the
swiss-root.) -/
def SwissRowEncodes (env : VmRowEnv) (pre post : CellState) (swissDigestNew : ℤ) : Prop :=
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.BALANCE_HI) = pre.balHi
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
  ∧ env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  ∧ env.loc (sbCol state.RESERVED) = pre.reserved
  ∧ env.loc (prmCol paramSE.SWISS_DIGEST_NEW) = swissDigestNew
  ∧ env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.BALANCE_HI) = post.balHi
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
  ∧ env.loc (saCol state.CAP_ROOT) = post.capRoot
  ∧ env.loc (saCol state.RESERVED) = post.reserved

/-- The per-cell swiss spec: the moved cell's WHOLE post-state is `pre` with `swiss_root` (the
`cap_root` column) set to the new swiss-digest, every other field frozen. This is the per-cell
projection of universe-A's `ExportSpec` (`swiss` whole-list move ⟹ swiss-DIGEST column move; 16-field
freeze ⟹ frame freeze). -/
def SwissCellSpec (pre post : CellState) (swissDigestNew : ℤ) : Prop :=
  post.capRoot = swissDigestNew
  ∧ post.balLo = pre.balLo
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.reserved = pre.reserved

/-- Under `SwissRowEncodes`, `SwissExportRowIntent` IS the structured per-cell `SwissCellSpec`. -/
theorem intent_to_swissCellSpec (env : VmRowEnv) (pre post : CellState) (swissDigestNew : ℤ)
    (henc : SwissRowEncodes env pre post swissDigestNew) (hint : SwissExportRowIntent env) :
    SwissCellSpec pre post swissDigestNew := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hpDig,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes⟩ := henc
  obtain ⟨hsw, hlo, hhi, hnon, hres, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hsaCap, ← hpDig]; exact hsw
  · rw [← hsaLo, ← hsbLo]; exact hlo
  · rw [← hsaHi, ← hsbHi]; exact hhi
  · rw [← hsaN, ← hsbN]; exact hnon
  · intro i; rw [← hsaF i, ← hsbF i]; exact hfld i.val i.isLt
  · rw [← hsaRes, ← hsbRes]; exact hres

/-- **`swissExportDescriptor_full_sound` — the structured soundness (supported part).** Satisfying the
per-row gates under the `SwissRowEncodes` decoding forces the structured per-cell `SwissCellSpec` (post
`swiss_root` = the predicted swiss-digest, frame frozen). -/
theorem swissExportDescriptor_full_sound (env : VmRowEnv)
    (pre post : CellState) (swissDigestNew : ℤ)
    (henc : SwissRowEncodes env pre post swissDigestNew)
    (hgates : ∀ c ∈ swissExportRowGates, c.holdsVm env false false) :
    SwissCellSpec pre post swissDigestNew :=
  intent_to_swissCellSpec env pre post swissDigestNew henc ((swissExportVm_faithful env).mp hgates)

/-! ## §7 — THE ANTI-GHOST COMMITMENT TOOTH (whole-state binding, swiss-root included).

The GROUP-4 sites (identical to the transfer keystone's) absorb the post `swiss_root` (on the
`cap_root` column) into the published `state_commit`. Under `Poseidon2SpongeCR hash`, two satisfying
rows with the same published `NEW_COMMIT` have identical absorbed columns — so a tampered
post-`swiss_root` claiming the published commitment is impossible. Reuse the keystone's machinery. -/

open Dregg2.Circuit.Emit.EffectVmEmitTransfer (transferHashSites)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (absorbedCols absorbed_determined_by_commit)

/-- `swissExportHashSites` is DEFINITIONALLY the transfer keystone's `transferHashSites` (same ordered
4-site chain, same absorbed columns incl. the post `swiss_root` on the cap-root column). -/
theorem swissExportHashSites_eq : swissExportHashSites = transferHashSites := rfl

/-- **`swissExportDescriptor_commit_binds_state` — the whole-state tooth.** Two swiss-export rows that
satisfy the hash-sites and publish equal `state_commit`s have identical absorbed columns — the moved
post-`swiss_root` (an absorbed column, site 2) included. So a prover CANNOT tamper the post-`swiss_root`
(or any absorbed cell) while keeping the published commitment. -/
theorem swissExportDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ swissExportHashSites)
    (hs₂ : siteHoldsAll hash e₂ swissExportHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    absorbedCols e₁ = absorbedCols e₂ := by
  rw [swissExportHashSites_eq] at hs₁ hs₂
  exact absorbed_determined_by_commit hash hCR e₁ e₂ hs₁ hs₂ hcommit

/-! ## §8 — THE CONNECTOR — `swissRootProj` to universe-A's `swissExportA_full_sound`.

`swissRootProj D k = D k.swiss` reads a whole-list digest `D : List SwissRecord → ℤ` of the swiss
side-table (the SAME measure universe-A's `swissComponent`'s `listDigest LE cN` digests, packaged as
the single `D`). The unification: a committed universe-A `ExportSpec` makes the projected
post-`swiss_root` EXACTLY `D (exportRecord sw exporter target rights :: s.kernel.swiss)` — the digest
the descriptor's `paramSE.SWISS_DIGEST_NEW` carries. So the runnable `swiss_root` column transition IS
universe-A's `swiss`-digest transition. -/

open Dregg2.Circuit.Inst.SwissExportA (ExportArgs)
open Dregg2.Circuit.Spec.SwissExport (ExportSpec exportRecord)

/-- **`swissRootProj D k`** — the EffectVM `swiss_root` column value for kernel state `k`: the
whole-list digest `D` of the swiss side-table. -/
def swissRootProj (D : List SwissRecord → ℤ) (k : RecordKernelState) : ℤ := D k.swiss

/-- The predicted post swiss-digest the descriptor's `paramSE.SWISS_DIGEST_NEW` carries: `D` of the
post swiss-list (`exportRecord … :: pre`). -/
def exportSwissDigestNew (D : List SwissRecord → ℤ)
    (s : RecChainedState) (args : ExportArgs) : ℤ :=
  D (exportRecord args.sw args.exporter args.target args.rights :: s.kernel.swiss)

/-- **`unify_swissExport` — THE CONNECTOR.** When universe-A's `ExportSpec` holds, the projected
post-`swiss_root` is EXACTLY the post swiss-digest `exportSwissDigestNew D s args` — i.e. the column
move the descriptor pins. So `SwissCellSpec`'s `swiss_root` clause IS universe-A's `swiss`-clause,
projected to the digest column. (The frame clauses are universe-A's 16-field freeze projected to the
frozen columns. We discharge the `swiss_root` leg — the genuine swiss content.) -/
theorem unify_swissExport (D : List SwissRecord → ℤ)
    (s : RecChainedState) (args : ExportArgs) (s' : RecChainedState)
    (hspec : ExportSpec s args.sw args.actor args.exporter args.target args.rights s') :
    swissRootProj D s'.kernel = exportSwissDigestNew D s args := by
  -- ExportSpec's `swiss` clause is `s'.kernel.swiss = exportRecord … :: s.kernel.swiss`.
  obtain ⟨_, hsw, _⟩ := hspec
  show D s'.kernel.swiss = D (exportRecord args.sw args.exporter args.target args.rights :: s.kernel.swiss)
  rw [hsw]

/-- **`unify_swissExport_via_full_sound` — the runnable column move inherits the VALIDATED guarantee.**
Chaining universe-A's `swissExportA_full_sound` (a satisfying v2 full-state witness ⟹ `ExportSpec`)
with `unify_swissExport`: a satisfying universe-A witness forces the projected post-`swiss_root` to the
post swiss-digest — the EXACT column value the runnable descriptor's `paramSE.SWISS_DIGEST_NEW` carries.
So the runnable `swiss_root` move is universe-A's validated `swiss` transition, not a fourth spec.
(The guard + list-structure remain enforced ONLY inside `swissExportA_full_sound` — IR-BLOCKED at the
row, header.) -/
theorem unify_swissExport_via_full_sound
    (S : Surface2) (D : List SwissRecord → ℤ)
    (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : Dregg2.Circuit.ListCommit.compressNInjective cN)
    (hLE : Dregg2.Circuit.ListCommit.listLeafInjective LE)
    (hRest : Dregg2.Circuit.Inst.SwissExportA.RestIffNoSwiss S.RH)
    (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : ExportArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (Dregg2.Circuit.Inst.SwissExportA.swissExportE LE cN hN hLE)
        (encodeE2 S (Dregg2.Circuit.Inst.SwissExportA.swissExportE LE cN hN hLE) s args s')) :
    swissRootProj D s'.kernel = exportSwissDigestNew D s args :=
  unify_swissExport D s args s'
    (Dregg2.Circuit.Inst.SwissExportA.swissExportA_full_sound S LE cN hN hLE hRest hLog s args s' h)

/-! ## §9 — NON-VACUITY: a concrete swiss-export row that satisfies the intent, and one that does not.

A row `swissGoodRow`: a swiss-digest move where `swiss_root 11 → 77` (the new digest), nonce `5 → 5`
frozen, everything else `0`/frozen. And `swissBadRow`: same but post-`swiss_root` forged to `999 ≠ 77`. -/

/-- A concrete swiss-export row: `swiss_root` (cap-root column) moves to the param digest `77`, frame
frozen at `0`. -/
def swissGoodRow : VmRowEnv where
  loc := fun v =>
    if v = selSE.SWISS_EXPORT then 1
    else if v = sbCol state.CAP_ROOT then 11
    else if v = saCol state.CAP_ROOT then 77
    else if v = prmCol paramSE.SWISS_DIGEST_NEW then 77
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- `swissGoodRow` is a genuine swiss-export row. -/
theorem swissGoodRow_isSwissExportRow : IsSwissExportRow swissGoodRow := by
  unfold IsSwissExportRow swissGoodRow
  constructor <;> norm_num [selSE.SWISS_EXPORT, sel.NOOP, sbCol, saCol, prmCol, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.CAP_ROOT,
    paramSE.SWISS_DIGEST_NEW]

/-- **NON-VACUITY (witness TRUE).** `swissGoodRow` REALIZES the swiss-export intent: post `swiss_root =
77` = the param digest, balance/nonce/reserved/fields frozen at `0`. -/
theorem swissGoodRow_realizes_intent : SwissExportRowIntent swissGoodRow := by
  unfold SwissExportRowIntent swissGoodRow
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [saCol, prmCol, STATE_AFTER_BASE, PARAM_BASE, STATE_BEFORE_BASE, NUM_EFFECTS,
      STATE_SIZE, NUM_PARAMS, state.CAP_ROOT, paramSE.SWISS_DIGEST_NEW]
  all_goals
    simp only [saCol, sbCol, prmCol, selSE.SWISS_EXPORT, STATE_AFTER_BASE, STATE_BEFORE_BASE,
      PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.CAP_ROOT, state.BALANCE_LO,
      state.BALANCE_HI, state.NONCE, state.RESERVED, state.FIELD_BASE, paramSE.SWISS_DIGEST_NEW]
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · intro i hi
    have e1 : ¬ (76 + (3 + i) = 3) := by omega
    have e2 : ¬ (76 + (3 + i) = 65) := by omega
    have e3 : ¬ (76 + (3 + i) = 87) := by omega
    have e4 : ¬ (76 + (3 + i) = 70) := by omega
    have f1 : ¬ (54 + (3 + i) = 3) := by omega
    have f2 : ¬ (54 + (3 + i) = 65) := by omega
    have f3 : ¬ (54 + (3 + i) = 87) := by omega
    have f4 : ¬ (54 + (3 + i) = 70) := by omega
    simp only [if_neg e1, if_neg e2, if_neg e3, if_neg e4, if_neg f1, if_neg f2, if_neg f3, if_neg f4]

/-- A forged swiss-export row: `swissGoodRow` with the post-`swiss_root` tampered to `999 ≠ 77`. -/
def swissBadRow : VmRowEnv where
  loc := fun v => if v = saCol state.CAP_ROOT then 999 else swissGoodRow.loc v
  nxt := swissGoodRow.nxt
  pub := swissGoodRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `swissBadRow`'s post-`swiss_root` is NOT the
param digest, so the `gSwissMove` gate REJECTS it — a concrete UNSAT. -/
theorem swissBadRow_rejected : ¬ (VmConstraint.gate gSwissMove).holdsVm swissBadRow false false := by
  apply swissExportVm_rejects_wrong_swissRoot
  show (if saCol state.CAP_ROOT = saCol state.CAP_ROOT then (999:ℤ) else swissGoodRow.loc _)
      ≠ swissBadRow.loc (prmCol paramSE.SWISS_DIGEST_NEW)
  rw [if_pos rfl]
  show (999:ℤ) ≠ (if saCol state.CAP_ROOT = prmCol paramSE.SWISS_DIGEST_NEW then (999:ℤ)
    else swissGoodRow.loc (prmCol paramSE.SWISS_DIGEST_NEW))
  have hne : ¬ (saCol state.CAP_ROOT = prmCol paramSE.SWISS_DIGEST_NEW) := by
    simp only [saCol, prmCol, STATE_AFTER_BASE, PARAM_BASE, STATE_BEFORE_BASE, NUM_EFFECTS,
      STATE_SIZE, NUM_PARAMS, state.CAP_ROOT, paramSE.SWISS_DIGEST_NEW]
  rw [if_neg hne]
  show (999:ℤ) ≠ swissGoodRow.loc (prmCol paramSE.SWISS_DIGEST_NEW)
  show (999:ℤ) ≠ (if prmCol paramSE.SWISS_DIGEST_NEW = selSE.SWISS_EXPORT then (1:ℤ)
    else if prmCol paramSE.SWISS_DIGEST_NEW = sbCol state.CAP_ROOT then 11
    else if prmCol paramSE.SWISS_DIGEST_NEW = saCol state.CAP_ROOT then 77
    else if prmCol paramSE.SWISS_DIGEST_NEW = prmCol paramSE.SWISS_DIGEST_NEW then 77 else 0)
  norm_num [prmCol, saCol, sbCol, selSE.SWISS_EXPORT, STATE_AFTER_BASE, STATE_BEFORE_BASE, PARAM_BASE,
    NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.CAP_ROOT, paramSE.SWISS_DIGEST_NEW]

/-! ## §10 — Axiom-hygiene tripwires (the honesty tripwire). -/

#guard swissExportVmDescriptor.constraints.length == 13 + 14 + 4  -- 13 gates + 14 transitions + 4 first
#guard swissExportVmDescriptor.hashSites.length == 4
#guard swissExportVmDescriptor.traceWidth == 186

#assert_axioms swissExportRowGates_holds_iff
#assert_axioms swissExportVm_faithful
#assert_axioms swissExportVm_rejects_wrong_swissRoot
#assert_axioms swissExportVm_rejects_wrong_output
#assert_axioms intent_to_swissCellSpec
#assert_axioms swissExportDescriptor_full_sound
#assert_axioms swissExportDescriptor_commit_binds_state
#assert_axioms unify_swissExport
#assert_axioms unify_swissExport_via_full_sound
#assert_axioms swissGoodRow_realizes_intent
#assert_axioms swissBadRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitSwissExport
