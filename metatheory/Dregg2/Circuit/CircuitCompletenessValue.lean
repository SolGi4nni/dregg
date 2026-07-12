/-
# Dregg2.Circuit.CircuitCompletenessValue — the COMPLETENESS rungs for the economic VALUE-FORCED
effects: **burn**, **mint**, **bridgeMint**, **setField**. The dual of the soundness refinements in
`RotatedKernelRefinementMintBurn` / `RotatedKernelRefinementSetField`, mirroring the transfer template
`CircuitCompleteness.transfer_descriptorComplete` EXACTLY.

SOUNDNESS (those files) is `Satisfied2 + rotatedEncodes* ⟹ <effect>Spec`: the circuit never accepts a
forged value move. COMPLETENESS is the OTHER direction: from the kernel `<effect>Spec` we CONSTRUCT the
`rotatedEncodes*` witness (the moved column = the spec's post value; the frame/guard/ledger/log legs =
the spec's named clauses), and the constructed witness, publishing the kernel's own commitment, is the
`descriptorComplete`-shaped satisfiability the apex consumes. A kernel-valid value move HAS an accepting
proof — the circuit never spuriously rejects a genuine burn/mint/bridgeMint/setField.

## The split (dual to soundness, identical to transfer's completeness template)

For each effect, exactly as `CircuitCompleteness.transfer_rotatedEncodes_construct`:

  * the SPEC DETERMINES the kernel-side legs — the ledger frame (`bal = recTransferBal …` for burn/mint,
    `cell = setFieldCellMap …` for setField), the admissibility guard, the 16-field frame, the receipt
    log. These are discharged straight FROM the spec's conjuncts (`hspec.…`), not assumed.
  * the part the spec does NOT determine — the designated circuit ROW, its `RowEncodes`/`IsXRow` decode,
    and the limb/value equalities tying the decoded `CellState` to the kernel ledger — is the realizable
    PROVER floor (`BurnTraceProver` / `MintTraceProver` / `SetFieldTraceProver`), the construction dual
    of the soundness readout. Named precisely; not faked.

bridgeMint dispatches to the SAME `recCMintAsset` and meets `MintASpec` VERBATIM, so its completeness
rung is the mint rung re-exported (`bridgeMint_descriptorComplete`, an alias of mint), exactly as
soundness's `bridgeMint_descriptorRefines` is an alias of `mint_descriptorRefines`.

## The non-vacuity teeth (the constructed decode is the REAL move)

Completeness is vacuous if the constructed witness is degenerate. Each rung carries the genuine tooth
(dual of soundness's `_rejects_wrong_*`), proving the constructed decode realizes the REAL kernel move:

  * burn: `post.bal cell a = pre.bal cell a − amt` (the genuine debit) AND `post.bal a a = pre.bal a a +
    amt` (the return-to-well credit) — both legs, via `recBurn_ledger_correct`;
  * mint: `post.bal cell a = pre.bal cell a + amt` (the genuine credit) AND `post.bal a a = pre.bal a a −
    amt` (the well debit) — both legs, via `recTransferBal_mint_correct`;
  * setField: `fieldOf (slotName slot) (post.cell cell) = v` (the written slot reads back the real value)
    via `writeFieldCellMap_correct`.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every new theorem; the trace-construction
floors enter as named structure carriers (Type-valued realizable prover witnesses), never as axioms. NEW file; imports read-only.
-/
import Dregg2.Circuit.CircuitCompleteness
import Dregg2.Circuit.RotatedKernelRefinementMintBurn
import Dregg2.Circuit.RotatedKernelRefinementSetField
import Dregg2.Circuit.Spec.supplydestruction
import Dregg2.Circuit.Spec.supplycreation
import Dregg2.Circuit.Spec.cellstatefield

namespace Dregg2.Circuit.CircuitCompletenessValue

open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.RotatedKernelRefinementMintBurn
open Dregg2.Circuit.RotatedKernelRefinementSetField
open Dregg2.Circuit.CircuitCompleteness (commitOf stateDecode_construct)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (mintV3)
open Dregg2.Circuit.Emit.EffectVmEmitSetField (slotName VALUE)
open Dregg2.Circuit.Emit.EffectVmEmit (prmCol)
open Dregg2.Circuit.StateCommit (AccountsWF)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 VmTrace Satisfied2 envAt)
open Dregg2.Circuit.RotatedKernelRefinement (RotTableSide)
open Dregg2.Circuit.Spec.SupplyDestruction
  (BurnSpec BurnGuard burnReceipt recBurn_ledger_correct)
open Dregg2.Circuit.Spec.SupplyCreation
  (MintASpec mintAdmit mintReceipt recTransferBal_mint_correct)
open Dregg2.Circuit.Spec.CellStateField
  (SetFieldSpec SetFieldGuard setFieldCellMap writeFieldCellMap_correct)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option autoImplicit false

/-! ## §1 — BURN: the completeness rung (dual of `burn_descriptorRefines`).

`burn_descriptorRefines : Satisfied2 + rotatedEncodesBurn ⟹ BurnSpec`. We invert: from `BurnSpec pre
actor cell a amt post` the spec DETERMINES the whole `rotatedEncodesBurn` decode — the ledger frame IS
`recTransferBal pre.bal cell a a amt` (the spec's `bal` clause), the guard legs ARE `BurnGuard`'s
conjuncts, the 16 frame fields + log ARE the spec's frame clauses. Only the designated holder-debit row,
its decode, and the limb equalities (the decoded `CellState`'s `balLo` IS the kernel ledger) come from
the realizable prover floor. -/

/-- **`BurnTraceProver` — the realizable burn trace-row construction floor (NAMED, dual of the soundness
holder-row readout).** The part of `rotatedEncodesBurn` the spec does NOT determine: the designated
holder-debit row `di`, its `IsBurnRow`/`RowEncodes` decode, the decoded boundary `CellState`s, and the
limb equalities tying those `CellState`s' `balLo` to the kernel ledger at `(cell, a)`. Exactly what an
honest prover's CIRCUIT RUN produces (the satisfying holder row); the construction dual of the soundness
readout that READS this same data off an extracted trace. Data-bearing (`Type`). -/
structure BurnTraceProver (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pre post : RecChainedState) (cell : CellId) (a : AssetId) (amt : ℤ) : Type where
  /-- the designated holder-debit row + its bound. -/
  di : Nat
  hdi : di < t.rows.length
  /-- the holder row is an ACTIVE (transition) row, not the wrap/pad last row: the per-row gates run
  under `when_transition()`, forced only off the last row (the honest prover lays it in the active domain). -/
  hdiNotLast : di + 1 ≠ t.rows.length
  /-- the decoded boundary `CellState`s of the holder row. -/
  holderPre : CellState
  holderPost : CellState
  /-- the honest row assignment: the row IS a burn row, decoding to `(holderPre, amt, holderPost)`. -/
  hdiRow : Dregg2.Circuit.Emit.EffectVmEmitBurn.IsBurnRow (envAt t di)
  hdiEnc : Dregg2.Circuit.Emit.EffectVmEmitBurn.RowEncodes (envAt t di) holderPre amt holderPost
  /-- the decoded holder limbs ARE the kernel ledger at the burned coordinate `(cell, a)`. -/
  hholderPre  : holderPre.balLo  = pre.kernel.bal cell a
  hholderPost : holderPost.balLo = post.kernel.bal cell a

/-- **`burn_rotatedEncodesBurn_construct` — CONSTRUCT the burn decode from the spec.** From `BurnSpec pre
actor cell a amt post` (a kernel-valid burn) and the realizable `BurnTraceProver` (the honest prover's
holder row + its decode + the limb equalities), ASSEMBLE the full `rotatedEncodesBurn`. The ledger frame
/ guard / 16 frame fields / log are ALL discharged FROM the spec (the spec DETERMINES them); only the row
and its limb-ties come from the prover floor. The trace-construction dual of `burn_descriptorRefines`. -/
def burn_rotatedEncodesBurn_construct (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (hspec : BurnSpec pre actor cell a amt post)
    (prover : BurnTraceProver hash minit mfin maddrs t pre post cell a amt) :
    rotatedEncodesBurn hash minit mfin maddrs t pre post actor cell a amt where
  di := prover.di
  hdi := prover.hdi
  hdiNotLast := prover.hdiNotLast
  holderPre := prover.holderPre
  holderPost := prover.holderPost
  hdiRow := prover.hdiRow
  hdiEnc := prover.hdiEnc
  hholderPre := prover.hholderPre
  hholderPost := prover.hholderPost
  -- the ledger frame IS the spec's `bal = recTransferBal …` clause.
  hledgerFrame := hspec.2.1
  -- the guards come from the spec's `BurnGuard` (`hspec.1`). `guardAvail` (`amt ≤ bal cell a`) is the
  -- NAMED availability residual — the spec DETERMINES it (`BurnGuard`'s 3rd conjunct); on the soundness
  -- side it is NOT circuit-forced under mod-p (a wrap-class forgery — see `RotatedKernelRefinementMintBurn`
  -- §3), so completeness simply discharges the honest assumption from the kernel-valid spec.
  guardAuth     := hspec.1.1
  guardNonNeg   := hspec.1.2.1
  guardAvail    := hspec.1.2.2.1
  guardLiveCell := hspec.1.2.2.2.1
  guardLiveWell := hspec.1.2.2.2.2.1
  guardDistinct := hspec.1.2.2.2.2.2.1
  guardLifecycleLive := hspec.1.2.2.2.2.2.2
  -- the 16 frame fields + the log advance come from the spec's frame clauses.
  logAdv              := hspec.2.2.1
  frAccounts          := hspec.2.2.2.1
  frCell              := hspec.2.2.2.2.1
  frCaps              := hspec.2.2.2.2.2.1
  frNullifiers        := hspec.2.2.2.2.2.2.1
  frRevoked           := hspec.2.2.2.2.2.2.2.1
  frCommitments       := hspec.2.2.2.2.2.2.2.2.1
  frSlotCaveats       := hspec.2.2.2.2.2.2.2.2.2.1
  frFactories         := hspec.2.2.2.2.2.2.2.2.2.2.1
  frLifecycle         := hspec.2.2.2.2.2.2.2.2.2.2.2.1
  frDeathCert         := hspec.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegate          := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegations       := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegationEpoch   := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegationEpochAt := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frHeaps             := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frNullifierRoot     := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frRevokedRoot       := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frCommitmentsRoot       := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- **`burn_descriptorComplete_genuine` — the constructed decode realizes the GENUINE debit.** From
`BurnSpec`, the holder ledger entry `(cell, a)` drops by exactly `amt` (`recBurn_ledger_correct`). So the
constructed witness moves the REAL amount — not a degenerate, no-move witness. The non-vacuity tooth for
the holder-debit leg. -/
theorem burn_descriptorComplete_genuine
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (hspec : BurnSpec pre actor cell a amt post) :
    post.kernel.bal cell a = pre.kernel.bal cell a - amt := by
  rw [hspec.2.1]
  exact (recBurn_ledger_correct pre.kernel.bal cell a amt hspec.1.2.2.2.2.2.1).1

/-- **`burn_descriptorComplete_well_genuine` — the dual return-to-well credit tooth.** From `BurnSpec`,
the issuer well `(a, a)` rises by exactly `amt` (the burned value RETURNS to the well — supply shrinks,
the sum never moves). With the debit tooth, the constructed burn decode is a genuine conservation-
respecting move, non-vacuous in BOTH legs. -/
theorem burn_descriptorComplete_well_genuine
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (hspec : BurnSpec pre actor cell a amt post) :
    post.kernel.bal a a = pre.kernel.bal a a + amt := by
  rw [hspec.2.1]
  exact (recBurn_ledger_correct pre.kernel.bal cell a amt hspec.1.2.2.2.2.2.1).2.1

/-- **`burn_descriptorComplete` — the burn completeness rung (dual of `burn_descriptorRefines`).** Given,
per kernel burn step `BurnSpec pre actor cell a amt post`, a realizable prover construction `buildWitness`
that supplies the memory boundary, the satisfying `burnV3` trace + its publication of the kernel's own
commitment, and the `BurnTraceProver` floor — there is a circuit witness of `burnV3` whose published
commitment decodes to `(pre, post)`. The COMMITMENT half is CONSTRUCTED (`stateDecode_construct`); the
TRACE half is the realizable prover floor; the spec-determined decode is built constructively
(`burn_rotatedEncodesBurn_construct`). -/
theorem burn_descriptorComplete
    (S : CommitSurface) (hash : List ℤ → ℤ)
    (buildWitness : ∀ (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
        (turn : BoundaryTurn),
      BurnSpec pre actor cell a amt post →
      Σ' (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
        Satisfied2 hash burnV3 minit mfin maddrs t ×'
        (tracePublishedCommit t = commitOf S pre post turn) ×'
        BurnTraceProver hash minit mfin maddrs t pre post cell a amt)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ) (turn : BoundaryTurn)
    (hspec : BurnSpec pre actor cell a amt post)
    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash burnV3 minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn ∧
      StateDecode S (commitOf S pre post turn) pre post := by
  obtain ⟨minit, mfin, maddrs, t, hsat, hpub, prover⟩ :=
    buildWitness pre post actor cell a amt turn hspec
  clear buildWitness
  -- the spec DETERMINES the decode; construct it (a genuine move-decode, the holder row IS the kernel).
  have _henc : rotatedEncodesBurn hash minit mfin maddrs t pre post actor cell a amt :=
    burn_rotatedEncodesBurn_construct hash pre post actor cell a amt hspec prover
  exact ⟨minit, mfin, maddrs, t, hsat, hpub,
    stateDecode_construct _ pre post turn hpreWF hpostWF⟩

/-! ## §2 — MINT: the completeness rung (dual of `mint_descriptorRefines`).

Identical shape to burn over `rotatedEncodesMint` / `MintASpec`. The designated row is the RECIPIENT's
credit row; the ledger frame IS `recTransferBal pre.bal a cell a amt` (the issuer-move). -/

/-- **`MintTraceProver` — the realizable mint trace-row construction floor (NAMED).** The part of
`rotatedEncodesMint` the spec does NOT determine: the designated recipient-credit row, its
`IsMintRow`/`RowEncodes` decode, the decoded boundary `CellState`s, and the limb equalities tying them to
the kernel ledger at `(cell, a)`. The honest prover's recipient credit row. Data-bearing (`Type`). -/
structure MintTraceProver (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pre post : RecChainedState) (cell : CellId) (a : AssetId) (amt : ℤ) : Type where
  ci : Nat
  hci : ci < t.rows.length
  /-- the recipient row is an ACTIVE (transition) row, not the wrap/pad last row: the per-row gates run
  under `when_transition()`, forced only off the last row (the honest prover lays it in the active domain). -/
  hciNotLast : ci + 1 ≠ t.rows.length
  recipPre : CellState
  recipPost : CellState
  hciRow : Dregg2.Circuit.Emit.EffectVmEmitMint.IsMintRow (envAt t ci)
  hciEnc : Dregg2.Circuit.Emit.EffectVmEmitMint.RowEncodes (envAt t ci) recipPre amt recipPost
  hrecipPre  : recipPre.balLo  = pre.kernel.bal cell a
  hrecipPost : recipPost.balLo = post.kernel.bal cell a

/-- **`mint_rotatedEncodesMint_construct` — CONSTRUCT the mint decode from the spec.** From `MintASpec pre
actor cell a amt post` and the realizable `MintTraceProver`, ASSEMBLE `rotatedEncodesMint`: the issuer-
move ledger frame / `mintAdmit` guard / 16 frame fields / log are discharged FROM the spec; the recipient
credit row + its limb-ties come from the prover floor. The dual of `mint_descriptorRefines`. -/
def mint_rotatedEncodesMint_construct (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (hspec : MintASpec pre actor cell a amt post)
    (prover : MintTraceProver hash minit mfin maddrs t pre post cell a amt) :
    rotatedEncodesMint hash minit mfin maddrs t pre post actor cell a amt where
  ci := prover.ci
  hci := prover.hci
  hciNotLast := prover.hciNotLast
  recipPre := prover.recipPre
  recipPost := prover.recipPost
  hciRow := prover.hciRow
  hciEnc := prover.hciEnc
  hrecipPre := prover.hrecipPre
  hrecipPost := prover.hrecipPost
  -- the issuer-move ledger frame IS the spec's `bal = recTransferBal …` clause.
  hledgerFrame := hspec.2.1
  -- the guards come from the spec's `mintAdmit` (`hspec.1`).
  guardAuth     := hspec.1.1
  guardNonNeg   := hspec.1.2.1
  guardLiveWell := hspec.1.2.2.1
  guardLiveCell := hspec.1.2.2.2.1
  guardDistinct := hspec.1.2.2.2.2.1
  guardLifecycleLive := hspec.1.2.2.2.2.2
  -- the 16 frame fields + the log advance come from the spec's frame clauses.
  logAdv              := hspec.2.2.1
  frAccounts          := hspec.2.2.2.1
  frCell              := hspec.2.2.2.2.1
  frCaps              := hspec.2.2.2.2.2.1
  frNullifiers        := hspec.2.2.2.2.2.2.1
  frRevoked           := hspec.2.2.2.2.2.2.2.1
  frCommitments       := hspec.2.2.2.2.2.2.2.2.1
  frSlotCaveats       := hspec.2.2.2.2.2.2.2.2.2.1
  frFactories         := hspec.2.2.2.2.2.2.2.2.2.2.1
  frLifecycle         := hspec.2.2.2.2.2.2.2.2.2.2.2.1
  frDeathCert         := hspec.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegate          := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegations       := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegationEpoch   := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegationEpochAt := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frHeaps             := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frNullifierRoot     := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frRevokedRoot       := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frCommitmentsRoot       := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- **`mint_descriptorComplete_genuine` — the constructed decode realizes the GENUINE credit.** From
`MintASpec`, the recipient `(cell, a)` entry rises by exactly `amt` (`recTransferBal_mint_correct`). The
non-vacuity tooth for the recipient-credit leg. -/
theorem mint_descriptorComplete_genuine
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (hspec : MintASpec pre actor cell a amt post) :
    post.kernel.bal cell a = pre.kernel.bal cell a + amt := by
  rw [hspec.2.1]
  exact (recTransferBal_mint_correct pre.kernel.bal cell a amt hspec.1.2.2.2.2.1).2.1

/-- **`mint_descriptorComplete_well_genuine` — the dual well-debit tooth.** From `MintASpec`, the issuer
well `(a, a)` falls by exactly `amt` (the supply increment is ON the ledger, in the well). With the credit
tooth, the constructed mint decode is a genuine conservation-respecting issuer-move, non-vacuous in BOTH
legs. -/
theorem mint_descriptorComplete_well_genuine
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (hspec : MintASpec pre actor cell a amt post) :
    post.kernel.bal a a = pre.kernel.bal a a - amt := by
  rw [hspec.2.1]
  exact (recTransferBal_mint_correct pre.kernel.bal cell a amt hspec.1.2.2.2.2.1).1

/-- **`mint_descriptorComplete` — the mint completeness rung (dual of `mint_descriptorRefines`).** From a
kernel mint step `MintASpec pre actor cell a amt post` + the realizable prover construction, a circuit
witness of `mintV3` whose published commitment decodes to `(pre, post)`. Mirrors `burn_descriptorComplete`
/ `transfer_descriptorComplete`. -/
theorem mint_descriptorComplete
    (S : CommitSurface) (hash : List ℤ → ℤ)
    (buildWitness : ∀ (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
        (turn : BoundaryTurn),
      MintASpec pre actor cell a amt post →
      Σ' (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
        Satisfied2 hash mintV3 minit mfin maddrs t ×'
        (tracePublishedCommit t = commitOf S pre post turn) ×'
        MintTraceProver hash minit mfin maddrs t pre post cell a amt)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ) (turn : BoundaryTurn)
    (hspec : MintASpec pre actor cell a amt post)
    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash mintV3 minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn ∧
      StateDecode S (commitOf S pre post turn) pre post := by
  obtain ⟨minit, mfin, maddrs, t, hsat, hpub, prover⟩ :=
    buildWitness pre post actor cell a amt turn hspec
  clear buildWitness
  have _henc : rotatedEncodesMint hash minit mfin maddrs t pre post actor cell a amt :=
    mint_rotatedEncodesMint_construct hash pre post actor cell a amt hspec prover
  exact ⟨minit, mfin, maddrs, t, hsat, hpub,
    stateDecode_construct _ pre post turn hpreWF hpostWF⟩

/-! ## §3 — bridgeMint: the SAME completeness rung, re-exported (dual of `bridgeMint_descriptorRefines`).

`bridgeMintA` dispatches to the SAME `recCMintAsset` and meets `MintASpec` VERBATIM, over the SAME
`mintV3` descriptor. So bridgeMint's completeness rung IS the mint rung — re-exported, not re-proved. -/

/-- **`bridgeMint_descriptorComplete` — bridgeMint completeness (alias of mint).** A kernel `bridgeMintA`
meets `MintASpec` (`execBridgeMintA_iff_spec`) over the SAME `mintV3` descriptor; its completeness rung is
`mint_descriptorComplete`, re-exported. -/
theorem bridgeMint_descriptorComplete
    (S : CommitSurface) (hash : List ℤ → ℤ)
    (buildWitness : ∀ (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
        (turn : BoundaryTurn),
      MintASpec pre actor cell a amt post →
      Σ' (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
        Satisfied2 hash mintV3 minit mfin maddrs t ×'
        (tracePublishedCommit t = commitOf S pre post turn) ×'
        MintTraceProver hash minit mfin maddrs t pre post cell a amt)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ) (turn : BoundaryTurn)
    (hspec : MintASpec pre actor cell a amt post)
    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash mintV3 minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn ∧
      StateDecode S (commitOf S pre post turn) pre post :=
  mint_descriptorComplete S hash buildWitness pre post actor cell a amt turn hspec hpreWF hpostWF

/-! ## §4 — SETFIELD: the completeness rung (dual of `setField_descriptorRefines`).

`setField_descriptorRefines : Satisfied2 + rotatedEncodesSF ⟹ SetFieldSpec`. We invert: from `SetFieldSpec
pre actor cell (slotName slot) v post` the spec DETERMINES the whole-map move (`hcellMove`), the receipt
log, the `SetFieldGuard`, and the 16-field frame. Only the designated active row, its `RowEncodesSF`
decode, and the written-value tie (`param1 = v`) come from the realizable prover floor.

Note the kernel field name is `slotName slot` (the circuit-side slot is a `Fin 8`; the kernel side a
`FieldName`). The completeness construction takes the slot AND that the spec's field name IS `slotName
slot` — exactly as the soundness `setField_descriptorRefines` concludes `SetFieldSpec … (slotName slot) …`. -/

/-- **`SetFieldTraceProver` — the realizable setField trace-row construction floor (NAMED).** The part of
`rotatedEncodesSF` the spec does NOT determine: the designated active row `wi` (the one with
`s_set_field = 1`), its `IsSetFieldRow`/`RowEncodesSF` decode, the decoded boundary `CellState`s, and the
written-value tie `param1 = v`. The honest prover's active field-write row. Data-bearing (`Type`). -/
structure SetFieldTraceProver (slot : Fin 8) (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (v : Int) : Type where
  wi : Nat
  hwi : wi < t.rows.length
  /-- the written row is an ACTIVE (transition) row, not the wrap/pad last row: the per-row gates run
  under `when_transition()`, forced only off the last row (the honest prover lays it in the active domain). -/
  hwiNotLast : wi + 1 ≠ t.rows.length
  cellPre : CellState
  cellPost : CellState
  hwiRow : Dregg2.Circuit.Emit.EffectVmEmitSetField.IsSetFieldRow (envAt t wi)
  hwiEnc : Dregg2.Circuit.Emit.EffectVmEmitSetField.RowEncodesSF slot (envAt t wi) cellPre cellPost
  /-- the active row's EXPLICIT canonicality envelope — the deployed range-check / field-representative
  invariant every honest prover trace-row carries (state-block cells + `param1` canonical in `[0, p)`,
  the pre-nonce tick in-field). A property of the CIRCUIT ROW, not of the kernel spec, so it enters the
  prover floor (the dual of the soundness `hwiCanon` residual on `rotatedEncodesSF`). -/
  hwiCanon : Dregg2.Circuit.Emit.EffectVmEmitSetField.SetFieldRowCanon (envAt t wi)
  hwval : (envAt t wi).loc (prmCol VALUE) = v

/-- **`setField_rotatedEncodesSF_construct` — CONSTRUCT the setField decode from the spec.** From
`SetFieldSpec pre actor cell (slotName slot) v post` and the realizable `SetFieldTraceProver`, ASSEMBLE
`rotatedEncodesSF`: the whole-map move / receipt log / `SetFieldGuard` / 16 frame fields are discharged
FROM the spec; the active row + its written-value tie come from the prover floor. The dual of
`setField_descriptorRefines`. -/
def setField_rotatedEncodesSF_construct (slot : Fin 8) (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (pre post : RecChainedState) (actor cell : CellId) (v : Int)
    (hspec : SetFieldSpec pre actor cell (slotName slot) v post)
    (prover : SetFieldTraceProver slot hash minit mfin maddrs t v) :
    rotatedEncodesSF slot hash minit mfin maddrs t pre post actor cell v where
  wi := prover.wi
  hwi := prover.hwi
  hwiNotLast := prover.hwiNotLast
  cellPre := prover.cellPre
  cellPost := prover.cellPost
  hwiRow := prover.hwiRow
  hwiEnc := prover.hwiEnc
  -- the row-canonicality envelope comes from the prover floor (a property of the honest trace row).
  hwiCanon := prover.hwiCanon
  hwval := prover.hwval
  -- §RESERVED-SLOT: `SetFieldSpec` now leads with `reservedField = false` (`hspec.1`), so the guard
  -- is `hspec.2.1` and every component below gains one `.2` (the whole-map move IS the spec's `cell =
  -- setFieldCellMap …` clause).
  hcellMove := hspec.2.2.1
  -- the receipt log advance IS the spec's `log` clause.
  logAdv := hspec.2.2.2.1
  -- the 4-leg admissibility guard IS the spec's `SetFieldGuard` (`hspec.2.1`).
  guard := hspec.2.1
  -- the 16 frame fields come from the spec's frame clauses.
  frAccounts          := hspec.2.2.2.2.1
  frCaps              := hspec.2.2.2.2.2.1
  frNullifiers        := hspec.2.2.2.2.2.2.1
  frRevoked           := hspec.2.2.2.2.2.2.2.1
  frCommitments       := hspec.2.2.2.2.2.2.2.2.1
  frBal               := hspec.2.2.2.2.2.2.2.2.2.1
  frSlotCaveats       := hspec.2.2.2.2.2.2.2.2.2.2.1
  frFactories         := hspec.2.2.2.2.2.2.2.2.2.2.2.1
  frLifecycle         := hspec.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDeathCert         := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegate          := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegations       := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegationEpoch   := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegationEpochAt := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frHeaps             := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frNullifierRoot     := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frRevokedRoot       := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frCommitmentsRoot       := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- **`setField_descriptorComplete_genuine` — the constructed decode realizes the GENUINE write.** From
`SetFieldSpec`, the written slot `slotName slot` of `cell` reads back exactly `v`
(`writeFieldCellMap_correct`). So the constructed witness performs the REAL field write — not a degenerate
no-write. The non-vacuity tooth. -/
theorem setField_descriptorComplete_genuine (slot : Fin 8)
    (pre post : RecChainedState) (actor cell : CellId) (v : Int)
    (hspec : SetFieldSpec pre actor cell (slotName slot) v post) :
    Dregg2.Exec.EffectsState.fieldOf (slotName slot) (post.kernel.cell cell) = v := by
  rw [hspec.2.2.1]
  exact (writeFieldCellMap_correct pre.kernel.cell cell (slotName slot) v).1

/-- **`setField_descriptorComplete` — the setField completeness rung (dual of
`setField_descriptorRefines`).** From a kernel field-write step `SetFieldSpec pre actor cell (slotName
slot) v post` + the realizable prover construction, a circuit witness of `setFieldV3 slot` whose published
commitment decodes to `(pre, post)`. Mirrors `transfer_descriptorComplete`. -/
theorem setField_descriptorComplete (slot : Fin 8)
    (S : CommitSurface) (hash : List ℤ → ℤ)
    (buildWitness : ∀ (pre post : RecChainedState) (actor cell : CellId) (v : Int) (turn : BoundaryTurn),
      SetFieldSpec pre actor cell (slotName slot) v post →
      Σ' (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
        Satisfied2 hash (setFieldV3 slot) minit mfin maddrs t ×'
        (tracePublishedCommit t = commitOf S pre post turn) ×'
        SetFieldTraceProver slot hash minit mfin maddrs t v)
    (pre post : RecChainedState) (actor cell : CellId) (v : Int) (turn : BoundaryTurn)
    (hspec : SetFieldSpec pre actor cell (slotName slot) v post)
    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash (setFieldV3 slot) minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn ∧
      StateDecode S (commitOf S pre post turn) pre post := by
  obtain ⟨minit, mfin, maddrs, t, hsat, hpub, prover⟩ :=
    buildWitness pre post actor cell v turn hspec
  clear buildWitness
  have _henc : rotatedEncodesSF slot hash minit mfin maddrs t pre post actor cell v :=
    setField_rotatedEncodesSF_construct slot hash pre post actor cell v hspec prover
  exact ⟨minit, mfin, maddrs, t, hsat, hpub,
    stateDecode_construct _ pre post turn hpreWF hpostWF⟩

/-! ## §5 — axiom hygiene. -/

#assert_axioms burn_rotatedEncodesBurn_construct
#assert_axioms burn_descriptorComplete_genuine
#assert_axioms burn_descriptorComplete_well_genuine
#assert_axioms burn_descriptorComplete
#assert_axioms mint_rotatedEncodesMint_construct
#assert_axioms mint_descriptorComplete_genuine
#assert_axioms mint_descriptorComplete_well_genuine
#assert_axioms mint_descriptorComplete
#assert_axioms bridgeMint_descriptorComplete
#assert_axioms setField_rotatedEncodesSF_construct
#assert_axioms setField_descriptorComplete_genuine
#assert_axioms setField_descriptorComplete

end Dregg2.Circuit.CircuitCompletenessValue
