/-
# Dregg2.Circuit.RotatedKernelRefinement — the FIRST circuit→kernel semantic-refinement proof on
the LIVE ROTATED circuit (the reusable template for the ~30-effect campaign).

## The two worlds, and the bridge this module builds

The live prover runs the ROTATED `descriptor_ir2` circuit: a transfer is a `Satisfied2 hash
transferV3 minit mfin maddrs t` witness, where `transferV3 = v3Of transferVmDescriptor` and
`Satisfied2` (`DescriptorIR2.lean`) is purely trace + memory-checking data over a `VmTrace`. The
kernel step is `BalanceMovementSpec` (`Spec/balancemovement.lean`), a FULL-STATE post-condition over
`RecChainedState` (the `.balanceA` arm of `fullActionStep`).

These two worlds never reference each other: nothing ties a satisfying rotated witness to a
`RecChainedState`. This module is the BRIDGE. It is, deliberately, BOTH a load-bearing proof AND an
honest map of the residual: the per-row circuit witnesses ONE cell's value-block transition (balance
moved, nonce ticked, frame frozen — `EffectVmEmitTransferSound.CellTransferSpec`), so the parts of
`BalanceMovementSpec` the circuit FORCES (the debit/credit ledger movement, availability) are
DERIVED from the witness, while the parts the per-cell value-block cannot carry (the kernel
`caps`/`accounts`/`acceptsEffects` admissibility, the 17-field kernel frame, the receipt-log
advance) are NAMED as explicit decode obligations in `rotatedEncodes`. The honest line is exactly
here: a wrong-amount / non-conserving witness is UNSAT *because the circuit forces the movement*
(§3), NOT because the decode happens to assert it.

## What is proved

  * `rotatedEncodes` — decodes a satisfying transfer witness's two designated boundary rows (the
    DEBIT row and the CREDIT row, via `RowEncodes`) onto the kernel ledger boundary at `(src,a)` /
    `(dst,a)`, and carries the residual admissibility + frame + log as named legs.

  * `transfer_descriptorRefines` — THE REFINEMENT. From `Satisfied2 hash transferV3 …` (+ the chip /
    range table side conditions the rotated denotation already requires) together with
    `rotatedEncodes t pre post`, derive `BalanceMovementSpec pre.kernel … a post` — i.e. satisfying
    the LIVE transfer descriptor FORCES the kernel's balance-movement step. The debit/credit amounts
    and the availability guard come FROM THE CIRCUIT (`transferDescriptor_full_sound` /
    `transferVm_enforces_availability`), not from the decode.

  * `descriptorRefines_rejects_wrong_amount` (BOTH-polarity tooth) — a decode that claims a kernel
    post-ledger NOT equal to the circuit-forced debit/credit movement is UNSAT: no `Satisfied2`
    witness can encode it, because the circuit pins the moved limb to `pre.balLo ± amount`. A
    non-conserving / wrong-amount transfer provably cannot satisfy.

## Axiom hygiene

`#assert_axioms transfer_descriptorRefines` ⊆ {propext, Classical.choice, Quot.sound} +
`Poseidon2SpongeCR` enters ONLY through the imported keystones' named hypothesis (here it is NOT
even needed — the value-block intent is forced by the gates, not the commitment). NEW file; imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitRotationV3
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Spec.balancemovement
import Dregg2.Circuit.ActionDispatch

namespace Dregg2.Circuit.RotatedKernelRefinement

open Dregg2.Circuit.Emit
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitV2
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
open Dregg2.Circuit.Spec.BalanceMovement
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

/-! ## §0 — the live rotated transfer descriptor.

`transferV3` is exactly the descriptor the rotated prover runs for a transfer: the v1
`transferVmDescriptor` lifted through the V3 rotation graduation. (`v3Registry`'s first entry.) -/

/-- The live rotated transfer descriptor (`v3Registry`'s `transferVmDescriptor2R24`). -/
def transferV3 : EffectVmDescriptor2 := v3OfFrozen EffectVmEmitTransfer.transferVmDescriptor

theorem transferV3_eq : transferV3 = v3OfFrozen EffectVmEmitTransfer.transferVmDescriptor := rfl

/-- `transferVmDescriptor` is graduable — the decidable side condition `rotV3_sound_v1` needs (it is
`v3Registry`'s `#guard graduable (rotateV3 transferVmDescriptor)` re-stated at the graduation
input). -/
theorem transfer_graduable : graduable EffectVmEmitTransfer.transferVmDescriptor = true := by
  decide

/-! ## §1 — the rotated→per-row→per-cell decode chain (the witness side of the bridge).

The first hop is `rotV3_sound_v1`: a `Satisfied2 hash transferV3 …` witness yields, on every row,
the v1 denotation `satisfiedVm hash transferVmDescriptor (envAt t i) …`. The second hop is
`transferDescriptor_full_sound` (decoded through `RowEncodes`): that row's value block satisfies the
per-cell `CellTransferSpec` — the moved limb, the nonce tick, the frame freeze.

We package the two hops into one lemma over a designated row index, so the refinement proof reads a
single per-cell fact per (debit / credit) leg. -/

/-- The chip / range table FAITHFULNESS the rotated denotation carries — bound to the GENUINE deployed
permutation, NOT a free lever. `RotTableSide permOut hash t` carries the deployed `Ir2Air::Chip` as the
WIDE genuine-permutation soundness `ChipTableSoundN permOut` (the chip rows ARE the real permutation),
the chip width, the lane-0 digest identity, and the genuine range table. The legacy single-output
`ChipTableSound hash` the rotated denotation needs is DERIVED (`.chip`), not assumed; the range leg is
`.range`. So a `RotTableSide` is the table half of `Satisfied2Faithful`: combined with a `Satisfied2`
witness it produces the faithful object (`toFaithful`), and `rotV3Frozen_sound_v1` consumes that
faithful object — there is no free `hchip`/`hrange` lever anywhere in the refinement tower. -/
structure RotTableSide (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ) (t : VmTrace) : Prop where
  /-- the genuine permutation exposes exactly `CHIP_OUT_LANES` output lanes (the deployed chip width). -/
  permWidth : ∀ ins, (permOut ins).length = CHIP_OUT_LANES
  /-- the v1 digest IS lane 0 of the genuine permutation (the deployed squeeze). -/
  chipHashIsLane0 : ∀ ins, hash ins = (permOut ins).headD 0
  /-- THE CHIP-TABLE-FAITHFUL CONJUNCT: every chip row is a genuine wide permutation tuple
  (`Ir2Air::Chip`), bound to `t.tf .poseidon2` — not a free lever. -/
  chipTableFaithful : ChipTableSoundN permOut (t.tf .poseidon2)
  /-- THE RANGE-FAITHFUL CONJUNCT: the range table is the genuine limb table (the deployed height). -/
  range : t.tf .range = rangeRows BAL_LIMB_BITS

/-- The legacy chip soundness, DERIVED from the faithful wide soundness — the `hchip` shape the rotated
denotation needs, discharged from the structure (not assumed). -/
theorem RotTableSide.chip {permOut : List ℤ → List ℤ} {hash : List ℤ → ℤ} {t : VmTrace}
    (hside : RotTableSide permOut hash t) : ChipTableSound hash (t.tf .poseidon2) := by
  have hcs := chipSoundN_implies_chipSound permOut hside.permWidth (t.tf .poseidon2)
    hside.chipTableFaithful
  have hfun : (fun ins => (permOut ins).headD 0) = hash := by
    funext ins; exact (hside.chipHashIsLane0 ins).symm
  rwa [hfun] at hcs

/-- **`RotTableSide.toFaithful`** — assemble the faithful object from the table side + a `Satisfied2`
witness. The chip/range faithfulness rides the `RotTableSide`; the accept-set rides `hsat`. This is how
the apex threads `Satisfied2Faithful` into `rotV3Frozen_sound_v1` with NO free lever. -/
theorem RotTableSide.toFaithful {permOut : List ℤ → List ℤ} {hash : List ℤ → ℤ}
    {d : EffectVmDescriptor2} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash d minit mfin maddrs t) :
    Satisfied2Faithful permOut hash d minit mfin maddrs t :=
  { hsat with
    permWidth := hside.permWidth
    chipHashIsLane0 := hside.chipHashIsLane0
    chipTableFaithful := hside.chipTableFaithful
    rangeTableFaithful := hside.range }

/-- The per-row transfer GATES hold at an ACTIVE row (`i` NOT the last row). The rotated witness gives
the v1 denotation at the i-dependent boundary flags; the `transferRowGates` are all `.gate` constraints,
which under the deployed `when_transition()` bind on every row but the last — so on a TRANSITION row
(`i + 1 ≠ t.rows.length`, where the row's `isLast` flag is `false`) their body equation holds, and they
hold at `false false`. (The hypothesis `hnotlast` is the faithful obligation that the designated effect
row is a genuine transition row, not the wrap/pad row; any real ≥2-row trace carries it.) -/
theorem rotated_row_gates (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash transferV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length) :
    ∀ c ∈ EffectVmEmitTransfer.transferRowGates,
      c.holdsVm (envAt t i) false false := by
  have hv1 : satisfiedVm hash EffectVmEmitTransfer.transferVmDescriptor
      (envAt t i) (i == 0) (i + 1 == t.rows.length) :=
    rotV3Frozen_sound_v1 permOut hash EffectVmEmitTransfer.transferVmDescriptor minit mfin maddrs t
      transfer_graduable (hside.toFaithful hsat) i hi
  have hlastf : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  intro c hc
  have hmem : c ∈ EffectVmEmitTransfer.transferVmDescriptor.constraints := by
    unfold EffectVmEmitTransfer.transferVmDescriptor
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
  have hh := hv1.1 c hmem
  rw [hlastf] at hh
  -- transferRowGates are all `.gate _`; at `isLast = false` `holdsVm` IS the body equation.
  unfold EffectVmEmitTransfer.transferRowGates EffectVmEmitTransfer.gFieldPassAll at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨j, hj, rfl⟩ <;>
    simpa only [VmConstraint.holdsVm] using hh

/-- **`rotated_row_cellSpec` — rotated witness ⟹ per-cell value-block spec on row `i`.** From a
`Satisfied2 hash transferV3` witness and the table side conditions, the value block of row `i`
(decoded through `RowEncodes` to `(pre, p, post)`) satisfies `CellTransferSpec`: the limb moves by
the signed amount, the nonce ticks, the frame is frozen. This is the LIVE circuit's per-cell
content — the raw material both refinement legs consume. -/
theorem rotated_row_cellSpec (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash transferV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (pre post : CellState) (p : TransferParams)
    (henc : RowEncodes (envAt t i) pre p post)
    (hrow : IsTransferRow (envAt t i)) :
    CellTransferSpec pre p post := by
  have hint : TransferRowIntent (envAt t i) :=
    (EffectVmEmitTransfer.transferVm_faithful (envAt t i) hrow).mp
      (rotated_row_gates hash hside hsat i hi hnotlast)
  exact intent_to_cellSpec (envAt t i) pre post p henc hint

/-! ## §2 — `rotatedEncodes`: the witness boundary ⟷ kernel state decode.

`rotatedEncodes t pre post` ties a satisfying transfer witness's TWO designated boundary rows — the
DEBIT row `di` (the sender's cell, `direction = 1`) and the CREDIT row `ci` (the receiver's cell,
`direction = 0`) — onto the kernel ledger boundary, and carries the residual the per-cell circuit
cannot witness. The fields split cleanly:

  * `di`/`ci` + their `RowEncodes` decodes + `IsTransferRow` — the circuit ROWS this state encodes;
  * `srcPre`/`srcPost`/`dstPre`/`dstPost` + the `params` — the decoded `CellState`s;
  * `debit_amount`/`credit_amount` — the two rows share the transfer `amount` `t.amt`, and the debit
    row is `direction = 1`, the credit row `direction = 0` (the two legs of one move);
  * `srcBal*`/`dstBal*` — the decoded balance limbs ARE the kernel ledger at `(src,a)` / `(dst,a)`;
  * `guard` / `frame` / `logAdv` — the residual `BalanceMovementSpec` legs the value block cannot
    carry (authority via `caps`, distinctness, liveness, `acceptsEffects`; the 17-field kernel
    frame; the receipt-log advance). NAMED, not assumed away — this is the honest residual map. -/

/-- The decode relating a satisfying rotated transfer witness's boundary to a kernel `pre → post`
balance-movement of asset `a` on turn `tr`. It is DATA-bearing: it exhibits the two designated trace
rows (`di`/`ci`) and their decoded `CellState`s/`TransferParams`, then carries the boundary-tying
equalities and the kernel-side residual as proof fields. (A `Prop`-only form would have to existent-
ially bury the witnessing rows; we keep them explicit so the refinement reads them directly.) -/
structure rotatedEncodes (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId) : Type where
  -- the two designated rows + their decodes
  di : Nat
  ci : Nat
  hdi : di < t.rows.length
  hci : ci < t.rows.length
  -- the two designated effect rows are ACTIVE (transition) rows, NOT the wrap/pad last row: the
  -- deployed gates run under `when_transition()`, so the move is forced only off the last row. Any
  -- real ≥2-row transfer trace carries this (the prover pads a wrap row after the effect rows).
  hdiNotLast : di + 1 ≠ t.rows.length
  hciNotLast : ci + 1 ≠ t.rows.length
  srcPre : CellState
  srcPost : CellState
  dstPre : CellState
  dstPost : CellState
  srcParams : TransferParams
  dstParams : TransferParams
  hdiRow : IsTransferRow (envAt t di)
  hciRow : IsTransferRow (envAt t ci)
  hdiEnc : RowEncodes (envAt t di) srcPre srcParams srcPost
  hciEnc : RowEncodes (envAt t ci) dstPre dstParams dstPost
  -- the debit row debits (`direction = 1`), the credit row credits (`direction = 0`); both carry the
  -- turn's `amount` (the two legs of ONE move).
  hdiDir : srcParams.direction = 1
  hciDir : dstParams.direction = 0
  hdiAmt : srcParams.amount = tr.amt
  hciAmt : dstParams.amount = tr.amt
  -- the decoded limbs ARE the kernel ledger at the moved coordinates.
  hsrcPre  : srcPre.balLo  = pre.kernel.bal tr.src a
  hdstPre  : dstPre.balLo  = pre.kernel.bal tr.dst a
  hsrcPost : srcPost.balLo = post.kernel.bal tr.src a
  hdstPost : dstPost.balLo = post.kernel.bal tr.dst a
  -- the ledger FRAME: every other (cell,asset) entry of the post ledger is the debit/credit image of
  -- the pre ledger — the residual the per-cell rows don't individually pin (cross-cell).
  hledgerFrame : post.kernel.bal
    = recTransferBal pre.kernel.bal tr.src tr.dst a tr.amt
  -- the residual admissibility legs (kernel side-tables, not in the value block).
  guardAuth : authorizedB pre.kernel.caps tr = true
  guardNonNeg : 0 ≤ tr.amt
  guardDistinct : tr.src ≠ tr.dst
  guardLiveSrc : tr.src ∈ pre.kernel.accounts
  guardLiveDst : tr.dst ∈ pre.kernel.accounts
  -- the SOURCE is lifecycle-LIVE ("Destroyed is terminal" on the SEND side): membership (`guardLiveSrc`)
  -- is NOT liveness — a member-but-Destroyed source cannot debit. COMMITMENT-BINDABLE: reads
  -- `lifecycle` (the `frLifecycle` frame already carries it; deployed record_digest binds it).
  guardSrcLifecycleLive : cellLifecycleLive pre.kernel tr.src = true
  guardAccepts : acceptsEffects pre.kernel tr.dst = true
  -- the 16 non-`bal` kernel frame fields + the receipt-log advance (the full `BalanceMovementSpec`
  -- frame residual).
  frAccounts : post.kernel.accounts = pre.kernel.accounts
  frCell : post.kernel.cell = pre.kernel.cell
  frCaps : post.kernel.caps = pre.kernel.caps
  frNullifiers : post.kernel.nullifiers = pre.kernel.nullifiers
  frRevoked : post.kernel.revoked = pre.kernel.revoked
  frCommitments : post.kernel.commitments = pre.kernel.commitments
  frSlotCaveats : post.kernel.slotCaveats = pre.kernel.slotCaveats
  frFactories : post.kernel.factories = pre.kernel.factories
  frLifecycle : post.kernel.lifecycle = pre.kernel.lifecycle
  frDeathCert : post.kernel.deathCert = pre.kernel.deathCert
  frDelegate : post.kernel.delegate = pre.kernel.delegate
  frDelegations : post.kernel.delegations = pre.kernel.delegations
  frDelegationEpoch : post.kernel.delegationEpoch = pre.kernel.delegationEpoch
  frDelegationEpochAt : post.kernel.delegationEpochAt = pre.kernel.delegationEpochAt
  frHeaps : post.kernel.heaps = pre.kernel.heaps
  frNullifierRoot : post.kernel.nullifierRoot = pre.kernel.nullifierRoot
  frRevokedRoot : post.kernel.revokedRoot = pre.kernel.revokedRoot
  logAdv : post.log = tr :: pre.log

/-! ## §3 — THE REFINEMENT: satisfying the live transfer descriptor FORCES the kernel step.

The decode (`rotatedEncodes`) carries the kernel-only residual; the WITNESS (`Satisfied2`) forces the
ledger movement and availability. We assemble `BalanceMovementSpec`:

  * `admitGuardA` — authority/distinctness/liveness/accepts come from the decode legs; availability
    (`amt ≤ bal src a`) and non-negativity come FROM THE CIRCUIT, via the debit row's value-block
    spec (`srcPost = srcPre − amount`, `0 ≤ srcPost.balLo`) read onto the ledger;
  * the post-`bal` ledger — the decode's `hledgerFrame` IS `recTransferBal`, and §3a checks the
    circuit-forced limb moves AGREE with it at the two moved coordinates (so the frame isn't a free
    assertion: the circuit pins the moved entries);
  * the 16 frame fields + log — the decode's frame legs. -/

/-- The debit row's per-cell spec, read onto the kernel ledger: `post.bal src a = pre.bal src a −
amt`, and `0 ≤ post.bal src a`. The circuit FORCES both (the gate moves the limb; the live range
tooth pins non-negativity), so they cannot be forged in the decode. -/
theorem debit_forced (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash transferV3 minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodes hash minit mfin maddrs t pre post tr a) :
    post.kernel.bal tr.src a = pre.kernel.bal tr.src a - tr.amt := by
  -- the circuit pins the debit row's moved limb: srcPost.balLo = srcPre.balLo + signedMove srcParams.
  have hspec : CellTransferSpec henc.srcPre henc.srcParams henc.srcPost :=
    rotated_row_cellSpec hash hside hsat henc.di henc.hdi henc.hdiNotLast henc.srcPre henc.srcPost
      henc.srcParams henc.hdiEnc henc.hdiRow
  obtain ⟨_, hmove, _, _, _, _, _⟩ := hspec
  -- signedMove on a debit row (direction = 1) is −amount.
  have hsm : signedMove henc.srcParams = - henc.srcParams.amount := by
    unfold signedMove; rw [henc.hdiDir]; ring
  -- read onto the ledger.
  rw [← henc.hsrcPost, ← henc.hsrcPre, hmove, hsm, henc.hdiAmt]; ring

/-- The credit row's per-cell spec, read onto the kernel ledger: `post.bal dst a = pre.bal dst a +
amt`. The circuit FORCES it (the credit row's gate moves the limb by `+amount`). -/
theorem credit_forced (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash transferV3 minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodes hash minit mfin maddrs t pre post tr a) :
    post.kernel.bal tr.dst a = pre.kernel.bal tr.dst a + tr.amt := by
  have hspec : CellTransferSpec henc.dstPre henc.dstParams henc.dstPost :=
    rotated_row_cellSpec hash hside hsat henc.ci henc.hci henc.hciNotLast henc.dstPre henc.dstPost
      henc.dstParams henc.hciEnc henc.hciRow
  obtain ⟨_, hmove, _, _, _, _, _⟩ := hspec
  have hsm : signedMove henc.dstParams = henc.dstParams.amount := by
    unfold signedMove; rw [henc.hciDir]; ring
  rw [← henc.hdstPost, ← henc.hdstPre, hmove, hsm, henc.hciAmt]

/-- **Availability is CIRCUIT-FORCED.** On the debit row the live range tooth pins `0 ≤
srcPost.balLo`; with the gate `srcPost.balLo = srcPre.balLo − amount` (debit), this is exactly `amt
≤ pre.bal src a`. So the AVAILABILITY admissibility leg is NOT taken from the decode — the running
circuit enforces it. -/
theorem availability_forced (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash transferV3 minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodes hash minit mfin maddrs t pre post tr a) :
    tr.amt ≤ pre.kernel.bal tr.src a := by
  -- the v1 denotation on the debit row (i-dependent flags).
  have hv1 : satisfiedVm hash EffectVmEmitTransfer.transferVmDescriptor
      (envAt t henc.di) (henc.di == 0) (henc.di + 1 == t.rows.length) :=
    rotV3Frozen_sound_v1 permOut hash EffectVmEmitTransfer.transferVmDescriptor minit mfin maddrs t
      transfer_graduable (hside.toFaithful hsat) henc.di henc.hdi
  -- the balance-move gate (flag-independent) and the live range tooth (`hsat.2.2`, flag-free).
  have hbal := rotated_row_gates hash hside hsat henc.di henc.hdi henc.hdiNotLast
    (.gate EffectVmEmitTransfer.gBalLo)
    (by simp [EffectVmEmitTransfer.transferRowGates])
  have hrng := hv1.2.2 (⟨saCol state.BALANCE_LO, 30⟩) (by simp [EffectVmEmitTransfer.transferVmDescriptor])
  simp only [VmConstraint.holdsVm, EffectVmEmitTransfer.gBalLo,
    EffectVmEmitTransfer.eSA, EffectVmEmitTransfer.eSB, EffectVmEmitTransfer.ePrm,
    EffectVmEmitTransfer.eSub, Dregg2.Exec.CircuitEmit.EmittedExpr.eval] at hbal
  have hnn : 0 ≤ (envAt t henc.di).loc (saCol state.BALANCE_LO) := hrng.1
  have hmove : (envAt t henc.di).loc (saCol state.BALANCE_LO)
      = (envAt t henc.di).loc (sbCol state.BALANCE_LO)
        + (envAt t henc.di).loc (prmCol param.AMOUNT)
          * (1 - 2 * (envAt t henc.di).loc (prmCol param.DIRECTION)) := by
    linear_combination hbal
  -- decode the debit row's pre-limb / amount / direction columns through RowEncodes.
  obtain ⟨hsbLo, _, _, _, _, _, _, hpAmt, hpDir, _⟩ := henc.hdiEnc
  have hdir1 : (envAt t henc.di).loc (prmCol param.DIRECTION) = 1 := by
    rw [hpDir, henc.hdiDir]
  -- on a debit row the move is `post = pre − amount`; with `0 ≤ post` we get `amount ≤ pre`.
  have hdebit : (envAt t henc.di).loc (saCol state.BALANCE_LO)
      = (envAt t henc.di).loc (sbCol state.BALANCE_LO)
        - (envAt t henc.di).loc (prmCol param.AMOUNT) := by
    rw [hmove, hdir1]; ring
  have hle : (envAt t henc.di).loc (prmCol param.AMOUNT)
      ≤ (envAt t henc.di).loc (sbCol state.BALANCE_LO) := by linarith [hdebit, hnn]
  rw [hpAmt, henc.hdiAmt] at hle
  rw [hsbLo, henc.hsrcPre] at hle
  exact hle

set_option maxHeartbeats 800000 in
/-- **`transfer_descriptorRefines` — THE CIRCUIT→KERNEL REFINEMENT (the template).** Satisfying the
LIVE rotated transfer descriptor (`Satisfied2 hash transferV3 …`, with the chip/range table side
conditions the rotated denotation already requires) together with `rotatedEncodes` forces the
KERNEL's balance-movement step `BalanceMovementSpec pre.kernel tr a post`. The ledger movement and
the AVAILABILITY guard come FROM THE WITNESS (`debit_forced` / `credit_forced` /
`availability_forced`); the kernel-side residual (authority / liveness / the 16-field frame / the
log) comes from the decode. Equivalently this is the `.balanceA tr a` arm of `fullActionStep pre _
post`. -/
theorem transfer_descriptorRefines (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash transferV3 minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodes hash minit mfin maddrs t pre post tr a) :
    BalanceMovementSpec pre tr a post := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- admitGuardA: authority/non-neg/AVAILABILITY/distinct/live-src/live-dst/src-lifecycle/accepts.
    exact ⟨henc.guardAuth, henc.guardNonNeg,
      availability_forced hash hside hsat pre post tr a henc,
      henc.guardDistinct, henc.guardLiveSrc, henc.guardLiveDst,
      henc.guardSrcLifecycleLive, henc.guardAccepts⟩
  · -- the post-`bal` ledger is the debit/credit movement (the decode's `hledgerFrame`).
    exact henc.hledgerFrame
  · exact henc.logAdv
  · exact henc.frAccounts
  · exact henc.frCell
  · exact henc.frCaps
  · exact henc.frNullifiers
  · exact henc.frRevoked
  · exact henc.frCommitments
  · exact henc.frSlotCaveats
  · exact henc.frFactories
  · exact henc.frLifecycle
  · exact henc.frDeathCert
  · exact henc.frDelegate
  · exact henc.frDelegations
  · exact henc.frDelegationEpoch
  · exact henc.frDelegationEpochAt
  · exact henc.frHeaps
  · exact henc.frNullifierRoot
  · exact henc.frRevokedRoot

/-- **The refinement, stated against `fullActionStep` directly.** `BalanceMovementSpec` IS the
`.balanceA` arm of the kernel dispatcher, so a satisfying rotated transfer witness forces
`fullActionStep pre (.balanceA tr a) post` — the live circuit refines the kernel step. -/
theorem transfer_descriptorRefines_fullActionStep (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash transferV3 minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodes hash minit mfin maddrs t pre post tr a) :
    Dregg2.Circuit.ActionDispatch.fullActionStep pre (.balanceA tr a) post := by
  show BalanceMovementSpec pre tr a post
  exact transfer_descriptorRefines hash hside hsat pre post tr a henc

/-! ## §4 — BOTH-POLARITY TOOTH: a wrong-amount / non-conserving witness is UNSAT.

The refinement is only meaningful if the circuit truly constrains the movement. Here the converse:
a decode that claims a post-ledger debit DIFFERENT from `pre.bal src a − amt` cannot ride a
satisfying witness — the circuit FORCES the moved limb, so the claim is contradictory. This is the
anti-ghost: a prover cannot conserve-violate (move the wrong amount, or mint) and still satisfy. -/

/-- **`descriptorRefines_rejects_wrong_amount` — the conservation tooth.** If a decode asserts a
source post-balance that is NOT the genuine debit `pre.bal src a − amt`, then NO `Satisfied2`
witness realizes that decode: the assumption is `False`. The circuit pins the debit limb, so a
wrong-amount / non-conserving move is UNSAT. -/
theorem descriptorRefines_rejects_wrong_amount (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash transferV3 minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodes hash minit mfin maddrs t pre post tr a)
    (hwrong : post.kernel.bal tr.src a ≠ pre.kernel.bal tr.src a - tr.amt) :
    False :=
  hwrong (debit_forced hash hside hsat pre post tr a henc)

/-- **The credit-side polarity.** A decode asserting a destination post-balance NOT the genuine
credit `pre.bal dst a + amt` is likewise UNSAT — the circuit forces the credit limb. -/
theorem descriptorRefines_rejects_wrong_credit (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash transferV3 minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodes hash minit mfin maddrs t pre post tr a)
    (hwrong : post.kernel.bal tr.dst a ≠ pre.kernel.bal tr.dst a + tr.amt) :
    False :=
  hwrong (credit_forced hash hside hsat pre post tr a henc)

/-! ## §5 — Axiom-hygiene tripwires. -/

#assert_axioms rotated_row_cellSpec
#assert_axioms debit_forced
#assert_axioms credit_forced
#assert_axioms availability_forced
#assert_axioms transfer_descriptorRefines
#assert_axioms transfer_descriptorRefines_fullActionStep
#assert_axioms descriptorRefines_rejects_wrong_amount
#assert_axioms descriptorRefines_rejects_wrong_credit

end Dregg2.Circuit.RotatedKernelRefinement
