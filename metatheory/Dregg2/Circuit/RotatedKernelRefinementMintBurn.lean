/-
# Dregg2.Circuit.RotatedKernelRefinementMintBurn — the VALUE-leg circuit→kernel refinement for the
**burn**, **mint**, and **bridgeMint** effects, on the LIVE ROTATED descriptors.

This module is the burn/mint clone of `RotatedKernelRefinement` (the `transfer` template). For each
effect it builds the apex obligation: satisfying the LIVE rotated descriptor (a `Satisfied2 hash
<effect>V3 …` witness, with the chip/range side conditions the rotated denotation already requires)
together with the boundary decode FORCES the kernel leaf-spec's state movement
(`Spec.SupplyDestruction.BurnSpec` / `Spec.SupplyCreation.MintASpec`).

## The two worlds, and what the circuit FORCES vs. what the decode carries

The live prover runs the ROTATED descriptors:
  * `burnV3  := v3OfFrozen EffectVmEmitBurn.burnVmDescriptor`  (registry `burnVmDescriptor2R24`);
  * `mintV3  := v3OfFrozen mintTickFace = v3OfFrozen EffectVmEmitMint.mintVmDescriptor` (`mintVmDescriptor2R24`).
The kernel leaves are `BurnSpec` (holder `(cell,a)` debit, well `(a,a)` credit; the W1 return-to-well)
and `MintASpec` (well `(a,a)` debit, recipient `(cell,a)` credit; the W1 issuer-move). bridgeMint
dispatches to the SAME `recCMintAsset` and meets `MintASpec` VERBATIM, so its refinement is the mint
refinement re-exported (`bridgeMint_descriptorRefines`, an alias).

Just as `transfer_descriptorRefines`, the honest split is:
  * the per-row circuit (`burnVm_faithful` / `mintVm_faithful`, lifted through `RowEncodes` to
    `CellBurnSpec` / `CellMintSpec`) FORCES the moved limb of the DESIGNATED debit/credit row — now, after
    the DEBT-A field migration, as a mod-`p` (BabyBear) CONGRUENCE (`burn_debit_forced` /
    `mint_credit_forced`);
  * the kernel-only residual (the authority/liveness/distinctness guard, the 16-field frame, the
    receipt log, and the CROSS-cell ledger frame `recTransferBal`) is NAMED as explicit decode legs in
    `rotatedEncodesBurn` / `rotatedEncodesMint` — not assumed away.

⚠⚠ DEBT-A FINDING (burn availability WAS a deployed forgery; it is now the shape of this BARE path
only). The mod-`p` migration REMOVED burn availability (`amt ≤ bal cell a`) from the circuit-forced
bucket: the bare debit gate is a field congruence and `BURN_AMOUNT_LO` is un-range-checked, so with
`p < 2^31` an over-burn wraps into the 30-bit range. This is WORSE than transfer's twin — burn's ledger
frame CREDITS the well `(a,a)` by `amt`, so the over-burn INFLATES well supply = mint-from-nothing (§3,
`⚠⚠ BURN AVAILABILITY IS NOT CIRCUIT-FORCED`, concrete forgery given). Availability is therefore a NAMED
`rotatedEncodesBurn.guardAvail` residual ON THE BARE DESCRIPTOR. ✅ THE DENOTATION FIX AND THE DEPLOYMENT
BOTH LANDED: `RotatedKernelRefinementMintBurnAvail.lean:41-48` ("The deployment step — DONE (GAP 1-6 VK
epoch flip)") records that the live registry routes the HARDENED burn avail member — `EmitRotationV3.lean:121`
maps `burnVmDescriptor2R24` → `Emit.AvailWireMembers.burnV3AvailWire` — materialized into the re-keyed VK
epoch with the Rust 15-bit range table (commits aa282f8c0 → 1e12d8886 → 764225f0c → 72469afd0), so
production burn availability is circuit-FORCED and the well-supply-inflation forgery is UNSAT on the wire.
Mint has NO availability gate (the well is negative-capable) → NO mint-side forgery. The mod-`p`
conservation teeth (`burn_debit_forced` / `mint_credit_forced`) still forbid wrong-amount witnesses on the
bare path.

The both-polarity teeth (`burn_descriptorRefines_rejects_wrong_debit`, … `_wrong_credit` for mint)
witness that the circuit genuinely bites: a decode claiming a moved-limb post NOT `≡ pre ∓ amount [ZMOD
p]` is UNSAT, because the gate pins the limb as a BabyBear field congruence.

## Axiom hygiene

`#assert_axioms` on every theorem ⊆ {propext, Classical.choice, Quot.sound} + the named carriers
inherited through the imports (here NONE of the hash carriers are even needed — the value-block intent
is forced by the gates, not the commitment). NEW file; imports are read-only.
-/
import Dregg2.Circuit.RotatedKernelRefinement
import Dregg2.Circuit.Emit.EffectVmEmitBurn
import Dregg2.Circuit.Emit.EffectVmEmitMint
import Dregg2.Circuit.Spec.supplydestruction
import Dregg2.Circuit.Spec.supplycreation

namespace Dregg2.Circuit.RotatedKernelRefinementMintBurn

open Dregg2.Circuit.Emit
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitV2
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (eSA eSB eSub)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.RotatedKernelRefinement (RotTableSide)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §0 — the live rotated burn / mint descriptors.

`burnV3` is exactly the descriptor the rotated prover runs for a burn (`v3Registry`'s
`burnVmDescriptor2R24`). `mintV3` is the rotated tick-faced BridgeMint (`mintVmDescriptor2R24`); since
`mintTickFace = EffectVmEmitMint.mintVmDescriptor` definitionally, `mintV3 = v3OfFrozen mintVmDescriptor`. -/

/-- The live rotated burn descriptor (`v3Registry`'s `burnVmDescriptor2R24`). -/
def burnV3 : EffectVmDescriptor2 := v3OfFrozen EffectVmEmitBurn.burnVmDescriptor

theorem burnV3_eq : burnV3 = v3OfFrozen EffectVmEmitBurn.burnVmDescriptor := rfl

/-- The live rotated BridgeMint descriptor (`v3Registry`'s `mintVmDescriptor2R24`), through the
tick-faced source which COINCIDES with `mintVmDescriptor` (`mintTickFace_eq_source`). -/
theorem mintV3_eq_source : mintV3 = v3OfFrozen EffectVmEmitMint.mintVmDescriptor := rfl

/-- `burnVmDescriptor` is graduable — the decidable side condition `rotV3Frozen_sound_v1` needs. -/
theorem burn_graduable : graduable EffectVmEmitBurn.burnVmDescriptor = true := by decide

/-- `mintVmDescriptor` is graduable. -/
theorem mint_graduable : graduable EffectVmEmitMint.mintVmDescriptor = true := by decide

/-! ## §1 — BURN: the rotated→per-row→per-cell decode chain (the witness side).

`rotV3Frozen_sound_v1` yields, on every row, the v1 denotation of `burnVmDescriptor`; the burn per-row gates
(`burnRowGates`, all flag-independent `.gate`s) hold; `burnVm_faithful` + `intent_to_cellSpec` lift the
row's value block to `CellBurnSpec` (the `bal_lo` debit by `param1`, the frame freeze). -/

/-- The per-row burn GATES hold at an ACTIVE row (`i` NOT the last row), mirroring transfer's
`rotated_row_gates`. The burn gates are all `.gate` constraints which under the deployed
`when_transition()` bind on every row but the last — so on a TRANSITION row (`i + 1 ≠ t.rows.length`,
`isLast` flag `false`) their body equation holds at `false false`. (The `hnotlast` hypothesis is the
faithful obligation that the designated effect row is a genuine transition row, not the wrap/pad row;
any real ≥2-row trace carries it.) -/
theorem rotated_row_gates_burn (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash burnV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length) :
    ∀ c ∈ EffectVmEmitBurn.burnRowGates, c.holdsVm (envAt t i) false false := by
  have hv1 : satisfiedVm hash EffectVmEmitBurn.burnVmDescriptor
      (envAt t i) (i == 0) (i + 1 == t.rows.length) :=
    rotV3Frozen_sound_v1 permOut hash EffectVmEmitBurn.burnVmDescriptor minit mfin maddrs t
      burn_graduable (hside.toFaithful hsat) i hi
  have hlastf : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  intro c hc
  have hmem : c ∈ EffectVmEmitBurn.burnVmDescriptor.constraints := by
    unfold EffectVmEmitBurn.burnVmDescriptor
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
  have hh := hv1.1 c hmem
  rw [hlastf] at hh
  unfold EffectVmEmitBurn.burnRowGates EffectVmEmitBurn.gFieldFixAll at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨j, hj, rfl⟩ <;>
    simpa only [VmConstraint.holdsVm] using hh

/-- **`rotated_row_cellSpec_burn` — rotated witness ⟹ per-cell burn spec on row `i`.** -/
theorem rotated_row_cellSpec_burn (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash burnV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (pre post : CellState) (amt : ℤ)
    (henc : EffectVmEmitBurn.RowEncodes (envAt t i) pre amt post)
    (hrow : EffectVmEmitBurn.IsBurnRow (envAt t i)) :
    EffectVmEmitBurn.CellBurnSpec pre amt post := by
  have hint : EffectVmEmitBurn.BurnRowIntent (envAt t i) :=
    (EffectVmEmitBurn.burnVm_faithful (envAt t i) hrow).mp
      (rotated_row_gates_burn hash hside hsat i hi hnotlast)
  exact EffectVmEmitBurn.intent_to_cellSpec (envAt t i) pre post amt henc hint

/-! ## §2 — `rotatedEncodesBurn`: the witness boundary ⟷ kernel state decode (burn).

The designated DEBIT row is the HOLDER's burn row (`(cell,a)`): the burn gate debits its `bal_lo` by
`param1`. The well credit (`(a,a)` rises by `amt`) and the cross-cell ledger frame live in the named
`hledgerFrame := recTransferBal pre.bal cell a a amt` leg (the per-cell row debits ONE entry; the
single-sign burn gate cannot also CREDIT the well — that leg is the kernel `recTransferBal` definition,
carried, with the circuit forcing the holder limb to agree). The guard / frame / log are the kernel
residual the value block cannot carry — NAMED, mirroring transfer's `rotatedEncodes`. -/

/-- The decode relating a satisfying rotated burn witness's HOLDER debit row to a kernel `pre → post`
burn of asset `a` from holder `cell` (well `a`) by `amt`, on actor `actor`. DATA-bearing (`Type`):
exhibits the designated debit row + its `CellState`s, the boundary-tying limb equalities, and the
kernel-side residual. -/
structure rotatedEncodesBurn (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ) : Type where
  -- the designated holder-debit row + its decode
  di : Nat
  hdi : di < t.rows.length
  -- the designated debit row is an ACTIVE (transition) row, NOT the wrap/pad last row: the deployed
  -- gates run under `when_transition()`, so the move is forced only off the last row. Any real ≥2-row
  -- burn trace carries this (the prover pads a wrap row after the effect row).
  hdiNotLast : di + 1 ≠ t.rows.length
  holderPre : CellState
  holderPost : CellState
  hdiRow : EffectVmEmitBurn.IsBurnRow (envAt t di)
  hdiEnc : EffectVmEmitBurn.RowEncodes (envAt t di) holderPre amt holderPost
  -- the decoded holder limbs ARE the kernel ledger at the burned coordinate `(cell,a)`.
  hholderPre  : holderPre.balLo  = pre.kernel.bal cell a
  hholderPost : holderPost.balLo = post.kernel.bal cell a
  -- the ledger FRAME: the post ledger is the return-to-well image of the pre ledger (the residual the
  -- per-cell holder row does not pin cross-cell — `recTransferBal cell a a amt`).
  hledgerFrame : post.kernel.bal = recTransferBal pre.kernel.bal cell a a amt
  -- the residual admissibility legs (kernel side-tables, not in the value block) — the `BurnGuard`.
  -- STAGE-3 authority split: holder self-redeem (`actor = cell`) OR issuer authority.
  guardAuth : actor = cell ∨ mintAuthorizedB pre.kernel.caps actor a = true
  guardNonNeg : 0 ≤ amt
  -- ⚠⚠ AVAILABILITY — NAMED decode residual (NOT circuit-forced). SEE `⚠⚠ BURN AVAILABILITY IS NOT
  -- CIRCUIT-FORCED`, §3. The mod-`p` (BabyBear) `bal_lo` debit gate + the 30-bit range check do NOT
  -- enforce `amt ≤ bal cell a` over ℤ: `p = 2013265921 < 2^31`, and `BURN_AMOUNT_LO` is un-range-checked,
  -- so an underflow `pre.bal − amt + p ∈ [0, 2^30)` passes the range while over-burning. This is WORSE
  -- than the transfer twin: burn's ledger frame CREDITS the well `(a,a)` by `amt` (`recTransferBal cell a
  -- a amt`), so an over-burn INFLATES well supply — a mint-from-nothing. Relocated here as an honest,
  -- visible admissibility obligation (joining `guardAuth`). ⚑ ON THE DEPLOYED PATH IT IS DISCHARGED, NOT
  -- ASSUMED: the borrow-chain fix shipped and the live registry routes the hardened burn member
  -- (`EmitRotationV3.lean:121` → `AvailWireMembers.burnV3AvailWire`; "The deployment step — DONE" at
  -- `RotatedKernelRefinementMintBurnAvail.lean:41-48`), where `burn_availability_and_exact_move_forced` derives
  -- this leg from the witness and `rotatedEncodesBurnAvail.toEncodes` rebuilds THIS structure with
  -- `guardAvail` proven. Nothing deployed reads the bare residual.
  guardAvail : amt ≤ pre.kernel.bal cell a
  guardLiveCell : cell ∈ pre.kernel.accounts
  guardLiveWell : a ∈ pre.kernel.accounts
  guardDistinct : cell ≠ a
  -- the issuer well is lifecycle-LIVE ("Destroyed is terminal"): membership (`guardLiveWell`) is NOT
  -- liveness — a member-but-Destroyed well is refused. COMMITMENT-BINDABLE: it reads `lifecycle`,
  -- which the deployed record_digest binds (and the `frLifecycle` frame already carries it).
  guardLifecycleLive : cellLifecycleLive pre.kernel a = true
  -- the 16 non-`bal` kernel frame fields + the receipt-log advance (the full `BurnSpec` frame residual).
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
  frCommitmentsRoot : post.kernel.commitmentsRoot = pre.kernel.commitmentsRoot
  logAdv : post.log = Spec.SupplyDestruction.burnReceipt actor cell a amt :: pre.log

/-! ## §3 — BURN: the circuit FORCES the holder debit (mod-`p`); availability is a NAMED residual. -/

/-- The holder row's per-cell spec, read onto the kernel ledger: `post.bal cell a ≡ pre.bal cell a −
amt [ZMOD p]`. **MOD-p CORRECTION (DEBT-A migration):** the deployed `bal_lo` debit gate `holdsVm` now
denotes `gBalLoDebit.eval ≡ 0 [ZMOD 2013265921]` (a BabyBear field constraint), NOT the old ℤ `= 0`, and
`CellBurnSpec` migrated to a `≡ [ZMOD p]` congruence. So the circuit FORCES the debit move only as a
mod-`p` congruence — a canonical trace can carry an ℤ residual equal to `p ≠ 0`. The move IS still
circuit-forced, just in the field (mirror of transfer's `debit_forced`). -/
theorem burn_debit_forced (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash burnV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (henc : rotatedEncodesBurn hash minit mfin maddrs t pre post actor cell a amt) :
    post.kernel.bal cell a ≡ pre.kernel.bal cell a - amt [ZMOD 2013265921] := by
  have hspec : EffectVmEmitBurn.CellBurnSpec henc.holderPre amt henc.holderPost :=
    rotated_row_cellSpec_burn hash hside hsat henc.di henc.hdi henc.hdiNotLast henc.holderPre
      henc.holderPost amt henc.hdiEnc henc.hdiRow
  obtain ⟨hmove, _, _, _, _, _⟩ := hspec
  -- hmove : holderPost.balLo ≡ holderPre.balLo − amt [ZMOD p]; the limb ties are ℤ equalities of subterms.
  rwa [henc.hholderPost, henc.hholderPre] at hmove

/-! ### ⚠⚠ BURN AVAILABILITY IS NOT CIRCUIT-FORCED under the mod-p denotation — the wrap-class forgery.

**Finding (DEBT-A migration, 2026-07-11).** The old `burn_availability_forced` derived `amt ≤ pre.bal
cell a` from `0 ≤ holderPost.balLo` (range) + `holderPost.balLo = holderPre.balLo − amount` (gate, over
ℤ). The mod-p migration replaced the debit gate ℤ equality with a BabyBear field congruence: `holdsVm
(.gate gBalLoDebit)` now denotes `gBalLoDebit.eval ≡ 0 [ZMOD 2013265921]`, so the circuit forces only
`holderPost.balLo ≡ holderPre.balLo − amt [ZMOD p]`, and the range table pins only `0 ≤ holderPost.balLo
< 2^30`. Because `p = 2013265921 < 2^31` and `BURN_AMOUNT_LO` carries **no** range check, a prover can
pick `amt` with `pre.bal − amt < 0` yet whose canonical field value `pre.bal − amt + p` lands in
`[0, 2^30)` — passing the range check while over-burning.

CONCRETE forgery (holder-debit gate `post − pre + amt ≡ 0 [ZMOD p]`):
  `pre.bal cell a = 0`, `amt = 1000000000` ⟹ `holderPost.balLo = p − 1000000000 = 1013265921 ∈ [0, 2^30)`.
The gate holds mod-`p` and `0 ≤ holderPost.balLo < 2^30`, yet `amt = 10^9 > 0 = pre.bal cell a` — an
underflow. This is the SAME wrap-class as transfer's availability gap, but **WORSE**: burn's ledger
frame `hledgerFrame = recTransferBal pre.bal cell a a amt` CREDITS the well `(a,a)` by `amt`, so the
over-burn INFLATES the well's supply — a mint-from-nothing (the debit "spends" a balance that was not
there, the credit manufactures the well side). Mod-`p` alone does not pin the ℤ value, and the adversary
picks a `p`-shifted decomposition.

An INEQUALITY has no mod-`p`-faithful restatement (order is not preserved mod `p`), so — unlike
`burn_debit_forced` — burn availability CANNOT be restated-and-proved on THIS bare gate set. It was a
genuine deployed forgery the migration exposed. ✅ THE DENOTATION FIX SHIPPED, and it is the borrow
option: the §8¾ hardened burn descriptor decomposes the debit into 15-bit limbs with a borrow chain and
a no-final-borrow gate, range-checks the amount and operand limbs, and DERIVES availability in-circuit
(`RotatedKernelRefinementMintBurnAvail.burn_availability_and_exact_move_forced`, with the over-burn
UNSAT via `burn_descriptorRefinesAvail_rejects_overburn`). The live registry routes that member
(`EmitRotationV3.lean:121`), so the forgery above is a fact about the BARE gate set only.

⚑ HONEST RELOCATION (not laundering): burn availability is therefore moved OUT of the circuit-forced
bucket and NAMED as an explicit `rotatedEncodesBurn.guardAvail` decode residual — joining `guardAuth` /
`guardLiveCell` / … as an admissibility leg the per-cell value block does not carry — with this note as
its provenance. `burn_descriptorRefines` sources availability from `henc.guardAvail`, so a wrong-amount /
non-conserving burn is still refused by `burn_debit_forced` (mod-`p`), while the availability leg rides an
honest, visible assumption. On the DEPLOYED path that assumption is discharged, not assumed:
`RotatedKernelRefinementMintBurnAvail` derives it from the witness and `ClosureFinalAvail.lean:162-164`
carries it to the apex ("availability … is FORCED by the deployed borrow chain — the `_availFix` `ext`
slot carries NO `availOf`: `availOf` is DISCHARGED at the apex"). -/

set_option maxHeartbeats 800000 in
/-- **`burn_descriptorRefines` — THE BURN CIRCUIT→KERNEL REFINEMENT.** Satisfying the LIVE rotated burn
descriptor (`Satisfied2 hash burnV3 …`, with the chip/range side conditions) together with
`rotatedEncodesBurn` forces the kernel's `BurnSpec pre actor cell a amt post`. The holder ledger debit
MOVEMENT comes FROM THE WITNESS (`burn_debit_forced`, mod-`p`); ⚠ AVAILABILITY (`amt ≤ bal cell a`) is
NO LONGER circuit-forced under mod-`p` (a wrap-class forgery that INFLATES the well — see `⚠⚠ BURN
AVAILABILITY IS NOT CIRCUIT-FORCED`, §3) and is a NAMED decode residual `henc.guardAvail`. The rest of the
kernel-side residual (authority / liveness / distinctness / the 16-field frame / the well-credit ledger
frame / the log) comes from the decode. -/
theorem burn_descriptorRefines (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash burnV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (henc : rotatedEncodesBurn hash minit mfin maddrs t pre post actor cell a amt) :
    Spec.SupplyDestruction.BurnSpec pre actor cell a amt post := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- BurnGuard: authority / non-neg / AVAILABILITY / live-cell / live-well / distinct / lifecycle-live.
    -- ⚠ availability is `henc.guardAvail` — a NAMED decode residual, NOT circuit-forced under mod-p (a
    -- wrap-class forgery that inflates the well; see `⚠⚠ BURN AVAILABILITY IS NOT CIRCUIT-FORCED`, §3).
    -- The debit MOVEMENT is still circuit-forced (mod-p) via `burn_debit_forced` (the §3 tooth).
    exact ⟨henc.guardAuth, henc.guardNonNeg, henc.guardAvail,
      henc.guardLiveCell, henc.guardLiveWell, henc.guardDistinct, henc.guardLifecycleLive⟩
  · exact henc.hledgerFrame
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
  · exact henc.frCommitmentsRoot

/-- **`burn_descriptorRefines_rejects_wrong_debit` — the conservation tooth (burn, mod-p).** A decode
claiming a holder post-balance NOT the genuine debit `pre.bal cell a − amt` **mod `p`** rides NO
satisfying witness: the circuit pins the burn limb as a BabyBear field congruence, so a wrong-amount /
non-conserving burn (one that is not `≡ pre.bal − amt [ZMOD p]`) is UNSAT. -/
theorem burn_descriptorRefines_rejects_wrong_debit (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash burnV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (henc : rotatedEncodesBurn hash minit mfin maddrs t pre post actor cell a amt)
    (hwrong : ¬ (post.kernel.bal cell a ≡ pre.kernel.bal cell a - amt [ZMOD 2013265921])) :
    False :=
  hwrong (burn_debit_forced hash hside hsat pre post actor cell a amt henc)

/-! ## §4 — MINT: the rotated→per-row→per-cell decode chain (the witness side).

Identical shape to burn, over `mintV3` / `mintVmDescriptor` / `mintRowGates` / `mintVm_faithful`. The
designated row is the RECIPIENT's credit row (`(cell,a)`): the mint gate credits its `bal_lo` by
`param1`. The well debit (`(a,a)` falls) + the cross-cell ledger frame are the named `recTransferBal a
cell a amt` leg. -/

/-- The per-row mint GATES hold at an ACTIVE row (`i` NOT the last row). The mint gates are all
`.gate` constraints which under the deployed `when_transition()` bind on every row but the last — so
on a TRANSITION row (`i + 1 ≠ t.rows.length`, `isLast` flag `false`) their body equation holds at
`false false`. (The `hnotlast` hypothesis is the faithful obligation that the designated effect row
is a genuine transition row, not the wrap/pad row.) -/
theorem rotated_row_gates_mint (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash mintV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length) :
    ∀ c ∈ EffectVmEmitMint.mintRowGates, c.holdsVm (envAt t i) false false := by
  have hv1 : satisfiedVm hash EffectVmEmitMint.mintVmDescriptor
      (envAt t i) (i == 0) (i + 1 == t.rows.length) :=
    rotV3Frozen_sound_v1 permOut hash EffectVmEmitMint.mintVmDescriptor minit mfin maddrs t
      mint_graduable (hside.toFaithful hsat) i hi
  have hlastf : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  intro c hc
  have hmem : c ∈ EffectVmEmitMint.mintVmDescriptor.constraints := by
    unfold EffectVmEmitMint.mintVmDescriptor
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl hc))
  have hh := hv1.1 c hmem
  rw [hlastf] at hh
  unfold EffectVmEmitMint.mintRowGates EffectVmEmitMint.gFieldFixAll at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨j, hj, rfl⟩ <;>
    simpa only [VmConstraint.holdsVm] using hh

/-- **`rotated_row_cellSpec_mint` — rotated witness ⟹ per-cell mint spec on row `i`.** -/
theorem rotated_row_cellSpec_mint (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash mintV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (pre post : CellState) (amt : ℤ)
    (henc : EffectVmEmitMint.RowEncodes (envAt t i) pre amt post)
    (hrow : EffectVmEmitMint.IsMintRow (envAt t i)) :
    EffectVmEmitMint.CellMintSpec pre amt post := by
  have hint : EffectVmEmitMint.MintRowIntent (envAt t i) :=
    (EffectVmEmitMint.mintVm_faithful (envAt t i) hrow).mp
      (rotated_row_gates_mint hash hside hsat i hi hnotlast)
  exact EffectVmEmitMint.intent_to_cellSpec (envAt t i) pre post amt henc hint

/-! ## §5 — `rotatedEncodesMint`: the witness boundary ⟷ kernel state decode (mint).

The designated CREDIT row is the RECIPIENT's mint row (`(cell,a)`). The named residual carries the
`MintASpec` guard (`mintAdmit`), the well-debit ledger frame `recTransferBal a cell a amt`, the 16
frame fields, and the receipt log. -/

/-- The decode relating a satisfying rotated mint witness's RECIPIENT credit row to a kernel
`pre → post` mint of asset `a` into recipient `cell` (well `a`) by `amt`, on actor `actor`. -/
structure rotatedEncodesMint (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ) : Type where
  -- the designated recipient-credit row + its decode
  ci : Nat
  hci : ci < t.rows.length
  -- the designated credit row is an ACTIVE (transition) row, NOT the wrap/pad last row: the deployed
  -- gates run under `when_transition()`, so the move is forced only off the last row. Any real ≥2-row
  -- mint trace carries this (the prover pads a wrap row after the effect row).
  hciNotLast : ci + 1 ≠ t.rows.length
  recipPre : CellState
  recipPost : CellState
  hciRow : EffectVmEmitMint.IsMintRow (envAt t ci)
  hciEnc : EffectVmEmitMint.RowEncodes (envAt t ci) recipPre amt recipPost
  -- the decoded recipient limbs ARE the kernel ledger at the minted coordinate `(cell,a)`.
  hrecipPre  : recipPre.balLo  = pre.kernel.bal cell a
  hrecipPost : recipPost.balLo = post.kernel.bal cell a
  -- the ledger FRAME: the post ledger is the issuer-move image of the pre ledger
  -- (`recTransferBal a cell a amt` — well `(a,a)` debited, recipient `(cell,a)` credited).
  hledgerFrame : post.kernel.bal = recTransferBal pre.kernel.bal a cell a amt
  -- the residual admissibility legs (the `mintAdmit` guard).
  guardAuth : mintAuthorizedB pre.kernel.caps actor a = true
  guardNonNeg : 0 ≤ amt
  guardLiveWell : a ∈ pre.kernel.accounts
  guardLiveCell : cell ∈ pre.kernel.accounts
  guardDistinct : a ≠ cell
  -- the issuer (well / bridge) cell is lifecycle-LIVE ("Destroyed is terminal"): a member-but-Destroyed
  -- issuer is refused. COMMITMENT-BINDABLE: reads `lifecycle` (deployed record_digest binds it; the
  -- `frLifecycle` frame already carries it).
  guardLifecycleLive : cellLifecycleLive pre.kernel a = true
  -- the 16 non-`bal` kernel frame fields + the receipt-log advance.
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
  frCommitmentsRoot : post.kernel.commitmentsRoot = pre.kernel.commitmentsRoot
  logAdv : post.log = Spec.SupplyCreation.mintReceipt actor cell a amt :: pre.log

/-! ## §6 — MINT: the circuit FORCES the recipient credit. -/

/-- The recipient row's per-cell spec, read onto the kernel ledger: `post.bal cell a ≡ pre.bal cell a +
amt [ZMOD p]`. **MOD-p CORRECTION (DEBT-A migration):** the deployed `bal_lo` credit gate `holdsVm` now
denotes a BabyBear field congruence and `CellMintSpec` migrated to `≡ [ZMOD p]`, so the circuit FORCES the
`+amount` credit only as a mod-`p` congruence (mirror of transfer's `credit_forced`). (Note: a mint has
NO availability gate — the well is negative-capable — so there is NO mint-side availability forgery.) -/
theorem mint_credit_forced (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash mintV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (henc : rotatedEncodesMint hash minit mfin maddrs t pre post actor cell a amt) :
    post.kernel.bal cell a ≡ pre.kernel.bal cell a + amt [ZMOD 2013265921] := by
  have hspec : EffectVmEmitMint.CellMintSpec henc.recipPre amt henc.recipPost :=
    rotated_row_cellSpec_mint hash hside hsat henc.ci henc.hci henc.hciNotLast henc.recipPre
      henc.recipPost amt henc.hciEnc henc.hciRow
  obtain ⟨hmove, _, _, _, _, _⟩ := hspec
  -- hmove : recipPost.balLo ≡ recipPre.balLo + amt [ZMOD p]; the limb ties are ℤ equalities of subterms.
  rwa [henc.hrecipPost, henc.hrecipPre] at hmove

set_option maxHeartbeats 800000 in
/-- **`mint_descriptorRefines` — THE MINT CIRCUIT→KERNEL REFINEMENT.** Satisfying the LIVE rotated mint
descriptor (`Satisfied2 hash mintV3 …`) together with `rotatedEncodesMint` forces the kernel's
`MintASpec pre actor cell a amt post`. The recipient ledger credit comes FROM THE WITNESS
(`mint_credit_forced`); the kernel-side residual (the `mintAdmit` guard, the well-debit ledger frame,
the 16-field frame, the log) comes from the decode. (Note: a mint has NO availability gate — the well
is negative-capable — so the guard has no circuit-availability leg, unlike burn/transfer.) -/
theorem mint_descriptorRefines (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash mintV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (henc : rotatedEncodesMint hash minit mfin maddrs t pre post actor cell a amt) :
    Spec.SupplyCreation.MintASpec pre actor cell a amt post := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- mintAdmit: authority / non-neg / well-membership / recipient-membership / distinctness / lifecycle-live.
    exact ⟨henc.guardAuth, henc.guardNonNeg, henc.guardLiveWell, henc.guardLiveCell,
      henc.guardDistinct, henc.guardLifecycleLive⟩
  · exact henc.hledgerFrame
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
  · exact henc.frCommitmentsRoot

/-- **`mint_descriptorRefines_rejects_wrong_credit` — the conservation tooth (mint, mod-p).** A decode
claiming a recipient post-balance NOT the genuine credit `pre.bal cell a + amt` **mod `p`** rides NO
satisfying witness: the circuit pins the mint limb as a BabyBear field congruence, so a wrong-amount
mint (one that is not `≡ pre.bal + amt [ZMOD p]`) is UNSAT. -/
theorem mint_descriptorRefines_rejects_wrong_credit (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash mintV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (henc : rotatedEncodesMint hash minit mfin maddrs t pre post actor cell a amt)
    (hwrong : ¬ (post.kernel.bal cell a ≡ pre.kernel.bal cell a + amt [ZMOD 2013265921])) :
    False :=
  hwrong (mint_credit_forced hash hside hsat pre post actor cell a amt henc)

/-! ## §7 — bridgeMint: the SAME refinement, re-exported.

`execFullA_bridgeMintA` dispatches to the SAME `recCMintAsset` and the bridge cell IS the issuer, so a
committed `bridgeMintA` meets `MintASpec` VERBATIM (`Spec.SupplyCreation.execBridgeMintA_iff_spec`). Its
live descriptor is the SAME `mintV3`. So bridgeMint's value-leg refinement is the mint refinement, with
no re-proof — the witness, decode, and conclusion are identical (the alias makes the intent explicit). -/

/-- **`bridgeMint_descriptorRefines` — bridgeMint refines to `MintASpec` (alias of mint).** Satisfying
the LIVE rotated `mintV3` descriptor (BridgeMint's registry leg) with `rotatedEncodesMint` forces
`MintASpec pre actor cell a amt post` — the SAME spec a committed `bridgeMintA` meets
(`execBridgeMintA_iff_spec`). Re-exported, not re-proved. -/
theorem bridgeMint_descriptorRefines (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash mintV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (henc : rotatedEncodesMint hash minit mfin maddrs t pre post actor cell a amt) :
    Spec.SupplyCreation.MintASpec pre actor cell a amt post :=
  mint_descriptorRefines hash hside hsat pre post actor cell a amt henc

/-! ## §8 — Axiom-hygiene tripwires. -/

#assert_axioms burn_graduable
#assert_axioms mint_graduable
#assert_axioms rotated_row_gates_burn
#assert_axioms rotated_row_cellSpec_burn
#assert_axioms burn_debit_forced
#assert_axioms burn_descriptorRefines
#assert_axioms burn_descriptorRefines_rejects_wrong_debit
#assert_axioms rotated_row_gates_mint
#assert_axioms rotated_row_cellSpec_mint
#assert_axioms mint_credit_forced
#assert_axioms mint_descriptorRefines
#assert_axioms mint_descriptorRefines_rejects_wrong_credit
#assert_axioms bridgeMint_descriptorRefines

end Dregg2.Circuit.RotatedKernelRefinementMintBurn
