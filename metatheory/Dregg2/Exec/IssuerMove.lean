/-
# Dregg2.Exec.IssuerMove — mint/burn AS ISSUER-MOVES over the real kernel (W1, DREGG3 §2.2 Asset).

The R2 probe (`Substrate/IssuerSupplyProbe.lean`) proved the issuer-supply value law and exhibited
mint-as-issuer-move as a commuting square over the EXISTING state; `Substrate/IssuerLedger.lean`
promoted it to the canonical forward model (both standalone). THIS module lands the mechanism in the
ANCHOR, over the REAL kernel state and the REAL step functions:

  * **`issuerMoveK`** — THE mint mechanism: an ordinary per-asset transfer `issuerOf a → dst`,
    gated on mint authority over the **ISSUER** cell (E2 — the issuer's program is the issuance
    policy), with **NO availability gate at the issuer's well** (E1 — the well is negative-capable;
    the issuer's balance IS −supply; solvency policy belongs to the issuer cell's program, the
    kernel keeps only conservation).
  * **`issuerBurnK`** — THE burn mechanism: the same move with the direction swapped (`src →
    issuerOf a`), gated on mint authority over the issuer PLUS availability at the HOLDER (`src` is
    an ordinary cell; you can only burn what you hold).
  * **`recKMintAssetIssuer` / `recKBurnAssetIssuer`** — the executor-shaped transitional wrappers
    (the SAME `(k, actor, cell, a, amt)` signature as the legacy `recKMintAsset`/`recKBurnAsset`,
    instantiated at the DREGG3 `AssetId := issuer-CellId` identity registry `issuerSelf`), each
    with its REAL equivalence theorem (`rfl` — the actual step functions, not the probe's
    view-level square). These are what the W1 VK rotation swaps the `execFullA` `.mintA`/`.burnA`/
    `.bridgeMintA` dispatch arms onto.
  * **Preservation**: both mechanisms preserve `ExactConservation` (the W1 value law,
    `RecordKernel §VALUE-UNIFY`) — the proof needs NO availability gate (conservation never
    depended on it; the negative well is sound for the value law).
  * **The non-vacuity teeth**: the LEGACY `recKMintAsset` (bare supply-increment credit) and
    `recKBurnAsset` (bare supply-decrement debit) each provably BREAK `ExactConservation` — so the
    issuer-move reformulation is a REPAIR, not a relabeling — and a supply-inflating step is
    provably rejected by the law. Plus the genesis-order tooth: `issuerMoveK` fail-closes on a
    non-live issuer, so the bootstrap order (create issuer cell → mint) is ENFORCED.
  * **`issuerMint_pointwise_vs_credit`** — the REAL-step commuting relation between the legacy
    credit law and the issuer-move: a committed issuer-mint's ledger IS the committed legacy mint's
    ledger with the issuer's well debited by exactly the minted amount — pointwise, at every
    `(cell, asset)`. The probe proved this through the issuer-supply VIEW; here it is the two
    ACTUAL step functions side by side.

The legacy `recKMintAsset`/`recKBurnAsset` (and the circuit weld stack over them —
`Circuit/Spec/supplycreation.lean`, `Circuit/Argus/Effects/BridgeMint.lean`, the `Witness/*` and
`Emit/EffectVm*` mint/burn files) stay in-tree describing the DEPLOYED circuits until the W1 VK
rotation regenerates them against these verbs. The dispatch-arm cutover + that sweep is the
rotation's executor-mirror worklist.

`#assert_axioms` on every keystone; no sorry; `#guard` non-vacuity witnesses (the negative well,
the genesis-order fail-close, the legacy break).
-/
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Exec.IssuerMove

open Dregg2.Exec
open Dregg2.Authority
open Dregg2.Exec.TurnExecutorFull (recKMintAsset recKBurnAsset recBalCredit
  recKMintAsset_delta recKBurnAsset_delta)

/-! ## §1 — the mechanism: mint = the issuer moving from its own (negative-capable) well. -/

section Mechanism

variable (issuerOf : AssetId → CellId)

/-- **`issuerMoveK` — THE mint mechanism (W1).** An ordinary per-asset transfer
`issuerOf a → dst` of `amt ≥ 0`, gated on mint authority over the **ISSUER** cell (E2) + issuer and
destination liveness + `issuerOf a ≠ dst` — and deliberately **NO availability gate** at the
issuer's well (E1: the well is negative-capable; its balance is −supply by construction; issuance
policy lives in the issuer cell's program, the kernel keeps conservation only). -/
def issuerMoveK (k : RecordKernelState) (actor : CellId) (a : AssetId) (dst : CellId) (amt : ℤ) :
    Option RecordKernelState :=
  if mintAuthorizedB k.caps actor (issuerOf a) = true ∧ 0 ≤ amt
      ∧ issuerOf a ∈ k.accounts ∧ dst ∈ k.accounts ∧ issuerOf a ≠ dst then
    some { k with bal := recTransferBal k.bal (issuerOf a) dst a amt }
  else none

/-- **`issuerBurnK` — THE burn mechanism (W1).** The issuer-move with the direction swapped:
`src → issuerOf a` of `amt ≥ 0`, gated on mint authority over the **ISSUER** + availability at the
HOLDER (`amt ≤ bal src a` — `src` is an ordinary cell: you can only burn what you hold) + liveness +
distinctness. Burning RETURNS value to the well (the well's balance rises toward zero — supply
shrinks). -/
def issuerBurnK (k : RecordKernelState) (actor : CellId) (a : AssetId) (src : CellId) (amt : ℤ) :
    Option RecordKernelState :=
  if mintAuthorizedB k.caps actor (issuerOf a) = true ∧ 0 ≤ amt ∧ amt ≤ k.bal src a
      ∧ src ∈ k.accounts ∧ issuerOf a ∈ k.accounts ∧ src ≠ issuerOf a then
    some { k with bal := recTransferBal k.bal src (issuerOf a) a amt }
  else none

/-- The shared conservation core: a committed `recTransferBal` write between two live, distinct
cells preserves `ExactConservation` — the moved column's debit/credit cancel
(`recTransferBal_sum_conserve_moved`), every other column is untouched (`recTransferBal_untouched`),
and the escrow store never moves on a `bal` write. NO availability premise. -/
private theorem transferBal_write_preserves_exact (k : RecordKernelState) {src dst : CellId}
    {a : AssetId} (amt : ℤ) (hsrc : src ∈ k.accounts) (hdst : dst ∈ k.accounts) (hne : src ≠ dst)
    (hex : ExactConservation k) :
    ExactConservation { k with bal := recTransferBal k.bal src dst a amt } := by
  intro b
  unfold recTotalAssetWithEscrow
  have hesc : escrowHeldAsset { k with bal := recTransferBal k.bal src dst a amt } b
      = escrowHeldAsset k b := rfl
  have hbal : recTotalAsset { k with bal := recTransferBal k.bal src dst a amt } b
      = recTotalAsset k b := by
    rcases eq_or_ne b a with rfl | hb
    · show (∑ c ∈ k.accounts, recTransferBal k.bal src dst b amt c b)
          = ∑ c ∈ k.accounts, k.bal c b
      exact recTransferBal_sum_conserve_moved k.accounts k.bal src dst b amt hsrc hdst hne
    · show (∑ c ∈ k.accounts, recTransferBal k.bal src dst a amt c b)
          = ∑ c ∈ k.accounts, k.bal c b
      exact Finset.sum_congr rfl
        (fun c _ => recTransferBal_untouched k.bal src dst a b amt hb c)
  rw [hbal, hesc]
  exact hex b

/-- **MINT-AS-ISSUER-MOVE preserves the value law (PROVED).** The reformed mint is a transfer, so
the debit/credit cancel. Note the proof needs NO availability gate: conservation never depended on
it — the negative well is sound for the value law. -/
theorem issuerMoveK_preserves_exact {k k' : RecordKernelState} {actor : CellId} {a : AssetId}
    {dst : CellId} {amt : ℤ} (h : issuerMoveK issuerOf k actor a dst amt = some k')
    (hex : ExactConservation k) : ExactConservation k' := by
  unfold issuerMoveK at h
  by_cases hg : mintAuthorizedB k.caps actor (issuerOf a) = true ∧ 0 ≤ amt
      ∧ issuerOf a ∈ k.accounts ∧ dst ∈ k.accounts ∧ issuerOf a ≠ dst
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨-, -, hiss, hdst, hne⟩ := hg
    exact transferBal_write_preserves_exact k amt hiss hdst hne hex
  · rw [if_neg hg] at h
    exact absurd h (by simp)

/-- **BURN-AS-ISSUER-MOVE preserves the value law (PROVED).** Symmetric: the burn is the same
transfer with direction swapped. -/
theorem issuerBurnK_preserves_exact {k k' : RecordKernelState} {actor : CellId} {a : AssetId}
    {src : CellId} {amt : ℤ} (h : issuerBurnK issuerOf k actor a src amt = some k')
    (hex : ExactConservation k) : ExactConservation k' := by
  unfold issuerBurnK at h
  by_cases hg : mintAuthorizedB k.caps actor (issuerOf a) = true ∧ 0 ≤ amt ∧ amt ≤ k.bal src a
      ∧ src ∈ k.accounts ∧ issuerOf a ∈ k.accounts ∧ src ≠ issuerOf a
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨-, -, -, hsrc, hiss, hne⟩ := hg
    exact transferBal_write_preserves_exact k amt hsrc hiss hne hex
  · rw [if_neg hg] at h
    exact absurd h (by simp)

/-- **The authority gate is over the ISSUER (E2), PROVED.** A committed issuer-mint proves the
actor held mint authority over the **issuer** cell — NOT the recipient (the legacy gate's target).
The cutover migrates mint capabilities recipient-shaped → issuer-shaped; this is the theorem the
migrated capability table must satisfy. -/
theorem issuerMoveK_authorized {k k' : RecordKernelState} {actor : CellId} {a : AssetId}
    {dst : CellId} {amt : ℤ} (h : issuerMoveK issuerOf k actor a dst amt = some k') :
    mintAuthorizedB k.caps actor (issuerOf a) = true := by
  unfold issuerMoveK at h
  by_cases hg : mintAuthorizedB k.caps actor (issuerOf a) = true ∧ 0 ≤ amt
      ∧ issuerOf a ∈ k.accounts ∧ dst ∈ k.accounts ∧ issuerOf a ≠ dst
  · exact hg.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- Burn's authority gate is over the ISSUER too. -/
theorem issuerBurnK_authorized {k k' : RecordKernelState} {actor : CellId} {a : AssetId}
    {src : CellId} {amt : ℤ} (h : issuerBurnK issuerOf k actor a src amt = some k') :
    mintAuthorizedB k.caps actor (issuerOf a) = true := by
  unfold issuerBurnK at h
  by_cases hg : mintAuthorizedB k.caps actor (issuerOf a) = true ∧ 0 ≤ amt ∧ amt ≤ k.bal src a
      ∧ src ∈ k.accounts ∧ issuerOf a ∈ k.accounts ∧ src ≠ issuerOf a
  · exact hg.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **GENESIS ORDER, fail-closed (the tooth).** A mint of an asset whose issuer is NOT a live
account REFUSES — the bootstrap order (create the issuer cell, then mint) is ENFORCED by the verb,
not assumed (the probe's `genesis_requires_issuer` made the order a theorem-level necessity; this
makes it a gate). -/
theorem issuerMoveK_requires_live_issuer (k : RecordKernelState) (actor : CellId) (a : AssetId)
    (dst : CellId) (amt : ℤ) (hno : issuerOf a ∉ k.accounts) :
    issuerMoveK issuerOf k actor a dst amt = none := by
  unfold issuerMoveK
  rw [if_neg (by rintro ⟨-, -, hiss, -, -⟩; exact hno hiss)]

/-- **Burn availability, fail-closed.** You cannot burn more than the holder has — the holder leg
keeps the ordinary availability gate (only the issuer WELL waives it). -/
theorem issuerBurnK_requires_availability (k : RecordKernelState) (actor : CellId) (a : AssetId)
    (src : CellId) (amt : ℤ) (hover : k.bal src a < amt) :
    issuerBurnK issuerOf k actor a src amt = none := by
  unfold issuerBurnK
  rw [if_neg (by rintro ⟨-, -, hav, -, -, -⟩; omega)]

end Mechanism

/-! ## §2 — the executor-shaped transitional wrappers (the rotation's dispatch targets). -/

/-- **The DREGG3 §2.2 identity registry: `AssetId := issuer CellId`.** An asset IS its issuer
cell's id. The mechanism above is parametric in the registry (`issuerOf`), so the identity is a
choice, not load-bearing; the executor wrappers instantiate it because it is the dregg3 design. -/
def issuerSelf : AssetId → CellId := fun a => a

/-- **`recKMintAssetIssuer` — the W1 mint, executor-shaped.** The SAME `(k, actor, cell, a, amt)`
signature as the legacy `recKMintAsset` (so the `execFullA` `.mintA`/`.bridgeMintA` arms swap onto
it 1:1 at the rotation), defined as a THIN WRAPPER over the issuer-move at the identity registry. -/
def recKMintAssetIssuer (k : RecordKernelState) (actor cell : CellId) (a : AssetId) (amt : ℤ) :
    Option RecordKernelState :=
  issuerMoveK issuerSelf k actor a cell amt

/-- **`recKBurnAssetIssuer` — the W1 burn, executor-shaped.** Thin wrapper over `issuerBurnK` at
the identity registry; same signature as the legacy `recKBurnAsset`. -/
def recKBurnAssetIssuer (k : RecordKernelState) (actor cell : CellId) (a : AssetId) (amt : ℤ) :
    Option RecordKernelState :=
  issuerBurnK issuerSelf k actor a cell amt

/-- **THE EQUIVALENCE, REAL (the actual step functions, by definition).** The executor-shaped W1
mint IS the issuer-move — not a view-level square: the two step functions are definitionally one. -/
theorem recKMintAssetIssuer_eq_issuerMove (k : RecordKernelState) (actor cell : CellId)
    (a : AssetId) (amt : ℤ) :
    recKMintAssetIssuer k actor cell a amt = issuerMoveK issuerSelf k actor a cell amt := rfl

/-- Burn's equivalence, real. -/
theorem recKBurnAssetIssuer_eq_issuerBurn (k : RecordKernelState) (actor cell : CellId)
    (a : AssetId) (amt : ℤ) :
    recKBurnAssetIssuer k actor cell a amt = issuerBurnK issuerSelf k actor a cell amt := rfl

/-- The W1 mint preserves the value law (the wrapper inherits the mechanism's preservation). -/
theorem recKMintAssetIssuer_preserves_exact {k k' : RecordKernelState} {actor cell : CellId}
    {a : AssetId} {amt : ℤ} (h : recKMintAssetIssuer k actor cell a amt = some k')
    (hex : ExactConservation k) : ExactConservation k' :=
  issuerMoveK_preserves_exact issuerSelf h hex

/-- The W1 burn preserves the value law. -/
theorem recKBurnAssetIssuer_preserves_exact {k k' : RecordKernelState} {actor cell : CellId}
    {a : AssetId} {amt : ℤ} (h : recKBurnAssetIssuer k actor cell a amt = some k')
    (hex : ExactConservation k) : ExactConservation k' :=
  issuerBurnK_preserves_exact issuerSelf h hex

/-! ## §3 — the non-vacuity teeth: the LEGACY laws provably BREAK the value law.

What makes the issuer-move a REPAIR: the deployed `recKMintAsset` (supply-increment credit) and
`recKBurnAsset` (supply-decrement debit) each take a conserved state to a NON-conserved one. A
supply-inflating step is provably rejected by `ExactConservation`. -/

/-- Shape of a committed legacy mint (gate-peeled): the post-state is the `recBalCredit` write. -/
private theorem recKMintAsset_shape {k k' : RecordKernelState} {actor cell : CellId} {a : AssetId}
    {amt : ℤ} (h : recKMintAsset k actor cell a amt = some k') :
    k' = { k with bal := recBalCredit k.bal cell a amt } := by
  unfold recKMintAsset at h
  by_cases hg : mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ cell ∈ k.accounts
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    exact h.symm
  · rw [if_neg hg] at h
    exact absurd h (by simp)

/-- Shape of a committed legacy burn. -/
private theorem recKBurnAsset_shape {k k' : RecordKernelState} {actor cell : CellId} {a : AssetId}
    {amt : ℤ} (h : recKBurnAsset k actor cell a amt = some k') :
    k' = { k with bal := recBalCredit k.bal cell a (-amt) } := by
  unfold recKBurnAsset at h
  by_cases hg : mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ amt ≤ k.bal cell a
      ∧ cell ∈ k.accounts
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    exact h.symm
  · rw [if_neg hg] at h
    exact absurd h (by simp)

/-- **NON-VACUITY TOOTH: the LEGACY mint provably BREAKS the value law.** A committed
`recKMintAsset` of a positive amount on a conserved state yields a NON-conserved state — supply
inflation is provably not conservation-preserving (instantiates `recKMintAsset_delta`). -/
theorem recKMintAsset_breaks_exact {k k' : RecordKernelState} {actor cell : CellId} {a : AssetId}
    {amt : ℤ} (h : recKMintAsset k actor cell a amt = some k') (hpos : 0 < amt)
    (hex : ExactConservation k) : ¬ ExactConservation k' := by
  intro hex'
  have hd := recKMintAsset_delta k k' actor cell a amt h a
  rw [if_pos rfl] at hd
  have hesc : escrowHeldAsset k' a = escrowHeldAsset k a := by
    rw [recKMintAsset_shape h]; rfl
  have h0 := hex a
  have h1 := hex' a
  unfold recTotalAssetWithEscrow at h0 h1
  omega

/-- **NON-VACUITY TOOTH: the LEGACY burn provably BREAKS the value law** (the dual: bare supply
destruction is just as non-conserving as bare creation). -/
theorem recKBurnAsset_breaks_exact {k k' : RecordKernelState} {actor cell : CellId} {a : AssetId}
    {amt : ℤ} (h : recKBurnAsset k actor cell a amt = some k') (hpos : 0 < amt)
    (hex : ExactConservation k) : ¬ ExactConservation k' := by
  intro hex'
  have hd := recKBurnAsset_delta k k' actor cell a amt h a
  rw [if_pos rfl] at hd
  have hesc : escrowHeldAsset k' a = escrowHeldAsset k a := by
    rw [recKBurnAsset_shape h]; rfl
  have h0 := hex a
  have h1 := hex' a
  unfold recTotalAssetWithEscrow at h0 h1
  omega

/-! ## §4 — the REAL-step commuting relation (legacy ⟷ issuer-move, both actual step functions). -/

/-- **`issuerMint_pointwise_vs_credit` (PROVED).** Run the LEGACY mint and the W1 issuer-mint from
the SAME state with the SAME arguments (recipient `cell`, asset `a`, amount `amt`); if both commit,
the W1 post-ledger IS the legacy post-ledger with the issuer's well debited by exactly `amt` at `a`
— pointwise, at every `(cell, asset)`. The probe proved this through the issuer-supply VIEW
(`mint_is_issuer_move`); this is the two ACTUAL step functions side by side: the reform changes
NOTHING about the recipient's credit, it only makes the supply increment land ON the ledger (in the
well) instead of off it. -/
theorem issuerMint_pointwise_vs_credit {k kL kI : RecordKernelState} {actor cell : CellId}
    {a : AssetId} {amt : ℤ}
    (hL : recKMintAsset k actor cell a amt = some kL)
    (hI : recKMintAssetIssuer k actor cell a amt = some kI) :
    ∀ c b, kI.bal c b
      = kL.bal c b - (if c = issuerSelf a ∧ b = a then amt else 0) := by
  -- peel both committed writes.
  have hLs := recKMintAsset_shape hL
  have hIs : kI = { k with bal := recTransferBal k.bal (issuerSelf a) cell a amt } := by
    unfold recKMintAssetIssuer issuerMoveK at hI
    by_cases hg : mintAuthorizedB k.caps actor (issuerSelf a) = true ∧ 0 ≤ amt
        ∧ issuerSelf a ∈ k.accounts ∧ cell ∈ k.accounts ∧ issuerSelf a ≠ cell
    · rw [if_pos hg] at hI
      simp only [Option.some.injEq] at hI
      exact hI.symm
    · rw [if_neg hg] at hI
      exact absurd hI (by simp)
  -- the issuer ≠ recipient gate (from the committed issuer-move).
  have hne : issuerSelf a ≠ cell := by
    unfold recKMintAssetIssuer issuerMoveK at hI
    by_cases hg : mintAuthorizedB k.caps actor (issuerSelf a) = true ∧ 0 ≤ amt
        ∧ issuerSelf a ∈ k.accounts ∧ cell ∈ k.accounts ∧ issuerSelf a ≠ cell
    · exact hg.2.2.2.2
    · rw [if_neg hg] at hI
      exact absurd hI (by simp)
  intro c b
  rw [hLs, hIs]
  show recTransferBal k.bal (issuerSelf a) cell a amt c b
      = recBalCredit k.bal cell a amt c b - (if c = issuerSelf a ∧ b = a then amt else 0)
  unfold recTransferBal recBalCredit
  rcases eq_or_ne b a with hba | hba
  · -- the minted asset's column: rewrite `b := a`, then decide the cell.
    rw [hba]
    by_cases hci : c = issuerSelf a
    · -- c is the issuer (hence not the recipient): the well-debit lands here.
      have hcc : ¬ (c = cell ∧ a = a) := fun hp => hne (hci.symm.trans hp.1)
      rw [if_pos (show a = a from rfl), if_pos hci, if_neg hcc,
          if_pos (show c = issuerSelf a ∧ a = a from ⟨hci, rfl⟩)]
    · by_cases hcc : c = cell
      · -- c is the recipient: the credit is IDENTICAL on both sides.
        rw [if_pos (show a = a from rfl), if_neg hci, if_pos hcc,
            if_pos (show c = cell ∧ a = a from ⟨hcc, rfl⟩),
            if_neg (show ¬ (c = issuerSelf a ∧ a = a) from fun hp => hci hp.1)]
        ring
      · -- bystander cell: untouched on both sides.
        rw [if_pos (show a = a from rfl), if_neg hci, if_neg hcc,
            if_neg (show ¬ (c = cell ∧ a = a) from fun hp => hcc hp.1),
            if_neg (show ¬ (c = issuerSelf a ∧ a = a) from fun hp => hci hp.1)]
        ring
  · -- every other asset's column is literally untouched on both sides.
    rw [if_neg hba, if_neg (show ¬ (c = cell ∧ b = a) from fun hp => hba hp.2),
        if_neg (show ¬ (c = issuerSelf a ∧ b = a) from fun hp => hba hp.2)]
    ring

/-! ## §5 — axiom hygiene. -/

#assert_axioms issuerMoveK_preserves_exact
#assert_axioms issuerBurnK_preserves_exact
#assert_axioms issuerMoveK_authorized
#assert_axioms issuerBurnK_authorized
#assert_axioms issuerMoveK_requires_live_issuer
#assert_axioms issuerBurnK_requires_availability
#assert_axioms recKMintAssetIssuer_eq_issuerMove
#assert_axioms recKBurnAssetIssuer_eq_issuerBurn
#assert_axioms recKMintAssetIssuer_preserves_exact
#assert_axioms recKBurnAssetIssuer_preserves_exact
#assert_axioms recKMintAsset_breaks_exact
#assert_axioms recKBurnAsset_breaks_exact
#assert_axioms issuerMint_pointwise_vs_credit

/-! ## §6 — non-vacuity (`#guard`): the negative well, the genesis order, the legacy break.

Identity registry: asset `0`'s issuer IS cell `0`. Live cells {0 (the issuer), 2}; actor 9 holds
the `node 0` mint cap — authority over the ISSUER (E2), not the recipient. -/

/-- Genesis-shaped state: live cells {0 (issuer of asset 0), 2}, zero ledger, no escrows; actor 9
holds mint authority over the issuer cell 0. -/
def kGen : RecordKernelState :=
  { accounts := {0, 2}
    cell := fun _ => Value.record [("balance", Value.int 0)]
    caps := fun c => if c = 9 then [Cap.node 0] else [] }

-- BOOTSTRAP: genesis is exact, the W1 mint commits, and the post-state shows the NEGATIVE-CAPABLE
-- WELL: issuer 0 at −5, recipient 2 at +5, sum EXACTLY 0 — with NO availability gate consulted
-- (the issuer's well went below zero from a zero start).
#guard (recTotalAssetWithEscrow kGen 0 == 0)
#guard ((recKMintAssetIssuer kGen 9 2 0 5).isSome)
#guard ((recKMintAssetIssuer kGen 9 2 0 5).map (fun k' => (k'.bal 0 0, k'.bal 2 0)))
        == some (-5, 5)
#guard ((recKMintAssetIssuer kGen 9 2 0 5).map (fun k' => recTotalAssetWithEscrow k' 0)) == some 0
-- other assets untouched:
#guard ((recKMintAssetIssuer kGen 9 2 0 5).map (fun k' => recTotalAssetWithEscrow k' 1)) == some 0
-- GENESIS-ORDER TOOTH (fail-closed): with the issuer NOT a live account, the mint REFUSES.
#guard ((recKMintAssetIssuer { kGen with accounts := {2} } 9 2 0 5).isNone)
-- AUTHORITY IS OVER THE ISSUER: an actor holding `node 2` (the RECIPIENT — the legacy gate's
-- target) but not `node 0` (the issuer) is REFUSED.
#guard ((recKMintAssetIssuer { kGen with caps := fun c => if c = 9 then [Cap.node 2] else [] }
          9 2 0 5).isNone)

-- BURN: after minting 5 to cell 2, burning 3 from holder 2 returns value to the well
-- (issuer −5 → −2, holder 5 → 2, sum stays 0); over-burning 6 > 2 is REFUSED (holder availability).
#guard (((recKMintAssetIssuer kGen 9 2 0 5).bind
          (fun k' => recKBurnAssetIssuer k' 9 2 0 3)).map
            (fun k'' => (k''.bal 0 0, k''.bal 2 0, recTotalAssetWithEscrow k'' 0)))
        == some (-2, 2, 0)
#guard (((recKMintAssetIssuer kGen 9 2 0 5).bind
          (fun k' => recKBurnAssetIssuer k' 9 2 0 6)).isNone)

/-- A legacy-mint fixture: actor 9 holds `node 2` — the RECIPIENT-shaped cap the legacy gate
checks. -/
def kGenLegacy : RecordKernelState :=
  { kGen with caps := fun c => if c = 9 then [Cap.node 2] else [] }

-- THE LEGACY BREAK, witnessed: the deployed credit-mint commits and the supply at asset 0 INFLATES
-- to 5 ≠ 0 — the conserved state is taken OUT of the law (the executable face of
-- `recKMintAsset_breaks_exact`).
#guard ((recKMintAsset kGenLegacy 9 2 0 5).isSome)
#guard ((recKMintAsset kGenLegacy 9 2 0 5).map (fun k' => recTotalAssetWithEscrow k' 0)) == some 5
#guard (((recKMintAsset kGenLegacy 9 2 0 5).map
          (fun k' => recTotalAssetWithEscrow k' 0 == 0)) == some false)

end Dregg2.Exec.IssuerMove
