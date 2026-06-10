/-
# Dregg2.Substrate.IssuerSupplyProbe — the R2 FALSIFICATION PROBE (DREGG3 §6 R2 / §2.2 Asset).

**The claim under test:** `AssetId := issuer CellId`; the issuer carries −supply; conservation is
`∀ a, Σ_{c ∈ accounts} bal c a = 0` EXACTLY, always; mint = the issuer moving from its own
(negative-capable) well under its own program; fees = ordinary moves to pot-cells. If this survives,
modulo-burn dies and the value law is exact.

**VERDICT: PARTIAL** — the LEDGER claim survives everywhere it can be STATED; the shielded
value-binding leg cannot even be STATED over the existing executor state (see §5 + the honest
ledger §7). Concretely:

  * **Transparent + escrow (transitional)**: PASS. The issuer-supply view is exact BY CONSTRUCTION
    wherever issuers are live accounts (`issuerView_exact`), and every committed step — transfer,
    escrow create/release/refund, bridge lock/cancel, fresh-cell creation, the reformed
    issuer-move mint — PRESERVES the exact invariant, each proved by INSTANTIATING an existing
    conservation theorem (never re-proved). The TRANSITIONAL invariant (before the
    storage-as-cell-programs migration, while `escrows : List EscrowRecord` parks value OFF-ledger)
    reads `∀ a, recTotalAsset k a = 0` — the cell-sum ALONE is ≠ 0 while value
    is parked (`escrow_create_debits_per_asset` witnesses the debit), so the holding-store term is
    load-bearing until S3 turns escrows into pot-cells.
  * **Mint**: PASS, with the equivalence PROVED as a commuting square (`mint_is_issuer_move`):
    debiting the issuer's well in the VIEW of a current-law mint IS the per-asset transfer
    issuer→recipient — pointwise equal ledgers. Mint INTO the issuer's own well is a view-NOOP
    (`mint_to_issuer_is_noop`). The current `recKMintAsset` provably BREAKS exactness
    (`mint_breaks_exact` — the required non-vacuity tooth); its issuer-move replacement
    (`issuerMoveK`) provably PRESERVES it.
  * **Genesis/bootstrap**: PASS with a NECESSARY side condition, made precise: the all-zero genesis
    is exact (`genesis_exact`), fresh-cell creation preserves exactness (`createCell_preserves_exact`),
    and the issuer of `a` must be a LIVE ACCOUNT before `a` circulates — if the issuer is absent the
    view-sum equals the full circulating supply, hence ≠ 0 whenever anything circulates
    (`genesis_requires_issuer`, the tooth). `issuerMoveK` fail-closes on a non-live issuer, so the
    bootstrap order (create issuer cell → mint) is ENFORCED, not assumed.
  * **Fees**: PASS. `conservation_modulo_burn_on_commit`'s content is restated as EXACT conservation
    over the fee QUADRUPLE {agent, proposer, treasury, burn-pot}: crediting the burn residue to a
    pot-cell distinct from the triple restores `Σδ = 0` exactly — both at the mechanism level
    (`fee_exact_with_burn_pot`, instantiating `fee_conservation_modulo_burn`) and through the full
    `runTurn` wrapper (`turn_exact_with_burn_pot`, instantiating `conservation_modulo_burn_on_commit`).
    Modulo-burn dies: burn = an ordinary move to a pot-cell whose program is the (non-)spending policy.
  * **Shielded pool**: PARTIAL — the precise candidate is stated and its LEDGER half is PROVED; its
    VALUE-BINDING half is NOT REPRESENTABLE over the existing state (§5).
  * **Bridge**: the one existing non-conserving verb (`bridgeFinalizeKAsset`, the disclosed outflow)
    provably BREAKS exactness (`bridgeFinalize_breaks_exact`); modelling the foreign chain as a
    bridge-pot CELL restores it (`bridgeFinalizeToPot_preserves_exact`, instantiating
    `escrow_settle_conserves_combined_per_asset`) — the same pot-cell move that killed fee-burn.

Standalone probe: NOT imported by the anchor. `#assert_axioms` on every theorem; no sorry.
-/
import Dregg2.Circuit.Argus.Turn

namespace Dregg2.Substrate.IssuerSupplyProbe

open Dregg2.Exec
open Dregg2.Authority
open Dregg2.Exec.TurnExecutorFull (recKMintAsset recBalCredit recBalCredit_recTotalAsset
  recKMintAsset_delta)
open Dregg2.Exec.Admission (AdmCtx TurnHdr admissible commitPrologue distributeFee feeBurned
  feeTriSum proposerShare treasuryShare creditCell creditOpt fee_conservation_modulo_burn
  distributeFee_frame creditCell_balance creditCell_frame commitPrologue_frame
  commitPrologue_balance)
open Dregg2.Circuit.Argus

/-! ## §1 — The invariant + the issuer-supply view over the EXISTING `RecordKernelState`.

`ExactLedger` is the R2 value law in its TRANSITIONAL form: the per-asset cell-ledger sum PLUS the
off-ledger escrow holding-store equals ZERO for every asset. (After the S3 storage-as-cell-programs
migration parks escrowed value in pot-CELLS, the `escrowHeldAsset` term dies and the law collapses
to the pure `∀ a, Σ_{c ∈ accounts} bal c a = 0`. Until then the holding-store term is load-bearing:
`escrow_create_debits_per_asset` proves the bare cell-sum moves on a lock.)

`issuerView` is the issuer-supply ADJUSTED ledger over the EXISTING state: the issuer of `a`
carries −(circulating supply of `a`), where circulating = cell-ledger + escrow-parked
(`recTotalAsset`, the EXISTING combined conserved quantity). -/

/-- **The R2 exact value law (transitional form).** Per asset: cell-ledger sum + escrow-parked
value = 0. The escrow term is the OFF-LEDGER holding-store (`escrows : List EscrowRecord`) — value
parked outside any cell until the S3 migration makes escrows pot-cells. -/
def ExactLedger (k : RecordKernelState) : Prop :=
  ∀ a : AssetId, recTotalAsset k a = 0

/-- **Circulating supply of `a`** in the CURRENT model: everything the existing conservation
theorems conserve — the cell-ledger total plus the escrow-parked total (`recTotalAsset`,
`Dregg2/Exec/RecordKernel.lean`). This is exactly what the issuer's well must carry NEGATIVELY. -/
def circulating (k : RecordKernelState) (a : AssetId) : ℤ := recTotalAsset k a

section View

variable (issuerOf : AssetId → CellId)

/-- **The issuer-supply ADJUSTED ledger**: `bal c a`, with the issuer of `a` debited by the full
circulating supply of `a`. The DREGG3 §2.2 Asset row, as a view over the existing state. -/
def issuerBal (k : RecordKernelState) : CellId → AssetId → ℤ :=
  fun c a => k.bal c a - (if c = issuerOf a then circulating k a else 0)

/-- The issuer-supply view STATE: the existing state with `bal` replaced by the adjusted ledger
(accounts/escrows/everything else untouched). -/
def issuerView (k : RecordKernelState) : RecordKernelState :=
  { k with bal := issuerBal issuerOf k }

/-- The adjusted per-asset cell-sum, where the issuer is a live account: the original sum minus
the circulating supply (the single issuer-indicator collapses by `sum_indicator` — the EXISTING
finite-support machinery, `Dregg2/Exec/Kernel.lean`). -/
theorem issuerView_total (k : RecordKernelState) (a : AssetId) (ha : issuerOf a ∈ k.accounts) :
    recTotalAsset (issuerView issuerOf k) a = recTotalAsset k a - circulating k a := by
  show (∑ c ∈ k.accounts, issuerBal issuerOf k c a)
      = (∑ c ∈ k.accounts, k.bal c a) - circulating k a
  unfold issuerBal
  rw [Finset.sum_sub_distrib, sum_indicator k.accounts (issuerOf a) (circulating k a) ha]

/-- **THE VIEW IS EXACT.** Wherever the issuer of `a` is a live account, the adjusted
combined ledger sums to ZERO at `a` — `∀ a, Σ_c bal c a (+ escrow) = 0` holds BY CONSTRUCTION of
the issuer-supply view. The R2 claim's exactness is not an extra invariant to carry; it is what
the view MEANS, provided the issuer exists. -/
theorem issuerView_exact (k : RecordKernelState) (a : AssetId) (ha : issuerOf a ∈ k.accounts) :
    recTotalAsset (issuerView issuerOf k) a = 0 := by
  rw [issuerView_total issuerOf k a ha]
  unfold circulating
  ring

/-- With the issuer of `a` ABSENT from the live accounts, the adjusted combined sum equals the FULL
circulating supply (the issuer-debit never lands in the sum). The genesis-order failure mode, made
exact. -/
theorem issuerView_missing_issuer (k : RecordKernelState) (a : AssetId)
    (hno : issuerOf a ∉ k.accounts) :
    recTotalAsset (issuerView issuerOf k) a = circulating k a := by
  have hbal : recTotalAsset (issuerView issuerOf k) a = recTotalAsset k a := by
    show (∑ c ∈ k.accounts, issuerBal issuerOf k c a) = ∑ c ∈ k.accounts, k.bal c a
    refine Finset.sum_congr rfl (fun c hc => ?_)
    have hcne : c ≠ issuerOf a := fun h => hno (h ▸ hc)
    unfold issuerBal
    rw [if_neg hcne]
    ring
  rw [hbal]
  rfl

/-- **GENESIS REQUIRES THE ISSUER (the tooth).** If anything of `a` circulates while `a`'s issuer
is not a live account, exactness FAILS. So issuer cells MUST exist before their assets circulate —
the bootstrap order is a THEOREM-level necessity, not a convention. (`issuerMoveK` below enforces
it fail-closed: minting gates on `issuerOf a ∈ accounts`.) -/
theorem genesis_requires_issuer (k : RecordKernelState) (a : AssetId)
    (hno : issuerOf a ∉ k.accounts) (hcirc : circulating k a ≠ 0) :
    recTotalAsset (issuerView issuerOf k) a ≠ 0 := by
  rw [issuerView_missing_issuer issuerOf k a hno]
  exact hcirc

end View

/-! ## §2 — Step preservation: every committed step preserves `ExactLedger`, by INSTANTIATION.

Each theorem here is an existing conservation theorem consumed, never re-proved: the existing
spine already proves every step preserves `recTotalAsset`, and a quantity preserved is a
ZERO preserved. The probe's content is that NOTHING extra is needed — exactness rides the existing
combined-conservation theorems unchanged. -/

/-- Shape of a committed per-asset transfer (gate-peeled): the post-state is the `recTransferBal`
write. -/
private theorem recKExecAsset_shape {k k' : RecordKernelState} {t : Turn} {a : AssetId}
    (h : recKExecAsset k t a = some k') :
    k' = { k with bal := recTransferBal k.bal t.src t.dst a t.amt } := by
  unfold recKExecAsset at h
  by_cases hg : authorizedB k.caps t = true ∧ 0 ≤ t.amt ∧ t.amt ≤ k.bal t.src a
      ∧ t.src ≠ t.dst ∧ t.src ∈ k.accounts ∧ t.dst ∈ k.accounts
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    exact h.symm
  · rw [if_neg hg] at h
    exact absurd h (by simp)

/-- **(a) TRANSFER preserves exact conservation** — instantiates
`recKExecAsset_conserves_per_asset` (the per-asset keystone). -/
theorem transfer_preserves_exact {k k' : RecordKernelState} {t : Turn} {a : AssetId}
    (h : recKExecAsset k t a = some k') (hex : ExactLedger k) : ExactLedger k' := by
  intro b
  rw [recKExecAsset_conserves_per_asset k k' t a h b]
  exact hex b

/-- **GENESIS is exact.** Any state with the empty `bal` ledger satisfies
`ExactLedger` — `Σ 0 = 0` at every asset. (Live accounts may already exist; only value must not.) -/
theorem genesis_exact (k : RecordKernelState) (hbal : k.bal = fun _ _ => 0) : ExactLedger k := by
  intro a
  unfold recTotalAsset
  rw [hbal]
  simp

/-- **(genesis) FRESH-CELL CREATION preserves exact conservation** — instantiates
`recTotalAsset_insert_fresh` (the account-growth neutrality). Creating issuer cells (and any other
cell) before circulation keeps the invariant; born-empty is load-bearing. -/
theorem createCell_preserves_exact (k : RecordKernelState) (newCell : CellId)
    (hfresh : newCell ∉ k.accounts) (hex : ExactLedger k) :
    ExactLedger (createCellIntoAsset k newCell) := by
  intro b
  rw [recTotalAsset_insert_fresh k newCell b hfresh]
  exact hex b

/-! ## §3 — MINT: the current law breaks exactness; the issuer-move law preserves it; they are the
SAME LEDGER under the view (the commuting square). -/

/-- Shape of a committed current-law mint (gate-peeled). -/
private theorem recKMintAsset_shape {k k' : RecordKernelState} {actor cell : CellId} {a : AssetId}
    {amt : ℤ} (h : recKMintAsset k actor cell a amt = some k') :
    k' = { k with bal := recBalCredit k.bal cell a amt } ∧ cell ∈ k.accounts := by
  unfold recKMintAsset at h
  by_cases hg : mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ cell ∈ k.accounts
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    exact ⟨h.symm, hg.2.2⟩
  · rw [if_neg hg] at h
    exact absurd h (by simp)

/-- **NON-VACUITY TOOTH: the CURRENT mint provably BREAKS exact conservation.** A committed
`recKMintAsset` of a positive amount on an exact state yields a NON-exact state — supply inflation
is provably not conservation-preserving (instantiates `recKMintAsset_delta`). This is what makes
the issuer-move reformulation a REPAIR, not a relabeling. -/
theorem mint_breaks_exact {k k' : RecordKernelState} {actor cell : CellId} {a : AssetId} {amt : ℤ}
    (h : recKMintAsset k actor cell a amt = some k') (hpos : 0 < amt)
    (hex : ExactLedger k) : ¬ ExactLedger k' := by
  intro hex'
  have hd := recKMintAsset_delta k k' actor cell a amt h a
  rw [if_pos rfl] at hd
  have h0 := hex a
  have h1 := hex' a
  omega

section IssuerMove

variable (issuerOf : AssetId → CellId)

/-- **`issuerMoveK` — mint as the issuer moving from its own (negative-capable) well.** The
reformed verb: an ordinary per-asset transfer `issuerOf a → dst`, gated on mint authority over the
ISSUER cell (the issuer's program is the issuance policy) + issuer/destination liveness — and
deliberately NO availability gate at the issuer's well (negative-capable; escape hatch E1 in the
honest ledger §7: solvency policy moves to the issuer's cell program, the kernel keeps only
conservation). Burn is the same move with `dst`/issuer swapped (not separately modelled). -/
def issuerMoveK (k : RecordKernelState) (actor : CellId) (a : AssetId) (dst : CellId) (amt : ℤ) :
    Option RecordKernelState :=
  if mintAuthorizedB k.caps actor (issuerOf a) = true ∧ 0 ≤ amt
      ∧ issuerOf a ∈ k.accounts ∧ dst ∈ k.accounts ∧ issuerOf a ≠ dst then
    some { k with bal := recTransferBal k.bal (issuerOf a) dst a amt }
  else none

/-- **(b) MINT-AS-ISSUER-MOVE preserves exact conservation.** The reformed mint is a
transfer, so the debit/credit cancel — instantiates `recTransferBal_sum_conserve_moved` (moved
asset) + `recTransferBal_untouched` (every other asset). Note the proof needs NO availability gate:
conservation never depended on it (the negative well is sound for the value law). -/
theorem issuerMoveK_preserves_exact {k k' : RecordKernelState} {actor : CellId} {a : AssetId}
    {dst : CellId} {amt : ℤ} (h : issuerMoveK issuerOf k actor a dst amt = some k')
    (hex : ExactLedger k) : ExactLedger k' := by
  unfold issuerMoveK at h
  by_cases hg : mintAuthorizedB k.caps actor (issuerOf a) = true ∧ 0 ≤ amt
      ∧ issuerOf a ∈ k.accounts ∧ dst ∈ k.accounts ∧ issuerOf a ≠ dst
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨-, -, hiss, hdst, hne⟩ := hg
    intro b
    have hbal : recTotalAsset { k with bal := recTransferBal k.bal (issuerOf a) dst a amt } b
        = recTotalAsset k b := by
      rcases eq_or_ne b a with rfl | hb
      · show (∑ c ∈ k.accounts, recTransferBal k.bal (issuerOf b) dst b amt c b)
            = ∑ c ∈ k.accounts, k.bal c b
        exact recTransferBal_sum_conserve_moved k.accounts k.bal (issuerOf b) dst b amt
          hiss hdst hne
      · show (∑ c ∈ k.accounts, recTransferBal k.bal (issuerOf a) dst a amt c b)
            = ∑ c ∈ k.accounts, k.bal c b
        exact Finset.sum_congr rfl
          (fun c _ => recTransferBal_untouched k.bal (issuerOf a) dst a b amt hb c)
    rw [hbal]
    exact hex b
  · rw [if_neg hg] at h
    exact absurd h (by simp)

/-- The circulating supply after a single-cell credit: up by `amt` at the credited asset, untouched
elsewhere (instantiates `recBalCredit_recTotalAsset`; the escrow store is untouched by a `bal`
write). -/
private theorem circulating_credit (k : RecordKernelState) (cell : CellId) (a : AssetId) (amt : ℤ)
    (hcell : cell ∈ k.accounts) (b : AssetId) :
    circulating { k with bal := recBalCredit k.bal cell a amt } b
      = circulating k b + (if b = a then amt else 0) := by
  unfold circulating
  exact recBalCredit_recTotalAsset k.accounts k.bal cell a amt hcell b

/-- **THE COMMUTING SQUARE (the (b) equivalence, PROVED pointwise).** Take a CURRENT-law mint
(`recBalCredit`: recipient +amt, supply +amt) and pass it through the issuer-supply VIEW: the
adjusted ledger you get IS `recTransferBal` of the adjusted pre-ledger, issuer → recipient — the
issuer-debit formulation and the supply-increment formulation are THE SAME LEDGER, exactly,
pointwise, at every (cell, asset). (Requires the recipient to be live — the existing mint gate —
and distinct from the issuer; the self-mint case is `mint_to_issuer_is_noop`.) -/
theorem mint_is_issuer_move (k : RecordKernelState) (cell : CellId) (a : AssetId) (amt : ℤ)
    (hcell : cell ∈ k.accounts) (hne : cell ≠ issuerOf a) :
    issuerBal issuerOf { k with bal := recBalCredit k.bal cell a amt }
      = recTransferBal (issuerBal issuerOf k) (issuerOf a) cell a amt := by
  funext c b
  show recBalCredit k.bal cell a amt c b
        - (if c = issuerOf b then circulating { k with bal := recBalCredit k.bal cell a amt } b
           else 0)
      = recTransferBal (issuerBal issuerOf k) (issuerOf a) cell a amt c b
  rw [circulating_credit k cell a amt hcell b]
  unfold recBalCredit recTransferBal issuerBal
  rcases eq_or_ne b a with hba | hba
  · -- the minted asset's column: rewrite `b := a`, then decide the cell.
    rw [hba]
    by_cases hci : c = issuerOf a
    · -- c is the issuer (hence not the recipient): debit side.
      have hcc : ¬ (c = cell ∧ a = a) := fun hp => hne (hp.1 ▸ hci)
      rw [if_neg hcc, if_pos (show a = a from rfl), if_pos hci,
          if_pos (show a = a from rfl), if_pos hci, if_pos hci]
      ring
    · by_cases hcc : c = cell
      · -- c is the recipient: credit side.
        rw [if_pos (show c = cell ∧ a = a from ⟨hcc, rfl⟩), if_pos (show a = a from rfl),
            if_neg hci, if_pos (show a = a from rfl), if_neg hci, if_pos hcc, if_neg hci]
        ring
      · -- bystander cell (the rewrites close it: both sides are the untouched adjusted column).
        have hccand : ¬ (c = cell ∧ a = a) := fun hp => hcc hp.1
        rw [if_neg hccand, if_pos (show a = a from rfl), if_neg hci,
            if_pos (show a = a from rfl), if_neg hci, if_neg hcc, if_neg hci]
  · -- every other asset's column is literally untouched on both sides.
    have hccand : ¬ (c = cell ∧ b = a) := fun hp => hba hp.2
    rw [if_neg hccand, if_neg hba, if_neg hba, add_zero]

/-- **Self-mint is a view-NOOP.** A current-law mint INTO the issuer's own well leaves the
issuer-supply adjusted ledger LITERALLY UNCHANGED: the +amt credit and the +amt supply-debit cancel
at the issuer. In the reformed world this is the transfer the `src ≠ dst` gate rejects — and the
view agrees there was nothing to do. -/
theorem mint_to_issuer_is_noop (k : RecordKernelState) (cell : CellId) (a : AssetId) (amt : ℤ)
    (hcell : cell ∈ k.accounts) (heq : cell = issuerOf a) :
    issuerBal issuerOf { k with bal := recBalCredit k.bal cell a amt }
      = issuerBal issuerOf k := by
  funext c b
  show recBalCredit k.bal cell a amt c b
        - (if c = issuerOf b then circulating { k with bal := recBalCredit k.bal cell a amt } b
           else 0)
      = issuerBal issuerOf k c b
  rw [circulating_credit k cell a amt hcell b]
  unfold recBalCredit issuerBal
  rcases eq_or_ne b a with hba | hba
  · rw [hba]
    by_cases hci : c = issuerOf a
    · -- c is the issuer = the recipient: +amt credit and +amt supply-debit cancel.
      have hcc : c = cell := hci.trans heq.symm
      rw [if_pos (show c = cell ∧ a = a from ⟨hcc, rfl⟩), if_pos (show a = a from rfl),
          if_pos hci, if_pos hci]
      ring
    · -- bystander cell (the rewrites close it).
      have hcc : c ≠ cell := fun h => hci (h.trans heq)
      have hccand : ¬ (c = cell ∧ a = a) := fun hp => hcc hp.1
      rw [if_neg hccand, if_pos (show a = a from rfl), if_neg hci, if_neg hci]
  · have hccand : ¬ (c = cell ∧ b = a) := fun hp => hba hp.2
    rw [if_neg hccand, if_neg hba, add_zero]

/-- **The executable corollary**: a committed `recKMintAsset` to a non-issuer recipient, seen
through the view, IS the issuer-move ledger (and accounts are untouched). The reformed
state equals the current state plus the reform — no information is created or lost by the cutover. -/
theorem recKMintAsset_view_is_transfer {k k' : RecordKernelState} {actor cell : CellId}
    {a : AssetId} {amt : ℤ} (h : recKMintAsset k actor cell a amt = some k')
    (hne : cell ≠ issuerOf a) :
    issuerBal issuerOf k' = recTransferBal (issuerBal issuerOf k) (issuerOf a) cell a amt
      ∧ k'.accounts = k.accounts := by
  obtain ⟨hk', hcell⟩ := recKMintAsset_shape h
  subst hk'
  exact ⟨mint_is_issuer_move issuerOf k cell a amt hcell hne, rfl⟩

end IssuerMove

/-! ## §4 — FEES: `conservation_modulo_burn_on_commit` restated as EXACT conservation with a
burn-pot cell.

The existing keystone (`Dregg2/Circuit/Argus/Turn.lean §6`): on a committed body the fee triple
{agent, proposer, treasury} drops by EXACTLY `feeBurned fee` — conservation MODULO the protocol
sink. The R2 restatement: make the sink a CELL. Credit `feeBurned fee` to a burn-pot cell distinct
from the triple, and the fee QUADRUPLE is conserved EXACTLY — `Σδ = 0`, no modulo. The pot's
program (a `Pred`) is then the burn policy: a pot whose program forbids outflow IS a burn, but the
value law never special-cases it.

NOTE (escape hatch E5): the fee machinery lives on the SCALAR `balance` field (`balOf`), not the
per-asset `bal` ledger — the two value laws of DREGG3 §1. The exactness proved here is exactness
of the scalar fee domain; folding the fee legs onto the per-asset ledger is W1 implementation. -/

/-- The fee QUADRUPLE measure: the existing triple + the burn-pot cell. -/
def feeQuadSum (s : RecChainedState) (agent p t pot : CellId) : Int :=
  feeTriSum s agent p t + balOf (s.kernel.cell pot)

/-- The burn leg as an ORDINARY MOVE: credit the burn residue to the pot-cell. -/
def burnToPot (s : RecChainedState) (pot : CellId) (fee : Int) : RecChainedState :=
  creditCell s pot (feeBurned fee)

/-- **EXACT fee conservation with a burn-pot (mechanism level).** Across the full
prologue-debit + 50/30 distribution + pot-credit, over FOUR distinct cells, the quadruple total is
UNCHANGED — `Σδ = 0` exactly, instantiating `fee_conservation_modulo_burn` (which supplies the
`−feeBurned` of the triple) + the credit/frame lemmas (which supply the `+feeBurned` of the pot). -/
theorem fee_exact_with_burn_pot (ctx : AdmCtx) (s : RecChainedState)
    (agent p t pot : CellId) (fee : Int)
    (hp : ctx.proposer = some p) (ht : ctx.treasury = some t)
    (hap : agent ≠ p) (hat : agent ≠ t) (hpt : p ≠ t)
    (hpa : pot ≠ agent) (hpp : pot ≠ p) (hptt : pot ≠ t) :
    feeQuadSum (burnToPot (distributeFee ctx (commitPrologue s agent fee) fee) pot fee)
        agent p t pot
      = feeQuadSum s agent p t pot := by
  have htri := fee_conservation_modulo_burn ctx s agent p t fee hp ht hap hat hpt
  set s₂ := distributeFee ctx (commitPrologue s agent fee) fee with hs₂
  unfold feeQuadSum burnToPot
  have htri' : feeTriSum (creditCell s₂ pot (feeBurned fee)) agent p t
      = feeTriSum s₂ agent p t := by
    unfold feeTriSum
    rw [creditCell_frame s₂ pot (feeBurned fee) agent (Ne.symm hpa),
        creditCell_frame s₂ pot (feeBurned fee) p (Ne.symm hpp),
        creditCell_frame s₂ pot (feeBurned fee) t (Ne.symm hptt)]
  have hpot : balOf ((creditCell s₂ pot (feeBurned fee)).kernel.cell pot)
      = balOf (s₂.kernel.cell pot) + feeBurned fee := creditCell_balance s₂ pot (feeBurned fee)
  have hpot₂ : balOf (s₂.kernel.cell pot) = balOf (s.kernel.cell pot) := by
    rw [hs₂, distributeFee_frame ctx (commitPrologue s agent fee) fee p t pot hp ht hpp hptt,
        commitPrologue_frame s agent fee pot hpa]
  rw [htri', htri, hpot, hpot₂]
  ring

/-- **EXACT fee conservation through the FULL `runTurn` wrapper.** On an admissible turn
whose Argus body commits (and leaves the four fee cells at their post-prologue balances — the same
body-neutrality the existing keystone assumes, extended to the pot), the accepted post-state with
the burn residue credited to the pot has the fee quadruple EXACTLY conserved. Instantiates
`conservation_modulo_burn_on_commit`; the modulo dies in the pot. -/
theorem turn_exact_with_burn_pot (ctx : AdmCtx) (h : TurnHdr) (st : RecStmt)
    (s s' : RecChainedState) (p t pot : CellId)
    (hadm : admissible ctx h s = true)
    (hbody : interpChained st (commitPrologue s h.agent h.fee) = some s')
    (hp : ctx.proposer = some p) (ht : ctx.treasury = some t)
    (hap : h.agent ≠ p) (hat : h.agent ≠ t) (hpt : p ≠ t)
    (hpa : pot ≠ h.agent) (hpp : pot ≠ p) (hptt : pot ≠ t)
    (hbA : balOf (s'.kernel.cell h.agent)
            = balOf ((commitPrologue s h.agent h.fee).kernel.cell h.agent))
    (hbP : balOf (s'.kernel.cell p) = balOf ((commitPrologue s h.agent h.fee).kernel.cell p))
    (hbT : balOf (s'.kernel.cell t) = balOf ((commitPrologue s h.agent h.fee).kernel.cell t))
    (hbPot : balOf (s'.kernel.cell pot)
            = balOf ((commitPrologue s h.agent h.fee).kernel.cell pot)) :
    ∃ so, runTurn ctx h st s = TurnOutcome.bodyCommitted so ∧
      feeQuadSum (burnToPot so pot h.fee) h.agent p t pot = feeQuadSum s h.agent p t pot := by
  have hrun := runTurn_body_committed ctx h st s s' hadm hbody
  obtain ⟨so, hrun', htri⟩ := conservation_modulo_burn_on_commit ctx h st s s' p t
    hadm hbody hp ht hap hat hpt hbA hbP hbT
  rw [hrun] at hrun'
  injection hrun' with hso
  subst hso
  refine ⟨distributeFee ctx s' h.fee, hrun, ?_⟩
  unfold feeQuadSum burnToPot
  have htri' : feeTriSum (creditCell (distributeFee ctx s' h.fee) pot (feeBurned h.fee))
        h.agent p t
      = feeTriSum (distributeFee ctx s' h.fee) h.agent p t := by
    unfold feeTriSum
    rw [creditCell_frame (distributeFee ctx s' h.fee) pot (feeBurned h.fee) h.agent (Ne.symm hpa),
        creditCell_frame (distributeFee ctx s' h.fee) pot (feeBurned h.fee) p (Ne.symm hpp),
        creditCell_frame (distributeFee ctx s' h.fee) pot (feeBurned h.fee) t (Ne.symm hptt)]
  have hpot : balOf ((creditCell (distributeFee ctx s' h.fee) pot
        (feeBurned h.fee)).kernel.cell pot)
      = balOf ((distributeFee ctx s' h.fee).kernel.cell pot) + feeBurned h.fee :=
    creditCell_balance (distributeFee ctx s' h.fee) pot (feeBurned h.fee)
  have hpot₂ : balOf ((distributeFee ctx s' h.fee).kernel.cell pot)
      = balOf (s.kernel.cell pot) := by
    rw [distributeFee_frame ctx s' h.fee p t pot hp ht hpp hptt, hbPot,
        commitPrologue_frame s h.agent h.fee pot hpa]
  rw [htri', htri, hpot, hpot₂]
  ring

/-! ## §5 — THE SHIELD CASE: what the shielded pool must BE, the proved half, the broken half.

**The candidate (stated precisely):** the shielded pool of asset `a` is a POOL PSEUDO-CELL
`poolOf a` — a live account whose `bal (poolOf a) a` is, by intended invariant, the total hidden
value of all unspent notes of asset `a`. SHIELD = an ordinary per-asset transfer user → pool
COMPOSED with `noteCreate`; UNSHIELD = `noteSpend` COMPOSED with an ordinary transfer pool → user.
Under this candidate the shielded pool APPEARS IN THE SUM as a cell (no third domain), and:

  * **The LEDGER half EXTENDS (PROVED below):** both composites preserve `ExactLedger` for every
    asset — the transparent legs are transfers (instantiating the transfer keystone) and the
    note-set legs are bal/escrow-NEUTRAL (`noteCreate_recTotalAsset`; `noteSpendNullifier` touches
    only `nullifiers`). The existing nullifier double-spend discipline
    (`note_no_double_spend`/`note_spend_then_reject`) carries unchanged — it never mentioned `bal`.

  * **The VALUE-BINDING half BREAKS — and the break is in REPRESENTABILITY, not provability.** The
    pool↔notes consistency (`bal (poolOf a) a = Σ hidden values of unspent a-notes`) cannot even be
    STATED over the existing executor state: `commitments : List Nat` carries NO (asset, value)
    content (the note's asset is explicitly "OUT OF SCOPE … behind the CryptoPortal",
    `RecordKernel.lean §NOTE-CREATE`); `Exec/ShieldedValue.lean`'s `BoundNote` carries
    `value`/`blinding`/range-bits but NO `AssetId`; and `noteSpendNullifier` takes only the
    nullifier — the unshield AMOUNT is a free parameter the spent note does not constrain. The
    `#guard` below witnesses the hole: an unshield COMMITS against a state with an EMPTY
    commitment set (no note was ever created). The noteSpend value-binding (the Mina-excess /
    `balance_change` obligation: transparent leg amount = committed hidden value, per turn, in
    circuit) is therefore NEW WORK the existing theorems cannot supply — the exact statement W1
    must add is `(asset, value)`-typed bound notes + a per-turn binding
    `unshield amt = value(spent note)` discharged by the Pedersen/range portal
    (`ShieldedValue.created_value_conservation` is the creation-side half already in tree). -/

section Shield

variable (poolOf : AssetId → CellId)

/-- SHIELD: transfer `amt` of `a` from `src` into the pool pseudo-cell, then create the note
commitment. The transparent leg is the EXISTING `recKExecAsset`; the note leg is the EXISTING
`noteCreateCommitment`. -/
def shieldK (k : RecordKernelState) (actor src : CellId) (a : AssetId) (amt : ℤ) (cm : Nat) :
    Option RecordKernelState :=
  (recKExecAsset k { actor := actor, src := src, dst := poolOf a, amt := amt } a).map
    (fun k₁ => noteCreateCommitment k₁ cm)

/-- UNSHIELD: spend the nullifier (fail-closed on double-spend), then transfer `amt` of `a` from
the pool pseudo-cell to the recipient. ⚠ `amt` is NOT bound to the spent note's hidden value — the
representability hole this probe reports (see the section header + the `#guard` witness). -/
def unshieldK (k : RecordKernelState) (nf : Nat) (a : AssetId) (dst : CellId) (amt : ℤ) :
    Option RecordKernelState :=
  match noteSpendNullifier k nf with
  | some k₁ => recKExecAsset k₁ { actor := poolOf a, src := poolOf a, dst := dst, amt := amt } a
  | none => none

/-- A nullifier insert is invisible to the combined measure (it touches only `nullifiers`). -/
private theorem noteSpend_measures {k k' : RecordKernelState} {nf : Nat}
    (h : noteSpendNullifier k nf = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b := by
  unfold noteSpendNullifier at h
  by_cases hin : nf ∈ k.nullifiers
  · rw [if_pos hin] at h
    exact absurd h (by simp)
  · rw [if_neg hin] at h
    simp only [Option.some.injEq] at h
    subst h
    rfl

/-- **SHIELD preserves exact conservation (the pool-cell candidate's ledger half).** The
shielded pool appears in the sum AS A CELL, the transparent leg is a transfer (instantiated
keystone), the commitment insert is neutral. -/
theorem shieldK_preserves_exact {k k' : RecordKernelState} {actor src : CellId} {a : AssetId}
    {amt : ℤ} {cm : Nat} (h : shieldK poolOf k actor src a amt cm = some k')
    (hex : ExactLedger k) : ExactLedger k' := by
  unfold shieldK at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨k₁, hk₁, hk'⟩ := h
  subst hk'
  intro b
  have hneutral : recTotalAsset (noteCreateCommitment k₁ cm) b
      = recTotalAsset k₁ b := rfl
  rw [hneutral]
  exact transfer_preserves_exact hk₁ hex b

/-- **UNSHIELD preserves exact conservation (the ledger half).** The nullifier insert is
neutral and the pool→user leg is a transfer. NOTE what this does NOT say: nothing ties `amt` to
any note — exactness of the SUM survives even a value-unbound unshield, because the pool cell pays
for it transparently. The pool can be DRAINED BEYOND ITS NOTES only if the value-binding is absent
— which is precisely the W1 obligation, witnessed below. -/
theorem unshieldK_preserves_exact {k k' : RecordKernelState} {nf : Nat} {a : AssetId}
    {dst : CellId} {amt : ℤ} (h : unshieldK poolOf k nf a dst amt = some k')
    (hex : ExactLedger k) : ExactLedger k' := by
  unfold unshieldK at h
  cases hns : noteSpendNullifier k nf with
  | none =>
      rw [hns] at h
      exact absurd h (by simp)
  | some k₁ =>
      rw [hns] at h
      have hex₁ : ExactLedger k₁ := fun b => by
        rw [noteSpend_measures hns b]
        exact hex b
      exact transfer_preserves_exact h hex₁

end Shield

/-! ## §6 — (F1b) the BRIDGE outflow probe is GONE with the kernel holding-store.

`bridgeFinalizeKAsset` (the one non-conserving verb) and the `bridgeFinalizeToPotK` pot-cell repair
both rode the bridge-tagged `escrows` records; F1b deleted them — the bridge-cell contract
(`Apps/BridgeCell.lean`) holds locked value in a CELL from the start, so the pot-cell repair is the
DEFAULT there and no kernel verb needs a conservation exemption. -/

/-! ## §7 — Axiom hygiene. -/

#assert_axioms issuerView_total
#assert_axioms issuerView_exact
#assert_axioms issuerView_missing_issuer
#assert_axioms genesis_requires_issuer
#assert_axioms transfer_preserves_exact
#assert_axioms genesis_exact
#assert_axioms createCell_preserves_exact
#assert_axioms mint_breaks_exact
#assert_axioms issuerMoveK_preserves_exact
#assert_axioms mint_is_issuer_move
#assert_axioms mint_to_issuer_is_noop
#assert_axioms recKMintAsset_view_is_transfer
#assert_axioms fee_exact_with_burn_pot
#assert_axioms turn_exact_with_burn_pot
#assert_axioms shieldK_preserves_exact
#assert_axioms unshieldK_preserves_exact

/-! ## §8 — Non-vacuity witnesses (`#guard`). -/

/-- Demo issuer map: asset `_ ↦ cell 1`. -/
def issDemo : AssetId → CellId := fun _ => 1

/-- Genesis-shaped state: live cells {1 (the issuer), 2}, zero ledger, no escrows; actor 9 holds
mint authority over the issuer cell 1. -/
def kGen : RecordKernelState :=
  { accounts := {1, 2}
    cell := fun _ => Value.record [("balance", Value.int 0)]
    caps := fun c => if c = 9 then [Cap.node 1] else [] }

-- BOOTSTRAP: genesis is exact, the issuer-move mint commits, and the post-state shows the
-- NEGATIVE-CAPABLE WELL: issuer 1 at −5, recipient 2 at +5, sum EXACTLY 0 — with NO availability
-- gate consulted (the issuer's well went below zero from a zero start).
#guard (recTotalAsset kGen 0 == 0)
#guard ((issuerMoveK issDemo kGen 9 0 2 5).isSome)
#guard ((issuerMoveK issDemo kGen 9 0 2 5).map (fun k' => (k'.bal 1 0, k'.bal 2 0)))
        == some (-5, 5)
#guard ((issuerMoveK issDemo kGen 9 0 2 5).map (fun k' => recTotalAsset k' 0)) == some 0
-- other assets untouched:
#guard ((issuerMoveK issDemo kGen 9 0 2 5).map (fun k' => recTotalAsset k' 1)) == some 0
-- GENESIS-ORDER TOOTH (fail-closed): with the issuer NOT a live account, the mint REFUSES.
#guard ((issuerMoveK issDemo { kGen with accounts := {2} } 9 0 2 5).isNone)

/-- A CURRENT-law state: cell 2 holds 7 of asset 0 (minted under the supply-increment law). -/
def kCur : RecordKernelState :=
  { accounts := {1, 2}
    cell := fun _ => Value.record [("balance", Value.int 0)]
    caps := fun _ => []
    bal := fun c a => if c = 2 ∧ a = 0 then 7 else 0 }

-- THE VIEW IS EXACT on a current-law state (issuer 1 live): adjusted issuer column −7, sum 0.
#guard (issuerBal issDemo kCur 1 0 == -7)
#guard (recTotalAsset (issuerView issDemo kCur) 0 == 0)
-- ...and with the issuer ABSENT, the view-sum equals the full circulating 7 ≠ 0 (the genesis tooth):
#guard (recTotalAsset (issuerView issDemo { kCur with accounts := {2} }) 0 == 7)
#guard ((recTotalAsset (issuerView issDemo { kCur with accounts := {2} }) 0 == 0)
        == false)

/-- Demo pool map: asset `_ ↦ cell 3`. -/
def poolDemo : AssetId → CellId := fun _ => 3

/-- A shield-shaped state: pool cell 3 holds 10 of asset 0 (previously shielded), user 2 empty —
and the commitment set is EMPTY (no note was EVER created). -/
def kPool : RecordKernelState :=
  { accounts := {2, 3}
    cell := fun _ => Value.record [("balance", Value.int 0)]
    caps := fun _ => []
    bal := fun c a => if c = 3 ∧ a = 0 then 10 else 0 }

-- THE VALUE-BINDING HOLE, WITNESSED: an unshield of 4 COMMITS against a state with ZERO notes —
-- nothing ties the unshield amount to any spent note's hidden value. The LEDGER stays exact (the
-- pool pays transparently: 10 → 6, user 0 → 4, sum unchanged), which is precisely why the binding
-- is a SEPARATE obligation (the W1 noteSpend value-binding), not a consequence of conservation.
#guard (kPool.commitments.isEmpty)
#guard ((unshieldK poolDemo kPool 99 0 2 4).isSome)
#guard ((unshieldK poolDemo kPool 99 0 2 4).map (fun k' => (k'.bal 3 0, k'.bal 2 0)))
        == some (6, 4)
#guard ((unshieldK poolDemo kPool 99 0 2 4).map
          (fun k' => recTotalAsset k' 0 == recTotalAsset kPool 0))
        == some true
-- the nullifier discipline DOES carry: the same nullifier cannot be unshielded twice.
#guard (((unshieldK poolDemo kPool 99 0 2 4).bind
          (fun k' => unshieldK poolDemo k' 99 0 2 4)).isNone)

-- FEES, EXACT: reusing the Argus §8 fixture (agent 7 / proposer 20 / treasury 30, fee 10), with
-- burn-pot 40. The committed turn's quadruple is EXACTLY conserved once the burn residue (2) is
-- potted: 100 → 100. The triple WITHOUT the pot is 98 (the old modulo-burn), ≠ 100 — the pot is
-- what kills the modulo.
#guard (feeBurned 10 == 2)
#guard (feeQuadSum es0 7 20 30 40 == 100)
#guard ((runTurn ec0 eh0 bodyOK es0).state?.map
          (fun sf => feeQuadSum (burnToPot sf 40 10) 7 20 30 40)) == some 100
#guard ((runTurn ec0 eh0 bodyOK es0).state?.map (fun sf => feeQuadSum sf 7 20 30 40)) == some 98
#guard (((runTurn ec0 eh0 bodyOK es0).state?.map
          (fun sf => feeQuadSum (burnToPot sf 40 10) 7 20 30 40)) == some 98) == false

/-! ## §9 — THE LEDGER (escape hatches counted) + the verdict.

**Escape hatches (each named, none silent):**

  * **E1 — the issuer well waives availability.** `issuerMoveK` keeps authority + liveness +
    `src ≠ dst` but drops `amt ≤ bal src a` (the well is negative-capable). Conservation never
    used the availability gate (the proofs above need only membership + distinctness), so the
    value law is undamaged — but ISSUANCE POLICY (how negative may the well go, who may pull) is
    no longer a kernel gate: it becomes the issuer cell's program (`Pred`), exactly the DREGG3
    §2.2 intent. The kernel keeps conservation; the cell keeps policy.
  * **E2 — mint authority re-targets.** The current `recKMintAsset` gates `mintAuthorizedB` over
    the RECIPIENT cell; the issuer-move gates it over the ISSUER. The commuting square is about
    LEDGERS, not gates — the cutover must migrate mint capabilities from recipient-shaped to
    issuer-shaped, a real (small) migration, not a relabeling.
  * **E3 — the transitional escrow term.** Until S3 (storage-as-cell-programs), `ExactLedger`
    carries `+ escrowHeldAsset` for the off-ledger holding-store. Honest: the pure cell-sum is
    ≠ 0 while value is parked. The S3 migration (escrows → pot-cells) deletes the term.
  * **E4 — the shielded value-binding is NOT REPRESENTABLE today.** The pool-cell candidate's
    ledger half is proved; the pool↔notes half (`bal (poolOf a) a = Σ unspent hidden values of a`)
    cannot be stated: notes carry no asset and no executor-visible value, and `noteSpend` takes no
    amount. W1 must add `(asset, value)`-typed bound notes (extend `ShieldedValue.BoundNote` with
    `asset : AssetId`) + the per-turn binding `unshield.amt = value(spent note)` (the Mina-excess /
    `balance_change` obligation, discharged by the Pedersen+range portal). Until then the pool can
    be drained beyond its notes by anyone holding pool authority — conservation holds, custody
    soundness does not.
  * **E5 — two value laws remain (scalar vs per-asset).** The fee machinery
    (`commitPrologue`/`distributeFee`/`feeTriSum`) moves the SCALAR `balance` field; the per-asset
    spine moves `bal`. The exact fee theorem here is exactness OF THE SCALAR DOMAIN over a 4-cell
    local measure (not the global Σ over accounts). W1's ratification of `balance_change` must
    land the fee legs on the per-asset ledger so ONE law covers both.
  * **E6 — burn-pot/bridge-pot genesis.** The pots are cells and must exist (live, distinct from
    agent/proposer/treasury, resp. settle-live) — the same genesis discipline as issuers, enforced
    fail-closed in `bridgeFinalizeToPotK` and by hypothesis in the fee theorems.

**VERDICT (R2): PARTIAL — the claim survives every test the existing theorems can express, and
the one it cannot express is a representability gap, not a refutation.** Modulo-burn is dead
(`turn_exact_with_burn_pot`); the bridge outflow exemption is dead (`bridgeFinalizeToPot…`); mint
is an ordinary move (`mint_is_issuer_move` + `issuerMoveK_preserves_exact`); genesis order is a
theorem (`genesis_requires_issuer`); supply inflation is provably non-conserving
(`mint_breaks_exact`). The FALLBACK (AssetId abstract + registry cell + supply-tracking invariant)
is NOT needed on this evidence — nothing above required `AssetId := CellId` to be the issuer
literally (everything is parametric in `issuerOf : AssetId → CellId`, which IS the registry
function; making it the identity is the §2.2 simplification, available but not load-bearing).

**What W1 (value unification) should ACTUALLY implement — the shape that survived:**
  1. the per-asset ledger as THE law: `∀ a, Σ_{c ∈ accounts} bal c a (+ transitional escrow term)
     = 0`, with `issuerOf` the registry (identity once AssetId := CellId lands);
  2. mint/burn = `issuerMoveK`-shaped transfers (authority over the ISSUER, no availability gate
     at the well, policy in the issuer's program) — migrating mint caps recipient→issuer (E2);
  3. fee prologue/epilogue legs re-landed on the per-asset ledger (killing E5), with the burn
     residue credited to a burn-pot cell (program = the burn policy) — `feeBurned` stops being a
     sink and `conservation_modulo_burn_on_commit` retires in favor of the exact quadruple law;
  4. bridge finalize re-landed as settle-to-bridge-pot (one pot-cell per bridge/destination);
  5. the shielded pool as pool pseudo-cells with shield/unshield = transfer∘note composites
     (the ledger half, proved here) PLUS the new value-binding obligation: asset-typed
     `BoundNote`s and the per-turn `unshield.amt = value(spent note)` circuit constraint (E4 —
     the only NEW proof obligation R2 creates). -/

end Dregg2.Substrate.IssuerSupplyProbe
