/-
# Dregg2.Circuit.Spec.supplycreation — INDEPENDENT full-state spec + executor⟺spec for the
dregg2 effect family **supply-creation** (variant: `mintA` — W1: the ISSUER-MOVE).

This is a *leaf* module in the `Transfer.lean` lineage: it builds, for the per-asset privileged
MINT effect, the SAME triangle corner the reference `TransferSpec`/`recKExec_iff_spec` establish
for `Transfer`, but written INDEPENDENTLY of the executor.

**W1 (DREGG3 §2.2 Asset)**: `AssetId := CellId` — the asset IS its issuer cell. A committed mint is
an ordinary per-asset transfer FROM the issuer's negative-capable well TO the recipient: the supply
increment lands ON the ledger (in the well), so `Σ_c bal c a` is EXACTLY unchanged. The deliverables,
mirroring the reference pattern (`Dregg2/Circuit/Transfer.lean` §6b):

  1. `MintASpec st t st'` : Prop — the FULL declarative post-state of a committed `mintA`. It is
     the conjunction of
       * the admissibility guard `mintAuthorizedB caps actor a ∧ 0 ≤ amt ∧ a ∈ accounts ∧
         cell ∈ accounts ∧ a ≠ cell` (the EXACT `recKMintAsset` `if`, read off the CODE — the gate
         target is the ISSUER `a`, the production law E2; `a ∈ accounts` is the genesis-order gate);
       * the EXACT touched components — `kernel.bal` is the `recTransferBal … a cell a amt`
         issuer-move write and the receipt `log` prepended with the truthful well→recipient turn
         `{actor, src:=a, dst:=cell, amt}`;
       * EVERY OTHER state component LITERALLY unchanged — the FRAME. No frame clause mentions any
         executor helper.
  2. `execMintA_iff_spec : execFullA st (.mintA actor cell a amt) = some st' ↔ MintASpec …` — BOTH
     directions. The `→` VALIDATES the executor against the independent spec: a silently-mutated
     field would make the frame clause unprovable.
  3. `recTransferBal_mint_correct` — the post-`bal` helper validated DECLARATIVELY (the issuer's
     well debited by `amt`, the recipient credited by `amt`, every other (cell,asset) entry
     literally preserved), so the spec's `bal = recTransferBal …` clause encodes
     debit ∧ credit ∧ ledger-frame, not blind trust.

The supply-creation family on `execFullA` is `mintA` (and its §8-portal twin `bridgeMintA`, which
dispatches to the SAME `recCMintAsset` — a corollary, `execBridgeMintA_iff_spec`, is included; W1:
the bridge cell IS the issuer of the bridged asset). The companion conservation corollary
`mintA_supply_delta` pins the W1 semantic content: a committed mint leaves EVERY asset's supply
EXACTLY unchanged — exactness, not disclosure.
-/
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Circuit.Spec.SupplyCreation

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority

/-! ## §1 — the admissibility guard, lifted from the CODE.

`recKMintAsset` commits IFF this exact conjunction holds. The gate target is the **ISSUER** cell
`a` (W1/E2: `mintAuthorizedB caps actor a` — the privileged `node`/`control` cap over the asset's
issuer; authority to mint IS the issuer capability, never a recipient-shaped grant). `a ∈ accounts`
is the genesis-order gate (the issuer well must be live before its asset circulates); `a ≠ cell`
rejects the self-mint no-move; there is deliberately NO availability gate at the well (E1 — the
well is negative-capable, its balance IS −supply). -/

/-- **`mintAdmit`** — the full admissibility guard `recKMintAsset`/`recCMintAsset` checks, as a
`Prop` (the conjunction in the executor's `if`). ISSUER authority ∧ non-negativity ∧ issuer-well
liveness ∧ recipient liveness ∧ distinctness. -/
def mintAdmit (k : RecordKernelState) (actor cell : CellId) (a : AssetId) (amt : ℤ) : Prop :=
  mintAuthorizedB k.caps actor a = true ∧ 0 ≤ amt
    ∧ a ∈ k.accounts ∧ cell ∈ k.accounts ∧ a ≠ cell

/-- The truthful receipt a committed `mintA` prepends to the log: the issuer-move row
`well a → recipient cell` of size `amt` — exactly `recCMintAsset`'s `log` head. -/
def mintReceipt (actor cell : CellId) (a : AssetId) (amt : ℤ) : Turn :=
  { actor := actor, src := a, dst := cell, amt := amt }

/-! ## §2 — the post-`bal` helper, validated DECLARATIVELY.

`recTransferBal bal a cell a amt` (the issuer-move write) is the ONLY thing a committed mint does
to the ledger. We validate it relationally (the well debited, the recipient credited, every other
entry preserved) so the spec's `bal = recTransferBal …` clause carries real meaning rather than
trusting the helper's name. -/

/-- **`recTransferBal_mint_correct`** — the issuer-move ledger write validated DECLARATIVELY (for
`a ≠ cell`, the committed case): the issuer's well `(a, a)` is debited by exactly `amt`, the
recipient `(cell, a)` is credited by exactly `amt`, and every OTHER (cell,asset) entry is literally
untouched. Debit ∧ credit ∧ ledger-frame. -/
theorem recTransferBal_mint_correct (bal : CellId → AssetId → ℤ) (cell : CellId) (a : AssetId)
    (amt : ℤ) (hne : a ≠ cell) :
    recTransferBal bal a cell a amt a a = bal a a - amt
    ∧ recTransferBal bal a cell a amt cell a = bal cell a + amt
    ∧ (∀ c b, ¬ (c = a ∧ b = a) → ¬ (c = cell ∧ b = a)
        → recTransferBal bal a cell a amt c b = bal c b) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold recTransferBal
    rw [if_pos rfl, if_pos rfl]
  · unfold recTransferBal
    rw [if_pos rfl, if_neg (Ne.symm hne), if_pos rfl]
  · intro c b hni hnc
    unfold recTransferBal
    rcases eq_or_ne b a with hb | hb
    · have hci : c ≠ a := fun h => hni ⟨h, hb⟩
      have hcc : c ≠ cell := fun h => hnc ⟨h, hb⟩
      rw [if_pos hb, if_neg hci, if_neg hcc]
    · rw [if_neg hb]

/-! ## §3 — the executor projection: `execFullA` on `mintA` IS `recCMintAsset`. -/

@[simp] theorem execFullA_mintA (st : RecChainedState) (actor cell : CellId) (a : AssetId)
    (amt : ℤ) :
    execFullA st (.mintA actor cell a amt) = recCMintAsset st actor cell a amt := rfl

/-! ## §4 — FULL-STATE SEMANTIC SPEC (the INDEPENDENT reference) + executor⟺spec.

`MintASpec` is the COMPLETE declarative post-state of a committed `mintA`, written INDEPENDENTLY of
the executor: the guard holds; the post `kernel.bal` is the issuer-move write; the post `log` is
the truthful receipt prepended; and ALL non-`bal` kernel components are LITERALLY unchanged. No
frame clause mentions `execFullA`/`recCMintAsset`/`recKMintAsset`. -/

/-- **The full-state declarative spec of a committed supply-creation (`mintA`, W1 issuer-move)** —
the INDEPENDENT reference semantics. Enumerates the FRAME completely: the touched `bal` + `log`,
and every untouched non-`bal` kernel field. -/
def MintASpec (st : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (st' : RecChainedState) : Prop :=
  mintAdmit st.kernel actor cell a amt
  ∧ st'.kernel.bal = recTransferBal st.kernel.bal a cell a amt
  ∧ st'.log = mintReceipt actor cell a amt :: st.log
  -- THE FRAME: every non-`bal` kernel field literally unchanged.
  ∧ st'.kernel.accounts = st.kernel.accounts
  ∧ st'.kernel.cell = st.kernel.cell
  ∧ st'.kernel.caps = st.kernel.caps
  ∧ st'.kernel.nullifiers = st.kernel.nullifiers
  ∧ st'.kernel.revoked = st.kernel.revoked
  ∧ st'.kernel.commitments = st.kernel.commitments
  ∧ st'.kernel.slotCaveats = st.kernel.slotCaveats
  ∧ st'.kernel.factories = st.kernel.factories
  ∧ st'.kernel.lifecycle = st.kernel.lifecycle
  ∧ st'.kernel.deathCert = st.kernel.deathCert
  ∧ st'.kernel.delegate = st.kernel.delegate
  ∧ st'.kernel.delegations = st.kernel.delegations
  ∧ st'.kernel.delegationEpoch = st.kernel.delegationEpoch
  ∧ st'.kernel.delegationEpochAt = st.kernel.delegationEpochAt
  ∧ st'.kernel.heaps = st.kernel.heaps

/-- **`recCMintAsset_iff_spec` — CHAINED EXECUTOR ⟺ SPEC (FULL state, both directions).** The
chained record kernel commits a `mintA` into `st'` IFF `st'` is EXACTLY the spec'd full post-state.
The `→` VALIDATES `recCMintAsset` against the independent spec — all 18 components
(`bal` + `log` + 16 frame fields) are checked, so a silently-mutated component would make the proof
FAIL; the `←` reconstructs the committed state from the spec. -/
theorem recCMintAsset_iff_spec (st : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (st' : RecChainedState) :
    recCMintAsset st actor cell a amt = some st' ↔ MintASpec st actor cell a amt st' := by
  unfold recCMintAsset recKMintAsset MintASpec mintAdmit mintReceipt
  by_cases hg : mintAuthorizedB st.kernel.caps actor a = true ∧ 0 ≤ amt
      ∧ a ∈ st.kernel.accounts ∧ cell ∈ st.kernel.accounts ∧ a ≠ cell
  · rw [if_pos hg]
    constructor
    · intro h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨hg, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rintro ⟨_, hbal, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
      -- reconstruct st' from the spec: split both records and substitute every field.
      obtain ⟨k', lg'⟩ := st'
      obtain ⟨acc, cl, cp, nl, rv, cm, bl, sc, fc, lc, dc, dl, dn, dge, dgea, hp⟩ := k'
      simp only at hbal hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
      subst hbal hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
      rfl
  · rw [if_neg hg]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨hg', _⟩; exact absurd hg' hg

/-- **`execMintA_iff_spec` — THE DELIVERABLE: `execFullA`-LEVEL EXECUTOR ⟺ SPEC (FULL state, both
directions).** The one gated executor commits a `mintA` turn into `st'` IFF `st'` is EXACTLY the
independent full-state spec. Forward VALIDATES the executor (every one of the 18 components is
pinned); backward reconstructs. This is the supply-creation corner of the
spec⟺executor(⟺circuit) triangle, the `mintA` analog of `recKExec_iff_spec`. -/
theorem execMintA_iff_spec (st : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (st' : RecChainedState) :
    execFullA st (.mintA actor cell a amt) = some st' ↔ MintASpec st actor cell a amt st' := by
  rw [execFullA_mintA]; exact recCMintAsset_iff_spec st actor cell a amt st'

/-! ## §4b — the §8-portal twin `bridgeMintA` is the SAME effect (a corollary).

`execFullA`'s `bridgeMintA` arm dispatches to the SAME `recCMintAsset` verbatim (the §8 CryptoPortal
hypothesis is carried on the conservation keystone, not re-checked here). W1: the bridge cell IS the
issuer of the bridged asset — its well carries −(outstanding bridged supply). So the supply-creation
spec characterizes `bridgeMintA` IDENTICALLY. -/

@[simp] theorem execFullA_bridgeMintA (st : RecChainedState) (actor cell : CellId) (a : AssetId)
    (value : ℤ) :
    execFullA st (.bridgeMintA actor cell a value) = recCMintAsset st actor cell a value := rfl

/-- **`execBridgeMintA_iff_spec` — the bridge-mint twin meets the SAME spec.** -/
theorem execBridgeMintA_iff_spec (st : RecChainedState) (actor cell : CellId) (a : AssetId)
    (value : ℤ) (st' : RecChainedState) :
    execFullA st (.bridgeMintA actor cell a value) = some st' ↔ MintASpec st actor cell a value st' := by
  rw [execFullA_bridgeMintA]; exact recCMintAsset_iff_spec st actor cell a value st'

/-! ## §5 — derived guarantees off the spec.

The spec is the apex truth; these read off it without re-touching the executor. -/

/-- **`mintA_authorized` — no production without ISSUER authority (W1/E2).** A committed `mintA`
PROVES the actor held the privileged mint cap over the asset's ISSUER cell `a` (`mintAuthorizedB`,
NOT bare ownership, NOT a recipient-shaped grant). Read straight off the spec's guard. -/
theorem mintA_authorized (st : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (st' : RecChainedState) (h : execFullA st (.mintA actor cell a amt) = some st') :
    mintAuthorizedB st.kernel.caps actor a = true :=
  ((execMintA_iff_spec st actor cell a amt st').mp h).1.1

/-- **`mintA_nonneg` — no negative-amount supply.** A committed `mintA` PROVES `0 ≤ amt`. -/
theorem mintA_nonneg (st : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (st' : RecChainedState) (h : execFullA st (.mintA actor cell a amt) = some st') :
    0 ≤ amt :=
  ((execMintA_iff_spec st actor cell a amt st').mp h).1.2.1

/-- **`mintA_credit` — the issuer-move, row by row**: the well `(a, a)` debited by exactly `amt`,
the recipient `(cell, a)` credited by exactly `amt`, every OTHER (cell,asset) entry preserved
(`recTransferBal_mint_correct`). Derived from the spec's `bal` clause + the declaratively-validated
helper. -/
theorem mintA_credit (st : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (st' : RecChainedState) (h : execFullA st (.mintA actor cell a amt) = some st') :
    st'.kernel.bal a a = st.kernel.bal a a - amt
    ∧ st'.kernel.bal cell a = st.kernel.bal cell a + amt
    ∧ (∀ c b, ¬ (c = a ∧ b = a) → ¬ (c = cell ∧ b = a)
        → st'.kernel.bal c b = st.kernel.bal c b) := by
  have hspec := (execMintA_iff_spec st actor cell a amt st').mp h
  have hbal : st'.kernel.bal = recTransferBal st.kernel.bal a cell a amt := hspec.2.1
  have hne : a ≠ cell := hspec.1.2.2.2.2
  obtain ⟨hdeb, hcred, hframe⟩ := recTransferBal_mint_correct st.kernel.bal cell a amt hne
  refine ⟨?_, ?_, ?_⟩
  · rw [hbal]; exact hdeb
  · rw [hbal]; exact hcred
  · intro c b hni hnc; rw [hbal]; exact hframe c b hni hnc

/-- **`mintA_supply_delta` — W1 CONSERVATION CONTENT: a committed mint leaves EVERY asset's supply
EXACTLY unchanged** (`recKMintAsset_delta` lifted to the `execFullA` level). The issuer's well
absorbs the minted amount — the supply increment is ON the ledger, the sum never moves. This is the
semantic punchline of W1 supply-creation: exactness, not disclosed inflation. -/
theorem mintA_supply_delta (st : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (st' : RecChainedState) (h : execFullA st (.mintA actor cell a amt) = some st') (b : AssetId) :
    recTotalAsset st'.kernel b = recTotalAsset st.kernel b := by
  -- recover the chained-executor commitment from the execFullA-level one, then reuse the kernel delta.
  rw [execFullA_mintA] at h
  unfold recCMintAsset at h
  cases hm : recKMintAsset st.kernel actor cell a amt with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some k' =>
      rw [hm] at h; simp only [Option.some.injEq] at h
      have hk : st'.kernel = k' := by rw [← h]
      rw [hk]; exact recKMintAsset_delta st.kernel k' actor cell a amt hm b

/-! ## §6 — NON-VACUITY: the spec is a genuine GATE (rejects bad inputs).

A spec that accepts everything is worthless. `execFullA` REJECTS an unauthorized mint, a
negative-amount mint, a mint whose issuer well is dead (the genesis-order tooth), a mint to a dead
recipient, and the self-mint — each makes the guard FALSE, hence the executor returns `none` and
`MintASpec` is unsatisfiable. -/

/-- **`mintA_rejects_unauthorized`.** A `mintA` over a state where the actor lacks the privileged
mint cap over the ISSUER (`mintAuthorizedB caps actor a = false`) is REJECTED — `execFullA … =
none`. Unprivileged supply creation is impossible; a recipient-shaped cap does not help. -/
theorem mintA_rejects_unauthorized (st : RecChainedState) (actor cell : CellId) (a : AssetId)
    (amt : ℤ) (hbad : mintAuthorizedB st.kernel.caps actor a = false) :
    execFullA st (.mintA actor cell a amt) = none := by
  rw [execFullA_mintA]; unfold recCMintAsset recKMintAsset
  rw [if_neg (by rintro ⟨h, _⟩; rw [hbad] at h; exact absurd h (by simp))]

/-- **`mintA_rejects_negative`.** A `mintA` with a negative amount (`amt < 0`) is REJECTED. -/
theorem mintA_rejects_negative (st : RecChainedState) (actor cell : CellId) (a : AssetId)
    (amt : ℤ) (hbad : amt < 0) :
    execFullA st (.mintA actor cell a amt) = none := by
  rw [execFullA_mintA]; unfold recCMintAsset recKMintAsset
  rw [if_neg (by rintro ⟨_, h, _⟩; exact absurd h (by omega))]

/-- **`mintA_rejects_dead_issuer` (the genesis-order tooth).** A `mintA` of an asset whose ISSUER
well is not a live account (`a ∉ accounts`) is REJECTED — the bootstrap order (create the issuer
cell, then mint) is a gate, not a convention. -/
theorem mintA_rejects_dead_issuer (st : RecChainedState) (actor cell : CellId) (a : AssetId)
    (amt : ℤ) (hbad : a ∉ st.kernel.accounts) :
    execFullA st (.mintA actor cell a amt) = none := by
  rw [execFullA_mintA]; unfold recCMintAsset recKMintAsset
  rw [if_neg (by rintro ⟨_, _, h, _⟩; exact absurd h hbad)]

/-- **`mintA_rejects_dead_cell`.** A `mintA` to a recipient that is NOT a live account
(`cell ∉ accounts`) is REJECTED. -/
theorem mintA_rejects_dead_cell (st : RecChainedState) (actor cell : CellId) (a : AssetId)
    (amt : ℤ) (hbad : cell ∉ st.kernel.accounts) :
    execFullA st (.mintA actor cell a amt) = none := by
  rw [execFullA_mintA]; unfold recCMintAsset recKMintAsset
  rw [if_neg (by rintro ⟨_, _, _, h, _⟩; exact absurd h hbad)]

/-- **`mintA_rejects_self_mint`.** A `mintA` into the issuer's own well (`a = cell`) is REJECTED —
the no-move (the +amt credit and the +amt well-debit would cancel; the kernel refuses instead). -/
theorem mintA_rejects_self_mint (st : RecChainedState) (actor : CellId) (a : AssetId) (amt : ℤ) :
    execFullA st (.mintA actor a a amt) = none := by
  rw [execFullA_mintA]; unfold recCMintAsset recKMintAsset
  rw [if_neg (by rintro ⟨_, _, _, _, h⟩; exact absurd rfl h)]

/-- **`mintA_admits_iff` — the executor commits IFF the guard holds.** The clean characterization:
there is a committed post-state EXACTLY when supply-creation is admissible. -/
theorem mintA_admits_iff (st : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ) :
    (∃ st', execFullA st (.mintA actor cell a amt) = some st')
      ↔ mintAdmit st.kernel actor cell a amt := by
  rw [execFullA_mintA]
  unfold recCMintAsset recKMintAsset mintAdmit
  by_cases hg : mintAuthorizedB st.kernel.caps actor a = true ∧ 0 ≤ amt
      ∧ a ∈ st.kernel.accounts ∧ cell ∈ st.kernel.accounts ∧ a ≠ cell
  · rw [if_pos hg]; exact ⟨fun _ => hg, fun _ => ⟨_, rfl⟩⟩
  · rw [if_neg hg]
    constructor
    · rintro ⟨st', h⟩; exact absurd h (by simp)
    · intro hg'; exact absurd hg' hg

/-! ## §7 — concrete #guard non-vacuity witnesses (genuine `decide`, NOT `native_decide`).

Cells 0 (the ISSUER of asset 0) and 1 are live; actor 9 holds the `node 0` ISSUER cap; actor 0
holds NO mint cap. A privileged mint of 50 of asset 0 into cell 1 commits — the well goes NEGATIVE
(0 → −50, no availability gate at the well) and the sum stays EXACTLY 0; the unprivileged /
negative / dead-issuer / dead-recipient / self mints are decidably rejected. -/

/-- A concrete pre-state: cells {0, 1} live, ledger empty (a genesis shape), actor 9 holds the
`node 0` ISSUER cap for asset 0. -/
def stM0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun a => if a = 9 then [Cap.node 0] else [] }
    log := [] }

-- The privileged mint of 50 of asset 0 (issuer cell 0) into the live cell 1 COMMITS:
#guard (execFullA stM0 (.mintA 9 1 0 50)).isSome  --  true
-- ...the well went NEGATIVE-capable (0 → −50) and the recipient credited (+50): Σ stays 0:
#guard ((execFullA stM0 (.mintA 9 1 0 50)).map
        (fun s => (s.kernel.bal 0 0, s.kernel.bal 1 0, recTotalAsset s.kernel 0)))
        == some (-50, 50, 0)
-- An UNPRIVILEGED mint (actor 0, no `node 0` issuer cap) is REJECTED:
#guard decide ((execFullA stM0 (.mintA 0 1 0 50)).isNone)  --  true
-- A NEGATIVE-amount mint is REJECTED:
#guard decide ((execFullA stM0 (.mintA 9 1 0 (-5))).isNone)  --  true
-- A mint of an asset with a DEAD issuer well (asset 7: cell 7 ∉ accounts) is REJECTED:
#guard decide ((execFullA stM0 (.mintA 9 1 7 50)).isNone)  --  true
-- A mint to a DEAD recipient (cell 7 ∉ accounts) is REJECTED:
#guard decide ((execFullA stM0 (.mintA 9 7 0 50)).isNone)  --  true
-- The SELF-mint (into the issuer's own well) is REJECTED:
#guard decide ((execFullA stM0 (.mintA 9 0 0 50)).isNone)  --  true
-- mintAuthorizedB witnesses: actor 9 authorized over the issuer 0, actor 0 not:
#guard mintAuthorizedB stM0.kernel.caps 9 0 == true
#guard mintAuthorizedB stM0.kernel.caps 0 0 == false

/-! ## §8 — Axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms recTransferBal_mint_correct
#assert_axioms execFullA_mintA
#assert_axioms recCMintAsset_iff_spec
#assert_axioms execMintA_iff_spec
#assert_axioms execFullA_bridgeMintA
#assert_axioms execBridgeMintA_iff_spec
#assert_axioms mintA_authorized
#assert_axioms mintA_nonneg
#assert_axioms mintA_credit
#assert_axioms mintA_supply_delta
#assert_axioms mintA_rejects_unauthorized
#assert_axioms mintA_rejects_negative
#assert_axioms mintA_rejects_dead_issuer
#assert_axioms mintA_rejects_dead_cell
#assert_axioms mintA_rejects_self_mint
#assert_axioms mintA_admits_iff

end Dregg2.Circuit.Spec.SupplyCreation
