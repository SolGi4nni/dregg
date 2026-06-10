/-
# Dregg2.Circuit.Spec.supplycreation — INDEPENDENT full-state spec + executor⟺spec for the
dregg2 effect family **supply-creation** (variant: `mintA`).

This is a *leaf* module in the `Transfer.lean` lineage: it builds, for the per-asset privileged
MINT effect, the SAME triangle corner the reference `TransferSpec`/`recKExec_iff_spec` establish
for `Transfer`, but written INDEPENDENTLY of the executor. The deliverables, mirroring the
reference pattern (`Dregg2/Circuit/Transfer.lean` §6b):

  1. `MintASpec st t st'` : Prop — the FULL declarative post-state of a committed `mintA`. It is
     the conjunction of
       * the admissibility guard `mintAuthorizedB caps actor cell ∧ 0 ≤ amt ∧ cell ∈ accounts`
         (the EXACT `recKMintAsset` `if`, read off the CODE);
       * the EXACT touched components — `kernel.bal` credited by `recBalCredit … cell a amt` and the
         receipt `log` prepended with the disclosed mint turn `{actor, src:=cell, dst:=cell, amt}`;
       * EVERY OTHER state component LITERALLY unchanged: all 16 non-`bal` kernel fields
         (`accounts` `cell` `caps` `escrows` `nullifiers` `revoked` `commitments` `queues` `swiss`
         `slotCaveats` `factories` `lifecycle` `deathCert` `delegate` `delegations` `sealedBoxes`)
         — the FRAME. No frame clause mentions any executor helper.
  2. `execMintA_iff_spec : execFullA st (.mintA actor cell a amt) = some st' ↔ MintASpec …` — BOTH
     directions. The `→` VALIDATES the executor against the independent spec: a silently-mutated
     field would make the frame clause unprovable. (None was found — see frameGaps in the report.)
  3. `recBalCredit_correct` — the post-`bal` helper validated DECLARATIVELY (the `cell`/`a` cell is
     credited by `amt`, every other (cell,asset) entry literally preserved), so the spec's
     `bal = recBalCredit …` clause encodes credit ∧ ledger-frame, not blind trust.

The supply-creation family on `execFullA` is `mintA` (and its §8-portal twin `bridgeMintA`, which
dispatches to the SAME `recCMintAsset` — a corollary, `execBridgeMintA_iff_spec`, is included). The
companion conservation corollary `mintA_supply_delta` pins the SEMANTIC content: a committed mint
raises asset `a`'s supply by exactly `amt` and leaves every other asset's supply unchanged.
-/
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Circuit.Spec.SupplyCreation

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority

/-! ## §1 — the admissibility guard, lifted from the CODE.

`recKMintAsset` (`TurnExecutorFull.lean:687`) commits IFF this exact conjunction holds. The prompt's
"`supplyAuthB`" is the codebase's `mintAuthorizedB` (the privileged `node`/`control` gate — bare
ownership is deliberately NOT sufficient: a cell cannot coin its own supply). The third conjunct
`cell ∈ accounts` (liveness) is part of the real `if` and so part of the guard — omitting it would
under-specify the executor. -/

/-- **`mintAdmit`** — the full admissibility guard `recKMintAsset`/`recCMintAsset` checks, as a
`Prop` (the conjunction in the executor's `if`). PRIVILEGED supply authority ∧ non-negativity ∧
cell-liveness. -/
def mintAdmit (k : RecordKernelState) (actor cell : CellId) (amt : ℤ) : Prop :=
  mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ amt ∧ cell ∈ k.accounts

/-- The disclosed receipt a committed `mintA` prepends to the log (a self-edge `cell → cell` of size
`amt`, exactly `recCMintAsset`'s `log` head, `TurnExecutorFull.lean:758`). -/
def mintReceipt (actor cell : CellId) (amt : ℤ) : Turn :=
  { actor := actor, src := cell, dst := cell, amt := amt }

/-! ## §2 — the post-`bal` helper, validated DECLARATIVELY.

`recBalCredit bal cell a amt` is the ONLY thing a committed mint does to the ledger. We validate it
relationally (the touched entry is credited by `amt`, every other entry preserved) so the spec's
`bal = recBalCredit …` clause carries real meaning rather than trusting the helper's name. -/

/-- **`recBalCredit_correct`** — the ledger-update helper validated DECLARATIVELY: a mint credits
`(cell, a)` by exactly `amt`, and leaves every OTHER (cell,asset) entry literally untouched. So the
spec's `bal = recBalCredit …` clause encodes credit ∧ ledger-frame. -/
theorem recBalCredit_correct (bal : CellId → AssetId → ℤ) (cell : CellId) (a : AssetId) (amt : ℤ) :
    recBalCredit bal cell a amt cell a = bal cell a + amt
    ∧ (∀ c b, ¬ (c = cell ∧ b = a) → recBalCredit bal cell a amt c b = bal c b) := by
  refine ⟨?_, ?_⟩
  · simp only [recBalCredit, and_self, if_true]
  · intro c b hne; simp only [recBalCredit, if_neg hne]

/-! ## §3 — the executor projection: `execFullA` on `mintA` IS `recCMintAsset`.

The `mintA` arm of `execFullA` (`TurnExecutorFull.lean:3483`) is a SINGLE branch — it dispatches
straight to `recCMintAsset` with no rewrap. This is the "clean / single-branch" case the prompt
hopes for. We expose it as a definitional rewrite so the spec proof works on `recCMintAsset`. -/

@[simp] theorem execFullA_mintA (st : RecChainedState) (actor cell : CellId) (a : AssetId)
    (amt : ℤ) :
    execFullA st (.mintA actor cell a amt) = recCMintAsset st actor cell a amt := rfl

/-! ## §4 — FULL-STATE SEMANTIC SPEC (the INDEPENDENT reference) + executor⟺spec.

`MintASpec` is the COMPLETE declarative post-state of a committed `mintA`, written INDEPENDENTLY of
the executor: the guard holds; the post `kernel.bal` is the `recBalCredit` credit; the post `log` is
the disclosed mint receipt prepended; and ALL 16 non-`bal` kernel components are LITERALLY
unchanged. No frame clause mentions `execFullA`/`recCMintAsset`/`recKMintAsset`. -/

/-- **The full-state declarative spec of a committed supply-creation (`mintA`)** — the INDEPENDENT
reference semantics. Enumerates the FRAME completely: the touched `bal` + `log`, and every one of
the 16 untouched non-`bal` kernel fields. -/
def MintASpec (st : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (st' : RecChainedState) : Prop :=
  mintAdmit st.kernel actor cell amt
  ∧ st'.kernel.bal = recBalCredit st.kernel.bal cell a amt
  ∧ st'.log = mintReceipt actor cell amt :: st.log
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

/-- **`recCMintAsset_iff_spec` — CHAINED EXECUTOR ⟺ SPEC (FULL state, both directions).** The
chained record kernel commits a `mintA` into `st'` IFF `st'` is EXACTLY the spec'd full post-state.
The `→` VALIDATES `recCMintAsset` against the independent spec — all 18 components
(`bal` + `log` + 16 frame fields) are checked, so a silently-mutated component would make the proof
FAIL; the `←` reconstructs the committed state from the spec. -/
theorem recCMintAsset_iff_spec (st : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (st' : RecChainedState) :
    recCMintAsset st actor cell a amt = some st' ↔ MintASpec st actor cell a amt st' := by
  unfold recCMintAsset recKMintAsset MintASpec mintAdmit mintReceipt
  by_cases hg : mintAuthorizedB st.kernel.caps actor cell = true ∧ 0 ≤ amt ∧ cell ∈ st.kernel.accounts
  · rw [if_pos hg]
    constructor
    · intro h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨hg, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rintro ⟨_, hbal, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
      -- reconstruct st' from the spec: split both records and substitute every field.
      obtain ⟨k', lg'⟩ := st'
      obtain ⟨acc, cl, cp, nl, rv, cm, bl, sc, fc, lc, dc, dl, dn, dge, dgea⟩ := k'
      simp only at hbal hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
      subst hbal hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
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

`execFullA`'s `bridgeMintA` arm (`TurnExecutorFull.lean:3520`) dispatches to the SAME
`recCMintAsset` verbatim (the §8 CryptoPortal hypothesis is carried on the conservation keystone,
not re-checked here). So the supply-creation spec characterizes `bridgeMintA` IDENTICALLY. -/

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

/-- **`mintA_authorized` — no supply without privileged authority.** A committed `mintA` PROVES the
actor held the privileged mint cap (`mintAuthorizedB`, NOT bare ownership). Read straight off the
spec's guard. -/
theorem mintA_authorized (st : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (st' : RecChainedState) (h : execFullA st (.mintA actor cell a amt) = some st') :
    mintAuthorizedB st.kernel.caps actor cell = true :=
  ((execMintA_iff_spec st actor cell a amt st').mp h).1.1

/-- **`mintA_nonneg` — no negative-amount supply.** A committed `mintA` PROVES `0 ≤ amt` (no
inflation by negative mint). -/
theorem mintA_nonneg (st : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (st' : RecChainedState) (h : execFullA st (.mintA actor cell a amt) = some st') :
    0 ≤ amt :=
  ((execMintA_iff_spec st actor cell a amt st').mp h).1.2.1

/-- **`mintA_credit` — the touched ledger entry is credited by exactly `amt`** (the entries of every
OTHER cell/asset preserved — `recBalCredit_correct`). Derived from the spec's `bal` clause + the
declaratively-validated helper. -/
theorem mintA_credit (st : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (st' : RecChainedState) (h : execFullA st (.mintA actor cell a amt) = some st') :
    st'.kernel.bal cell a = st.kernel.bal cell a + amt
    ∧ (∀ c b, ¬ (c = cell ∧ b = a) → st'.kernel.bal c b = st.kernel.bal c b) := by
  have hspec := (execMintA_iff_spec st actor cell a amt st').mp h
  have hbal : st'.kernel.bal = recBalCredit st.kernel.bal cell a amt := hspec.2.1
  obtain ⟨hcred, hframe⟩ := recBalCredit_correct st.kernel.bal cell a amt
  refine ⟨?_, ?_⟩
  · rw [hbal]; exact hcred
  · intro c b hne; rw [hbal]; exact hframe c b hne

/-- **`mintA_supply_delta` — CONSERVATION CONTENT: a committed mint raises asset `a`'s supply by
exactly `amt`, and leaves every OTHER asset's supply unchanged** (`recKMintAsset_delta` lifted to
the `execFullA` level via the spec's `bal`-credit). This is the semantic punchline of
supply-creation: supply is created in a single asset, by exactly the disclosed amount, when the cell
is live. -/
theorem mintA_supply_delta (st : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (st' : RecChainedState) (h : execFullA st (.mintA actor cell a amt) = some st') (b : AssetId) :
    recTotalAsset st'.kernel b = recTotalAsset st.kernel b + (if b = a then amt else 0) := by
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
negative-amount mint, and a mint to a dead (non-account) cell — each makes the guard FALSE, hence
the executor returns `none` and `MintASpec` is unsatisfiable. -/

/-- **`mintA_rejects_unauthorized`.** A `mintA` over a state where the actor lacks the privileged
mint cap (`mintAuthorizedB = false`) is REJECTED — `execFullA … = none`. Unprivileged supply
creation is impossible. -/
theorem mintA_rejects_unauthorized (st : RecChainedState) (actor cell : CellId) (a : AssetId)
    (amt : ℤ) (hbad : mintAuthorizedB st.kernel.caps actor cell = false) :
    execFullA st (.mintA actor cell a amt) = none := by
  rw [execFullA_mintA]; unfold recCMintAsset recKMintAsset
  rw [if_neg (by rintro ⟨h, _⟩; rw [hbad] at h; exact absurd h (by simp))]

/-- **`mintA_rejects_negative`.** A `mintA` with a negative amount (`amt < 0`) is REJECTED. No
negative-amount inflation. -/
theorem mintA_rejects_negative (st : RecChainedState) (actor cell : CellId) (a : AssetId)
    (amt : ℤ) (hbad : amt < 0) :
    execFullA st (.mintA actor cell a amt) = none := by
  rw [execFullA_mintA]; unfold recCMintAsset recKMintAsset
  rw [if_neg (by rintro ⟨_, h, _⟩; exact absurd h (by omega))]

/-- **`mintA_rejects_dead_cell`.** A `mintA` to a cell that is NOT a live account
(`cell ∉ accounts`) is REJECTED. Supply can only be created on a live cell. -/
theorem mintA_rejects_dead_cell (st : RecChainedState) (actor cell : CellId) (a : AssetId)
    (amt : ℤ) (hbad : cell ∉ st.kernel.accounts) :
    execFullA st (.mintA actor cell a amt) = none := by
  rw [execFullA_mintA]; unfold recCMintAsset recKMintAsset
  rw [if_neg (by rintro ⟨_, _, h⟩; exact absurd h hbad)]

/-- **`mintA_admits_iff` — the executor commits IFF the guard holds.** The clean characterization:
there is a committed post-state EXACTLY when supply-creation is admissible. -/
theorem mintA_admits_iff (st : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ) :
    (∃ st', execFullA st (.mintA actor cell a amt) = some st') ↔ mintAdmit st.kernel actor cell amt := by
  rw [execFullA_mintA]
  unfold recCMintAsset recKMintAsset mintAdmit
  by_cases hg : mintAuthorizedB st.kernel.caps actor cell = true ∧ 0 ≤ amt ∧ cell ∈ st.kernel.accounts
  · rw [if_pos hg]; exact ⟨fun _ => hg, fun _ => ⟨_, rfl⟩⟩
  · rw [if_neg hg]
    constructor
    · rintro ⟨st', h⟩; exact absurd h (by simp)
    · intro hg'; exact absurd hg' hg

/-! ## §7 — concrete #guard non-vacuity witnesses (genuine `decide`, NOT `native_decide`).

Cell 0 is a live account; actor 9 holds a `node 0` mint cap (privileged supply over cell 0); actor 0
holds NO mint cap (bare ownership is insufficient). A privileged mint of +50 of asset 1 commits; the
unprivileged / negative / dead-cell mints are decidably rejected. -/

/-- A concrete pre-state: cell {0} live, ledger empty, actor 9 holds the `node 0` mint cap. -/
def stM0 : RecChainedState :=
  { kernel :=
      { accounts := {0}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun a => if a = 9 then [Cap.node 0] else [] }
    log := [] }

-- The privileged mint of +50 of asset 1 by actor 9 over the live cell 0 COMMITS:
#guard (execFullA stM0 (.mintA 9 0 1 50)).isSome  --  true
-- An UNPRIVILEGED mint (actor 0, bare ownership, no `node 0` cap) is REJECTED:
#guard decide ((execFullA stM0 (.mintA 0 0 1 50)).isNone)  --  true
-- A NEGATIVE-amount mint is REJECTED:
#guard decide ((execFullA stM0 (.mintA 9 0 1 (-5))).isNone)  --  true
-- A mint to a DEAD cell (cell 7 ∉ accounts) is REJECTED:
#guard decide ((execFullA stM0 (.mintA 9 7 1 50)).isNone)  --  true
-- mintAuthorizedB witnesses: actor 9 authorized over cell 0, actor 0 not:
#guard mintAuthorizedB stM0.kernel.caps 9 0 == true
#guard mintAuthorizedB stM0.kernel.caps 0 0 == false

/-! ## §8 — Axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms recBalCredit_correct
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
#assert_axioms mintA_rejects_dead_cell
#assert_axioms mintA_admits_iff

end Dregg2.Circuit.Spec.SupplyCreation
