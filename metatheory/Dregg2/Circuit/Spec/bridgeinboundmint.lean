/-
# Dregg2.Circuit.Spec.bridgeinboundmint — INDEPENDENT full-state spec + executor⟺spec for the
dregg2 effect family **bridge-inbound-mint** (variant: `bridgeMintA`).

Phase 2 of dregg1's two-phase cross-chain bridge, the INBOUND mint: when the OTHER chain confirms a
lock, this chain MINTS the asset into the recipient cell (dregg1's `finalize_bridge` credit leg /
`cell/src/note_bridge.rs`). Where `bridgeoutboundlock.lean` debits the originator and parks an
unresolved escrow record, the inbound mint is the dual: it CREDITS the destination cell's asset
ledger — a privileged supply-creation event whose authority is the §8 CryptoPortal hypothesis that
the destination signature / other-chain confirmation is present (carried on the conservation keystone,
NOT re-checked here; the in-VM gate is the SAME privileged mint authority `recCMintAsset` enforces).

This is a *leaf* module in the `Transfer.lean` lineage (imported by nothing; gated standalone). It
re-derives, INDEPENDENTLY of the executor, the SAME triangle corner the reference
`TransferSpec`/`recKExec_iff_spec`/`recTransfer_correct` establish for `Transfer`. The executor arm
this module specifies (`TurnExecutorFull.lean:3520`) is a SINGLE branch:

    execFullA s (.bridgeMintA actor cell a value) = recCMintAsset s actor cell a value

`recCMintAsset` (`TurnExecutorFull.lean:755`) is the chained per-asset mint: it runs the kernel mint
`recKMintAsset` (`TurnExecutorFull.lean:687`) and, on commit, PREPENDS a disclosed self-edge receipt
`{actor, src:=cell, dst:=cell, amt:=value}` onto the log. The kernel mint's admissibility guard is the
EXACT conjunction (read off the CODE — the prompt's "`supplyAuthB`" is the codebase's
`mintAuthorizedB`, the privileged `node`/`control` gate; bare ownership is NOT sufficient — and the
REAL `if` ALSO checks non-negativity AND destination liveness, the teeth omitting them would lose):

    mintAuthorizedB caps actor cell = true    -- (1) SUPPLY AUTHORITY (privileged; bare ownership insufficient)
  ∧ 0 ≤ value                                 -- (2) NON-NEGATIVITY (no negative-mint inflation)
  ∧ cell ∈ accounts                           -- (3) DESTINATION LIVENESS (mint only onto a live cell)

and on commit it produces `some { k with bal := recBalCredit k.bal cell a value }` — a SINGLE-cell,
single-asset CREDIT of `value` to `(cell, a)`, with EVERY other (cell,asset) ledger entry, every
OTHER kernel field, untouched.

## What is proved (the apex reference truth, BOTH directions)

  1. `InboundMintSpec st actor cell a value st'` — the INDEPENDENT declarative full-state
     post-condition: the admissibility guard (`inboundMintAdmit`), the EXACT post-`bal` ledger
     (`recBalCredit … cell a value`), the chained `log` advanced by exactly the disclosed mint receipt,
     AND the FRAME — every one of the 16 OTHER RecordKernelState components LITERALLY unchanged
     (`accounts cell caps escrows nullifiers revoked commitments queues swiss slotCaveats factories
     lifecycle deathCert delegate delegations sealedBoxes`). No frame clause mentions the executor.
     Missing ANY field reintroduces a ghost — all 17 kernel components + log are enumerated.

  2. `recBalCredit_inbound_correct` — the post-`bal` helper validated DECLARATIVELY (the `(cell,a)`
     entry credited by `value`, every other `(c,b)` entry literally preserved), so the spec's
     `bal = recBalCredit …` clause genuinely encodes credit ∧ ledger-frame rather than blind trust.

  3. `recCMintAsset_iff_inboundSpec` — the ⟺ on the chained step `recCMintAsset`.
     `execBridgeMintA_iff_spec` — execFullA ⟺ spec for the `bridgeMintA` variant (BOTH directions).
     The `→` VALIDATES the executor against the independent spec — all 17 kernel components
     (`bal` + the 16 frame fields) AND the log are checked, so a silently-mutated field would make the
     proof FAIL; the `←` reconstructs the committed state from the spec.

  4. Post-state corollaries: `bridgeMint_credit` (the per-asset credit at `(cell,a)` + ledger-frame),
     `bridgeMint_supply_delta` (the CONSERVATION CONTENT: a committed inbound mint raises asset `a`'s
     supply by exactly `value`, leaving every other asset's supply unchanged — the inbound dual of the
     outbound lock's debit), `bridgeMint_authorized`, `bridgeMint_nonneg`.

  5. Non-vacuity: `bridgeMint_rejects_unauthorized`, `bridgeMint_rejects_negative`,
     `bridgeMint_rejects_dead_cell`, plus `bridgeMint_admits_iff` — each forged input fails a guard leg
     ⇒ the executor returns `none` ⇒ no spec post-state exists. A spec that accepts everything is
     worthless. Concrete `#guard` witnesses (genuine `decide`, NOT `native_decide`) exhibit a good mint
     committing and the three forgeries decidably rejected.

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on every keystone.
-/
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Tactics

namespace Dregg2.Circuit.Spec.BridgeInboundMint

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

/-! ## §1 — the admissibility guard, lifted from the CODE.

`recKMintAsset` (`TurnExecutorFull.lean:687`) commits IFF this exact conjunction holds. The prompt's
"`supplyAuthB s.kernel.caps actor cell`" is the codebase's `mintAuthorizedB` (the privileged
`node`/`control` gate — a cell cannot coin its own supply by bare ownership). The non-negativity and
destination-liveness conjuncts are part of the REAL `if`, hence part of the guard; omitting them would
UNDER-specify the executor (a `→` direction would then be unprovable, or a `←` would over-admit). -/

/-- **`inboundMintAdmit`** — the full admissibility guard `recKMintAsset` (and so `recCMintAsset`,
the chained step `bridgeMintA` dispatches to) checks, as a `Prop`: PRIVILEGED supply authority ∧
non-negativity ∧ destination-cell liveness. -/
def inboundMintAdmit (k : RecordKernelState) (actor cell : CellId) (value : ℤ) : Prop :=
  mintAuthorizedB k.caps actor cell = true ∧ 0 ≤ value ∧ cell ∈ k.accounts

/-- The disclosed receipt a committed `bridgeMintA` prepends to the log: a self-edge `cell → cell` of
size `value`, exactly `recCMintAsset`'s `log` head (`TurnExecutorFull.lean:758`). Stated HERE so the
spec's `log` clause does not reference the executor's body. -/
def inboundMintReceipt (actor cell : CellId) (value : ℤ) : Turn :=
  { actor := actor, src := cell, dst := cell, amt := value }

/-! ## §2 — the post-`bal` helper, validated DECLARATIVELY.

`recBalCredit bal cell a value` is the ONLY thing a committed inbound mint does to the ledger. We
validate it relationally (the touched entry credited by `value`, every other entry preserved) so the
spec's `bal = recBalCredit …` clause carries real meaning rather than trusting the helper's name. -/

/-- **`recBalCredit_inbound_correct`** — the ledger-update helper validated DECLARATIVELY: an inbound
mint credits `(cell, a)` by exactly `value`, and leaves every OTHER (cell,asset) entry literally
untouched. So the spec's `bal = recBalCredit …` clause genuinely encodes credit ∧ ledger-frame. -/
theorem recBalCredit_inbound_correct (bal : CellId → AssetId → ℤ) (cell : CellId) (a : AssetId)
    (value : ℤ) :
    recBalCredit bal cell a value cell a = bal cell a + value
    ∧ (∀ c b, ¬ (c = cell ∧ b = a) → recBalCredit bal cell a value c b = bal c b) := by
  refine ⟨?_, ?_⟩
  · simp only [recBalCredit, and_self, if_true]
  · intro c b hne; simp only [recBalCredit, if_neg hne]

/-! ## §3 — the executor projection: `execFullA` on `bridgeMintA` IS `recCMintAsset`.

The `bridgeMintA` arm of `execFullA` (`TurnExecutorFull.lean:3520`) is a SINGLE branch — it dispatches
straight to `recCMintAsset` with no rewrap. This is the "clean / single-branch" case. We expose it as
a definitional rewrite so the spec proof works on `recCMintAsset`. -/

@[simp] theorem execFullA_bridgeMintA (st : RecChainedState) (actor cell : CellId) (a : AssetId)
    (value : ℤ) :
    execFullA st (.bridgeMintA actor cell a value) = recCMintAsset st actor cell a value := rfl

/-! ## §4 — FULL-STATE SEMANTIC SPEC (the INDEPENDENT reference) + executor⟺spec.

`InboundMintSpec` is the COMPLETE declarative post-state of a committed `bridgeMintA`, written
INDEPENDENTLY of the executor: the guard holds; the post `kernel.bal` is the `recBalCredit` credit;
the post `log` is the disclosed mint receipt prepended; and ALL 16 non-`bal` kernel components are
LITERALLY unchanged. No frame clause mentions `execFullA`/`recCMintAsset`/`recKMintAsset`. -/

/-- **The full-state declarative spec of a committed bridge-inbound-mint (`bridgeMintA`)** — the
INDEPENDENT reference semantics. Enumerates the FRAME completely: the touched `bal` + `log`, and every
one of the 16 untouched non-`bal` kernel fields. -/
def InboundMintSpec (st : RecChainedState) (actor cell : CellId) (a : AssetId) (value : ℤ)
    (st' : RecChainedState) : Prop :=
  inboundMintAdmit st.kernel actor cell value
  ∧ st'.kernel.bal = recBalCredit st.kernel.bal cell a value
  ∧ st'.log = inboundMintReceipt actor cell value :: st.log
  -- THE FRAME: every non-`bal` kernel field literally unchanged (16).
  ∧ st'.kernel.accounts = st.kernel.accounts
  ∧ st'.kernel.cell = st.kernel.cell
  ∧ st'.kernel.caps = st.kernel.caps
  ∧ st'.kernel.escrows = st.kernel.escrows
  ∧ st'.kernel.nullifiers = st.kernel.nullifiers
  ∧ st'.kernel.revoked = st.kernel.revoked
  ∧ st'.kernel.commitments = st.kernel.commitments
  ∧ st'.kernel.queues = st.kernel.queues
  ∧ st'.kernel.swiss = st.kernel.swiss
  ∧ st'.kernel.slotCaveats = st.kernel.slotCaveats
  ∧ st'.kernel.factories = st.kernel.factories
  ∧ st'.kernel.lifecycle = st.kernel.lifecycle
  ∧ st'.kernel.deathCert = st.kernel.deathCert
  ∧ st'.kernel.delegate = st.kernel.delegate
  ∧ st'.kernel.delegations = st.kernel.delegations
  ∧ st'.kernel.sealedBoxes = st.kernel.sealedBoxes

/-- **`recCMintAsset_iff_inboundSpec` — CHAINED EXECUTOR ⟺ SPEC (FULL state, both directions).** The
chained record kernel commits a `bridgeMintA` (via `recCMintAsset`) into `st'` IFF `st'` is EXACTLY
the spec'd full post-state. The `→` VALIDATES `recCMintAsset` against the independent spec — all 18
components (`bal` + `log` + 16 frame fields) are checked, so a silently-mutated component would make
the proof FAIL; the `←` reconstructs the committed state from the spec. -/
theorem recCMintAsset_iff_inboundSpec (st : RecChainedState) (actor cell : CellId) (a : AssetId)
    (value : ℤ) (st' : RecChainedState) :
    recCMintAsset st actor cell a value = some st' ↔ InboundMintSpec st actor cell a value st' := by
  unfold recCMintAsset recKMintAsset InboundMintSpec inboundMintAdmit inboundMintReceipt
  by_cases hg : mintAuthorizedB st.kernel.caps actor cell = true ∧ 0 ≤ value ∧ cell ∈ st.kernel.accounts
  · rw [if_pos hg]
    constructor
    · intro h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨hg, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rintro ⟨_, hbal, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩
      -- reconstruct st' from the spec: split both records and substitute every field.
      obtain ⟨k', lg'⟩ := st'
      obtain ⟨acc, cl, cp, es, nl, rv, cm, bl, qs, sw, sc, fc, lc, dc, dl, dn, sb⟩ := k'
      simp only at hbal hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
      subst hbal hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
      rfl
  · rw [if_neg hg]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨hg', _⟩; exact absurd hg' hg

/-- **`execBridgeMintA_iff_spec` — THE DELIVERABLE: `execFullA`-LEVEL EXECUTOR ⟺ SPEC (FULL state,
both directions).** The one gated executor commits a `bridgeMintA` turn into `st'` IFF `st'` is
EXACTLY the independent full-state spec. Forward VALIDATES the executor (every one of the 18
components is pinned); backward reconstructs. This is the bridge-inbound-mint corner of the
spec⟺executor(⟺circuit) triangle, the `bridgeMintA` analog of `recKExec_iff_spec`. -/
theorem execBridgeMintA_iff_spec (st : RecChainedState) (actor cell : CellId) (a : AssetId)
    (value : ℤ) (st' : RecChainedState) :
    execFullA st (.bridgeMintA actor cell a value) = some st'
      ↔ InboundMintSpec st actor cell a value st' := by
  rw [execFullA_bridgeMintA]; exact recCMintAsset_iff_inboundSpec st actor cell a value st'

/-! ## §5 — derived guarantees off the spec.

The spec is the apex truth; these read off it without re-touching the executor. -/

/-- **`bridgeMint_authorized` — no inbound supply without privileged authority.** A committed
`bridgeMintA` PROVES the actor held the privileged mint cap (`mintAuthorizedB`, NOT bare ownership).
Read straight off the spec's guard. -/
theorem bridgeMint_authorized (st : RecChainedState) (actor cell : CellId) (a : AssetId) (value : ℤ)
    (st' : RecChainedState) (h : execFullA st (.bridgeMintA actor cell a value) = some st') :
    mintAuthorizedB st.kernel.caps actor cell = true :=
  ((execBridgeMintA_iff_spec st actor cell a value st').mp h).1.1

/-- **`bridgeMint_nonneg` — no negative-amount inbound supply.** A committed `bridgeMintA` PROVES
`0 ≤ value` (no inflation by a negative inbound mint). -/
theorem bridgeMint_nonneg (st : RecChainedState) (actor cell : CellId) (a : AssetId) (value : ℤ)
    (st' : RecChainedState) (h : execFullA st (.bridgeMintA actor cell a value) = some st') :
    0 ≤ value :=
  ((execBridgeMintA_iff_spec st actor cell a value st').mp h).1.2.1

/-- **`bridgeMint_credit` — the touched ledger entry is credited by exactly `value`** (the entries of
every OTHER cell/asset preserved — `recBalCredit_inbound_correct`). Derived from the spec's `bal`
clause + the declaratively-validated helper. This is the inbound dual of the outbound lock's debit. -/
theorem bridgeMint_credit (st : RecChainedState) (actor cell : CellId) (a : AssetId) (value : ℤ)
    (st' : RecChainedState) (h : execFullA st (.bridgeMintA actor cell a value) = some st') :
    st'.kernel.bal cell a = st.kernel.bal cell a + value
    ∧ (∀ c b, ¬ (c = cell ∧ b = a) → st'.kernel.bal c b = st.kernel.bal c b) := by
  have hspec := (execBridgeMintA_iff_spec st actor cell a value st').mp h
  have hbal : st'.kernel.bal = recBalCredit st.kernel.bal cell a value := hspec.2.1
  obtain ⟨hcred, hframe⟩ := recBalCredit_inbound_correct st.kernel.bal cell a value
  refine ⟨?_, ?_⟩
  · rw [hbal]; exact hcred
  · intro c b hne; rw [hbal]; exact hframe c b hne

/-- **`bridgeMint_supply_delta` — CONSERVATION CONTENT: a committed inbound mint raises asset `a`'s
supply by exactly `value`, and leaves every OTHER asset's supply unchanged** (`recKMintAsset_delta`
lifted to the `execFullA` level via the chained commitment). This is the semantic punchline of
bridge-inbound-mint: supply is created in a single asset, by exactly the disclosed amount, when the
destination cell is live — the inbound dual of the outbound lock's per-asset debit. -/
theorem bridgeMint_supply_delta (st : RecChainedState) (actor cell : CellId) (a : AssetId) (value : ℤ)
    (st' : RecChainedState) (h : execFullA st (.bridgeMintA actor cell a value) = some st')
    (b : AssetId) :
    recTotalAsset st'.kernel b = recTotalAsset st.kernel b + (if b = a then value else 0) := by
  -- recover the chained-executor commitment, then reuse the kernel delta on the kernel post-state.
  rw [execFullA_bridgeMintA] at h
  unfold recCMintAsset at h
  cases hm : recKMintAsset st.kernel actor cell a value with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some k' =>
      rw [hm] at h; simp only [Option.some.injEq] at h
      have hk : st'.kernel = k' := by rw [← h]
      rw [hk]; exact recKMintAsset_delta st.kernel k' actor cell a value hm b

/-! ## §6 — NON-VACUITY: the spec is a genuine GATE (rejects bad inputs).

A spec that accepts everything is worthless. `execFullA` REJECTS an unauthorized inbound mint, a
negative-amount mint, and a mint to a dead (non-account) destination cell — each makes the guard
FALSE, hence the executor returns `none` and `InboundMintSpec` is unsatisfiable. -/

/-- **`bridgeMint_rejects_unauthorized`.** A `bridgeMintA` over a state where the actor lacks the
privileged mint cap (`mintAuthorizedB = false`) is REJECTED — `execFullA … = none`. Unprivileged
inbound supply is impossible (a forged other-chain confirmation cannot coin value). -/
theorem bridgeMint_rejects_unauthorized (st : RecChainedState) (actor cell : CellId) (a : AssetId)
    (value : ℤ) (hbad : mintAuthorizedB st.kernel.caps actor cell = false) :
    execFullA st (.bridgeMintA actor cell a value) = none := by
  rw [execFullA_bridgeMintA]; unfold recCMintAsset recKMintAsset
  rw [if_neg (by rintro ⟨h, _⟩; rw [hbad] at h; exact absurd h (by simp))]

/-- **`bridgeMint_rejects_negative`.** A `bridgeMintA` with a negative amount (`value < 0`) is
REJECTED. No negative-amount inflation through the inbound bridge. -/
theorem bridgeMint_rejects_negative (st : RecChainedState) (actor cell : CellId) (a : AssetId)
    (value : ℤ) (hbad : value < 0) :
    execFullA st (.bridgeMintA actor cell a value) = none := by
  rw [execFullA_bridgeMintA]; unfold recCMintAsset recKMintAsset
  rw [if_neg (by rintro ⟨_, h, _⟩; exact absurd h (by omega))]

/-- **`bridgeMint_rejects_dead_cell`.** A `bridgeMintA` to a destination that is NOT a live account
(`cell ∉ accounts`) is REJECTED. Inbound supply can only be minted onto a live cell. -/
theorem bridgeMint_rejects_dead_cell (st : RecChainedState) (actor cell : CellId) (a : AssetId)
    (value : ℤ) (hbad : cell ∉ st.kernel.accounts) :
    execFullA st (.bridgeMintA actor cell a value) = none := by
  rw [execFullA_bridgeMintA]; unfold recCMintAsset recKMintAsset
  rw [if_neg (by rintro ⟨_, _, h⟩; exact absurd h hbad)]

/-- **`bridgeMint_admits_iff` — the executor commits IFF the guard holds.** The clean
characterization: there is a committed post-state EXACTLY when the inbound mint is admissible. -/
theorem bridgeMint_admits_iff (st : RecChainedState) (actor cell : CellId) (a : AssetId) (value : ℤ) :
    (∃ st', execFullA st (.bridgeMintA actor cell a value) = some st')
      ↔ inboundMintAdmit st.kernel actor cell value := by
  rw [execFullA_bridgeMintA]
  unfold recCMintAsset recKMintAsset inboundMintAdmit
  by_cases hg : mintAuthorizedB st.kernel.caps actor cell = true ∧ 0 ≤ value ∧ cell ∈ st.kernel.accounts
  · rw [if_pos hg]; exact ⟨fun _ => hg, fun _ => ⟨_, rfl⟩⟩
  · rw [if_neg hg]
    constructor
    · rintro ⟨st', h⟩; exact absurd h (by simp)
    · intro hg'; exact absurd hg' hg

/-! ## §7 — concrete #guard non-vacuity witnesses (genuine `decide`, NOT `native_decide`).

Cell 0 is a live account; actor 9 holds a `node 0` mint cap (privileged supply over cell 0); actor 0
holds NO mint cap (bare ownership is insufficient). An inbound mint of +40 of asset 1 by the
privileged actor commits; the unprivileged / negative / dead-cell inbound mints are decidably
rejected. -/

/-- A concrete pre-state: cell {0} live, ledger empty, actor 9 holds the `node 0` mint cap. -/
def stB0 : RecChainedState :=
  { kernel :=
      { accounts := {0}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun a => if a = 9 then [Dregg2.Authority.Cap.node 0] else [] }
    log := [] }

-- The privileged inbound mint of +40 of asset 1 by actor 9 onto the live cell 0 COMMITS:
#guard (execFullA stB0 (.bridgeMintA 9 0 1 40)).isSome  --  true
-- An UNPRIVILEGED inbound mint (actor 0, bare ownership, no `node 0` cap) is REJECTED:
#guard decide ((execFullA stB0 (.bridgeMintA 0 0 1 40)).isNone)  --  true
-- A NEGATIVE-amount inbound mint is REJECTED:
#guard decide ((execFullA stB0 (.bridgeMintA 9 0 1 (-5))).isNone)  --  true
-- An inbound mint to a DEAD destination (cell 7 ∉ accounts) is REJECTED:
#guard decide ((execFullA stB0 (.bridgeMintA 9 7 1 40)).isNone)  --  true
-- mintAuthorizedB witnesses: actor 9 authorized over cell 0, actor 0 not:
#guard mintAuthorizedB stB0.kernel.caps 9 0 == true
#guard mintAuthorizedB stB0.kernel.caps 0 0 == false

/-! ## §8 — Axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms recBalCredit_inbound_correct
#assert_axioms execFullA_bridgeMintA
#assert_axioms recCMintAsset_iff_inboundSpec
#assert_axioms execBridgeMintA_iff_spec
#assert_axioms bridgeMint_authorized
#assert_axioms bridgeMint_nonneg
#assert_axioms bridgeMint_credit
#assert_axioms bridgeMint_supply_delta
#assert_axioms bridgeMint_rejects_unauthorized
#assert_axioms bridgeMint_rejects_negative
#assert_axioms bridgeMint_rejects_dead_cell
#assert_axioms bridgeMint_admits_iff

end Dregg2.Circuit.Spec.BridgeInboundMint
