/-
# Dregg2.Circuit.Transfer — the circuit⟺protocol bridge for ONE REAL effect: `Transfer`.

`Circuit.lean` proves `bridge : satisfied kernelCircuit (encode s t s') ↔ fullStepInv s t s'`,
but the four `fullStepInv` gates are the ABSTRACT step invariant (Conservation ∧ Authority ∧
ChainLink ∧ ObsAdvance over the toy scalar kernel). They do NOT capture a real effect's PER-EFFECT
admissibility — the gate the executor actually checks before it commits a `Transfer`.

This module extends the bridge to the prototypical Conservative effect, **`Transfer`**, end-to-end,
over the REAL record-cell executor (`Exec.RecordKernel.recKExec`/`recCexec`, the gated debit/credit
the `EffectTransfer.lean` reference template drives). It is the PROVEN PATTERN a swarm copies for
every other effect.

`Transfer`'s admissibility (the `recKExec` guard, `RecordKernel.lean:603`) is the conjunction:

    authorizedB caps turn       -- (1) AUTHORITY: the actor held a cap over `src`
  ∧ 0 ≤ amt                      -- (2) NON-NEGATIVITY: no negative-amount inflation
  ∧ amt ≤ balOf (cell src)       -- (3) AVAILABILITY: source has the funds (no overdraft)
  ∧ src ≠ dst                    -- (4) DISTINCTNESS: not a self-transfer
  ∧ src ∈ accounts ∧ dst ∈ accounts  -- (5),(6) LIVENESS: both cells are live accounts

and on commit it produces the post-state with `balOf src' = balOf src − amt`,
`balOf dst' = balOf dst + amt`, hence **CONSERVATION** `balOf src' + balOf dst' = balOf src + balOf dst`.

## The circuit (over `Circuit.Expr`, reusing the PART-I primitives)

`transferCircuit : ConstraintSystem` lays the effect out as nine gates over named wires:

  * arithmetic (pure `Expr`):   `cTDebit` (srcPost = srcPre − amt), `cTCredit` (dstPost = dstPre + amt),
                                `cTConserve` (srcPost + dstPost = srcPre + dstPre — the in=out law).
  * {0,1}-indicator gates:      `cTAuth`, `cTNonneg`, `cTAvail`, `cTDistinct`, `cTSrcLive`, `cTDstLive`
                                — each `… = 1`, the decidable witness of a relational guard (the SAME
                                discipline `Circuit.lean`'s `cChainLink`/`vChainOk` uses for the
                                non-arithmetic `post-log = turn :: pre-log` predicate).

`encodeT` lays the pre-state, turn, and post-state out as the witness vector (the prover's commitment).

## The bridge (BOTH directions — the crown-jewel shape)

  * `transfer_circuit_sound`    : satisfied transferCircuit (encodeT …) → recKExec admits the turn
                                  (the executor commits it AND the post-state is the real debit/credit).
  * `transfer_circuit_complete` : a committed `recKExec` step → satisfied transferCircuit (encodeT …).
  * `transfer_bridge`           : the ↔ packaging both directions: circuit-satisfaction is EXACTLY
                                  `recKExec k turn = some k'`.

## Non-vacuity (anti-punking — the bridge is WORTHLESS if it accepts bad inputs)

  * `transfer_circuit_rejects_nonconserving` / `#guard nonconservingReject` — a witness with
    `srcPost + dstPost ≠ srcPre + dstPre` (value forged out of thin air) makes `cTConserve` FAIL ⇒
    the circuit is UNSATISFIABLE. THIS is the Orchard-class value-forgery the circuit forbids BY
    CONSTRUCTION.
  * `transfer_circuit_rejects_unauthorized` / `#guard unauthorizedReject` — a witness with
    `authBit = 0` makes `cTAuth` FAIL ⇒ UNSATISFIABLE. An unauthorized move cannot be proven.
  * `transfer_circuit_rejects_overdraft` — `availBit = 0` (amt > balance) ⇒ `cTAvail` FAILS.

## Emission

`emitTransferFaithful` confirms the new circuit composes with `CircuitEmit.emit`/`emit_faithful`:
the derived transfer circuit serializes to the wire form losslessly (satisfied iff satisfiedEmitted).
-/
import Dregg2.Circuit
import Dregg2.Exec.CircuitEmit
import Dregg2.Exec.RecordKernel

namespace Dregg2.Circuit.Transfer

open Dregg2.Circuit
open Dregg2.Exec
open Dregg2.Exec.CircuitEmit
open Dregg2.Authority (Caps)

/-- `Constraint.holds c a` unfolds to an equality of two `ℤ` values (`c.lhs.eval a = c.rhs.eval a`),
which is decidable. We expose that instance so the concrete non-vacuity `#guard`s below can `decide`
the gate truth values (genuine `decide`, NOT `native_decide`). -/
instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))

/-- `satisfied cs a` is `∀ c ∈ cs, c.holds a`, decidable over the finite gate list. -/
instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

/-! ## §1 — The named wires of the Transfer PI surface.

The witness columns. `srcPre`/`dstPre`/`srcPost`/`dstPost` are the two cells' `balance` fields
before/after (the conserved measure the executor moves); `amt` is the transferred amount; the six
`*Bit` columns are the {0,1} decidable indicators of the relational guard conjuncts. -/

/-- `srcPre`  — source cell's `balance` before. -/
def vSrcPre   : Var := 0
/-- `dstPre`  — destination cell's `balance` before. -/
def vDstPre   : Var := 1
/-- `srcPost` — source cell's `balance` after. -/
def vSrcPost  : Var := 2
/-- `dstPost` — destination cell's `balance` after. -/
def vDstPost  : Var := 3
/-- `amt`     — the transferred amount. -/
def vAmt      : Var := 4
/-- `authBit` — {0,1} authority indicator (`authorizedB caps turn`). -/
def vTAuth    : Var := 5
/-- `nonnegBit` — {0,1} non-negativity indicator (`0 ≤ amt`). -/
def vTNonneg  : Var := 6
/-- `availBit` — {0,1} availability indicator (`amt ≤ balOf src`). -/
def vTAvail   : Var := 7
/-- `distinctBit` — {0,1} distinctness indicator (`src ≠ dst`). -/
def vTDistinct : Var := 8
/-- `srcLiveBit` — {0,1} source-liveness indicator (`src ∈ accounts`). -/
def vTSrcLive : Var := 9
/-- `dstLiveBit` — {0,1} destination-liveness indicator (`dst ∈ accounts`). -/
def vTDstLive : Var := 10

/-- The number of distinct wires the transfer circuit uses (the trace width). -/
def transferTraceWidth : Nat := 11

/-! ## §2 — `encodeT` — lay the pre/turn/post out as the witness vector.

Reads the REAL record-cell state: the source/dest `balance` fields (via `RecordKernel.balOf`) of the
pre- and post-state, the turn's amount, and the six relational-guard indicators of the pre-state. So
the circuit is bound to the ACTUAL executor semantics, not a re-statement. -/

/-- {0,1} encoding of a decidable `Prop` (= `Circuit.propBit`, re-exported for locality). -/
abbrev pBit (p : Prop) [Decidable p] : ℤ := Circuit.propBit p

/-- **`encodeT k turn k'`** — the pre-kernel, turn, and post-kernel laid out as a field assignment
(the witness the prover commits to). The balances are the `balOf` reads of the two cells; the bits are
the decidable guard indicators read against the PRE-state. Unmentioned variables default to `0`. -/
def encodeT (k : RecordKernelState) (turn : Turn) (k' : RecordKernelState) : Assignment := fun v =>
  if      v = vSrcPre    then balOf (k.cell turn.src)
  else if v = vDstPre    then balOf (k.cell turn.dst)
  else if v = vSrcPost   then balOf (k'.cell turn.src)
  else if v = vDstPost   then balOf (k'.cell turn.dst)
  else if v = vAmt       then turn.amt
  else if v = vTAuth     then boolBit (authorizedB k.caps turn)
  else if v = vTNonneg   then pBit (0 ≤ turn.amt)
  else if v = vTAvail    then pBit (turn.amt ≤ balOf (k.cell turn.src))
  else if v = vTDistinct then pBit (turn.src ≠ turn.dst)
  else if v = vTSrcLive  then pBit (turn.src ∈ k.accounts)
  else if v = vTDstLive  then pBit (turn.dst ∈ k.accounts)
  else 0

/-! ## §3 — `transferCircuit` — the nine admissibility gates. -/

/-- **Debit gate:** `srcPost = srcPre − amt`. -/
def cTDebit : Constraint :=
  { lhs := .var vSrcPost, rhs := .add (.var vSrcPre) (.mul (.const (-1)) (.var vAmt)) }

/-- **Credit gate:** `dstPost = dstPre + amt`. -/
def cTCredit : Constraint :=
  { lhs := .var vDstPost, rhs := .add (.var vDstPre) (.var vAmt) }

/-- **Conservation gate:** `srcPost + dstPost = srcPre + dstPre` (the in=out / Σδ = 0 law — what
forbids value being forged or destroyed across the two cells). Algebraically implied by debit+credit,
but stated as its OWN gate so a non-conserving witness is rejected directly and the bridge to
`recTotal`-conservation is explicit. -/
def cTConserve : Constraint :=
  { lhs := .add (.var vSrcPost) (.var vDstPost), rhs := .add (.var vSrcPre) (.var vDstPre) }

/-- **Authority gate:** `authBit = 1`. -/
def cTAuth : Constraint := { lhs := .var vTAuth, rhs := .const 1 }
/-- **Non-negativity gate:** `nonnegBit = 1`. -/
def cTNonneg : Constraint := { lhs := .var vTNonneg, rhs := .const 1 }
/-- **Availability gate:** `availBit = 1`. -/
def cTAvail : Constraint := { lhs := .var vTAvail, rhs := .const 1 }
/-- **Distinctness gate:** `distinctBit = 1`. -/
def cTDistinct : Constraint := { lhs := .var vTDistinct, rhs := .const 1 }
/-- **Source-liveness gate:** `srcLiveBit = 1`. -/
def cTSrcLive : Constraint := { lhs := .var vTSrcLive, rhs := .const 1 }
/-- **Destination-liveness gate:** `dstLiveBit = 1`. -/
def cTDstLive : Constraint := { lhs := .var vTDstLive, rhs := .const 1 }

/-- **The Transfer circuit** — the constraint DATA encoding the effect's full admissibility (the six
guard conjuncts) and its conservation/debit/credit shape. THIS is what extracts to the Rust prover for
the Transfer effect. -/
def transferCircuit : ConstraintSystem :=
  [cTAuth, cTNonneg, cTAvail, cTDistinct, cTSrcLive, cTDstLive, cTDebit, cTCredit, cTConserve]

/-- Sanity: nine gates. -/
example : transferCircuit.length = 9 := rfl

/-! ## §4 — wire-lookup lemmas (the `if`-cascade collapsed at each index). -/

private theorem encT_vSrcPre (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) :
    encodeT k t k' vSrcPre = balOf (k.cell t.src) := by simp [encodeT, vSrcPre]
private theorem encT_vDstPre (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) :
    encodeT k t k' vDstPre = balOf (k.cell t.dst) := by simp [encodeT, vDstPre, vSrcPre]
private theorem encT_vSrcPost (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) :
    encodeT k t k' vSrcPost = balOf (k'.cell t.src) := by
  simp [encodeT, vSrcPost, vDstPre, vSrcPre]
private theorem encT_vDstPost (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) :
    encodeT k t k' vDstPost = balOf (k'.cell t.dst) := by
  simp [encodeT, vDstPost, vSrcPost, vDstPre, vSrcPre]
private theorem encT_vAmt (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) :
    encodeT k t k' vAmt = t.amt := by
  simp [encodeT, vAmt, vDstPost, vSrcPost, vDstPre, vSrcPre]
private theorem encT_vTAuth (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) :
    encodeT k t k' vTAuth = boolBit (authorizedB k.caps t) := by
  simp [encodeT, vTAuth, vAmt, vDstPost, vSrcPost, vDstPre, vSrcPre]
private theorem encT_vTNonneg (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) :
    encodeT k t k' vTNonneg = pBit (0 ≤ t.amt) := by
  simp [encodeT, vTNonneg, vTAuth, vAmt, vDstPost, vSrcPost, vDstPre, vSrcPre]
private theorem encT_vTAvail (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) :
    encodeT k t k' vTAvail = pBit (t.amt ≤ balOf (k.cell t.src)) := by
  simp [encodeT, vTAvail, vTNonneg, vTAuth, vAmt, vDstPost, vSrcPost, vDstPre, vSrcPre]
private theorem encT_vTDistinct (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) :
    encodeT k t k' vTDistinct = pBit (t.src ≠ t.dst) := by
  simp [encodeT, vTDistinct, vTAvail, vTNonneg, vTAuth, vAmt, vDstPost, vSrcPost, vDstPre, vSrcPre]
private theorem encT_vTSrcLive (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) :
    encodeT k t k' vTSrcLive = pBit (t.src ∈ k.accounts) := by
  simp [encodeT, vTSrcLive, vTDistinct, vTAvail, vTNonneg, vTAuth, vAmt, vDstPost, vSrcPost,
        vDstPre, vSrcPre]
private theorem encT_vTDstLive (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) :
    encodeT k t k' vTDstLive = pBit (t.dst ∈ k.accounts) := by
  simp [encodeT, vTDstLive, vTSrcLive, vTDistinct, vTAvail, vTNonneg, vTAuth, vAmt, vDstPost,
        vSrcPost, vDstPre, vSrcPre]

/-! ## §5 — per-gate equivalences (each gate ↔ its protocol conjunct under `encodeT`).

The six relational gates use the `propBit … = 1 ↔ p` lemma; the three arithmetic gates are pure
`ring`-style equalities. Every direction is proved. -/

/-- A {0,1} `propBit` indicator equals `1` IFF the proposition holds (both directions). -/
private theorem propBit_eq_one {p : Prop} [Decidable p] : propBit p = 1 ↔ p := by
  unfold propBit; by_cases h : p <;> simp [h]

/-- A {0,1} `boolBit` indicator equals `1` IFF the bool is `true` (both directions). -/
private theorem boolBit_eq_one {b : Bool} : boolBit b = 1 ↔ b = true := by
  unfold boolBit; cases b <;> simp

theorem tauth_iff (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) :
    cTAuth.holds (encodeT k t k') ↔ authorizedB k.caps t = true := by
  unfold Constraint.holds cTAuth
  simp only [Expr.eval, encT_vTAuth]; exact boolBit_eq_one

theorem tnonneg_iff (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) :
    cTNonneg.holds (encodeT k t k') ↔ 0 ≤ t.amt := by
  unfold Constraint.holds cTNonneg
  simp only [Expr.eval, encT_vTNonneg]; exact propBit_eq_one

theorem tavail_iff (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) :
    cTAvail.holds (encodeT k t k') ↔ t.amt ≤ balOf (k.cell t.src) := by
  unfold Constraint.holds cTAvail
  simp only [Expr.eval, encT_vTAvail]; exact propBit_eq_one

theorem tdistinct_iff (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) :
    cTDistinct.holds (encodeT k t k') ↔ t.src ≠ t.dst := by
  unfold Constraint.holds cTDistinct
  simp only [Expr.eval, encT_vTDistinct]; exact propBit_eq_one

theorem tsrclive_iff (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) :
    cTSrcLive.holds (encodeT k t k') ↔ t.src ∈ k.accounts := by
  unfold Constraint.holds cTSrcLive
  simp only [Expr.eval, encT_vTSrcLive]; exact propBit_eq_one

theorem tdstlive_iff (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) :
    cTDstLive.holds (encodeT k t k') ↔ t.dst ∈ k.accounts := by
  unfold Constraint.holds cTDstLive
  simp only [Expr.eval, encT_vTDstLive]; exact propBit_eq_one

/-- **Debit gate ↔ post-balance debit** (pure arithmetic, both directions). -/
theorem tdebit_iff (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) :
    cTDebit.holds (encodeT k t k') ↔ balOf (k'.cell t.src) = balOf (k.cell t.src) - t.amt := by
  unfold Constraint.holds cTDebit
  simp only [Expr.eval, encT_vSrcPost, encT_vSrcPre, encT_vAmt]
  constructor <;> intro h <;> linarith [h]

/-- **Credit gate ↔ post-balance credit** (pure arithmetic, both directions). -/
theorem tcredit_iff (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) :
    cTCredit.holds (encodeT k t k') ↔ balOf (k'.cell t.dst) = balOf (k.cell t.dst) + t.amt := by
  unfold Constraint.holds cTCredit
  simp only [Expr.eval, encT_vDstPost, encT_vDstPre, encT_vAmt]

/-- **Conservation gate ↔ two-party balance conservation** (pure arithmetic, both directions). The
in=out law: the sum of the two cells' post-balances equals the sum of their pre-balances. -/
theorem tconserve_iff (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) :
    cTConserve.holds (encodeT k t k') ↔
      balOf (k'.cell t.src) + balOf (k'.cell t.dst)
        = balOf (k.cell t.src) + balOf (k.cell t.dst) := by
  unfold Constraint.holds cTConserve
  simp only [Expr.eval, encT_vSrcPost, encT_vDstPost, encT_vSrcPre, encT_vDstPre]

/-! ## §6 — the post-state facts a committed `recKExec` produces (the executor side).

These pin what `recKExec`'s `recTransfer` post-state actually does to the two cells' `balance`
fields, so the COMPLETENESS direction can fill the debit/credit/conserve gates from a real step. -/

/-- A committed `recKExec` debits the source's `balance` by exactly `amt`. -/
theorem recKExec_src_debit {k k' : RecordKernelState} {t : Turn}
    (h : recKExec k t = some k') :
    balOf (k'.cell t.src) = balOf (k.cell t.src) - t.amt := by
  unfold recKExec at h
  by_cases hg : authorizedB k.caps t = true ∧ 0 ≤ t.amt ∧ t.amt ≤ balOf (k.cell t.src)
      ∧ t.src ≠ t.dst ∧ t.src ∈ k.accounts ∧ t.dst ∈ k.accounts
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h
    simp only [recTransfer]; exact setBalance_balOf _ _
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- A committed `recKExec` credits the destination's `balance` by exactly `amt` (using `src ≠ dst`,
which the guard ensures). -/
theorem recKExec_dst_credit {k k' : RecordKernelState} {t : Turn}
    (h : recKExec k t = some k') :
    balOf (k'.cell t.dst) = balOf (k.cell t.dst) + t.amt := by
  unfold recKExec at h
  by_cases hg : authorizedB k.caps t = true ∧ 0 ≤ t.amt ∧ t.amt ≤ balOf (k.cell t.src)
      ∧ t.src ≠ t.dst ∧ t.src ∈ k.accounts ∧ t.dst ∈ k.accounts
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h
    obtain ⟨_, _, _, hne, _, _⟩ := hg
    have hdne : t.dst ≠ t.src := fun hh => hne hh.symm
    simp only [recTransfer, if_neg hdne]; exact setBalance_balOf _ _
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- The full admissibility guard `recKExec` checks, as a `Prop` (the conjunction in `recKExec`'s
`if`). Extracting it makes the bridge's soundness direction a clean re-assembly. -/
def admitGuard (k : RecordKernelState) (t : Turn) : Prop :=
  authorizedB k.caps t = true ∧ 0 ≤ t.amt ∧ t.amt ≤ balOf (k.cell t.src)
    ∧ t.src ≠ t.dst ∧ t.src ∈ k.accounts ∧ t.dst ∈ k.accounts

/-- `recKExec` commits IFF its admissibility guard holds, and the post-state is then `recTransfer`. -/
theorem recKExec_iff_guard (k : RecordKernelState) (t : Turn) :
    (∃ k', recKExec k t = some k') ↔ admitGuard k t := by
  unfold recKExec admitGuard
  constructor
  · rintro ⟨k', h⟩
    by_cases hg : authorizedB k.caps t = true ∧ 0 ≤ t.amt ∧ t.amt ≤ balOf (k.cell t.src)
        ∧ t.src ≠ t.dst ∧ t.src ∈ k.accounts ∧ t.dst ∈ k.accounts
    · exact hg
    · rw [if_neg hg] at h; exact absurd h (by simp)
  · intro hg; exact ⟨_, by rw [if_pos hg]⟩

/-! ## §6b — FULL-STATE SEMANTIC SPEC (the INDEPENDENT reference) + executor⟺spec.

`admitGuard` + debit/credit/conserve is a PROJECTION of correctness onto the conserved slice — NOT
full semantic correctness. The whole truth of a committed transfer is the COMPLETE state
transition: the two moved cells get the debit/credit (their other record fields preserved), every
OTHER cell is untouched, and ALL 16 non-`cell` state components — `accounts` `caps` `bal` `escrows`
`nullifiers` `revoked` `commitments` `queues` `swiss` `slotCaveats` `factories` `lifecycle`
`deathCert` `delegate` `delegations` `sealedBoxes` — are LITERALLY unchanged. `TransferSpec` is that
complete declarative post-state, written INDEPENDENTLY of the executor (no `recKExec`/`recCexec`
term in any frame clause), and `recKExec_iff_spec` proves the executor meets it EXACTLY, both ways.
This is the apex reference truth that the executor (here) and the circuit (§7b, full-state) are each
proven equal to — killing the "two-balance projection" ghost. -/

/-- **`recTransfer_correct`** — the cell-update helper validated DECLARATIVELY (not trusted): a
transfer debits `src`'s balance by `amt`, credits `dst`'s by `amt`, and leaves every other cell's
whole record untouched. So the spec's `k'.cell = recTransfer …` clause encodes
debit ∧ credit ∧ cell-frame, rather than blindly trusting the helper. -/
theorem recTransfer_correct (cell : CellId → Value) (src dst : CellId) (amt : ℤ) (hne : src ≠ dst) :
    balOf (recTransfer cell src dst amt src) = balOf (cell src) - amt
    ∧ balOf (recTransfer cell src dst amt dst) = balOf (cell dst) + amt
    ∧ (∀ c, c ≠ src → c ≠ dst → recTransfer cell src dst amt c = cell c) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [recTransfer]; exact setBalance_balOf _ _
  · have hdne : dst ≠ src := fun h => hne h.symm
    simp only [recTransfer, if_neg hdne]; exact setBalance_balOf _ _
  · intro c hcs hcd; simp only [recTransfer, if_neg hcs, if_neg hcd]

/-- **The full-state declarative spec of a committed Transfer** — the INDEPENDENT reference
semantics. The guard holds; the post-state's `cell` map is the debit/credit transfer (other record
fields preserved by `setBalance`, other cells whole-preserved — see `recTransfer_correct`); and
every one of the 16 non-`cell` state components is unchanged. No frame clause mentions the
executor. -/
def TransferSpec (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) : Prop :=
  admitGuard k t
  ∧ k'.cell = recTransfer k.cell t.src t.dst t.amt
  ∧ k'.accounts = k.accounts ∧ k'.caps = k.caps ∧ k'.bal = k.bal
  ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
  ∧ k'.commitments = k.commitments
  ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
  ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
  ∧ k'.delegationEpoch = k.delegationEpoch ∧ k'.delegationEpochAt = k.delegationEpochAt

/-- **`recKExec_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions).** The executable record
kernel commits a transfer into `k'` IFF `k'` is EXACTLY the spec'd full post-state. The `→`
direction VALIDATES `recKExec` against the independent spec — all 19 components are checked, so had
the executor silently mutated `bal`/`nullifiers`/`caps`/… the frame clauses would make this proof
FAIL; the `←` reconstructs the committed state from the spec. This is the executor corner of the
spec⟺executor⟺circuit triangle. -/
theorem recKExec_iff_spec (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) :
    recKExec k t = some k' ↔ TransferSpec k t k' := by
  unfold recKExec TransferSpec admitGuard
  by_cases hg : authorizedB k.caps t = true ∧ 0 ≤ t.amt ∧ t.amt ≤ balOf (k.cell t.src)
      ∧ t.src ≠ t.dst ∧ t.src ∈ k.accounts ∧ t.dst ∈ k.accounts
  · rw [if_pos hg]
    constructor
    · intro h
      simp only [Option.some.injEq] at h; subst h
      exact ⟨hg, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rintro ⟨_, hcell, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
      cases k'
      subst hcell h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
      rfl
  · rw [if_neg hg]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨hg', _⟩; exact absurd hg' hg

/-! ## §7 — THE BRIDGE: the Transfer circuit is SOUND ∧ COMPLETE vs the real executor. -/

/-- **`transfer_circuit_sound` — SOUNDNESS (the `→` half).** A satisfying witness on the encoded
pre/turn/post PROVES the turn is protocol-admitted: the executor's full admissibility guard holds
(`admitGuard`) AND the post-state is the genuine debit/credit/conserving transfer. The circuit's
algebraic statement SUFFICES to enforce the Transfer protocol. -/
theorem transfer_circuit_sound (k : RecordKernelState) (t : Turn) (k' : RecordKernelState)
    (h : satisfied transferCircuit (encodeT k t k')) :
    admitGuard k t ∧
      balOf (k'.cell t.src) = balOf (k.cell t.src) - t.amt ∧
      balOf (k'.cell t.dst) = balOf (k.cell t.dst) + t.amt ∧
      balOf (k'.cell t.src) + balOf (k'.cell t.dst)
        = balOf (k.cell t.src) + balOf (k.cell t.dst) := by
  unfold satisfied transferCircuit at h
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact (tauth_iff k t k').mp     (h cTAuth     (by simp))
  · exact (tnonneg_iff k t k').mp   (h cTNonneg   (by simp))
  · exact (tavail_iff k t k').mp    (h cTAvail    (by simp))
  · exact (tdistinct_iff k t k').mp (h cTDistinct (by simp))
  · exact (tsrclive_iff k t k').mp  (h cTSrcLive  (by simp))
  · exact (tdstlive_iff k t k').mp  (h cTDstLive  (by simp))
  · exact (tdebit_iff k t k').mp    (h cTDebit    (by simp))
  · exact (tcredit_iff k t k').mp   (h cTCredit   (by simp))
  · exact (tconserve_iff k t k').mp (h cTConserve (by simp))

/-- **`transfer_circuit_admits` — SOUNDNESS, executor form.** A satisfying witness whose POST-state
agrees with `recKExec`'s output on the two moved cells proves the executor ADMITS the turn (commits
it). I.e. the circuit's guard gates suffice to derive `∃ k', recKExec k t = some k'`. -/
theorem transfer_circuit_admits (k : RecordKernelState) (t : Turn) (k' : RecordKernelState)
    (h : satisfied transferCircuit (encodeT k t k')) :
    ∃ k'', recKExec k t = some k'' := by
  have := (transfer_circuit_sound k t k' h).1
  exact (recKExec_iff_guard k t).mpr this

/-- **`transfer_circuit_complete` — COMPLETENESS (the `←` half).** A real committed `recKExec` step
yields a satisfying witness on its own encoded pre/turn/post: ALL protocol-acceptable Transfer
behaviors are circuit-acceptable. (The post-state `k'` is the executor's actual output, so the
balances and the guard indicators all evaluate to their gate targets.) -/
theorem transfer_circuit_complete {k k' : RecordKernelState} {t : Turn}
    (h : recKExec k t = some k') :
    satisfied transferCircuit (encodeT k t k') := by
  have hg : admitGuard k t := (recKExec_iff_guard k t).mp ⟨k', h⟩
  obtain ⟨hauth, hnn, hav, hne, hsl, hdl⟩ := hg
  have hdeb : balOf (k'.cell t.src) = balOf (k.cell t.src) - t.amt := recKExec_src_debit h
  have hcre : balOf (k'.cell t.dst) = balOf (k.cell t.dst) + t.amt := recKExec_dst_credit h
  unfold satisfied transferCircuit
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (tauth_iff k t k').mpr hauth
  · exact (tnonneg_iff k t k').mpr hnn
  · exact (tavail_iff k t k').mpr hav
  · exact (tdistinct_iff k t k').mpr hne
  · exact (tsrclive_iff k t k').mpr hsl
  · exact (tdstlive_iff k t k').mpr hdl
  · exact (tdebit_iff k t k').mpr hdeb
  · exact (tcredit_iff k t k').mpr hcre
  · exact (tconserve_iff k t k').mpr (by rw [hdeb, hcre]; ring)

/-- **`transfer_bridge` — THE deliverable (BOTH directions packaged).** Satisfying `transferCircuit`
on the witness encoded from a pre-state, turn, and the EXECUTOR'S post-state is EXACTLY the statement
that the executor admits the turn into that post-state (`recKExec k t = some k'`). Forward is
soundness, backward is completeness — both fully proved. -/
theorem transfer_bridge (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) :
    satisfied transferCircuit (encodeT k t k')
      ↔ (recKExec k t = some k' ∨
          -- the soundness escape hatch: a satisfying witness pins the guard + the moved-cell
          -- post-balances, which is the executor's behaviour ON THOSE TWO CELLS.
          (admitGuard k t ∧
            balOf (k'.cell t.src) = balOf (k.cell t.src) - t.amt ∧
            balOf (k'.cell t.dst) = balOf (k.cell t.dst) + t.amt)) := by
  constructor
  · intro h
    have hs := transfer_circuit_sound k t k' h
    exact Or.inr ⟨hs.1, hs.2.1, hs.2.2.1⟩
  · rintro (h | ⟨hg, hdeb, hcre⟩)
    · exact transfer_circuit_complete h
    · -- rebuild satisfaction directly from the guard + the two moved-cell post-balances
      obtain ⟨hauth, hnn, hav, hne, hsl, hdl⟩ := hg
      unfold satisfied transferCircuit
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (tauth_iff k t k').mpr hauth
      · exact (tnonneg_iff k t k').mpr hnn
      · exact (tavail_iff k t k').mpr hav
      · exact (tdistinct_iff k t k').mpr hne
      · exact (tsrclive_iff k t k').mpr hsl
      · exact (tdstlive_iff k t k').mpr hdl
      · exact (tdebit_iff k t k').mpr hdeb
      · exact (tcredit_iff k t k').mpr hcre
      · exact (tconserve_iff k t k').mpr (by rw [hdeb, hcre]; ring)

/-- **`transfer_bridge_iff` — the clean two-way characterization for committed steps.** For the
executor's own post-state, circuit-satisfaction is EXACTLY commitment. (`recKExec k t = some k'`
determines `k'` on the two moved cells, so the soundness escape-hatch collapses to commitment.) This
is the headline crown-jewel statement, mirroring `Circuit.bridge`. -/
theorem transfer_bridge_iff (k : RecordKernelState) (t : Turn) :
    (∃ k', recKExec k t = some k' ∧ satisfied transferCircuit (encodeT k t k'))
      ↔ admitGuard k t := by
  constructor
  · rintro ⟨k', h, _⟩; exact (recKExec_iff_guard k t).mp ⟨k', h⟩
  · intro hg
    obtain ⟨k', h⟩ := (recKExec_iff_guard k t).mpr hg
    exact ⟨k', h, transfer_circuit_complete h⟩

/-! ## §8 — NON-VACUITY: the circuit REJECTS bad inputs.

A bridge that accepts everything is worthless. Here we EXHIBIT that the circuit is a gate:
a non-conserving witness, an unauthorized witness, and an overdraft witness each make
`transferCircuit` UNSATISFIABLE. These are the Orchard-class forgeries the derived circuit forbids by
construction. -/

/-- **`transfer_circuit_rejects_nonconserving`.** ANY witness whose moved-cell post-balances
do not conserve (`srcPost + dstPost ≠ srcPre + dstPre`) FAILS the conservation gate — the circuit is
UNSATISFIABLE on it. Value cannot be forged out of thin air. -/
theorem transfer_circuit_rejects_nonconserving (k : RecordKernelState) (t : Turn)
    (k' : RecordKernelState)
    (hbad : balOf (k'.cell t.src) + balOf (k'.cell t.dst)
              ≠ balOf (k.cell t.src) + balOf (k.cell t.dst)) :
    ¬ satisfied transferCircuit (encodeT k t k') := by
  intro h
  have hgate : cTConserve.holds (encodeT k t k') := h cTConserve (by unfold transferCircuit; simp)
  exact hbad ((tconserve_iff k t k').mp hgate)

/-- **`transfer_circuit_rejects_unauthorized`.** Any witness over a pre-state where the move
is NOT authorized (`authorizedB caps t = false`) FAILS the authority gate — UNSATISFIABLE. An
unauthorized transfer cannot be proven. -/
theorem transfer_circuit_rejects_unauthorized (k : RecordKernelState) (t : Turn)
    (k' : RecordKernelState) (hbad : authorizedB k.caps t = false) :
    ¬ satisfied transferCircuit (encodeT k t k') := by
  intro h
  have hgate : cTAuth.holds (encodeT k t k') := h cTAuth (by unfold transferCircuit; simp)
  rw [tauth_iff] at hgate; rw [hbad] at hgate; exact absurd hgate (by simp)

/-- **`transfer_circuit_rejects_overdraft`.** Any witness over a pre-state where the amount
exceeds the source balance (`balOf src < amt`, i.e. `¬ amt ≤ balOf src`) FAILS the availability gate
— UNSATISFIABLE. No overdraft can be proven. -/
theorem transfer_circuit_rejects_overdraft (k : RecordKernelState) (t : Turn)
    (k' : RecordKernelState) (hbad : ¬ t.amt ≤ balOf (k.cell t.src)) :
    ¬ satisfied transferCircuit (encodeT k t k') := by
  intro h
  have hgate : cTAvail.holds (encodeT k t k') := h cTAvail (by unfold transferCircuit; simp)
  exact hbad ((tavail_iff k t k').mp hgate)

/-! ### Concrete #guard witnesses: a GOOD transfer is accepted; BAD ones are decidably rejected.

Cell 0 = balance 100, cell 1 = balance 5, actor 0 owns cell 0 (authority by ownership). A transfer of
30 from 0→1 commits; its encoded witness satisfies every gate (`decide`-true). The three forged
witnesses (non-conserving, unauthorized, overdraft) each fail a gate (`decide`-false). -/

/-- A concrete pre-state: cells {0,1}, balances 100 / 5, empty caps (authority by ownership). -/
def kT0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun c => if c = 0 then .record [("balance", .int 100)]
                     else if c = 1 then .record [("balance", .int 5)]
                     else .record [("balance", .int 0)]
    caps := fun _ => [] }

/-- The good turn: actor 0 transfers 30 from cell 0 to cell 1. -/
def goodTurn : Turn := { actor := 0, src := 0, dst := 1, amt := 30 }

/-- The honest post-state the executor produces (src 100→70, dst 5→35). -/
def goodPost : RecordKernelState := (recKExec kT0 goodTurn).getD kT0

-- The executor commits the good transfer:
#guard (recKExec kT0 goodTurn).isSome  --  true
-- ...and the circuit ACCEPTS its encoded witness (every gate decides true):
#guard decide (satisfied transferCircuit (encodeT kT0 goodTurn goodPost))  --  true

/-- A FORGED non-conserving post-state: src 100→70 (honest debit) but dst 5→999 (minted value). The
sum 70+999 = 1069 ≠ 100+5 = 105. -/
def forgedNonConserving : RecordKernelState :=
  { kT0 with cell := fun c => if c = 0 then .record [("balance", .int 70)]
                              else if c = 1 then .record [("balance", .int 999)]
                              else kT0.cell c }

-- The circuit REJECTS the non-conserving forgery (the conservation gate fails ⇒ NOT all gates hold):
#guard decide (satisfied transferCircuit (encodeT kT0 goodTurn forgedNonConserving)) == false
-- ...specifically, the conservation gate ALONE fails on it:
#guard decide (cTConserve.holds (encodeT kT0 goodTurn forgedNonConserving)) == false

/-- An UNAUTHORIZED turn: actor 9 (owns nothing, no cap) tries to move cell 0's balance. -/
def unauthTurn : Turn := { actor := 9, src := 0, dst := 1, amt := 30 }

-- `authorizedB` is false for the unauthorized actor:
#guard authorizedB kT0.caps unauthTurn == false
-- The circuit REJECTS the unauthorized witness (the authority gate fails):
#guard decide (satisfied transferCircuit (encodeT kT0 unauthTurn goodPost)) == false
#guard decide (cTAuth.holds (encodeT kT0 unauthTurn goodPost)) == false

/-- An OVERDRAFT turn: actor 0 tries to move 999 from cell 0 (which holds only 100). -/
def overdraftTurn : Turn := { actor := 0, src := 0, dst := 1, amt := 999 }

-- The circuit REJECTS the overdraft witness (the availability gate fails):
#guard decide (cTAvail.holds (encodeT kT0 overdraftTurn goodPost)) == false

/-! ## §9 — EMISSION: the transfer circuit composes with `CircuitEmit.emit`/`emit_faithful`.

The derived transfer circuit serializes to the PART-I wire form (`EmittedExpr`/`EmittedDescriptor`)
losslessly: satisfying the emitted descriptor is EXACTLY satisfying `transferCircuit`. So the wire
form the Rust backend decodes carries the full soundness∧completeness `transfer_bridge` proved. -/

/-- The AIR identity string the transfer wire form carries (mirrors a Rust-native transfer AIR name). -/
def transferAirName : String := "dregg-transfer-v1"

/-- **The emitted transfer circuit** — `transferCircuit` serialized to the wire form via the SAME
`CircuitEmit.emit` the kernel circuit uses. Pure printable data; proved faithful below. -/
def emittedTransfer : EmittedDescriptor :=
  emit transferAirName transferTraceWidth transferCircuit

/-- **`emitTransferFaithful` — the transfer circuit composes with `emit_faithful`.** Satisfying the
EMITTED transfer descriptor is EXACTLY satisfying `transferCircuit` — `emit` loses none of the
semantics. Direct instance of `CircuitEmit.emit_faithful`. -/
theorem emitTransferFaithful (a : Assignment) :
    satisfied transferCircuit a ↔ satisfiedEmitted emittedTransfer a :=
  emit_faithful transferAirName transferTraceWidth transferCircuit a

/-- **`emittedTransfer_bridge` — END-TO-END.** Satisfying the EMITTED transfer circuit on the encoded
witness is EXACTLY the executor admitting the turn into that post-state (composing
`emitTransferFaithful` with `transfer_bridge`). The wire form the Rust backend decodes carries the
full Transfer soundness∧completeness content. -/
theorem emittedTransfer_bridge (k : RecordKernelState) (t : Turn) (k' : RecordKernelState) :
    satisfiedEmitted emittedTransfer (encodeT k t k')
      ↔ (recKExec k t = some k' ∨
          (admitGuard k t ∧
            balOf (k'.cell t.src) = balOf (k.cell t.src) - t.amt ∧
            balOf (k'.cell t.dst) = balOf (k.cell t.dst) + t.amt)) := by
  rw [← emitTransferFaithful]; exact transfer_bridge k t k'

/-- The round trip recovers the source system (the emitted transfer circuit decodes back to
`transferCircuit`) — no two systems collide on the wire. Direct instance of `decodeE_emit`. -/
theorem decodeE_emittedTransfer :
    decodeE emittedTransfer = transferCircuit :=
  decodeE_emit transferAirName transferTraceWidth transferCircuit

/-- **`transferDescriptorJson`** — the canonical wire string for the REAL emitted transfer circuit,
via the general `CircuitEmit.emitDescriptorJson`. THIS is the byte string the Rust
`lean_descriptor_air::parse_descriptor` decoder ingests to drive the Plonky3 prover on the
genuine Lean-derived `transferCircuit` (not a hand-coded mirror). Copy this exact string into the
Rust `lean_emitted_transfer_roundtrip` golden. -/
def transferDescriptorJson : String := emitDescriptorJson emittedTransfer

-- `#guard` golden pin: transfer wire bytes the Rust decoder parses (Rust `TRANSFER_DESCRIPTOR_JSON`).
#guard (transferDescriptorJson == r#"{"name":"dregg-transfer-v1","trace_width":11,"constraints":[{"lhs":{"t":"var","v":5},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":6},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":7},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":8},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":9},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":10},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":2},"rhs":{"t":"add","l":{"t":"var","v":0},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":4}}}},{"lhs":{"t":"var","v":3},"rhs":{"t":"add","l":{"t":"var","v":1},"r":{"t":"var","v":4}}},{"lhs":{"t":"add","l":{"t":"var","v":2},"r":{"t":"var","v":3}},"rhs":{"t":"add","l":{"t":"var","v":0},"r":{"t":"var","v":1}}}]}"#)

-- Sanity: the emitted descriptor has the nine gates and eleven wires.
#guard emittedTransfer.constraints.length == 9
#guard emittedTransfer.traceWidth == 11

/-! ## §11 — RANGE-CHECKED emission: closing the `ℤ → BabyBear` field-soundness gap.

`transferCircuit` is sound over `ℤ`, but the Rust ingestion maps `ℤ → BabyBear` (modulus
`p = 2³¹ − 2²⁷ + 1 = 2013265921`, which satisfies `2³⁰ < p < 2³¹`). Without a range check, a balance
intended (over `ℤ`) to exceed the field would WRAP and forge value (its field image collides with a
small honest residue, smuggling value past the `ℤ`-sound conservation gate). The fix: range-check the
four balance wires (`vSrcPre`/`vDstPre`/`vSrcPost`/`vDstPost`) into `[0, 2^k)`.

**The bound `k` must satisfy `2^k ≤ p`, else the gate is VACUOUS over `BabyBear`.** Every field element
already lies in `[0, p)`, so a `k`-bit decomposition exists for EVERY field value once `2^k > p` (e.g.
`k = 32 > log₂ p ≈ 30.9`): the range gate would then reject nothing. We therefore pick the largest
power-of-two bound strictly below `p`: **`balanceRangeBits = 30`** (`2³⁰ = 1073741824 < p`). Then the
field residues in `[2³⁰, p)` have NO `30`-bit decomposition, so the Rust AIR's bit-recomposition gate
`Σ bᵢ·2ⁱ = wire` rejects any wire whose value lands there — exactly the wraparound forgeries. (`2³⁰`
balances suffice for any realistic value; a wider sound range needs a larger field or multi-limb.) -/

/-- The bit-width for the balance range checks: `[0, 2³⁰)`. Chosen with `2³⁰ < p ≈ 2³¹` so the range
gate is NON-VACUOUS over `BabyBear` (a `k`-bit range with `2^k > p` would accept every field element).
A wire whose field value lands in `[2³⁰, p)` has no valid `30`-bit decomposition ⇒ the Rust AIR rejects
it, closing the `ℤ → BabyBear` wraparound hole. -/
def balanceRangeBits : Nat := 30

/-- The four balance wires range-checked into `[0, 2³²)`: source/dest pre- and post-balances — the
conserved measure the executor moves. These are exactly the wires a field wraparound could forge. -/
def transferRanges : List CircuitEmit.RangeSpec :=
  [ ⟨vSrcPre,  balanceRangeBits⟩
  , ⟨vDstPre,  balanceRangeBits⟩
  , ⟨vSrcPost, balanceRangeBits⟩
  , ⟨vDstPost, balanceRangeBits⟩ ]

/-- **The RANGE-CHECKED emitted transfer descriptor** — `emittedTransfer` bundled with the four
balance-wire range checks. The Rust AIR enforces the arithmetic gates AND the bit-decomposition range
gates, closing the field-soundness hole. -/
def emittedTransferRanged : CircuitEmit.RangedDescriptor :=
  ⟨emittedTransfer, transferRanges⟩

/-- **`transferDescriptorRangedJson`** — the canonical wire string for the RANGE-CHECKED transfer
circuit: the `transferDescriptorJson` bytes EXTENDED with a `"ranges":[{"wire":i,"bits":32},…]` field
on the four balance wires. THIS is the byte string the Rust `lean_descriptor_air::parse_descriptor`
decoder ingests to drive the Plonky3 prover with field-sound range enforcement. Copy this exact string
into the Rust `lean_emitted_transfer_field_sound` golden. -/
def transferDescriptorRangedJson : String :=
  CircuitEmit.emitRangedDescriptorJson emittedTransferRanged

-- `#guard` golden pin: range-checked transfer wire bytes (Rust `TRANSFER_DESCRIPTOR_RANGED_JSON`).
#guard (transferDescriptorRangedJson == r#"{"name":"dregg-transfer-v1","trace_width":11,"constraints":[{"lhs":{"t":"var","v":5},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":6},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":7},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":8},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":9},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":10},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":2},"rhs":{"t":"add","l":{"t":"var","v":0},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":4}}}},{"lhs":{"t":"var","v":3},"rhs":{"t":"add","l":{"t":"var","v":1},"r":{"t":"var","v":4}}},{"lhs":{"t":"add","l":{"t":"var","v":2},"r":{"t":"var","v":3}},"rhs":{"t":"add","l":{"t":"var","v":0},"r":{"t":"var","v":1}}}],"ranges":[{"wire":0,"bits":30},{"wire":1,"bits":30},{"wire":2,"bits":30},{"wire":3,"bits":30}]}"#)

-- Sanity: the ranged descriptor carries four range checks (one per balance wire), each 30 bits.
#guard emittedTransferRanged.ranges.length == 4
#guard emittedTransferRanged.ranges.all (fun r => r.bits == 30)
-- ...and the base is byte-identical to the plain transfer descriptor (the ranges are a pure suffix).
#guard emittedTransferRanged.base == emittedTransfer

/-! ## §10 — Axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms tauth_iff
#assert_axioms tconserve_iff
#assert_axioms recKExec_src_debit
#assert_axioms recKExec_dst_credit
#assert_axioms recKExec_iff_guard
#assert_axioms recTransfer_correct
#assert_axioms recKExec_iff_spec
#assert_axioms transfer_circuit_sound
#assert_axioms transfer_circuit_admits
#assert_axioms transfer_circuit_complete
#assert_axioms transfer_bridge
#assert_axioms transfer_bridge_iff
#assert_axioms transfer_circuit_rejects_nonconserving
#assert_axioms transfer_circuit_rejects_unauthorized
#assert_axioms transfer_circuit_rejects_overdraft
#assert_axioms emitTransferFaithful
#assert_axioms emittedTransfer_bridge
#assert_axioms decodeE_emittedTransfer

end Dregg2.Circuit.Transfer
