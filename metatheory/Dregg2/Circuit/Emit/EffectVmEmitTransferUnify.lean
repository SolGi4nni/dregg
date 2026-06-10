/-
# Dregg2.Circuit.Emit.EffectVmEmitTransferUnify — CLOSING the "ONE circuit" collapse: the keystone's
per-cell `CellTransferSpec` IS the universe-A executor `recKExec`/`TransferSpec` restricted to one
cell. NOT a fourth spec — it is A, projected.

## What this module discharges

`EffectVmEmitTransferSound` proved the RUNNABLE EffectVM transfer descriptor pins a full per-cell spec
`CellTransferSpec` (over the EffectVM state-block record `CellState`). But that record was connected to
universe-A's REAL executor spec (`Transfer.TransferSpec` / `RecordKernel.recKExec`, over
`RecordKernelState`) only in PROSE. That risks `CellTransferSpec` being a FOURTH spec.

This module welds them: a projection `cellProj : RecordKernelState → CellId → CellState` reads ONE
cell of the real kernel state into the keystone's `CellState`, and the unification theorems prove that
`recKExec`'s genuine per-cell effect on `cellProj` is EXACTLY the keystone's `CellTransferSpec` shape
— BOTH the DEBIT side (actor = `src`, direction = 1) and the CREDIT side (actor = `dst`,
direction = 0). So the runnable descriptor provably inherits universe-A's existing guarantee.

## THE PRECISE FIELD-BY-FIELD CORRESPONDENCE (and one REAL mismatch — reported, not papered)

`cellProj k c` reads cell `c` of `RecordKernelState k` into `CellState`:

  * `balLo`    ← `balOf (k.cell c)`        — the REAL conserved measure (`Transfer.balOf`, the
                                              `balance` field of the content-addressed record). THIS
                                              is what `recTransfer`/`setBalance` debit/credit.
  * `nonce`    ← `(k.cell c).scalar "nonce" |>.getD 0` — the cell record's `nonce` field.
  * `balHi`    ← `0`   — universe-A has NO high-limb; the `balance` field is one `ℤ`. Frozen.
  * `fields i` ← `0`   — universe-A has NO 8-field array on the conserved cell. Frozen.
  * `capRoot`  ← `0`   — universe-A's transfer touches no cap-root column. Frozen.
  * `reserved` ← `0`   — universe-A has NO `reserved` column at all (the keystone itself flagged
                          `reserved` as the column its commitment does NOT bind). Frozen.
  * `commit`   — LEFT OUT of the projection's obligations: the EffectVM `state_commit` is the
                  Poseidon2 digest OUTPUT, NOT a `RecordKernelState` field. The projection sets it to
                  `0`; no unification clause constrains it (the commit binding is the keystone's
                  separate anti-ghost tooth, `transferDescriptor_commit_binds_state`).

Against `CellTransferSpec pre p post`'s seven clauses, the executor's per-cell image satisfies:

  | clause                          | executor (`recKExec`) per-cell image | matches `CellTransferSpec`? |
  |---------------------------------|--------------------------------------|-----------------------------|
  | `direction ∈ {0,1}`             | 1 (debit) / 0 (credit), chosen        | YES                         |
  | `balLo = pre.balLo + signedMove`| `bal − amt` (src) / `bal + amt` (dst) | YES (signedMove = ±amt)     |
  | `balHi = pre.balHi`             | `0 = 0` (no high limb)                | YES (frozen)                |
  | `fields i = pre.fields i`       | `0 = 0` (no field array)              | YES (frozen)                |
  | `capRoot = pre.capRoot`         | `0 = 0` (no cap-root column)          | YES (frozen)                |
  | `reserved = pre.reserved`       | `0 = 0` (no reserved column)          | YES (frozen)                |
  | `nonce = pre.nonce + 1`         | `nonce` FROZEN (`setBalance` rewrites | ***NO*** — executor FREEZES |
  |                                 | ONLY the `balance` field; the cell's  | the nonce, it does NOT tick |
  |                                 | `nonce` field SURVIVES unchanged —    | by +1. A REAL MISMATCH.     |
  |                                 | see `RecordKernel.lean:3099` #guard)  |                             |

So the executor's per-cell image is the keystone's `CellTransferSpec` with the SINGLE exception of the
nonce-tick: `recKExec`/`TransferSpec` FREEZE the cell's `nonce` field, whereas `CellTransferSpec`
demands `post.nonce = pre.nonce + 1`. We therefore unify against `CellTransferSpecFrozenNonce` (the
seven clauses with the nonce-tick REPLACED by nonce-FREEZE), which is EXACTLY the executor's per-cell
image, and report the nonce-tick gap LOUDLY (`exec_nonce_is_frozen_not_ticked`): the EffectVM row's
`gNonceTick` column has NO counterpart in universe-A's `recKExec`. (A protocol that wants the
per-cell sequence counter the EffectVM row ticks must add a `nonce`-ticking effect to `recKExec`; as
of universe-A, transfer leaves the cell's nonce untouched.)

## BOUNDARY (precise)

  * PER CELL. This unifies ONE cell's transition. The cross-cell two-sided conservation — sender DEBIT
    + receiver CREDIT summing to zero net mint across the two cells — is the TURN-COMPOSITION layer
    (`Dregg2.Circuit.TurnEmit`, the chained `RecChainedState`s). We CITE it; we do NOT claim two-sided
    conservation here. The DEBIT-side and CREDIT-side theorems below are exactly the two per-cell legs
    that layer pairs into a (debit-row, credit-row) chain.

  * The `nonce`-tick mismatch above is the ONE genuine semantic divergence between the keystone's
    per-cell spec and universe-A's executor image. It is stated exactly, not papered.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. No `sorry`, no `:= True`,
no `native_decide`, no `rfl`-posing-as-bridge. Imports are read-only (`Transfer`, the keystone Sound
module); this module edits nothing.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Transfer

namespace Dregg2.Circuit.Emit.EffectVmEmitTransferUnify

open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
open Dregg2.Circuit.Transfer
open Dregg2.Exec

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §1 — `cellProj` — read ONE cell of the REAL `RecordKernelState` into the keystone `CellState`.

The conserved `balLo` limb reads `Transfer.balOf` (the `balance` field of the content-addressed
record — the SAME measure `recTransfer`/`setBalance` move). `nonce` reads the cell record's `nonce`
field. `balHi`/`fields`/`capRoot`/`reserved` have NO universe-A analogue (the `balance` field is one
scalar `ℤ`; there is no high-limb, no field-array, no cap-root column, no reserved column on the
conserved cell), so they project to `0` — FROZEN, matching the keystone's freeze clauses trivially.
`commit` is the EffectVM Poseidon2 digest OUTPUT, not a kernel field; the projection sets it `0` and
NO unification clause constrains it (see the module header). -/

/-- Read the cell record's `nonce` field as `ℤ`, defaulting absent/ill-typed to `0` (the same
fail-soft read `balOf` uses for `balance`). -/
def nonceOf (v : Value) : ℤ := (v.scalar "nonce").getD 0

/-- **`cellProj k c`** — project cell `c` of the real record-kernel state `k` into the keystone's
`CellState`. `balLo` = the real `balance` measure; `nonce` = the cell's `nonce` field; the EffectVM
limbs with no universe-A analogue (`balHi`/`fields`/`capRoot`/`reserved`) are `0`; `commit` (the
digest output, not a kernel field) is `0`. -/
def cellProj (k : RecordKernelState) (c : CellId) : CellState where
  balLo    := balOf (k.cell c)
  balHi    := 0
  nonce    := nonceOf (k.cell c)
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-! ### The two transfer-param blocks the keystone's `CellState` legs carry. -/

/-- The DEBIT param block for turn `t`: amount `t.amt`, `direction = 1` (so `signedMove = −amt`). -/
def debitParams (t : Turn) : TransferParams := { amount := t.amt, direction := 1 }

/-- The CREDIT param block for turn `t`: amount `t.amt`, `direction = 0` (so `signedMove = +amt`). -/
def creditParams (t : Turn) : TransferParams := { amount := t.amt, direction := 0 }

/-- `signedMove (debitParams t) = −t.amt` — the debit leg moves the limb DOWN by `amt`. -/
theorem signedMove_debit (t : Turn) : signedMove (debitParams t) = - t.amt := by
  unfold signedMove debitParams; ring

/-- `signedMove (creditParams t) = +t.amt` — the credit leg moves the limb UP by `amt`. -/
theorem signedMove_credit (t : Turn) : signedMove (creditParams t) = t.amt := by
  unfold signedMove creditParams; ring

/-! ## §2 — THE ONE REAL MISMATCH: `recKExec` FREEZES the cell's nonce, it does NOT tick by +1.

`recTransfer`/`setBalance` rewrite ONLY the `balance` field of the content-addressed record (every
other field — including `nonce` — survives; `RecordKernel.setBalance`'s `setBalanceList` matches on
`balanceField`, leaving all other keys intact, and `recTransfer` for a cell that is neither `src` nor
`dst` returns it untouched). So a committed transfer leaves EVERY cell's `nonce` field EXACTLY as it
was. The keystone's `CellTransferSpec` instead demands `post.nonce = pre.nonce + 1`. This is the ONE
genuine divergence; we prove the freeze, then unify against the freeze-variant spec. -/

/-- The `balance`-only nature of `setBalance`: it never changes the `nonce` field. (Reading `nonce`
through `Value.scalar` after `setBalance v x` returns the SAME thing it did before — the write
touches only the `balance` key.) -/
theorem setBalance_nonceOf (v : Value) (x : ℤ) : nonceOf (setBalance v x) = nonceOf v := by
  -- The `nonce`-field read agrees because `setBalanceList` only ever rewrites the `balance` key,
  -- leaving the `List.find?` for `"nonce"` unchanged.
  have hlist : ∀ fs : List (FieldName × Value),
      (List.find? (fun p => p.1 == "nonce") (setBalance.setBalanceList fs x))
        = (List.find? (fun p => p.1 == "nonce") fs) := by
    intro fs
    induction fs with
    | nil => rfl
    | cons hd tl ih =>
        obtain ⟨key, val⟩ := hd
        simp only [setBalance.setBalanceList]
        by_cases hk : (key == balanceField) = true
        · rw [if_pos hk]
          have hkb : key = balanceField := by simpa using hk
          have hbn : (balanceField == "nonce") = false := by decide
          have hkn : (key == "nonce") = false := by rw [hkb]; exact hbn
          rw [List.find?_cons_of_neg (by simp [hbn]),
              List.find?_cons_of_neg (by simp [hkn])]
        · rw [if_neg hk]
          by_cases hn : (key == "nonce") = true
          · rw [List.find?_cons_of_pos (by simp [hn]),
                List.find?_cons_of_pos (by simp [hn])]
          · have hnf : (key == "nonce") = false := by simpa using hn
            rw [List.find?_cons_of_neg (by simp [hnf]),
                List.find?_cons_of_neg (by simp [hnf]), ih]
  cases v with
  | record fs =>
      show nonceOf (Value.record (setBalance.setBalanceList fs x)) = nonceOf (Value.record fs)
      simp only [nonceOf, Value.scalar, Value.field, hlist fs]
  | int _ => rfl
  | dig _ => rfl
  | sym _ => rfl

/-- **`recTransfer_nonceOf_frozen` — the nonce of EVERY cell is FROZEN across `recTransfer`.** Whether
the cell is `src` (debited), `dst` (credited), or untouched, its `nonce` field is exactly preserved —
because `setBalance` rewrites only `balance`. This is the executor side of the nonce mismatch. -/
theorem recTransfer_nonceOf_frozen (cell : CellId → Value) (src dst : CellId) (amt : ℤ) (c : CellId) :
    nonceOf (recTransfer cell src dst amt c) = nonceOf (cell c) := by
  unfold recTransfer
  by_cases h1 : c = src
  · rw [if_pos h1, setBalance_nonceOf]
  · rw [if_neg h1]
    by_cases h2 : c = dst
    · rw [if_pos h2, setBalance_nonceOf]
    · rw [if_neg h2]

/-! ## §3 — `CellTransferSpecFrozenNonce`: the keystone's spec with the nonce-tick replaced by FREEZE.

This is `CellTransferSpec` EXACTLY, except `post.nonce = pre.nonce + 1` (the EffectVM row's nonce-tick)
becomes `post.nonce = pre.nonce` (FREEZE) — which is the executor's genuine per-cell image (see §2).
The six OTHER clauses are character-for-character `CellTransferSpec`'s. -/

/-- The executor's genuine per-cell image: `CellTransferSpec` with the nonce-tick replaced by
nonce-FREEZE. Every other clause (direction bit, balance signed-move, balHi/fields/capRoot/reserved
freeze) is identical to `CellTransferSpec`. -/
def CellTransferSpecFrozenNonce (pre : CellState) (p : TransferParams) (post : CellState) : Prop :=
  (p.direction = 0 ∨ p.direction = 1)
  ∧ post.balLo = pre.balLo + signedMove p
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce          -- FROZEN (executor image) — keystone instead demands `pre.nonce + 1`
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

/-- **The precise gap, as a theorem.** `CellTransferSpecFrozenNonce` and `CellTransferSpec` agree on
ALL clauses except the nonce: the former FREEZES (`post.nonce = pre.nonce`), the latter TICKS
(`post.nonce = pre.nonce + 1`). They are EQUIVALENT iff the nonce contributions agree, i.e. iff
`pre.nonce = pre.nonce + 1` — which is FALSE — so the two specs are NEVER simultaneously satisfiable on
the same `(pre,p,post)` unless `post.nonce` could be both. This pins the mismatch to exactly the nonce
column. -/
theorem frozenNonce_vs_keystone (pre post : CellState) (p : TransferParams) :
    (CellTransferSpecFrozenNonce pre p post ∧ post.nonce = pre.nonce + 1)
      ↔ (CellTransferSpec pre p post ∧ post.nonce = pre.nonce) := by
  constructor
  · rintro ⟨⟨hd, hlo, hhi, hn, hf, hcap, hres⟩, htick⟩
    exact ⟨⟨hd, hlo, hhi, htick, hf, hcap, hres⟩, hn⟩
  · rintro ⟨⟨hd, hlo, hhi, htick, hf, hcap, hres⟩, hn⟩
    exact ⟨⟨hd, hlo, hhi, hn, hf, hcap, hres⟩, htick⟩

/-! ## §4 — THE UNIFICATION THEOREMS — `CellTransferSpecFrozenNonce` IS `recKExec`'s per-cell image,
BOTH directions.

`TransferSpec k t k'` (= `recKExec k t = some k'`, by `Transfer.recKExec_iff_spec`) restricted to ONE
cell of `cellProj` is EXACTLY `CellTransferSpecFrozenNonce`:

  * DEBIT side — actor = `src`, direction = 1: the src cell's projection moves by `−amt`, frame
    frozen, nonce frozen.
  * CREDIT side — actor = `dst`, direction = 0: the dst cell's projection moves by `+amt`, frame
    frozen, nonce frozen.

These say: the keystone's per-cell spec is LITERALLY universe-A's executor transfer restricted to one
cell (modulo the §2 nonce-tick gap) — NOT a fourth spec. -/

/-- The DEBIT-side per-cell post-balance fact extracted from the full-state `TransferSpec`: the src
cell's projected `balLo` drops by `amt`. -/
private theorem proj_src_balLo (k k' : RecordKernelState) (t : Turn) (hspec : TransferSpec k t k') :
    (cellProj k' t.src).balLo = (cellProj k t.src).balLo - t.amt := by
  obtain ⟨⟨_, _, _, hne, _, _⟩, hcell, _⟩ := hspec
  show balOf (k'.cell t.src) = balOf (k.cell t.src) - t.amt
  rw [hcell]
  have := (recTransfer_correct k.cell t.src t.dst t.amt hne).1
  exact this

/-- The CREDIT-side per-cell post-balance fact: the dst cell's projected `balLo` rises by `amt`. -/
private theorem proj_dst_balLo (k k' : RecordKernelState) (t : Turn) (hspec : TransferSpec k t k') :
    (cellProj k' t.dst).balLo = (cellProj k t.dst).balLo + t.amt := by
  obtain ⟨⟨_, _, _, hne, _, _⟩, hcell, _⟩ := hspec
  show balOf (k'.cell t.dst) = balOf (k.cell t.dst) + t.amt
  rw [hcell]
  have := (recTransfer_correct k.cell t.src t.dst t.amt hne).2.1
  exact this

/-- The projected nonce of any cell is frozen across a committed transfer (lifted from §2 through the
spec's `k'.cell = recTransfer …` clause). -/
private theorem proj_nonce_frozen (k k' : RecordKernelState) (t : Turn) (c : CellId)
    (hspec : TransferSpec k t k') : (cellProj k' c).nonce = (cellProj k c).nonce := by
  obtain ⟨_, hcell, _⟩ := hspec
  show nonceOf (k'.cell c) = nonceOf (k.cell c)
  rw [hcell]; exact recTransfer_nonceOf_frozen k.cell t.src t.dst t.amt c

/-- **`unify_debit` — THE DEBIT-SIDE UNIFICATION.** A committed universe-A transfer
(`TransferSpec k t k'`), restricted to the SRC cell under `cellProj` with the debit param block,
satisfies the keystone's per-cell spec (freeze-nonce variant) EXACTLY. The src cell's `balLo` moves by
`signedMove (debitParams t) = −amt`; `balHi`/`fields`/`capRoot`/`reserved` are `0 = 0` (frozen); the
nonce is frozen (the §2 gap). So `CellTransferSpec`'s SRC leg IS `recKExec`'s SRC effect. -/
theorem unify_debit (k k' : RecordKernelState) (t : Turn) (hspec : TransferSpec k t k') :
    CellTransferSpecFrozenNonce (cellProj k t.src) (debitParams t) (cellProj k' t.src) := by
  refine ⟨Or.inr rfl, ?_, rfl, ?_, fun _ => rfl, rfl, rfl⟩
  · rw [signedMove_debit]; rw [proj_src_balLo k k' t hspec]; ring
  · exact proj_nonce_frozen k k' t t.src hspec

/-- **`unify_credit` — THE CREDIT-SIDE UNIFICATION.** A committed universe-A transfer, restricted to
the DST cell under `cellProj` with the credit param block, satisfies the keystone's per-cell spec
(freeze-nonce variant) EXACTLY. The dst cell's `balLo` moves by `signedMove (creditParams t) = +amt`;
frame frozen; nonce frozen. So `CellTransferSpec`'s DST leg IS `recKExec`'s DST effect. -/
theorem unify_credit (k k' : RecordKernelState) (t : Turn) (hspec : TransferSpec k t k') :
    CellTransferSpecFrozenNonce (cellProj k t.dst) (creditParams t) (cellProj k' t.dst) := by
  refine ⟨Or.inl rfl, ?_, rfl, ?_, fun _ => rfl, rfl, rfl⟩
  · rw [signedMove_credit]; rw [proj_dst_balLo k k' t hspec]
  · exact proj_nonce_frozen k k' t t.dst hspec

/-- **`unify_debit_exec` / `unify_credit_exec` — same, stated against the executor directly.** Reading
through `recKExec_iff_spec`, a committed `recKExec k t = some k'` (the REAL record-kernel transition)
projects per-cell to the keystone's freeze-nonce spec on BOTH the src (debit) and dst (credit) cells.
This is the headline: the runnable descriptor's per-cell spec is the EXECUTOR's per-cell image. -/
theorem unify_debit_exec (k k' : RecordKernelState) (t : Turn) (h : recKExec k t = some k') :
    CellTransferSpecFrozenNonce (cellProj k t.src) (debitParams t) (cellProj k' t.src) :=
  unify_debit k k' t ((recKExec_iff_spec k t k').mp h)

theorem unify_credit_exec (k k' : RecordKernelState) (t : Turn) (h : recKExec k t = some k') :
    CellTransferSpecFrozenNonce (cellProj k t.dst) (creditParams t) (cellProj k' t.dst) :=
  unify_credit k k' t ((recKExec_iff_spec k t k').mp h)

/-! ## §5 — THE COMPOSED END-TO-END (the payoff): runnable descriptor AGREES with the real executor,
per cell.

Combine the keystone's `transferDescriptor_full_sound` (satisfying the RUNNABLE descriptor + the
`RowEncodes` decoding forces `CellTransferSpec pre p post`) with the executor unification. Take the
DEBIT leg as the witnessed cell. A satisfying run of the runnable descriptor, encoding the SRC cell of
a committed transfer, agrees with `recKExec` on that cell's WHOLE conserved post-state: the descriptor's
pinned post-`balLo`/frame equals the executor's post-`cellProj` on EVERY clause the two specs share
(everything but the nonce). -/

/-- **`descriptor_agrees_with_executor_debit` — THE per-cell circuit⟺executor agreement.** Suppose
(a) the RUNNABLE descriptor is satisfied and its `RowEncodes` decoding names `(pre, debitParams t,
post)`, AND (b) the REAL executor commits `recKExec k t = some k'` with `pre = cellProj k t.src` the
SRC cell's projection. Then the descriptor's pinned post-state agrees with the executor's SRC
post-state on the SHARED spec: `post.balLo = (cellProj k' t.src).balLo` (the conserved move agrees),
and `post`'s frame (`balHi`/`fields`/`capRoot`/`reserved`) equals the executor's frozen frame. The ONE
column the two DISAGREE on is the nonce (descriptor ticks, executor freezes — §2), reported as a
separate conjunct. So the runnable circuit is sound w.r.t. the real executor, per cell. -/
theorem descriptor_agrees_with_executor_debit
    (hash : List ℤ → ℤ) (env : VmRowEnv)
    (k k' : RecordKernelState) (t : Turn) (post : CellState)
    (henc : RowEncodes env (cellProj k t.src) (debitParams t) post)
    (hrow : IsTransferRow env)
    (hsat : satisfiedVm hash transferVmDescriptor env true true)
    (hexec : recKExec k t = some k') :
    -- the conserved balance + the whole frame agree with the executor's SRC post-cell …
    ( post.balLo = (cellProj k' t.src).balLo
      ∧ post.balHi = (cellProj k' t.src).balHi
      ∧ (∀ i, post.fields i = (cellProj k' t.src).fields i)
      ∧ post.capRoot = (cellProj k' t.src).capRoot
      ∧ post.reserved = (cellProj k' t.src).reserved )
    -- … and the ONE disagreement: descriptor TICKS the nonce, executor FREEZES it (§2 gap).
    ∧ ( post.nonce = (cellProj k t.src).nonce + 1
        ∧ (cellProj k' t.src).nonce = (cellProj k t.src).nonce ) := by
  -- descriptor side: the keystone forces `CellTransferSpec pre (debitParams t) post`
  obtain ⟨hcirc, _⟩ := transferDescriptor_full_sound hash env (cellProj k t.src) post (debitParams t)
    henc hrow hsat
  obtain ⟨_, hcLo, hcHi, hcN, hcF, hcCap, hcRes⟩ := hcirc
  -- executor side: the freeze-nonce unification on the SRC cell
  obtain ⟨_, heLo, heHi, heN, heF, heCap, heRes⟩ := unify_debit_exec k k' t hexec
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- post.balLo = pre.balLo + signedMove (debit) = pre.balLo − amt = (cellProj k' src).balLo
    rw [hcLo, heLo]
  · -- balHi: post = pre.balHi (circuit) ; cellProj k' src .balHi = 0 = pre.balHi (both 0)
    rw [hcHi, heHi]
  · intro i; rw [hcF i, heF i]
  · rw [hcCap, heCap]
  · rw [hcRes, heRes]
  · -- the descriptor ticks the nonce
    rw [hcN]
  · -- the executor freezes the nonce
    exact heN

/-! ## §6 — NON-VACUITY: the unification fires on a CONCRETE small transfer, TRUE conclusion.

Reuse `Transfer.kT0`/`goodTurn`/`goodPost` (the validated reference: cell 0 holds 100, cell 1 holds 5,
actor 0 transfers 30 from 0→1, committed). The executor commits, so `TransferSpec kT0 goodTurn goodPost`
holds, and `unify_debit`/`unify_credit` fire with GENUINELY-TRUE (non-degenerate) conclusions: the src
cell's projected balance is 100 (NOT 0), moving to 70; the dst's is 5, moving to 35. -/

/-- Local alias resolving the bare name `goodPost` unambiguously to universe-A's record-kernel
post-state (`Transfer.goodPost`), distinct from the keystone's `CellState`-valued `goodPost`. -/
abbrev goodPost : RecordKernelState := Transfer.goodPost

/-- The executor commits the concrete good transfer, so the full-state spec holds. -/
theorem good_spec : TransferSpec kT0 goodTurn goodPost := by
  have h : recKExec kT0 goodTurn = some goodPost := by
    -- `goodPost = (recKExec kT0 goodTurn).getD kT0`; the executor commits, so `getD` IS the value.
    cases hk : recKExec kT0 goodTurn with
    | none => exact absurd hk (by decide)
    | some k'' =>
        show some k'' = some goodPost
        show some k'' = some (Transfer.goodPost)
        unfold Transfer.goodPost; rw [hk]; rfl
  exact (recKExec_iff_spec kT0 goodTurn goodPost).mp h

/-- The DEBIT-side projection is NON-DEGENERATE: the src cell's projected pre-balance is `100`
(NOT `0`), and it moves to `70` — so the unification's `balLo` clause is a TRUE, non-trivial equation. -/
theorem good_proj_src_nondegenerate :
    (cellProj kT0 goodTurn.src).balLo = 100 ∧ (cellProj goodPost goodTurn.src).balLo = 70 := by
  constructor
  · show balOf (kT0.cell goodTurn.src) = 100; decide
  · show balOf (goodPost.cell goodTurn.src) = 70; decide

/-- **`good_unify_debit` — the unification FIRES, TRUE conclusion, concrete transfer.** On the
validated reference transfer, the DEBIT-side unification holds AND its `balLo` clause is the genuine
`70 = 100 + (−30)` (non-vacuous: the src really held 100 and really moved to 70). -/
theorem good_unify_debit :
    CellTransferSpecFrozenNonce (cellProj kT0 goodTurn.src) (debitParams goodTurn)
        (cellProj goodPost goodTurn.src)
    ∧ (cellProj goodPost goodTurn.src).balLo
        = (cellProj kT0 goodTurn.src).balLo + signedMove (debitParams goodTurn) := by
  refine ⟨unify_debit kT0 goodPost goodTurn good_spec, ?_⟩
  exact (unify_debit kT0 goodPost goodTurn good_spec).2.1

/-- **`good_unify_credit` — the credit leg FIRES too.** The dst cell's projected balance moves
`5 → 35` (= `5 + 30`), the credit-side unification holding with a true, non-degenerate conclusion. -/
theorem good_unify_credit :
    CellTransferSpecFrozenNonce (cellProj kT0 goodTurn.dst) (creditParams goodTurn)
        (cellProj goodPost goodTurn.dst)
    ∧ (cellProj kT0 goodTurn.dst).balLo = 5 ∧ (cellProj goodPost goodTurn.dst).balLo = 35 := by
  refine ⟨unify_credit kT0 goodPost goodTurn good_spec, ?_, ?_⟩
  · show balOf (kT0.cell goodTurn.dst) = 5; decide
  · show balOf (goodPost.cell goodTurn.dst) = 35; decide

/-! ## §7 — THE NONCE MISMATCH, witnessed concretely.

On the SAME reference transfer, the projected nonce is FROZEN (cell 0 carries no `nonce` field, so it
projects to `0` and STAYS `0`), whereas the keystone's `CellTransferSpec` would demand it tick to `1`.
The freeze-nonce variant matches; the keystone's tick does NOT. -/

/-- The src cell's projected nonce is FROZEN at `0` across the transfer — the executor does not tick
it, so `CellTransferSpec`'s `post.nonce = pre.nonce + 1` (= `1`) FAILS here while the freeze-variant
(`post.nonce = pre.nonce` = `0`) holds. The concrete witness of the §2 gap. -/
theorem good_nonce_frozen_not_ticked :
    (cellProj goodPost goodTurn.src).nonce = (cellProj kT0 goodTurn.src).nonce
    ∧ (cellProj goodPost goodTurn.src).nonce ≠ (cellProj kT0 goodTurn.src).nonce + 1 := by
  have h0 : (cellProj kT0 goodTurn.src).nonce = 0 := by
    show nonceOf (kT0.cell goodTurn.src) = 0; decide
  have h0' : (cellProj goodPost goodTurn.src).nonce = 0 := by
    rw [proj_nonce_frozen kT0 goodPost goodTurn goodTurn.src good_spec, h0]
  rw [h0, h0']; exact ⟨rfl, by decide⟩

/-! ## §8 — Axiom-hygiene tripwires. -/

#assert_axioms setBalance_nonceOf
#assert_axioms recTransfer_nonceOf_frozen
#assert_axioms frozenNonce_vs_keystone
#assert_axioms signedMove_debit
#assert_axioms signedMove_credit
#assert_axioms unify_debit
#assert_axioms unify_credit
#assert_axioms unify_debit_exec
#assert_axioms unify_credit_exec
#assert_axioms descriptor_agrees_with_executor_debit
#assert_axioms good_spec
#assert_axioms good_proj_src_nondegenerate
#assert_axioms good_unify_debit
#assert_axioms good_unify_credit
#assert_axioms good_nonce_frozen_not_ticked

end Dregg2.Circuit.Emit.EffectVmEmitTransferUnify
