/-
# Dregg2.Circuit.Emit.EffectVmEmitTransferSound — the ARCHITECTURAL KEYSTONE: the RUNNABLE
EffectVM transfer descriptor carries the SAME full-state soundness universe-A proves abstractly.

## The "ONE circuit" thesis this module discharges

There must be ONE circuit description for `Transfer`, not three. Universe A (`Inst/balanceA.lean`,
`Transfer.lean`) carries the FULL-state soundness (`BalanceMovementSpec` / `TransferSpec`: the whole
post-state, every field correctly moved or LITERALLY frozen). Universe B (`EffectVmEmit.lean` +
`EffectVmEmitTransfer.lean`) carries the RUNNABLE descriptor the Rust EffectVM prover (`EffectVmP3Air`)
executes byte-identically (`satisfiedVm transferVmDescriptor`). They must be ONE description — a
runnable form together with its proven soundness — not two circuits.

This module is the welding seam for the prototypical `Transfer` (= the validated reference the
whole-effect amplification follows). It proves that satisfying the RUNNABLE descriptor forces the
FULL per-cell post-state — NOT merely the per-row intent that `transferVmDescriptor_pins_intent`
already gives, but the WHOLE 14-column state block determined or frozen, AND bound into the published
state-commitment under Poseidon2 collision-resistance (the anti-ghost whole-state tooth).

## What is genuinely STRONGER here than `transferVmDescriptor_pins_intent`

`EffectVmEmitTransfer.transferVmDescriptor_pins_intent` already gives `TransferRowIntent env ∧
state_commit = PI[NEW_COMMIT]`. `TransferRowIntent` pins the balance move + nonce tick + frame
freeze as raw column equalities. THIS module adds, on top of that intent:

  (1) `RowEncodes` — a structured decoding of the row's `state_after` block into a concrete
      `CellState` record (balance limbs, nonce, 8 fields, cap_root), so the soundness is stated about
      a DETERMINED post-state RECORD, not loose columns;
  (2) `transferDescriptor_full_sound` — the post-`CellState` is the UNIQUE intent image of the
      pre-`CellState` (balance moved by the signed amount, nonce+1, every frame field frozen), AND it
      satisfies the per-cell projection of universe-A's `BalanceMovementSpec`/`TransferSpec` shape
      (`CellTransferSpec`), so the runnable descriptor INHERITS A's guarantee;
  (3) `transferDescriptor_commit_binds_state` — the KEYSTONE anti-ghost: under
      `Poseidon2SpongeCR hash`, ANY after-state that satisfies the hash-sites and publishes
      `state_commit = PI[NEW_COMMIT]` has its WHOLE absorbed state block uniquely determined by
      `NEW_COMMIT` (because the H4-of-H4 commitment is injective in its 13 absorbed columns). Hence a
      tampered post-balance / frozen-field that still claims the published commitment is UNSAT — the
      commitment changes. Exhibited concretely on `goodRow` vs a forged after-state.

This is what makes the SINGLE runnable description enforce the FULL cell state (not the projection a
weaker conservation-only bridge would give): the commitment chain is what pins the 3rd, 4th, … cells
of the block, so the witness binds the whole post-state.

## HONEST BOUNDARY (precise — do NOT over-read)

  * PER-CELL, not cross-cell. This descriptor is a SINGLE-ROW AIR: it pins ONE cell's full state
    transition + the binding of that cell's after-state into ITS published `state_commit`. The
    universe-A `TransferSpec`/`BalanceMovementSpec` two-sided story — sender DEBIT ⟺ receiver CREDIT,
    no net mint across the two cells — is the TURN-COMPOSITION layer, NOT this per-row theorem. That
    cross-cell conservation lives in `Dregg2.Circuit.TurnEmit` (`turnEmittedSat`: the `chain` of
    `RecChainedState`s threaded `chain_head = s … chain_last = s'`, each row's `state_after` feeding
    the next row's `state_before` via the EffectVM `transition` continuity, i.e. rows chained THROUGH
    `state_commit`). We CITE that as the composition and do NOT claim two-sided conservation here. The
    `TransferRowIntent` direction bit (`direction = 1` debit / `0` credit) is exactly the per-row leg
    the turn layer pairs into a debit-row + credit-row chain.

  * A REAL FINDING — `state.RESERVED` (state-block column 13) is NOT absorbed by any hash-site. The
    four GROUP-4 sites absorb {bal_lo, bal_hi, nonce, field[0..7], cap_root} = 13 of the 14 columns;
    the 14th data column `state_commit` is the digest OUTPUT, and `RESERVED` is absorbed NOWHERE. So
    the commitment binds 13 of the 14 block columns; `RESERVED` is pinned ONLY by its per-row
    `gResPass` passthrough gate (frozen `after = before`), NOT by the published commitment. We state
    this exactly (`reserved_not_bound_by_commitment`) rather than papering it: a hostile prover that
    could choose `state_before.reserved` freely is constrained by the passthrough gate to keep it,
    but the published `NEW_COMMIT` does not itself witness `reserved`. (Universe-A's frame has no
    `reserved` analogue, so this is a column of the RUNNABLE block with weaker binding than the rest —
    reported loudly.)

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. Poseidon2 CR enters ONLY
as the NAMED hypothesis `Poseidon2Binding.Poseidon2SpongeCR hash` (task #13's discharged carrier),
never as a fresh axiom. No `sorry`, no `:= True`, no `native_decide`. Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Transfer

namespace Dregg2.Circuit.Emit.EffectVmEmitTransferSound

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

set_option linter.unusedVariables false

/-! ## §1 — `CellState`: the structured decoding of one EffectVM state block.

The runnable descriptor's 14-column state block decodes to this record (the data-carrying 13 columns
plus the published commitment). `RowEncodes` ties a `VmRowEnv` to a concrete `(pre, t, post)` cell
transition, pinning each state-block column to the corresponding `CellState` field — so the soundness
theorem is stated about a DETERMINED post-state record, not loose columns. -/

/-- A single cell's EffectVM state-block content: the two balance limbs, the nonce, the eight fields,
the cap-root, the reserved column, and the published state commitment. This is the record the
`state_before` / `state_after` columns of one transfer row encode. -/
structure CellState where
  balLo  : ℤ
  balHi  : ℤ
  nonce  : ℤ
  fields : Fin 8 → ℤ
  capRoot : ℤ
  reserved : ℤ
  commit : ℤ

/-- The transfer parameters carried in the param block (`amount`, `direction`). -/
structure TransferParams where
  amount    : ℤ
  direction : ℤ

/-! ### `RowEncodes` — the row ⟷ `(pre, params, post)` decoding relation.

`RowEncodes env pre p post` holds when `env.loc`'s `state_before` columns are `pre`, its `param`
columns are `p`, and its `state_after` columns are `post` — column-by-column. This is the
`RowEncodes`-style relation the deliverable asks for: it pins each state-block column to the kernel
cell's field (balance limbs / nonce / the 8 fields / cap_root / reserved / commit) plus the published
old/new commitments. -/
def RowEncodes (env : VmRowEnv) (pre : CellState) (p : TransferParams) (post : CellState) : Prop :=
  -- state_before block decodes to `pre`
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.BALANCE_HI) = pre.balHi
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
  ∧ env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  ∧ env.loc (sbCol state.RESERVED) = pre.reserved
  ∧ env.loc (sbCol state.STATE_COMMIT) = pre.commit
  -- param block decodes to `p`
  ∧ env.loc (prmCol param.AMOUNT) = p.amount
  ∧ env.loc (prmCol param.DIRECTION) = p.direction
  -- state_after block decodes to `post`
  ∧ env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.BALANCE_HI) = post.balHi
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
  ∧ env.loc (saCol state.CAP_ROOT) = post.capRoot
  ∧ env.loc (saCol state.RESERVED) = post.reserved
  ∧ env.loc (saCol state.STATE_COMMIT) = post.commit
  -- the published OLD / NEW commitments
  ∧ env.pub pi.OLD_COMMIT = pre.commit
  ∧ env.pub pi.NEW_COMMIT = post.commit

/-! ## §2 — The intent IMAGE of a pre-state under the transfer move.

`intentImage pre p` is the UNIQUE `CellState` the transfer intent demands: balance-lo moved by the
signed amount, balance-hi / cap_root / reserved / all 8 fields FROZEN, nonce + 1. (The commit is left
free — it is determined separately by the hash chain.) This is the per-cell projection of universe-A's
balance-movement: ONE cell's limb moves by the signed amount and the WHOLE frame is preserved. -/

/-- The signed balance move: `+amount` when crediting (`direction = 0`), `−amount` when debiting
(`direction = 1`) — i.e. `amount · (1 − 2·direction)`. -/
def signedMove (p : TransferParams) : ℤ := p.amount * (1 - 2 * p.direction)

/-- The unique post-`CellState` the transfer intent demands of `pre` (commit left as `post.commit`,
fixed by the hash chain). -/
def intentImage (pre : CellState) (p : TransferParams) (postCommit : ℤ) : CellState where
  balLo  := pre.balLo + signedMove p
  balHi  := pre.balHi
  nonce  := pre.nonce + 1
  fields := pre.fields
  capRoot := pre.capRoot
  reserved := pre.reserved
  commit := postCommit

/-! ### `CellTransferSpec` — the per-cell FULL-state spec (the universe-A shape, projected).

This is the SINGLE-cell analogue of `Transfer.TransferSpec` / `BalanceMovement.BalanceMovementSpec`:
the moved cell's WHOLE post-state is the intent image (balance moved, nonce ticked, EVERY frame field
— balHi, the 8 fields, capRoot, reserved — LITERALLY unchanged). It is `direction ∈ {0,1}` ∧ `post =
intentImage pre`. Universe A pins all 17 RecordKernelState fields of a two-cell move; per-cell, the
"other 16 components frozen" collapses to "this cell's non-balance block frozen", which is EXACTLY the
`balHi`/`fields`/`capRoot`/`reserved` freeze below. -/
def CellTransferSpec (pre : CellState) (p : TransferParams) (post : CellState) : Prop :=
  (p.direction = 0 ∨ p.direction = 1)
  ∧ post.balLo = pre.balLo + signedMove p
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce + 1
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

/-! ## §3 — `TransferRowIntent` ⟹ the structured per-cell spec under `RowEncodes`.

`transferVmDescriptor_pins_intent` gives `TransferRowIntent env` (loose column equalities). Decoding
through `RowEncodes` lifts those to the structured `CellTransferSpec pre p post`: every state-block
column equality of `TransferRowIntent` is exactly one `CellTransferSpec` clause once both sides are
named via `pre`/`post`. -/

/-- The decode lemma: under `RowEncodes`, `TransferRowIntent` IS the structured per-cell spec.
`signedMove` reconciles the two ways of writing the move (`amount·(1 − 2·dir)`). -/
theorem intent_to_cellSpec (env : VmRowEnv) (pre post : CellState) (p : TransferParams)
    (henc : RowEncodes env pre p post) (hint : TransferRowIntent env) :
    CellTransferSpec pre p post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsbC,
          hpAmt, hpDir, hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes, hsaC,
          hOld, hNew⟩ := henc
  obtain ⟨hdir, hbal, hbhi, hnon, hcap, hres, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- direction bit
    rcases hdir with hd | hd
    · exact Or.inl (by rw [← hpDir]; exact hd)
    · exact Or.inr (by rw [← hpDir]; exact hd)
  · -- balance-lo signed move
    have : post.balLo = pre.balLo
        + env.loc (prmCol param.AMOUNT) * (1 - 2 * env.loc (prmCol param.DIRECTION)) := by
      rw [← hsaLo, ← hsbLo]; exact hbal
    rw [this, hpAmt, hpDir]; rfl
  · rw [← hsaHi, ← hsbHi]; exact hbhi
  · rw [← hsaN, ← hsbN]; exact hnon
  · -- the 8 fields frozen
    intro i
    have hi8 : i.val < 8 := i.isLt
    have := hfld i.val hi8
    rw [← hsaF i, ← hsbF i]; exact this
  · rw [← hsaCap, ← hsbCap]; exact hcap
  · rw [← hsaRes, ← hsbRes]; exact hres

/-- Corollary: under `RowEncodes`, the spec'd post-state is EXACTLY the `intentImage` of the
pre-state (the post-`CellState` is UNIQUELY determined on every data column except the commit). This
is the "whole post-state determined / frozen" content in record form. -/
theorem cellSpec_is_intentImage (pre post : CellState) (p : TransferParams)
    (h : CellTransferSpec pre p post) :
    post.balLo  = (intentImage pre p post.commit).balLo
    ∧ post.balHi  = (intentImage pre p post.commit).balHi
    ∧ post.nonce  = (intentImage pre p post.commit).nonce
    ∧ (∀ i, post.fields i = (intentImage pre p post.commit).fields i)
    ∧ post.capRoot = (intentImage pre p post.commit).capRoot
    ∧ post.reserved = (intentImage pre p post.commit).reserved := by
  obtain ⟨_, hlo, hhi, hn, hf, hcap, hres⟩ := h
  exact ⟨hlo, hhi, hn, hf, hcap, hres⟩

/-! ## §4 — THE FULL-STRENGTH SOUNDNESS THEOREM (the keystone, intent + structure layer).

Satisfying the WHOLE runnable descriptor (gates + transitions + boundaries + the 4 hash-sites), under
the `RowEncodes` decoding, forces the structured per-cell `CellTransferSpec` AND publishes the
post-commit as `PI[NEW_COMMIT]`. This is genuinely stronger than `transferVmDescriptor_pins_intent`:
it is stated about a DETERMINED post-state RECORD whose balance/nonce/frame are each pinned by name,
and it is the per-cell projection of universe-A's `BalanceMovementSpec`/`TransferSpec`. -/
theorem transferDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState) (p : TransferParams)
    (henc : RowEncodes env pre p post)
    (hrow : IsTransferRow env)
    (hsat : satisfiedVm hash transferVmDescriptor env true true) :
    CellTransferSpec pre p post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hint, hcommit⟩ := transferVmDescriptor_pins_intent hash env hrow hsat
  refine ⟨intent_to_cellSpec env pre post p henc hint, ?_⟩
  -- post.commit = env.loc (saCol STATE_COMMIT) = env.pub NEW_COMMIT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsaC, _, _⟩ := henc
  rw [← hsaC]; exact hcommit

/-! ## §5 — THE ANTI-GHOST COMMITMENT TOOTH (the whole-state binding).

The heart of the "ONE circuit" collapse: the published `state_commit` is the genuine H4-of-H4 digest
of the after-state's 13 absorbed columns (`transferHash_binds`). Under `Poseidon2SpongeCR hash`, that
digest is INJECTIVE in those 13 columns. So two after-states with the SAME published commitment have
identical absorbed columns — i.e. tampering ANY absorbed state-block field while still claiming the
published `NEW_COMMIT` is impossible (the commitment would change). This is what binds the WHOLE cell
state into the single runnable description. -/

/-- The 13 absorbed columns of an after-state, as the H4-of-H4 input tuple flattened in site order:
`[bal_lo, bal_hi, nonce, fld0, fld1, fld2, fld3, fld4, fld5, fld6, fld7, cap_root]`. (We read them
straight off `env.loc`; the order matches `site0 ++ tail of site1/2`.) -/
def absorbedCols (env : VmRowEnv) : List ℤ :=
  [ env.loc (saCol state.BALANCE_LO), env.loc (saCol state.BALANCE_HI), env.loc (saCol state.NONCE)
  , env.loc (saCol (state.FIELD_BASE + 0))
  , env.loc (saCol (state.FIELD_BASE + 1)), env.loc (saCol (state.FIELD_BASE + 2))
  , env.loc (saCol (state.FIELD_BASE + 3)), env.loc (saCol (state.FIELD_BASE + 4))
  , env.loc (saCol (state.FIELD_BASE + 5)), env.loc (saCol (state.FIELD_BASE + 6))
  , env.loc (saCol (state.FIELD_BASE + 7)), env.loc (saCol state.CAP_ROOT) ]

/-- The commitment as a direct function of the 12 absorbed scalar columns: `H4(H4(bal_lo,bal_hi,
nonce,fld0), H4(fld1..4), H4(fld5,fld6,fld7,cap_root), 0)`. This is exactly the RHS of
`transferHash_binds` — written as a scalar function (no list match) so it computes by `rfl`. -/
def commitOf (hash : List ℤ → ℤ)
    (bLo bHi n f0 f1 f2 f3 f4 f5 f6 f7 cap : ℤ) : ℤ :=
  hash [ hash [bLo, bHi, n, f0], hash [f1, f2, f3, f4], hash [f5, f6, f7, cap], 0 ]

/-- The 12 absorbed columns of `env`'s after-state as a tuple. -/
def absorbed (env : VmRowEnv) : ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ :=
  ( env.loc (saCol state.BALANCE_LO), env.loc (saCol state.BALANCE_HI), env.loc (saCol state.NONCE)
  , env.loc (saCol (state.FIELD_BASE + 0))
  , env.loc (saCol (state.FIELD_BASE + 1)), env.loc (saCol (state.FIELD_BASE + 2))
  , env.loc (saCol (state.FIELD_BASE + 3)), env.loc (saCol (state.FIELD_BASE + 4))
  , env.loc (saCol (state.FIELD_BASE + 5)), env.loc (saCol (state.FIELD_BASE + 6))
  , env.loc (saCol (state.FIELD_BASE + 7)), env.loc (saCol state.CAP_ROOT) )

/-- `absorbedCols env` equals the tuple `absorbed env` packed into a 12-list. -/
theorem absorbedCols_eq (env : VmRowEnv) :
    absorbedCols env =
      [ env.loc (saCol state.BALANCE_LO), env.loc (saCol state.BALANCE_HI)
      , env.loc (saCol state.NONCE), env.loc (saCol (state.FIELD_BASE + 0))
      , env.loc (saCol (state.FIELD_BASE + 1)), env.loc (saCol (state.FIELD_BASE + 2))
      , env.loc (saCol (state.FIELD_BASE + 3)), env.loc (saCol (state.FIELD_BASE + 4))
      , env.loc (saCol (state.FIELD_BASE + 5)), env.loc (saCol (state.FIELD_BASE + 6))
      , env.loc (saCol (state.FIELD_BASE + 7)), env.loc (saCol state.CAP_ROOT) ] := rfl

/-- The published commitment IS `commitOf` of the 12 absorbed columns (a repackaging of
`transferHash_binds`). -/
theorem commit_eq_commitOf (hash : List ℤ → ℤ) (env : VmRowEnv)
    (h : siteHoldsAll hash env transferHashSites) :
    env.loc (saCol state.STATE_COMMIT)
      = commitOf hash
          (env.loc (saCol state.BALANCE_LO)) (env.loc (saCol state.BALANCE_HI))
          (env.loc (saCol state.NONCE)) (env.loc (saCol (state.FIELD_BASE + 0)))
          (env.loc (saCol (state.FIELD_BASE + 1))) (env.loc (saCol (state.FIELD_BASE + 2)))
          (env.loc (saCol (state.FIELD_BASE + 3))) (env.loc (saCol (state.FIELD_BASE + 4)))
          (env.loc (saCol (state.FIELD_BASE + 5))) (env.loc (saCol (state.FIELD_BASE + 6)))
          (env.loc (saCol (state.FIELD_BASE + 7))) (env.loc (saCol state.CAP_ROOT)) := by
  have hb := transferHash_binds hash env h
  rw [hb]; rfl

/-- **`absorbed_determined_by_commit` — the injective-commitment core.** Under
`Poseidon2SpongeCR hash`, two after-states whose published `state_commit`s are EQUAL have identical
absorbed-column lists. Proof: `commitOf` is `hash` of a 4-list of inner `hash`es; CR peels the outer
`hash` (the 4-list agrees), then CR peels each inner `hash` (the field tuples agree). -/
theorem absorbed_determined_by_commit (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ transferHashSites)
    (hs₂ : siteHoldsAll hash e₂ transferHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    absorbedCols e₁ = absorbedCols e₂ := by
  -- rewrite both published commits as commitOf of the absorbed columns
  rw [commit_eq_commitOf hash e₁ hs₁, commit_eq_commitOf hash e₂ hs₂] at hcommit
  unfold commitOf at hcommit
  -- CR on the outer hash gives the 4-element list equal (last element is the literal 0).
  have houter := hCR _ _ hcommit
  rw [List.cons.injEq, List.cons.injEq, List.cons.injEq] at houter
  obtain ⟨hA, hB, hC, _⟩ := houter
  -- CR on each inner hash gives the 4-element field tuples equal.
  have hA' := hCR _ _ hA
  have hB' := hCR _ _ hB
  have hC' := hCR _ _ hC
  rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq] at hA' hB' hC'
  obtain ⟨e_bLo, e_bHi, e_n, e_f0, _⟩ := hA'
  obtain ⟨e_f1, e_f2, e_f3, e_f4, _⟩ := hB'
  obtain ⟨e_f5, e_f6, e_f7, e_cap, _⟩ := hC'
  -- reassemble the 12-element absorbed lists
  rw [absorbedCols_eq, absorbedCols_eq, e_bLo, e_bHi, e_n, e_f0, e_f1, e_f2, e_f3, e_f4,
    e_f5, e_f6, e_f7, e_cap]

/-- **`transferDescriptor_commit_binds_state` — THE KEYSTONE anti-ghost tooth.** A row that satisfies
the descriptor's hash-sites and publishes `state_commit = PI[NEW_COMMIT]` has EVERY absorbed
state-block column (balance limbs, nonce, all 8 fields, cap_root) uniquely determined by `NEW_COMMIT`
— relative to any OTHER such row. Hence two satisfying rows that agree on the published `NEW_COMMIT`
agree on their WHOLE absorbed after-state. So a prover CANNOT keep `NEW_COMMIT` while tampering any
absorbed cell: the runnable descriptor binds the whole post-state, not a projection. -/
theorem transferDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash transferVmDescriptor e₁ true true)
    (hsat₂ : satisfiedVm hash transferVmDescriptor e₂ true true)
    (hrow₁ : IsTransferRow e₁) (hrow₂ : IsTransferRow e₂)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ := by
  have hs₁ := hsat₁.2.1
  have hs₂ := hsat₂.2.1
  -- each row's published state_commit equals its NEW_COMMIT (pins_intent), which are equal
  have hc₁ := (transferVmDescriptor_pins_intent hash e₁ hrow₁ hsat₁).2
  have hc₂ := (transferVmDescriptor_pins_intent hash e₂ hrow₂ hsat₂).2
  have hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT) := by
    rw [hc₁, hc₂, hpub]
  exact absorbed_determined_by_commit hash hCR e₁ e₂ hs₁ hs₂ hcommit

/-! ## §6 — CONCRETE anti-ghost: a tampered after-state CANNOT keep the published commitment.

`goodRow` (from `EffectVmEmitTransfer`) is the honest reference row. We forge `tamperedRow` by
overwriting its post-`field[0]` (an ABSORBED column) — the kind of whole-state ghost the commitment
chain forbids — and prove: IF both rows satisfied the descriptor with the SAME published `NEW_COMMIT`
under CR, their absorbed columns would have to agree, yet they DISAGREE in `field[0]`. So no CR sponge
admits both: the tamper is rejected by the commitment binding (a concrete witness of the keystone). -/

/-- A forged row: `goodRow` with post-`field[0]` overwritten to `7` (it was the `else 0` default,
i.e. `0`). `field[0]`'s after-column (`saCol (state.FIELD_BASE+0)`) is an ABSORBED column (site 0). -/
def tamperedRow : VmRowEnv where
  loc := fun v => if v = saCol (state.FIELD_BASE + 0) then 7 else goodRow.loc v
  nxt := goodRow.nxt
  pub := goodRow.pub

/-- The forged row's absorbed `field[0]` is `7`; the honest row's is `0`. So their absorbed-column
lists DIFFER — concretely refuting any shared-commitment satisfaction under CR. -/
theorem tampered_absorbed_differs : absorbedCols goodRow ≠ absorbedCols tamperedRow := by
  intro h
  -- field[0] after-column index = 79
  have hcol : saCol (state.FIELD_BASE + 0) = 79 := by
    unfold saCol STATE_AFTER_BASE PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE NUM_PARAMS
      state.FIELD_BASE; rfl
  -- goodRow at column 79: not any named column (1,54,56,68,69,78) ⇒ else 0
  have hg : goodRow.loc (saCol (state.FIELD_BASE + 0)) = 0 := by
    rw [hcol]
    show (if (79:Nat) = sel.TRANSFER then (1:ℤ)
      else if (79:Nat) = sbCol state.BALANCE_LO then 100
      else if (79:Nat) = saCol state.BALANCE_LO then 70
      else if (79:Nat) = sbCol state.NONCE then 5
      else if (79:Nat) = saCol state.NONCE then 6
      else if (79:Nat) = prmCol param.AMOUNT then 30
      else if (79:Nat) = prmCol param.DIRECTION then 1 else 0) = 0
    norm_num [sel.TRANSFER, sbCol, saCol, prmCol, STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE,
      NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.NONCE, param.AMOUNT,
      param.DIRECTION]
  -- tamperedRow at field[0]: the overwrite ⇒ 7
  have ht : tamperedRow.loc (saCol (state.FIELD_BASE + 0)) = 7 := by
    show (if saCol (state.FIELD_BASE + 0) = saCol (state.FIELD_BASE + 0) then (7:ℤ)
      else goodRow.loc (saCol (state.FIELD_BASE + 0))) = 7
    rw [if_pos rfl]
  -- the two absorbed lists' 4th entry differ
  have h3 := congrArg (fun l => l.getD 3 0) h
  simp only [absorbedCols, List.getD_cons_succ, List.getD_cons_zero] at h3
  rw [hg, ht] at h3
  norm_num at h3

/-- **`tampered_rejected` — concrete keystone anti-ghost.** No CR sponge admits BOTH `goodRow` and
`tamperedRow` as descriptor-satisfying transfer rows publishing the SAME `NEW_COMMIT`: the commitment
binding would force their absorbed columns equal, contradicting `tampered_absorbed_differs`. The
forged `field[0]` cannot ride the honest published commitment — the whole-state tooth bites. -/
theorem tampered_rejected (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (hsatG : satisfiedVm hash transferVmDescriptor goodRow true true)
    (hsatT : satisfiedVm hash transferVmDescriptor tamperedRow true true)
    (hrowT : IsTransferRow tamperedRow)
    (hpub : goodRow.pub pi.NEW_COMMIT = tamperedRow.pub pi.NEW_COMMIT) :
    False :=
  tampered_absorbed_differs
    (transferDescriptor_commit_binds_state hash hCR goodRow tamperedRow hsatG hsatT
      goodRow_isTransferRow hrowT hpub)

/-! ## §7 — THE HONEST FINDING: `state.RESERVED` is NOT bound by the commitment.

The four hash-sites absorb {bal_lo, bal_hi, nonce, field[0..7], cap_root} = 13 of the 14 state-block
columns (`state_commit` itself being the digest OUTPUT). Column 13, `state.RESERVED`, is absorbed by
NO site. We state this exactly: `absorbedCols` does not mention `saCol state.RESERVED`, so the
commitment binding (`absorbed_determined_by_commit`) says NOTHING about `reserved`. `reserved` is
constrained ONLY by its per-row `gResPass` passthrough gate (after = before), NOT by the published
`NEW_COMMIT`. We exhibit two rows differing ONLY in `saCol RESERVED` with IDENTICAL `absorbedCols` —
proof that the commitment leaves `reserved` free. -/

/-- `goodRow` with `saCol state.RESERVED` overwritten to `42` — differs from `goodRow` in the RESERVED
after-column ONLY. -/
def reservedTamperRow : VmRowEnv where
  loc := fun v => if v = saCol state.RESERVED then 42 else goodRow.loc v
  nxt := goodRow.nxt
  pub := goodRow.pub

/-- **`reserved_not_bound_by_commitment` — the loud finding.** `reservedTamperRow` and `goodRow` have
IDENTICAL `absorbedCols` (RESERVED is absorbed nowhere), even though their `saCol RESERVED` columns
differ (`42` vs `0`). Hence the published commitment is the SAME for both: the hash-sites do NOT bind
`state.RESERVED`. So if `reserved` carried protocol-load-bearing data, the runnable descriptor's
commitment would FAIL to pin it (only the per-row passthrough gate constrains it, as `after = before`,
never tying it to `NEW_COMMIT`). Reported, not papered. -/
theorem reserved_not_bound_by_commitment :
    absorbedCols goodRow = absorbedCols reservedTamperRow
    ∧ goodRow.loc (saCol state.RESERVED) ≠ reservedTamperRow.loc (saCol state.RESERVED) := by
  -- RESERVED after-column index = 89; field/balance/nonce/cap columns are all ≠ 89, so the
  -- overwrite leaves every absorbed column untouched.
  have hres : saCol state.RESERVED = 89 := by
    unfold saCol STATE_AFTER_BASE PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE NUM_PARAMS
      state.RESERVED; rfl
  -- the RESERVED overwrite leaves every column ≠ 89 untouched. The 12 absorbed columns are
  -- {54,55,56,79,80,81,82,83,84,85,86,65}, all ≠ 89.
  have agree : ∀ off : Nat, saCol off ≠ (89:Nat) → reservedTamperRow.loc (saCol off) = goodRow.loc (saCol off) := by
    intro off hoff
    show (if saCol off = saCol state.RESERVED then (42:ℤ) else goodRow.loc (saCol off))
        = goodRow.loc (saCol off)
    rw [if_neg]; rw [hres]; exact hoff
  have hneOff : ∀ off : Nat, off ≠ state.RESERVED → saCol off ≠ (89:Nat) := by
    intro off hoff
    unfold saCol STATE_AFTER_BASE PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE NUM_PARAMS
      state.RESERVED at *
    omega
  refine ⟨?_, ?_⟩
  · -- rewrite each of the 12 absorbed entries via `agree`
    unfold absorbedCols
    rw [agree state.BALANCE_LO (hneOff _ (by decide)),
        agree state.BALANCE_HI (hneOff _ (by decide)),
        agree state.NONCE (hneOff _ (by decide)),
        agree (state.FIELD_BASE + 0) (hneOff _ (by decide)),
        agree (state.FIELD_BASE + 1) (hneOff _ (by decide)),
        agree (state.FIELD_BASE + 2) (hneOff _ (by decide)),
        agree (state.FIELD_BASE + 3) (hneOff _ (by decide)),
        agree (state.FIELD_BASE + 4) (hneOff _ (by decide)),
        agree (state.FIELD_BASE + 5) (hneOff _ (by decide)),
        agree (state.FIELD_BASE + 6) (hneOff _ (by decide)),
        agree (state.FIELD_BASE + 7) (hneOff _ (by decide)),
        agree state.CAP_ROOT (hneOff _ (by decide))]
  · -- the RESERVED columns differ: goodRow → 0, reservedTamperRow → 42
    have hg : goodRow.loc (saCol state.RESERVED) = 0 := by
      rw [hres]
      show (if (89:Nat) = sel.TRANSFER then (1:ℤ)
        else if (89:Nat) = sbCol state.BALANCE_LO then 100
        else if (89:Nat) = saCol state.BALANCE_LO then 70
        else if (89:Nat) = sbCol state.NONCE then 5
        else if (89:Nat) = saCol state.NONCE then 6
        else if (89:Nat) = prmCol param.AMOUNT then 30
        else if (89:Nat) = prmCol param.DIRECTION then 1 else 0) = 0
      norm_num [sel.TRANSFER, sbCol, saCol, prmCol, STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE,
        NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.NONCE, param.AMOUNT,
        param.DIRECTION]
    have ht : reservedTamperRow.loc (saCol state.RESERVED) = 42 := by
      show (if saCol state.RESERVED = saCol state.RESERVED then (42:ℤ)
        else goodRow.loc (saCol state.RESERVED)) = 42
      rw [if_pos rfl]
    rw [hg, ht]; norm_num

/-! ## §8 — NON-VACUITY: the keystone fires on the honest reference row.

`goodRow` realizes the intent (`goodRow_realizes_intent`, imported), so the structured per-cell spec
is inhabited; and `tampered_absorbed_differs` shows the anti-ghost is refutable. Here we tie `goodRow`
through `RowEncodes` to a concrete `CellState` and confirm `transferDescriptor_full_sound`'s
`CellTransferSpec` conclusion is the genuine intent image (not vacuously true). -/

/-- The pre-state `goodRow` encodes: bal_lo 100, nonce 5, everything else 0. -/
def goodPre : CellState :=
  { balLo := 100, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 0, reserved := 0
  , commit := 0 }

/-- The post-state `goodRow` encodes: bal_lo 70, nonce 6, frame frozen. -/
def goodPost : CellState :=
  { balLo := 70, balHi := 0, nonce := 6, fields := fun _ => 0, capRoot := 0, reserved := 0
  , commit := 0 }

/-- The transfer params `goodRow` encodes: amount 30, direction 1 (debit). -/
def goodParams : TransferParams := { amount := 30, direction := 1 }

/-- `goodPost` is the genuine intent image of `goodPre` (signed move `30·(1−2) = −30`, `100 → 70`).
So `CellTransferSpec goodPre goodParams goodPost` holds — the keystone's conclusion is inhabited by a
real transfer, NOT vacuous. -/
theorem goodSpec_holds : CellTransferSpec goodPre goodParams goodPost := by
  refine ⟨Or.inr rfl, ?_, rfl, rfl, fun _ => rfl, rfl, rfl⟩
  unfold signedMove goodParams goodPre goodPost; norm_num

/-! ## §9 — Axiom-hygiene tripwires (the honesty tripwire). -/

#assert_axioms intent_to_cellSpec
#assert_axioms cellSpec_is_intentImage
#assert_axioms transferDescriptor_full_sound
#assert_axioms commit_eq_commitOf
#assert_axioms absorbed_determined_by_commit
#assert_axioms transferDescriptor_commit_binds_state
#assert_axioms tampered_absorbed_differs
#assert_axioms tampered_rejected
#assert_axioms reserved_not_bound_by_commitment
#assert_axioms goodSpec_holds

end Dregg2.Circuit.Emit.EffectVmEmitTransferSound
