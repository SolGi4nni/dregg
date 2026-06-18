/-
# Dregg2.Circuit.Emit.EffectVmEmitTransfer — the TRANSFER effect's concrete circuit, EMITTED.

This module re-derives the running `Transfer` row constraints FROM the transfer intent and emits
them through the `EffectVmEmit` IR as `transferVmDescriptor`, then proves the emitted descriptor's
denotation is EQUIVALENT to that intent (`transferVm_faithful`) + the anti-ghost teeth. So the
EffectVM transfer circuit the Rust prover (`EffectVmP3Air`) runs IS the verified intent by
construction.

## The TARGET (the running prover's transfer constraints)

From `circuit/src/effect_vm_p3_full_air.rs` (mirror of `effect_vm/air.rs`), on a TRANSFER row
(`s_transfer = 1`, all other selectors 0, so `s_noop = 0`):

  * `new_bal_lo - old_bal_lo - amount + 2·direction·amount = 0`   (debit/credit on the lo limb)
  * `new_bal_hi - old_bal_hi = 0`                                  (hi limb unchanged)
  * `direction·(direction - 1) = 0`                               (direction ∈ {0,1})
  * `new_cap_root - old_cap_root = 0`, `new_reserved - old_reserved = 0`  (frame passthrough)
  * `fld_a i - fld_b i = 0`  for i ∈ 0..8                          (fields frozen)
  * `new_nonce - old_nonce - (1 - s_noop) = 0`  ⟹  `new_nonce = old_nonce + 1`  (nonce tick)
  * transition continuity `next.state_before[i] = this.state_after[i]` for the whole state block
  * GROUP-4 state-commitment hash chain: 4 ordered `H4` sites with
    `state_after.state_commit = H4(inter1, inter2, inter3, 0)`, the inters binding the after-state
  * boundary pins: row-0 `{nonce, bal_lo, bal_hi, state_commit}` to `{ACTOR_NONCE, INIT_BAL_LO,
    INIT_BAL_HI, OLD_COMMIT}`; last-row `{state_commit, bal_lo, bal_hi}` to `{NEW_COMMIT,
    FINAL_BAL_LO, FINAL_BAL_HI}`.

## The INTENT (independent, the faithfulness target)

`TransferRowIntent` is the field-level transfer move written from protocol intent — the SAME
debit/credit `Spec.CircuitSpecTriangle.intentTransfer` pins abstractly, projected to the EffectVM
row layout (balance limbs + nonce + frame). `transferVm_faithful` proves the emitted descriptor's
per-row gate set is satisfied on a transfer row IFF `TransferRowIntent` holds — so the concrete
circuit enforces EXACTLY the intent, and any wrong-output row (tampered balance / nonce / frame)
makes the descriptor UNSAT (`transferVm_rejects_*`).
-/
import Dregg2.Circuit.Emit.EffectVmEmit

namespace Dregg2.Circuit.Emit.EffectVmEmitTransfer

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Exec.CircuitEmit (EmittedExpr)

set_option linter.unusedVariables false

/-! ## §0 — Column readers as `EmittedExpr` (the gate-body builders).

These build the SAME `var`/`add`/`mul` ASTs the running prover's `lc`/`sb`/`sa`/`prm` accessors
read, so the emitted gate bodies are the prover's polynomials. -/

/-- `state_before[off]` as an expression. -/
def eSB (off : Nat) : EmittedExpr := .var (sbCol off)
/-- `state_after[off]` as an expression. -/
def eSA (off : Nat) : EmittedExpr := .var (saCol off)
/-- `param[i]` as an expression. -/
def ePrm (i : Nat) : EmittedExpr := .var (prmCol i)
/-- The transfer selector column as an expression. -/
def eSelTransfer : EmittedExpr := .var sel.TRANSFER
/-- The noop selector column as an expression. -/
def eSelNoop : EmittedExpr := .var sel.NOOP

/-- `a - b` as an `EmittedExpr` (`a + (-1)·b`). -/
def eSub (a b : EmittedExpr) : EmittedExpr := .add a (.mul (.const (-1)) b)

/-! ## §1 — The TRANSFER gate bodies (term-for-term the running prover's, ungated by `s_transfer`).

We emit the gates ALREADY specialized to a transfer row: the running prover multiplies each by
`s_transfer`, which is `1` on a transfer row, so the row-restricted gate body is the inner
polynomial. (The selector-validity / sum-to-one gates of GROUP 1 are global well-formedness; the
transfer faithfulness is about the per-effect transition, so we emit the transfer-specialized
bodies and PROVE they coincide with the intent on the transfer row.) -/

/-- Balance-lo debit/credit body: `new_bal_lo - old_bal_lo - amount + 2·direction·amount`. -/
def gBalLo : EmittedExpr :=
  .add (eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO))
    (.add (.mul (.const (-1)) (ePrm param.AMOUNT))
      (.mul (.const 2) (.mul (ePrm param.DIRECTION) (ePrm param.AMOUNT))))

/-- Balance-hi unchanged body: `new_bal_hi - old_bal_hi`. -/
def gBalHi : EmittedExpr := eSub (eSA state.BALANCE_HI) (eSB state.BALANCE_HI)

/-- Direction-boolean body: `direction·(direction - 1)`. -/
def gDirBool : EmittedExpr :=
  .mul (ePrm param.DIRECTION) (.add (ePrm param.DIRECTION) (.const (-1)))

/-- Nonce-increment body (ungated, transfer-specialized): `new_nonce - old_nonce - (1 - s_noop)`.
On a transfer row `s_noop = 0`, so this is `new_nonce - old_nonce - 1`. -/
def gNonce : EmittedExpr :=
  eSub (eSub (eSA state.NONCE) (eSB state.NONCE)) (eSub (.const 1) eSelNoop)

/-- Cap-root passthrough body: `new_cap_root - old_cap_root`. -/
def gCapPass : EmittedExpr := eSub (eSA state.CAP_ROOT) (eSB state.CAP_ROOT)

/-- Reserved passthrough body: `new_reserved - old_reserved`. -/
def gResPass : EmittedExpr := eSub (eSA state.RESERVED) (eSB state.RESERVED)

/-- Field-`i` passthrough body: `field_after[i] - field_before[i]`. -/
def gFieldPass (i : Nat) : EmittedExpr :=
  eSub (eSA (state.FIELD_BASE + i)) (eSB (state.FIELD_BASE + i))

/-- The eight field-passthrough gates. -/
def gFieldPassAll : List VmConstraint :=
  (List.range 8).map (fun i => VmConstraint.gate (gFieldPass i))

/-! ## §2 — The TRANSITION + BOUNDARY + PI constraints.

Transition continuity over the whole state block; the 7 boundary pins (4 first-row, 3 last-row)
as `piBinding`s. -/

/-- Transition continuity for the whole state block: `next.state_before[i] = this.state_after[i]`. -/
def transitionAll : List VmConstraint :=
  (List.range STATE_SIZE).map (fun i => VmConstraint.transition i i)

/-- The first-row boundary PI pins (`nonce`/`bal_lo`/`bal_hi`/`state_commit`). -/
def boundaryFirstPins : List VmConstraint :=
  [ .piBinding .first (sbCol state.NONCE)        pi.ACTOR_NONCE
  , .piBinding .first (sbCol state.BALANCE_LO)   pi.INIT_BAL_LO
  , .piBinding .first (sbCol state.BALANCE_HI)   pi.INIT_BAL_HI
  , .piBinding .first (sbCol state.STATE_COMMIT) pi.OLD_COMMIT ]

/-- The last-row boundary PI pins (`state_commit`/`bal_lo`/`bal_hi`). -/
def boundaryLastPins : List VmConstraint :=
  [ .piBinding .last (saCol state.STATE_COMMIT) pi.NEW_COMMIT
  , .piBinding .last (saCol state.BALANCE_LO)   pi.FINAL_BAL_LO
  , .piBinding .last (saCol state.BALANCE_HI)   pi.FINAL_BAL_HI ]

/-! ## §3 — The GROUP-4 state-commitment hash sites (ordered).

The four `H4` sites of the running prover (in the FIXED `hash_sites()` order), binding the
after-state cells into `state_after.state_commit`. Abstract `hash : List ℤ → ℤ` carrier. -/

/-- Site 0: `inter1 = H4(after.bal_lo, after.bal_hi, after.nonce, after.field[0])`. -/
def site0 : VmHashSite :=
  { digestCol := auxCol aux_off.STATE_INTER1
  , inputs := [ .col (saCol state.BALANCE_LO), .col (saCol state.BALANCE_HI)
              , .col (saCol state.NONCE),      .col (saCol (state.FIELD_BASE + 0)) ]
  , arity := 4 }

/-- Site 1: `inter2 = H4(after.field[1..5])`. -/
def site1 : VmHashSite :=
  { digestCol := auxCol aux_off.STATE_INTER2
  , inputs := [ .col (saCol (state.FIELD_BASE + 1)), .col (saCol (state.FIELD_BASE + 2))
              , .col (saCol (state.FIELD_BASE + 3)), .col (saCol (state.FIELD_BASE + 4)) ]
  , arity := 4 }

/-- Site 2: `inter3 = H4(after.field[5], after.field[6], after.field[7], after.cap_root)`. -/
def site2 : VmHashSite :=
  { digestCol := auxCol aux_off.STATE_INTER3
  , inputs := [ .col (saCol (state.FIELD_BASE + 5)), .col (saCol (state.FIELD_BASE + 6))
              , .col (saCol (state.FIELD_BASE + 7)), .col (saCol state.CAP_ROOT) ]
  , arity := 4 }

/-- Site 3: `state_commit = H4(inter1, inter2, inter3, record_digest)` (the published post-state
commitment). Result column is `state_after.state_commit` itself (the GROUP-4 `sa(STATE_COMMIT) ==
digest` binding), reading sites 0/1/2's digests. The FOURTH input is the witnessed authority-residue
`record_digest` (`aux_off.STATE_RECORD_DIGEST`, absolute col `auxCol 96 = 186`) — replacing the old
literal `.zero`, audit P0-2 — so `state_commit` (and thus `OLD_COMMIT`/`NEW_COMMIT`) binds the FULL
cell state. Matches the Rust `cell_state.rs::compute_commitment` / `air.rs` GROUP-4
(`local[AUX_BASE + aux_off::STATE_RECORD_DIGEST]`). A residue-free cell witnesses `0` here, so this is
byte-identical to the legacy `…, 0)` form. -/
def site3 : VmHashSite :=
  { digestCol := saCol state.STATE_COMMIT
  , inputs := [ .digest 0, .digest 1, .digest 2, .col (auxCol aux_off.STATE_RECORD_DIGEST) ]
  , arity := 4 }

/-- The ordered GROUP-4 hash sites (site `i` ↔ aux block `i`, the Rust `hash_sites()` contract). -/
def transferHashSites : List VmHashSite := [site0, site1, site2, site3]

/-! ## §4 — The emitted TRANSFER descriptor. -/

/-- The transfer AIR identity (carried for the fingerprint binding). -/
def transferVmAirName : String := "dregg-effectvm-transfer-v1"

/-- The transfer-specialized per-row gates (balance lo/hi, direction bool, nonce, frame). -/
def transferRowGates : List VmConstraint :=
  [ .gate gBalLo, .gate gBalHi, .gate gDirBool, .gate gNonce
  , .gate gCapPass, .gate gResPass ] ++ gFieldPassAll

/-- **`transferVmDescriptor`** — the TRANSFER effect's full concrete circuit, emitted through the
EffectVM IR: the per-row debit/credit/nonce/frame gates ++ transition continuity ++ the 7
boundary PI pins, with the 4 ordered GROUP-4 hash sites and the 2 balance-limb range checks. -/
def transferVmDescriptor : EffectVmDescriptor :=
  { name := transferVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := transferRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
                     ++ selectorGates sel.TRANSFER
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §5 — The TRANSFER ROW INTENT (the independent faithfulness target).

`TransferRowIntent` is the field-level transfer move, written from protocol intent (NOT from the
gate bodies): on a transfer row, the new balance is the old balance moved by `amount` in the
direction sign, the hi limb and the whole frame (cap/reserved/8 fields) are FIXED, the nonce
ticks by one, and `direction` is a bit. This is the EffectVM-row projection of
`CircuitSpecTriangle.intentTransfer`'s debit-src/credit-dst (here the actor cell's own limb moves
by the signed amount; `direction = 1` debits, `direction = 0` credits). -/

/-- **`TransferRowIntent env`** — the intended transfer move on the row `env.loc`. -/
def TransferRowIntent (env : VmRowEnv) : Prop :=
  -- direction is a bit
  (env.loc (prmCol param.DIRECTION) = 0 ∨ env.loc (prmCol param.DIRECTION) = 1)
  -- balance lo moves by the signed amount: new = old + amount·(1 - 2·direction)
  ∧ env.loc (saCol state.BALANCE_LO)
      = env.loc (sbCol state.BALANCE_LO)
        + env.loc (prmCol param.AMOUNT) * (1 - 2 * env.loc (prmCol param.DIRECTION))
  -- balance hi unchanged
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  -- nonce ticks by one
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE) + 1
  -- cap root + reserved fixed
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  -- the 8 fields fixed
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §6 — The transfer-row environment hypothesis (selectors).

On a genuine transfer row the transfer selector is `1` and the noop selector is `0` (GROUP-1
selector validity + sum-to-one forces exactly one selector hot). `IsTransferRow` names this; it
is what the running prover's `s_transfer = 1`, `s_noop = 0` factoring relies on. -/

/-- The row is a transfer row: `s_transfer = 1`, `s_noop = 0`. -/
def IsTransferRow (env : VmRowEnv) : Prop :=
  env.loc sel.TRANSFER = 1 ∧ env.loc sel.NOOP = 0

/-! ## §7 — FAITHFULNESS: the emitted per-row gates ⟺ the intent.

The load-bearing theorem: on a transfer row, the emitted descriptor's per-row gates
(`transferRowGates`) all hold IFF `TransferRowIntent` holds. The gate bodies are the SAME
polynomials the running prover asserts (specialized to the transfer row), and they pin EXACTLY
the intent move — so the concrete EffectVM circuit enforces the verified intent. -/

/-- Helper: every gate in `transferRowGates` holds means each body vanishes on `env.loc`. -/
theorem transferRowGates_holds_iff (env : VmRowEnv) (hrow : IsTransferRow env) :
    (∀ c ∈ transferRowGates, c.holdsVm env false false) ↔ TransferRowIntent env := by
  obtain ⟨_hsT, hsN⟩ := hrow
  unfold transferRowGates gFieldPassAll TransferRowIntent
  constructor
  · intro h
    -- extract each gate from membership
    have hLo := h (.gate gBalLo) (by simp)
    have hHi := h (.gate gBalHi) (by simp)
    have hDir := h (.gate gDirBool) (by simp)
    have hNon := h (.gate gNonce) (by simp)
    have hCap := h (.gate gCapPass) (by simp)
    have hRes := h (.gate gResPass) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldPass i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    -- unfold each holds
    simp only [VmConstraint.holdsVm, gBalLo, gBalHi, gDirBool, gNonce, gCapPass, gResPass,
      eSA, eSB, ePrm, eSub, eSelNoop, EmittedExpr.eval] at hLo hHi hDir hNon hCap hRes
    rw [hsN] at hNon
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- direction bit, from direction·(direction-1) = 0
      have hd0 : env.loc (prmCol param.DIRECTION)
                  * (env.loc (prmCol param.DIRECTION) + -1) = 0 := hDir
      rcases mul_eq_zero.mp hd0 with hd | hd
      · exact Or.inl hd
      · exact Or.inr (by linarith)
    · -- balance lo move: hLo is `(new - old) + (-amount + 2·(dir·amount)) = 0`.
      nlinarith [hLo]
    · linarith [hHi]
    · -- nonce: hNon is `(new - old) - (1 - 0) = 0`.
      linarith [hNon]
    · linarith [hCap]
    · linarith [hRes]
    · intro i hi
      have := hFld i hi
      simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval] at this
      linarith
  · rintro ⟨hDir, hLo, hHi, hNon, hCap, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    -- dispatch by which gate `c` is
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · -- gBalLo
      simp only [VmConstraint.holdsVm, gBalLo, eSA, eSB, ePrm, eSub, EmittedExpr.eval]
      rw [hLo]; ring
    · -- gBalHi
      simp only [VmConstraint.holdsVm, gBalHi, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hHi]; ring
    · -- gDirBool
      simp only [VmConstraint.holdsVm, gDirBool, ePrm, EmittedExpr.eval]
      rcases hDir with hd | hd <;> rw [hd] <;> ring
    · -- gNonce
      simp only [VmConstraint.holdsVm, gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
      rw [hsN, hNon]; ring
    · -- gCapPass
      simp only [VmConstraint.holdsVm, gCapPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hCap]; ring
    · -- gResPass
      simp only [VmConstraint.holdsVm, gResPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hRes]; ring
    · -- gFieldPass i
      simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hFld i hi]; ring

/-- **`transferVm_faithful` — THE deliverable (the load-bearing direction + converse).** On a
transfer row, the emitted descriptor's per-row gates hold IFF the transfer intent holds. So the
concrete EffectVM transfer circuit the Rust prover runs enforces EXACTLY the verified intent move
(`TransferRowIntent` = the EffectVM-row projection of `CircuitSpecTriangle.intentTransfer`). -/
theorem transferVm_faithful (env : VmRowEnv) (hrow : IsTransferRow env) :
    (∀ c ∈ transferRowGates, c.holdsVm env false false) ↔ TransferRowIntent env :=
  transferRowGates_holds_iff env hrow

/-! ## §8 — ANTI-GHOST: a wrong-output transfer row fails the emitted descriptor.

The contrapositive of `transferVm_faithful`: any transfer row whose post-state is NOT the intent
move (wrong balance, wrong nonce tick, tampered frame) violates some per-row gate, so the emitted
descriptor is UNSAT for it. -/

/-- **Anti-ghost (general).** A transfer row whose post-state is NOT the intent move does NOT
satisfy the per-row gates. -/
theorem transferVm_rejects_wrong_output (env : VmRowEnv) (hrow : IsTransferRow env)
    (hwrong : ¬ TransferRowIntent env) :
    ¬ (∀ c ∈ transferRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((transferVm_faithful env hrow).mp h)

/-- **Anti-ghost (balance tamper).** A transfer row whose post-`bal_lo` is NOT the signed move has
no satisfying gate set — the `gBalLo` gate alone rejects it (UNSAT). -/
theorem transferVm_rejects_wrong_balance (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO)
      ≠ env.loc (sbCol state.BALANCE_LO)
        + env.loc (prmCol param.AMOUNT) * (1 - 2 * env.loc (prmCol param.DIRECTION))) :
    ¬ (VmConstraint.gate gBalLo).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLo, eSA, eSB, ePrm, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

/-- **Anti-ghost (nonce tamper).** A transfer row whose nonce does NOT tick by one (`s_noop = 0`)
fails the `gNonce` gate. -/
theorem transferVm_rejects_wrong_nonce (env : VmRowEnv) (hsN : env.loc sel.NOOP = 0)
    (hwrong : env.loc (saCol state.NONCE) ≠ env.loc (sbCol state.NONCE) + 1) :
    ¬ (VmConstraint.gate gNonce).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
  intro h
  apply hwrong
  rw [hsN] at h
  linarith

/-! ## §9 — Boundary + transition faithfulness (the PI/continuity clauses pin the turn boundary).

The boundary/transition constraints are pure equalities, so their denotation is exactly the
intended pin. We expose them as faithfulness lemmas: a satisfying descriptor pins row-0
`state_before` to the OLD commitment / init balances / actor nonce, and the last row's
`state_after.state_commit` to the NEW commitment. -/

/-- The row-0 boundary pins, when satisfied on the first row, force `state_before`'s
nonce/balances/commitment to the public inputs (turn-identity binding). -/
theorem boundaryFirst_pins (env : VmRowEnv)
    (h : ∀ c ∈ boundaryFirstPins, c.holdsVm env true false) :
    env.loc (sbCol state.NONCE) = env.pub pi.ACTOR_NONCE
    ∧ env.loc (sbCol state.BALANCE_LO) = env.pub pi.INIT_BAL_LO
    ∧ env.loc (sbCol state.BALANCE_HI) = env.pub pi.INIT_BAL_HI
    ∧ env.loc (sbCol state.STATE_COMMIT) = env.pub pi.OLD_COMMIT := by
  have key : ∀ col k, VmConstraint.piBinding VmRow.first col k ∈ boundaryFirstPins →
      env.loc col = env.pub k := by
    intro col k hmem
    have hh := h _ hmem
    simp only [VmConstraint.holdsVm] at hh
    exact hh trivial
  refine ⟨key _ _ ?_, key _ _ ?_, key _ _ ?_, key _ _ ?_⟩ <;>
    · unfold boundaryFirstPins; simp

/-- The last-row boundary pins force `state_after.state_commit` to `NEW_COMMIT` (the published
post-state commitment) and the final balances to their PIs. -/
theorem boundaryLast_pins (env : VmRowEnv)
    (h : ∀ c ∈ boundaryLastPins, c.holdsVm env false true) :
    env.loc (saCol state.STATE_COMMIT) = env.pub pi.NEW_COMMIT
    ∧ env.loc (saCol state.BALANCE_LO) = env.pub pi.FINAL_BAL_LO
    ∧ env.loc (saCol state.BALANCE_HI) = env.pub pi.FINAL_BAL_HI := by
  have key : ∀ col k, VmConstraint.piBinding VmRow.last col k ∈ boundaryLastPins →
      env.loc col = env.pub k := by
    intro col k hmem
    have hh := h _ hmem
    simp only [VmConstraint.holdsVm] at hh
    exact hh trivial
  refine ⟨key _ _ ?_, key _ _ ?_, key _ _ ?_⟩ <;>
    · unfold boundaryLastPins; simp

/-! ## §10 — The hash-chain binding: the published commitment IS the genuine digest of the
after-state (under the abstract Poseidon carrier).

`transferHashSites` satisfied means `state_after.state_commit = H4(inter1, inter2, inter3, 0)`
with the inters the genuine `H4` of the after-state cells — the GROUP-4 anti-ghost that pins the
WHOLE post-state into the commitment. -/

/-- A satisfying hash-site set forces `state_after.state_commit` to the genuine 4-level digest of
the after-state (abstract `hash`). The site ORDER is load-bearing: site 3 reads sites 0/1/2's
digests, exactly as the running prover's `digests[3] = H4(digests[0], digests[1], digests[2], 0)`. -/
theorem transferHash_binds (hash : List ℤ → ℤ) (env : VmRowEnv)
    (h : siteHoldsAll hash env transferHashSites) :
    env.loc (saCol state.STATE_COMMIT)
      = hash [ hash [ env.loc (saCol state.BALANCE_LO), env.loc (saCol state.BALANCE_HI)
                    , env.loc (saCol state.NONCE), env.loc (saCol (state.FIELD_BASE + 0)) ]
             , hash [ env.loc (saCol (state.FIELD_BASE + 1)), env.loc (saCol (state.FIELD_BASE + 2))
                    , env.loc (saCol (state.FIELD_BASE + 3)), env.loc (saCol (state.FIELD_BASE + 4)) ]
             , hash [ env.loc (saCol (state.FIELD_BASE + 5)), env.loc (saCol (state.FIELD_BASE + 6))
                    , env.loc (saCol (state.FIELD_BASE + 7)), env.loc (saCol state.CAP_ROOT) ]
             , env.loc (auxCol aux_off.STATE_RECORD_DIGEST) ] := by
  -- unfold the ordered site walk: sites 0,1,2,3 in order.
  unfold siteHoldsAll transferHashSites at h
  simp only [siteHoldsAll.go, site0, site1, site2, site3, VmHashSite.resolvedInputs,
    HashInput.resolve, List.map_cons, List.map_nil, List.getD] at h
  obtain ⟨h0, h1, h2, h3, _⟩ := h
  -- h3 : env.loc (saCol STATE_COMMIT) = hash [d0, d1, d2, 0]; substitute the inter digests.
  rw [h3]
  -- the accumulator at site 3 is [d0, d1, d2]; its getD 0/1/2 are d0/d1/d2.
  rfl

/-! ## §11 — Putting it together: the satisfied descriptor pins the intent + boundary + commitment.

`transferVmDescriptor_pins_intent`: a transfer row satisfying the WHOLE emitted descriptor (gates
+ transitions + boundaries + hash sites) on the LAST row of the trace realizes the transfer intent
AND publishes the genuine post-state commitment. This is the corner-(b) statement at the concrete
EffectVM level: the running circuit's satisfaction ⇒ the verified intent. -/

/-- **`transferVmDescriptor_pins_intent` — corner (b), concrete.** A transfer row satisfying the
whole emitted descriptor realizes `TransferRowIntent` and binds the published `state_commit` to the
genuine digest of the after-state. (The first/last flags are taken `true` for the single-row trace
window so the boundary clauses are active; on a multi-row trace the same holds per-row with the
flags as supplied.) -/
theorem transferVmDescriptor_pins_intent (hash : List ℤ → ℤ) (env : VmRowEnv)
    (hrow : IsTransferRow env)
    (hsat : satisfiedVm hash transferVmDescriptor env true true) :
    TransferRowIntent env
    ∧ env.loc (saCol state.STATE_COMMIT) = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _hsites⟩ := hsat
  -- the per-row gates are a sub-list of the descriptor's constraints.
  have hgates : ∀ c ∈ transferRowGates, c.holdsVm env true true := by
    intro c hc
    apply hcs
    unfold transferVmDescriptor
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
  -- the per-row gates' `holdsVm` is flag-independent (gate clause ignores isFirst/isLast).
  have hgates' : ∀ c ∈ transferRowGates, c.holdsVm env false false := by
    intro c hc
    have := hgates c hc
    -- transferRowGates are all `.gate _`, whose holdsVm ignores the flags.
    unfold transferRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  refine ⟨(transferVm_faithful env hrow).mp hgates', ?_⟩
  -- last-row boundary pin: state_after.state_commit = PI[NEW_COMMIT].
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ transferVmDescriptor.constraints := by
      unfold transferVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inr hc)
    have hh := hcs c hmem
    -- boundaryLastPins are `.piBinding .last …`; holdsVm under (true,true) ⟹ under (false,true).
    unfold boundaryLastPins at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      · simp only [VmConstraint.holdsVm] at hh ⊢
        exact hh
  exact (boundaryLast_pins env hlast).1

/-! ## §11.5 — NON-VACUITY: a concrete transfer row that satisfies the intent, and one that does not.

The faithfulness biconditional is only meaningful if BOTH sides are inhabited and refutable. We
exhibit a concrete row `goodRow` (outgoing transfer of 30 from a cell with bal_lo 100 → 70, nonce
5 → 6, frame fixed) that REALIZES `TransferRowIntent` — and `badRow` (same but post-`bal_lo`
forged to 999) that VIOLATES it, so `transferVm_rejects_wrong_output` fires concretely. -/

/-- A concrete environment: a transfer row. `loc` reads the named EffectVM columns; everything
unmentioned is `0`. Outgoing (`direction = 1`) transfer of `amount = 30`: `bal_lo 100 → 70`,
`nonce 5 → 6`, frame (cap/reserved/fields) fixed at `0`. -/
def goodRow : VmRowEnv where
  loc := fun v =>
    if v = sel.TRANSFER then 1
    else if v = sbCol state.BALANCE_LO then 100
    else if v = saCol state.BALANCE_LO then 70
    else if v = sbCol state.NONCE then 5
    else if v = saCol state.NONCE then 6
    else if v = prmCol param.AMOUNT then 30
    else if v = prmCol param.DIRECTION then 1
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- `goodRow` is a genuine transfer row. -/
theorem goodRow_isTransferRow : IsTransferRow goodRow := by
  unfold IsTransferRow goodRow
  constructor <;> norm_num [sel.TRANSFER, sel.NOOP, sbCol, saCol, prmCol, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
    state.NONCE, param.AMOUNT, param.DIRECTION]

/-- **NON-VACUITY (witness TRUE).** `goodRow` REALIZES the transfer intent: bal_lo moves
`100 → 70 = 100 + 30·(1 - 2·1)`, hi/frame fixed, nonce `5 → 6`. So the faithfulness biconditional's
intent side is inhabited (not `False`). -/
theorem goodRow_realizes_intent : TransferRowIntent goodRow := by
  unfold TransferRowIntent goodRow
  simp only [sbCol, saCol, prmCol, sel.TRANSFER, STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE,
    NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.BALANCE_HI, state.NONCE,
    state.CAP_ROOT, state.RESERVED, state.FIELD_BASE, param.AMOUNT, param.DIRECTION]
  refine ⟨Or.inr ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · norm_num
  · rfl
  · rfl
  · rfl
  · rfl
  · intro i hi
    -- both `state_after.field[i]` (col 79+i) and `state_before.field[i]` (col 57+i) miss every
    -- named column of `goodRow`, so both sides are the final `else 0`.
    have e1 : (76 + (3 + i) = 1) = False := by simp; omega
    have e2 : (76 + (3 + i) = 54) = False := by simp; omega
    have e3 : (76 + (3 + i) = 76) = False := by simp
    have e4 : (76 + (3 + i) = 56) = False := by simp; omega
    have e5 : (76 + (3 + i) = 78) = False := by simp; omega
    have e6 : (76 + (3 + i) = 68) = False := by simp; omega
    have e7 : (76 + (3 + i) = 69) = False := by simp; omega
    have f1 : (54 + (3 + i) = 1) = False := by simp; omega
    have f2 : (54 + (3 + i) = 54) = False := by simp
    have f3 : (54 + (3 + i) = 76) = False := by simp; omega
    have f4 : (54 + (3 + i) = 56) = False := by simp; omega
    have f5 : (54 + (3 + i) = 78) = False := by simp; omega
    have f6 : (54 + (3 + i) = 68) = False := by simp; omega
    have f7 : (54 + (3 + i) = 69) = False := by simp; omega
    simp only [e1, e2, e3, e4, e5, e6, e7, f1, f2, f3, f4, f5, f6, f7, if_false]

/-- A FORGED transfer row: `goodRow` with the post-`bal_lo` tampered to `999` (a value not equal
to the intended `70`). -/
def badRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodRow.loc v
  nxt := goodRow.nxt
  pub := goodRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badRow`'s post-`bal_lo` is NOT the
signed move, so the `gBalLo` gate REJECTS it — a concrete UNSAT, the anti-ghost end-to-end. -/
theorem badRow_rejected : ¬ (VmConstraint.gate gBalLo).holdsVm badRow false false := by
  apply transferVm_rejects_wrong_balance
  simp only [badRow, goodRow, sbCol, saCol, prmCol, sel.TRANSFER, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
    state.NONCE, param.AMOUNT, param.DIRECTION]
  norm_num

/-! ## §11.5 — THE FEE DEBIT (trust-surface hole #5 close).

The deployed sovereign turn debits `turn.fee` from the actor cell in executor PHASE 1, BEFORE
proving; the proof was then built over the PRE-fee balance and the verifier blindly UNDID the
debit (`pre_balance = post_fee_balance + turn.fee`) from the TRUSTED `turn.fee`. So the fee debit
was NOT a constraint in the proven transition — a ledgerless light client could not verify the fee
was correctly taken. For a sovereign turn the fee is debited from the SAME cell the rotated proof
covers, so the fee debit becomes a balance constraint IN that proof.

The MECHANISM (off the ROT_WIDTH flag-day — no new committed column, no pre-limb geometry change):
the fee rides in the after-block `RESERVED` state column (`saCol state.RESERVED`), which is dead
weight in the v1 layout (a pure `before == after` passthrough, NOT absorbed into the state
commitment, NOT welded into any rotated pre-limb). The balance-lo gate is AUGMENTED to subtract the
fee column as well as the transfer move (`new = old − transfer − fee`), so the proven FINAL_BAL —
the value `NEW_COMMIT` binds — is the POST-fee balance the executor's PHASE-1 debit produced. The
rotated leg then pins the fee column to a published fee PI (`rotateV3WithFeePin`,
`EffectVmEmitRotationV3`), so the verifier's published `turn.fee` is FORCED equal to the balance
the proof actually moved. A proof claiming a SMALLER fee than the balance moved, or a fee not
debited (`post ≠ pre − transfer − fee`), is UNSAT — no trusted reconstruction. -/

/-- The fee column: the after-block `RESERVED` state limb carries `turn.fee`. Dead weight in the
unfee'd transfer (passthrough, commitment-free), repurposed here as the published fee carrier. -/
def feeCol : Nat := saCol state.RESERVED

/-- Balance-lo debit/credit body WITH the fee debit: `new_bal_lo − old_bal_lo − amount + 2·dir·amount
+ fee`. On a fee'd transfer row this forces `new = old − amount·(1−2·dir) − fee` — the transfer move
AND the fee debit, both on the actor's lo limb. -/
def gBalLoFee : EmittedExpr :=
  .add gBalLo (.var feeCol)

/-- The fee'd per-row gates: the transfer gates with `gBalLo` swapped for `gBalLoFee` and the
RESERVED passthrough `gResPass` DROPPED (RESERVED now carries the fee, so it is no longer frozen). -/
def transferFeeRowGates : List VmConstraint :=
  [ .gate gBalLoFee, .gate gBalHi, .gate gDirBool, .gate gNonce, .gate gCapPass ] ++ gFieldPassAll

/-- **`transferFeeVmDescriptor`** — the fee'd TRANSFER descriptor: identical to `transferVmDescriptor`
except the balance-lo gate also debits the fee column and RESERVED is no longer frozen (it carries
the fee). The fee column gets a 30-bit range check (a fee near the field modulus would WRAP and forge
a negative debit — the field-soundness tooth). The rotated leg (`rotateV3WithFeePin`) pins the fee
column to the published fee PI. -/
def transferFeeVmDescriptor : EffectVmDescriptor :=
  { name := transferVmAirName ++ "-fee"
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := transferFeeRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
                     ++ selectorGates sel.TRANSFER
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩, ⟨feeCol, 30⟩ ] }

/-- **`TransferFeeRowIntent env`** — the intended fee'd transfer move: the balance lo moves by the
signed transfer amount AND the fee is debited; everything else (hi limb, nonce tick, cap_root, the 8
fields) matches the unfee'd intent. RESERVED is NO LONGER frozen (it carries the fee). -/
def TransferFeeRowIntent (env : VmRowEnv) : Prop :=
  (env.loc (prmCol param.DIRECTION) = 0 ∨ env.loc (prmCol param.DIRECTION) = 1)
  ∧ env.loc (saCol state.BALANCE_LO)
      = env.loc (sbCol state.BALANCE_LO)
        + env.loc (prmCol param.AMOUNT) * (1 - 2 * env.loc (prmCol param.DIRECTION))
        - env.loc feeCol
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE) + 1
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-- **`transferFeeVm_faithful` — the fee'd deliverable.** On a transfer row, the fee'd descriptor's
per-row gates hold IFF the fee'd transfer intent holds. So the concrete circuit enforces EXACTLY
`new = old − transfer − fee` — the fee debit is now a proven balance constraint. -/
theorem transferFeeVm_faithful (env : VmRowEnv) (hrow : IsTransferRow env) :
    (∀ c ∈ transferFeeRowGates, c.holdsVm env false false) ↔ TransferFeeRowIntent env := by
  obtain ⟨_hsT, hsN⟩ := hrow
  unfold transferFeeRowGates gFieldPassAll TransferFeeRowIntent
  constructor
  · intro h
    have hLo := h (.gate gBalLoFee) (by simp)
    have hHi := h (.gate gBalHi) (by simp)
    have hDir := h (.gate gDirBool) (by simp)
    have hNon := h (.gate gNonce) (by simp)
    have hCap := h (.gate gCapPass) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldPass i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gBalLoFee, gBalLo, gBalHi, gDirBool, gNonce, gCapPass,
      eSA, eSB, ePrm, eSub, eSelNoop, EmittedExpr.eval] at hLo hHi hDir hNon hCap
    rw [hsN] at hNon
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hd0 : env.loc (prmCol param.DIRECTION)
                  * (env.loc (prmCol param.DIRECTION) + -1) = 0 := hDir
      rcases mul_eq_zero.mp hd0 with hd | hd
      · exact Or.inl hd
      · exact Or.inr (by linarith)
    · nlinarith [hLo]
    · linarith [hHi]
    · linarith [hNon]
    · linarith [hCap]
    · intro i hi
      have := hFld i hi
      simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval] at this
      linarith
  · rintro ⟨hDir, hLo, hHi, hNon, hCap, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · simp only [VmConstraint.holdsVm, gBalLoFee, gBalLo, eSA, eSB, ePrm, eSub, EmittedExpr.eval]
      rw [hLo]; ring
    · simp only [VmConstraint.holdsVm, gBalHi, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hHi]; ring
    · simp only [VmConstraint.holdsVm, gDirBool, ePrm, EmittedExpr.eval]
      rcases hDir with hd | hd <;> rw [hd] <;> ring
    · simp only [VmConstraint.holdsVm, gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
      rw [hsN, hNon]; ring
    · simp only [VmConstraint.holdsVm, gCapPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hCap]; ring
    · simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hFld i hi]; ring

/-- **Anti-ghost (fee tamper / the light-client tooth).** A fee'd transfer row whose post-`bal_lo`
is NOT `old − transfer − fee` — i.e. the published fee column claims a SMALLER fee than the balance
actually moved, or the fee was not debited — fails the `gBalLoFee` gate (UNSAT). This is the
in-circuit bite: a ledgerless verifier needs NO trusted `+ turn.fee` reconstruction. -/
theorem transferFeeVm_rejects_wrong_fee (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO)
      ≠ env.loc (sbCol state.BALANCE_LO)
        + env.loc (prmCol param.AMOUNT) * (1 - 2 * env.loc (prmCol param.DIRECTION))
        - env.loc feeCol) :
    ¬ (VmConstraint.gate gBalLoFee).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoFee, gBalLo, eSA, eSB, ePrm, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

/-! ## §12 — Axiom-hygiene pins (the honesty tripwire). -/

#guard transferVmDescriptor.constraints.length == 14 + 14 + 4 + 3 + 1  -- gates+transitions+4first+3last+selectorGate
#guard transferVmDescriptor.hashSites.length == 4
#guard transferVmDescriptor.ranges.length == 2
#guard transferVmDescriptor.traceWidth == 187

-- The fee'd descriptor: one fewer per-row gate (RESERVED passthrough dropped), one more range check.
#guard transferFeeVmDescriptor.constraints.length == 13 + 14 + 4 + 3 + 1
#guard transferFeeVmDescriptor.ranges.length == 3
#guard transferFeeVmDescriptor.traceWidth == 187
#assert_axioms transferFeeVm_faithful
#assert_axioms transferFeeVm_rejects_wrong_fee

#assert_axioms transferRowGates_holds_iff
#assert_axioms transferVm_faithful
#assert_axioms transferVm_rejects_wrong_output
#assert_axioms transferVm_rejects_wrong_balance
#assert_axioms transferVm_rejects_wrong_nonce
#assert_axioms transferHash_binds
#assert_axioms boundaryFirst_pins
#assert_axioms boundaryLast_pins
#assert_axioms transferVmDescriptor_pins_intent
#assert_axioms goodRow_realizes_intent
#assert_axioms badRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitTransfer
