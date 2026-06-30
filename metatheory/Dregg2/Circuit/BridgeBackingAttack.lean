/-
# Dregg2.Circuit.BridgeBackingAttack — ADVERSARIAL soundness audit of the deployed bridge-mint's
  foreign-spend backing (the G1 analog of `CustomCarrierAttack`).

This module attacks the deployed inbound-bridge-mint member head-on, IN LEAN, importing everything
read-only. It is a refutation file: the load-bearing arms are proved WITHOUT `sorry`, and the
conclusion is stated precisely.

## The target

A `BridgeMint` row credits the cell's balance by `value_lo` (`prmCol 1`) and carries a `mint_hash`
(`prmCol 0`) that the executor computes as a digest binding the foreign note-spend tuple
(nullifier, root, dest_federation, asset_type). The OFF-AIR verifier
(`turn::executor::apply::apply_bridge_mint`) re-runs the bespoke note-spend STARK
(`verify_note_spend_dsl_full`) against that tuple and consumes the `lock_id` nullifier
(`bridge_ledger.rs::bridge_mint_against_lock`) — but those checks live OUTSIDE the deployed
effect-vm AIR.

The deployed bridge-mint descriptor (`EffectVmEmitBridgeMint.bridgeMintVmDescriptor`, the
`mintVmDescriptor2R24` member) gates ONLY the balance credit + frame freeze + nonce tick + the
`state_commit` absorption (`bridgeMintVm_faithful` / `bridgeMintDescriptor_full_sound`). It has NO
proof-binding op and reads `mint_hash` (`prmCol 0`) in NONE of its constraints — so for a PURE LIGHT
CLIENT (one that only verifies the per-turn recursion tree) a `BridgeMint` credits balance with NO
witnessed backing. This is even starker than the custom carrier: custom at least carries a
(deployed-vacuous) `proofBind` op; the deployed bridge-mint has no in-AIR backing hook at all.

This is the SAME vacuity CLASS that `CustomCarrierAttack` proves for `Effect::Custom`: real as
re-executed, vacuous as deployed-light-client.

## What is proved here

§A `deployed_admits_unbacked_bridge` — the explicit FORGED bridge mint. A note-spend engine whose
   only verifying proof exposes spend-digest `123`, and an HONEST-looking bridge-mint row that
   SATISFIES the deployed descriptor's row intent (`BridgeMintRowIntent`: credit `value_lo`, freeze
   the frame, tick the nonce) while its published `mint_hash` is `0` — a digest NO verifying
   foreign spend backs. The deployed descriptor accepts it; the (staged) backing predicate rejects
   it. The deployed AIR admits a bridge mint whose foreign-spend backing does NOT verify.

§B `deployed_intent_does_not_force_backing` — there is NO uniform bridge "deployed-accepts ⟹
   backed": §A is the counterexample. So a light client that only checks the deployed bridge-mint
   AIR learns NOTHING about the foreign spend. The repair (the backing must come from the FOLD over
   the re-proved bridge-action / note-spend leaf) is named at §C, mirroring `CustomBindingFromFold`.

§C the consumed-nullifier corollary + the repair pointer. Even a `mint_hash` a verifying spend
   backs is accepted by the deployed descriptor when the spend's nullifier is ALREADY consumed
   (`deployed_admits_consumed_nullifier`) — the consume-once guard is the RE-EXEC tooth
   (`bridge_ledger.rs::bridge_mint_against_lock`, an atomic contains-then-insert over the committed
   `note_nullifiers` set), NOT a light-client one.

## Axiom hygiene
`#assert_axioms` on every load-bearing arm ⊆ {propext, Classical.choice, Quot.sound}. NO new axiom,
NO `sorry`. NEW file; all imports read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitBridgeMint

namespace Dregg2.Circuit.BridgeBackingAttack

open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitBridgeMint

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §0 — the foreign note-spend engine + the (staged) backing predicate.

A `NoteSpendEngine` abstracts the bespoke note-spend STARK the off-AIR verifier runs: `verify` is
its accepting bit, `spendDigest` is the `mint_hash` a VERIFYING spend exposes (the digest binding
nullifier/root/dest_federation/asset_type), and `nullifier` is the consumed `lock_id`. This is the
bridge analog of `CustomApex.ProofEngine` (`verify` + `piCommit`). -/

/-- An abstract foreign note-spend engine: its accepting bit, the `mint_hash` a verifying spend
exposes, and the spend's nullifier (the consume-once `lock_id`). -/
structure NoteSpendEngine where
  /-- The proof type of the foreign note-spend STARK. -/
  Proof : Type
  /-- The verifier's accepting bit. -/
  verify : Proof → Bool
  /-- The `mint_hash` digest a VERIFYING spend exposes (binds nullifier/root/dest_fed/asset_type). -/
  spendDigest : Proof → ℤ
  /-- The spend's nullifier (the consume-once `lock_id` the bridge ledger dedups). -/
  nullifier : Proof → ℤ

/-- The deployed bridge-mint row's `mint_hash` column: `param0` (`prmCol 0`). -/
def mintHashCol : Nat := prmCol 0

/-- The `mint_hash` a row publishes (the digest the off-AIR verifier checks the foreign spend
against). -/
def mintHashOf (env : VmRowEnv) : ℤ := env.loc mintHashCol

/-- **`BackedAt E consumed env`** — the STAGED backing predicate the deployed descriptor SHOULD (but
does not) enforce: the row's published `mint_hash` is the digest of SOME verifying foreign spend
whose nullifier is NOT already consumed. This is the bridge analog of
`CustomApex.ProofBind.boundAt` (the staged `proofBind` gate) — the content the deployed AIR omits. -/
def BackedAt (E : NoteSpendEngine) (consumed : ℤ → Prop) (env : VmRowEnv) : Prop :=
  ∃ q : E.Proof, E.verify q = true ∧ E.spendDigest q = mintHashOf env ∧ ¬ consumed (E.nullifier q)

/-! ## §A — the forged bridge mint: deployed-accepts what the backing predicate rejects.

We reuse the in-tree `goodBridgeMintRow` (an honest-looking bridge-mint row that already satisfies
the deployed row intent, `goodBridgeMintRow_realizes_intent`) whose published `mint_hash` (`prmCol
0`) is `0`. Against a demo engine whose ONLY verifying spend exposes digest `123`, the digest `0` is
backed by no verifying spend — yet the deployed descriptor accepts the row. -/

/-- A demo foreign-spend engine: the only verifying proof (`true`) exposes spend-digest `123` and
nullifier `7` (the same one-verifying-proof shape `CustomCarrierAttack.demoEngine` uses). -/
def demoSpend : NoteSpendEngine where
  Proof := Bool
  verify := fun b => b
  spendDigest := fun _ => 123
  nullifier := fun _ => 7

/-- No nullifier is consumed (the honest fresh-mint baseline). -/
def noneConsumed : ℤ → Prop := fun _ => False

/-- The forged bridge-mint row's published `mint_hash` is `0` — a digest NO verifying spend of
`demoSpend` exposes (the only verifying spend exposes `123`). -/
theorem mintHash_goodRow : mintHashOf goodBridgeMintRow = 0 := by
  simp only [mintHashOf, mintHashCol, prmCol, goodBridgeMintRow, selBM.BRIDGE_MINT, sbCol, saCol,
    STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS,
    state.BALANCE_LO, state.NONCE, param.BRIDGE_MINT_VALUE_LO]
  decide

/-- **The deployed descriptor ACCEPTS the forged row.** `goodBridgeMintRow` is a bridge-mint row
(`IsBridgeMintRow`) realizing the full deployed row intent (`BridgeMintRowIntent`: balance credited
by `value_lo`, frame frozen, nonce ticked) — the deployed bridge-mint member's per-row content. -/
theorem forged_deployed_accepts :
    IsBridgeMintRow goodBridgeMintRow ∧ BridgeMintRowIntent goodBridgeMintRow :=
  ⟨goodBridgeMintRow_isRow, goodBridgeMintRow_realizes_intent⟩

/-- **The forged row is REJECTED by the (staged) backing predicate.** Its `mint_hash` is `0`; the
only verifying spend of `demoSpend` exposes `123`, so no verifying spend backs it — `BackedAt`
fails. The deployed descriptor cannot detect this: it never reads `mint_hash`. -/
theorem forged_not_backed : ¬ BackedAt demoSpend noneConsumed goodBridgeMintRow := by
  rintro ⟨q, _hv, hd, _hfresh⟩
  -- demoSpend.spendDigest q ≡ 123 (defeq); mintHashOf goodBridgeMintRow = 0; 123 = 0 is false.
  rw [mintHash_goodRow] at hd
  simp only [demoSpend] at hd
  exact absurd hd (by decide)

/-- **§A keystone — `deployed_admits_unbacked_bridge`.** ∃ a foreign-spend engine and a bridge-mint
row that SATISFIES the deployed descriptor's row intent (credit + frame freeze + nonce tick) yet
whose published `mint_hash` is backed by NO verifying foreign spend: the deployed AIR admits a
bridge mint whose foreign-spend backing does not verify. This is the explicit forged bridge mint
the deployed circuit (and thus a pure light client) cannot detect — the G1 analog of
`CustomCarrierAttack.deployed_admits_unbacked`. -/
theorem deployed_admits_unbacked_bridge :
    ∃ (E : NoteSpendEngine) (consumed : ℤ → Prop) (env : VmRowEnv),
      (IsBridgeMintRow env ∧ BridgeMintRowIntent env) ∧ ¬ BackedAt E consumed env :=
  ⟨demoSpend, noneConsumed, goodBridgeMintRow, forged_deployed_accepts, forged_not_backed⟩

/-! ## §B — the deployed bridge-mint AIR does not force the backing. -/

/-- **§B keystone — `deployed_intent_does_not_force_backing`.** There is NO uniform implication
"the deployed bridge-mint row intent holds ⟹ the foreign spend is backed": §A exhibits a row whose
deployed intent holds while no verifying spend backs its `mint_hash`. So consuming a backing claim
against the deployed bridge-mint AIR asserts strictly MORE than the verifier enforces — the deployed
descriptor binds only the balance credit (`value_lo`), never the foreign-spend backing. The real
backing must come from the per-turn FOLD over the re-proved bridge-action / note-spend leaf (the
`bridge_leaf_adapter` leaf connected to the published `mint_hash` PI), exactly as
`CustomBindingFromFold` rebuilds the custom binding from `AggAirSound` — see §C. -/
theorem deployed_intent_does_not_force_backing :
    ¬ ∀ (E : NoteSpendEngine) (consumed : ℤ → Prop) (env : VmRowEnv),
        (IsBridgeMintRow env ∧ BridgeMintRowIntent env) → BackedAt E consumed env := by
  intro hbridge
  exact forged_not_backed (hbridge demoSpend noneConsumed goodBridgeMintRow forged_deployed_accepts)

/-! ## §C — the consumed-nullifier corollary + the repair pointer.

The deployed descriptor equally fails to witness nullifier FRESHNESS. Even a `mint_hash` that a
verifying spend backs is accepted by the deployed descriptor when that spend's nullifier is already
consumed: the consume-once guard is the RE-EXEC tooth (`bridge_ledger.rs::bridge_mint_against_lock`,
an atomic contains-then-insert over the committed `note_nullifiers` set, journaled + rollback-safe),
which a re-executing validator runs — NOT something a pure light client folding the deployed AIR
sees. We model "the spend's nullifier `7` is consumed" and show the backing predicate then rejects
even when the digest matches, while the deployed intent still holds. -/

/-- The nullifier `7` (the demo spend's `lock_id`) is already consumed. -/
def sevenConsumed : ℤ → Prop := fun x => x = 7

/-- **`deployed_admits_consumed_nullifier`.** Take the demo engine and a row whose published
`mint_hash` IS the verifying spend's digest `123` (so the digest binds) — but the spend's nullifier
`7` is already consumed. The deployed descriptor still accepts the row's intent, while `BackedAt`
(which requires a FRESH nullifier) rejects: the deployed AIR does not witness the consume-once
guard. (We reuse `goodBridgeMintRow` for the deployed-intent half; the `BackedAt` rejection holds
for ANY row because the only verifying spend's nullifier is consumed.) -/
theorem deployed_admits_consumed_nullifier :
    (IsBridgeMintRow goodBridgeMintRow ∧ BridgeMintRowIntent goodBridgeMintRow)
      ∧ ¬ BackedAt demoSpend sevenConsumed goodBridgeMintRow := by
  refine ⟨forged_deployed_accepts, ?_⟩
  rintro ⟨q, _hv, _hd, hfresh⟩
  -- demoSpend.nullifier q ≡ 7 (defeq); sevenConsumed 7 ≡ (7 = 7), so ¬ consumed fails.
  exact hfresh rfl

/-! ## §D — Axiom audit — every load-bearing arm. -/

#assert_axioms mintHash_goodRow
#assert_axioms forged_deployed_accepts
#assert_axioms forged_not_backed
#assert_axioms deployed_admits_unbacked_bridge
#assert_axioms deployed_intent_does_not_force_backing
#assert_axioms deployed_admits_consumed_nullifier

end Dregg2.Circuit.BridgeBackingAttack
