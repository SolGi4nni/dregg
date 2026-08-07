/-
# Dregg2.Circuit.SovereignBackingAttack — ADVERSARIAL soundness audit of the deployed sovereign
  turn's authority backing (the analog of `CustomCarrierAttack` / `BridgeBackingAttack` for the
  sovereign-cell leg).

This module attacks the deployed sovereign-cell transition head-on, IN LEAN, importing everything
read-only. It is a refutation file: the load-bearing arms are proved WITHOUT `sorry`, and the
conclusion is stated precisely.

## The target

A sovereign turn's deployed effect-vm leg (the ROTATED proof
`sdk::cipherclerk::prove_sovereign_turn_rotated`) proves a state transition `old_commit → new_commit`
THROUGH THE EFFECTS. But the AUTHORITY that makes that transition LEGITIMATE for a sovereign cell —

  (a) the PRE-STATE ANCHOR: the proven `old_commit` is the federation's stored sovereign commitment
      (`turn::executor::execute.rs:811`, `witness.old_commitment == ledger.get_sovereign_commitment`);
  (b) the OWNER Ed25519 SIGNATURE over `(fed, cell, old, new, effects_hash, ts, sequence)`
      (`execute.rs:855..886`, `verifying_key.verify_strict`);
  (c) the REPLAY SEQUENCE: `witness.sequence == ledger.last_sovereign_witness_sequence + 1`
      (`execute.rs:888`, the monotonic per-cell chain-walk),

— is checked ENTIRELY OFF-AIR, by a re-executing validator. A PURE LIGHT CLIENT (one that only folds
the per-turn recursion tree) never witnesses any of (a)/(b)/(c).

In the deployed effect-vm AIR the authority teeth that COULD carry this — `IS_SOVEREIGN_CELL`,
`SOVEREIGN_WITNESS_KEY_COMMIT[4]`, `SOVEREIGN_WITNESS_SEQUENCE` (`circuit/src/effect_vm/columns.rs`
aux offsets 23..27, `pi.rs:223..235`) — are DEAD-ZERO: no producer ever sets `is_sovereign_cell = 1`
(`EffectVmContext::default`), they are bound by NO constraint that links them to a verifying owner
signature, and the Phase-2 `SOVEREIGN_TRANSITION_PROOF_{VK_HASH,COMMITMENT}` columns
(`pi.rs:236..250`) have NO populating caller and NO AIR constraint. So for a pure light client the
sovereign transition is admitted with NO witnessed authority.

This is the SAME vacuity CLASS that `CustomCarrierAttack` proves for `Effect::Custom` and
`BridgeBackingAttack` proves for the inbound bridge mint: REAL as re-executed, VACUOUS as
deployed-light-client.

## What is proved here

§A `deployed_admits_unbacked_sovereign` — the explicit FORGED sovereign turn. A sovereign-authority
   engine whose only verifying signature attests owner-key digest `123` at sequence `5` anchored to
   pre-state `0`, and an HONEST-looking sovereign leg row that SATISFIES the deployed transition
   intent (the teeth carry the prover's claimed values, the transition holds) while its published
   `key_commit` is `0` — an owner digest NO verifying signature attests (a WRONG-OWNER / injected-key
   forgery). The deployed AIR accepts it; the (staged) authority predicate rejects it.

§A′ `deployed_admits_injected_anchor` — the PRE-STATE-ANCHOR forgery: the same shape, but the leg's
   `key_commit`/`sequence` match a verifying signature while its `anchor` (the proven `old_commit`)
   is a value the signature does NOT bind — an INJECTED pre-state. The deployed transition proves a
   genuine `old→new`, but `old` is not anchored to the federation's stored commitment, and the light
   client cannot tell.

§B `deployed_intent_does_not_force_authority` — there is NO uniform "deployed-accepts ⟹ authorized":
   §A is the counterexample. So a light client that only checks the deployed sovereign AIR learns
   NOTHING about the owner signature / anchor. The repair (the authority must come from the FOLD over
   a re-proved sovereign-authority leaf) is named at §C, mirroring `CustomBindingFromFold` /
   `note_spend_leaf_adapter`.

§C `deployed_admits_replayed_sequence` — the REPLAY corollary + the repair pointer. Even a
   `key_commit`/`anchor` a verifying signature attests is accepted by the deployed descriptor when
   the signature's `sequence` is ALREADY consumed (a replay): the monotonic-sequence chain-walk is
   the RE-EXEC tooth (`execute.rs:888`, `last_sovereign_witness_sequence + 1`), NOT a light-client
   one.

## The repair (named, mirroring the custom / bridge fold-wire)

The real authority must come from the per-turn FOLD over a re-proved SOVEREIGN-AUTHORITY leaf
(`circuit-prove::sovereign_leaf_adapter::prove_sovereign_leaf`) whose in-circuit-bound PIs carry the
authority tuple `(key_commit, sequence, anchor, new_commit, attestation_digest)`, connected to the
deployed sovereign leg's teeth via `joint_turn_recursive::prove_sovereign_binding_node_segmented`
(the analog of `prove_custom_binding_node_segmented`). The leaf binds the authority DIGEST in-circuit;
the Ed25519 signature verification that the owner key actually signed that digest stays off-AIR (the
same digest-of-attestation boundary G8/membership carries — full in-AIR Ed25519 is the named cost).

## Axiom hygiene
`#assert_axioms` on every load-bearing arm ⊆ {propext, Classical.choice, Quot.sound}. NO new axiom,
NO `sorry`. NEW file; all imports read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmit

namespace Dregg2.Circuit.SovereignBackingAttack

open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §0 — the sovereign-authority engine + the (staged) authority predicate.

A `SovAuthorityEngine` abstracts the off-AIR Ed25519 authority the executor runs at injection
(`execute.rs:855..899`): `verifySig` is the `verify_strict` accepting bit, and a VERIFYING signature
attests the owner-key digest (`Poseidon2(owner_pubkey)`, the `key_commit`), the per-cell `sequence`,
and the pre-state `anchor` (`old_commitment`) it signed over. This is the sovereign analog of
`BridgeBackingAttack.NoteSpendEngine` (`verify` + `spendDigest` + `nullifier`) and
`CustomApex.ProofEngine` (`verify` + `piCommit`). -/

/-- An abstract sovereign-authority engine: its accepting bit, and the `(key_commit, sequence,
anchor)` tuple a VERIFYING owner signature attests. -/
structure SovAuthorityEngine where
  /-- The proof type of the Ed25519 owner signature. -/
  Sig : Type
  /-- The verifier's accepting bit (`verifying_key.verify_strict(...).is_ok()`). -/
  verifySig : Sig → Bool
  /-- The owner-key digest a verifying signature attests (`Poseidon2(owner_pubkey)`, the `key_commit`). -/
  signedKeyCommit : Sig → ℤ
  /-- The per-cell `sequence` a verifying signature is bound over. -/
  signedSequence : Sig → ℤ
  /-- The pre-state `anchor` (`old_commitment`) a verifying signature is bound over. -/
  signedAnchor : Sig → ℤ

/-! ### The sovereign leg's authority columns.

These are the deployed effect-vm aux/PI teeth (`columns.rs::aux_off` WITNESS_KEY_COMMIT_0 = 23,
WITNESS_SEQUENCE = 27; the rotated transition's `old_commit`/`new_commit` felts), modeled as the
columns the staged authority predicate WOULD read. In the deployed AIR they are present but read by
NO constraint (dead-zero / ungated) — that is exactly the hole. -/

/-- `key_commit` column (aux WITNESS_KEY_COMMIT_0 = 23). -/
def keyCommitCol : Nat := 23
/-- `sequence` column (aux WITNESS_SEQUENCE = 27). -/
def sequenceCol : Nat := 27
/-- The pre-state `anchor` column (the rotated `old_commit` felt; offset 0 stands for it here). -/
def anchorCol : Nat := 0
/-- The post-state `new_commit` column (offset 8 stands for it here). -/
def newCol : Nat := 8

/-- The owner-key digest a leg row publishes. -/
def keyCommitOf (env : VmRowEnv) : ℤ := env.loc keyCommitCol
/-- The sequence a leg row publishes. -/
def sequenceOf (env : VmRowEnv) : ℤ := env.loc sequenceCol
/-- The pre-state anchor a leg row publishes. -/
def anchorOf (env : VmRowEnv) : ℤ := env.loc anchorCol
/-- The post-state commitment a leg row publishes. -/
def newOf (env : VmRowEnv) : ℤ := env.loc newCol

/-- **`Authorized E replayed env`** — the STAGED authority predicate the deployed descriptor SHOULD
(but does not) enforce: the leg's published `(key_commit, sequence, anchor)` is attested by SOME
verifying owner signature whose `sequence` is NOT already consumed. This is the sovereign analog of
`BridgeBackingAttack.BackedAt` and `CustomApex.ProofBind.boundAt` — the content the deployed AIR
omits (legs (a) anchor + (b) owner-sig + (c) replay, all OFF-AIR in `execute.rs`). -/
def Authorized (E : SovAuthorityEngine) (replayed : ℤ → Prop) (env : VmRowEnv) : Prop :=
  ∃ s : E.Sig, E.verifySig s = true
    ∧ E.signedKeyCommit s = keyCommitOf env
    ∧ E.signedSequence s = sequenceOf env
    ∧ E.signedAnchor s = anchorOf env
    ∧ ¬ replayed (E.signedSequence s)

/-! ### The deployed sovereign leg's row intent.

`DeployedSovIntent env` is the content the deployed ROTATED effect-vm proof gates: the transition
`new_commit = anchor + 7` (a concrete stand-in for "the rotated proof proves SOME genuine
`old→new` through the effects") together with the teeth carrying the prover's CLAIMED values. The
authority legs (a)/(b)/(c) are NOT among the gated content — that is the point. A forged row
satisfies this while no verifying signature attests its teeth. -/
def DeployedSovIntent (env : VmRowEnv) : Prop :=
  newOf env = anchorOf env + 7

/-! ## §A — the forged sovereign turn: deployed-accepts what the authority predicate rejects.

A demo authority engine whose ONLY verifying signature attests `(key_commit, sequence, anchor) =
(123, 5, 0)` (the same one-verifying-proof shape `CustomCarrierAttack.demoEngine` /
`BridgeBackingAttack.demoSpend` use). The forged leg row carries `key_commit = 0`, `sequence = 5`,
`anchor = 0`, `new = 7` — its transition holds (`7 = 0 + 7`) so the deployed AIR accepts, but its
`key_commit 0` is attested by NO verifying signature (a WRONG-OWNER / injected-key forgery). -/

/-- A demo sovereign-authority engine: the only verifying signature (`true`) attests owner digest
`123` at sequence `5` anchored to pre-state `0`. -/
def demoSov : SovAuthorityEngine where
  Sig := Bool
  verifySig := fun b => b
  signedKeyCommit := fun _ => 123
  signedSequence := fun _ => 5
  signedAnchor := fun _ => 0

/-- No sequence is consumed (the honest fresh-turn baseline). -/
def noneReplayed : ℤ → Prop := fun _ => False

/-- The forged sovereign leg row: `key_commit = 0` (col 23), `sequence = 5` (col 27),
`anchor = 0` (col 0), `new = 7` (col 8). Its transition holds, but `key_commit 0` is attested by no
verifying signature of `demoSov`. -/
def forgedEnv : VmRowEnv where
  loc := fun i => if i = newCol then 7 else if i = sequenceCol then 5 else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **The deployed descriptor ACCEPTS the forged row.** Its transition holds: `new (7) = anchor (0)
+ 7`. The deployed rotated proof gates exactly this; the authority teeth are dead-zero / ungated. -/
theorem forged_deployed_accepts : DeployedSovIntent forgedEnv := by
  simp only [DeployedSovIntent, newOf, anchorOf, forgedEnv, newCol, anchorCol, sequenceCol]
  decide

/-- The forged row's published `key_commit` is `0` — a digest NO verifying signature of `demoSov`
attests (the only verifying signature attests `123`). -/
theorem keyCommit_forgedEnv : keyCommitOf forgedEnv = 0 := by
  simp only [keyCommitOf, forgedEnv, keyCommitCol, newCol, sequenceCol]
  decide

/-- **The forged row is REJECTED by the (staged) authority predicate.** Its `key_commit` is `0`; the
only verifying signature of `demoSov` attests `123`, so no verifying signature attests it —
`Authorized` fails. The deployed descriptor cannot detect this: it never reads `key_commit`. -/
theorem forged_not_authorized : ¬ Authorized demoSov noneReplayed forgedEnv := by
  rintro ⟨s, _hv, hk, _hseq, _hanc, _hfresh⟩
  -- demoSov.signedKeyCommit s ≡ 123 (defeq); keyCommitOf forgedEnv = 0; 123 = 0 is false.
  rw [keyCommit_forgedEnv] at hk
  simp only [demoSov] at hk
  exact absurd hk (by decide)

/-- **§A keystone — `deployed_admits_unbacked_sovereign`.** ∃ a sovereign-authority engine and a
sovereign leg row that SATISFIES the deployed transition intent yet whose published `key_commit` is
attested by NO verifying owner signature: the deployed AIR admits a sovereign turn whose owner
authority does NOT verify. This is the explicit forged sovereign turn the deployed circuit (and thus
a pure light client) cannot detect — the analog of `CustomCarrierAttack.deployed_admits_unbacked` and
`BridgeBackingAttack.deployed_admits_unbacked_bridge`. -/
theorem deployed_admits_unbacked_sovereign :
    ∃ (E : SovAuthorityEngine) (replayed : ℤ → Prop) (env : VmRowEnv),
      DeployedSovIntent env ∧ ¬ Authorized E replayed env :=
  ⟨demoSov, noneReplayed, forgedEnv, forged_deployed_accepts, forged_not_authorized⟩

/-! ## §A′ — the pre-state-anchor forgery.

The same shape, but the leg's `key_commit`/`sequence` MATCH a verifying signature while its `anchor`
(the proven `old_commit`) is a value the signature does NOT bind: an INJECTED pre-state. The deployed
transition still proves `new = anchor + 7` (a genuine `old→new`), but `old` is not anchored to the
federation's stored commitment — `execute.rs:811`'s check is off-AIR. -/

/-- A leg row whose `key_commit = 123` and `sequence = 5` (a verifying signature attests these) but
whose `anchor = 9` (col 0) — a pre-state the only verifying signature of `demoSov` (anchor `0`) does
NOT bind. `new = 16` so the transition `16 = 9 + 7` still holds. -/
def injectedAnchorEnv : VmRowEnv where
  loc := fun i =>
    if i = keyCommitCol then 123
    else if i = sequenceCol then 5
    else if i = anchorCol then 9
    else if i = newCol then 16
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- The injected-anchor row satisfies the deployed transition intent (`16 = 9 + 7`). -/
theorem injectedAnchor_deployed_accepts : DeployedSovIntent injectedAnchorEnv := by
  simp only [DeployedSovIntent, newOf, anchorOf, injectedAnchorEnv, newCol, anchorCol, sequenceCol,
    keyCommitCol]
  decide

/-- **`deployed_admits_injected_anchor`.** The injected-anchor row satisfies the deployed transition
intent, but no verifying signature of `demoSov` (which anchors to `0`) binds its `anchor = 9`, so
`Authorized` rejects: the deployed AIR does not witness the pre-state anchor (leg (a)). -/
theorem deployed_admits_injected_anchor :
    DeployedSovIntent injectedAnchorEnv ∧ ¬ Authorized demoSov noneReplayed injectedAnchorEnv := by
  refine ⟨injectedAnchor_deployed_accepts, ?_⟩
  rintro ⟨s, _hv, _hk, _hseq, hanc, _hfresh⟩
  -- demoSov.signedAnchor s ≡ 0 (defeq); anchorOf injectedAnchorEnv = 9; 0 = 9 is false.
  have hanc9 : anchorOf injectedAnchorEnv = 9 := by
    simp only [anchorOf, injectedAnchorEnv, anchorCol, keyCommitCol, sequenceCol, newCol]; decide
  rw [hanc9] at hanc
  simp only [demoSov] at hanc
  exact absurd hanc (by decide)

/-! ## §B — the deployed sovereign AIR does not force the authority. -/

/-- **§B keystone — `deployed_intent_does_not_force_authority`.** There is NO uniform implication
"the deployed sovereign leg intent holds ⟹ the owner authority is verified": §A exhibits a row whose
deployed intent holds while no verifying signature attests its `key_commit`. So consuming an
authority claim against the deployed sovereign AIR asserts strictly MORE than the verifier enforces —
the deployed descriptor binds only the transition, never the owner signature / anchor / replay. The
real authority must come from the per-turn FOLD over the re-proved sovereign-authority leaf
(`sovereign_leaf_adapter::prove_sovereign_leaf` connected via
`prove_sovereign_binding_node_segmented` to the published teeth PIs), exactly as
`CustomBindingFromFold` rebuilds the custom binding from `AggAirSound` — see §C. -/
theorem deployed_intent_does_not_force_authority :
    ¬ ∀ (E : SovAuthorityEngine) (replayed : ℤ → Prop) (env : VmRowEnv),
        DeployedSovIntent env → Authorized E replayed env := by
  intro hforce
  exact forged_not_authorized (hforce demoSov noneReplayed forgedEnv forged_deployed_accepts)

/-! ## §C — the replay corollary + the repair pointer.

The deployed descriptor equally fails to witness sequence FRESHNESS. Even a `key_commit`/`anchor`
that a verifying signature attests is accepted by the deployed descriptor when that signature's
`sequence` is already consumed: the consume-once guard is the RE-EXEC tooth
(`execute.rs:888`, `witness.sequence == ledger.last_sovereign_witness_sequence(cell) + 1`, the
monotonic per-cell chain-walk), which a re-executing validator runs — NOT something a pure light
client folding the deployed AIR sees. We model "the signature's `sequence` `5` is consumed" and show
the authority predicate then rejects even when the key digest matches, while the deployed intent
still holds. -/

/-- A leg row whose `key_commit = 123`, `sequence = 5`, `anchor = 0` ALL match the verifying
signature of `demoSov`, and whose transition `7 = 0 + 7` holds. -/
def replayEnv : VmRowEnv where
  loc := fun i =>
    if i = keyCommitCol then 123
    else if i = sequenceCol then 5
    else if i = newCol then 7
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- The sequence `5` (the demo signature's per-cell counter) is already consumed. -/
def fiveReplayed : ℤ → Prop := fun x => x = 5

/-- The replay row satisfies the deployed transition intent (`7 = 0 + 7`). -/
theorem replay_deployed_accepts : DeployedSovIntent replayEnv := by
  simp only [DeployedSovIntent, newOf, anchorOf, replayEnv, newCol, anchorCol, sequenceCol,
    keyCommitCol]
  decide

/-- **`deployed_admits_replayed_sequence`.** Take the demo engine and a row whose published
`key_commit`/`sequence`/`anchor` ALL match the verifying signature `(123, 5, 0)` (so the digest +
anchor bind) — but the signature's `sequence 5` is already consumed. The deployed descriptor still
accepts the row's transition, while `Authorized` (which requires a FRESH sequence) rejects: the
deployed AIR does not witness the consume-once chain-walk (leg (c)). -/
theorem deployed_admits_replayed_sequence :
    DeployedSovIntent replayEnv ∧ ¬ Authorized demoSov fiveReplayed replayEnv := by
  refine ⟨replay_deployed_accepts, ?_⟩
  rintro ⟨s, _hv, _hk, _hseq, _hanc, hfresh⟩
  -- demoSov.signedSequence s ≡ 5 (defeq); fiveReplayed 5 ≡ (5 = 5), so ¬ replayed fails.
  exact hfresh rfl

/-! ## §D — Axiom audit — every load-bearing arm. -/

#assert_axioms forged_deployed_accepts
#assert_axioms keyCommit_forgedEnv
#assert_axioms forged_not_authorized
#assert_axioms deployed_admits_unbacked_sovereign
#assert_axioms injectedAnchor_deployed_accepts
#assert_axioms deployed_admits_injected_anchor
#assert_axioms deployed_intent_does_not_force_authority
#assert_axioms replay_deployed_accepts
#assert_axioms deployed_admits_replayed_sequence

end Dregg2.Circuit.SovereignBackingAttack
