/-
# Dregg2.Apps.ShieldedPaymentGated — a SHIELDED (private) PAYMENT on the ONE GATED executor.

A `starbridge`-shaped shielded payment (the Zcash/dregg1 note pattern: value lives in COMMITMENTS in a
note tree; a transfer CREATES a new commitment for the recipient and SPENDS the sender's note by
publishing its NULLIFIER — which must be both backed by a valid §8 spending PROOF and FRESH, so the same
note can never be spent twice), modelled as REAL note moves on the production turn entry —
`Dregg2.Exec.FullForestAuth.execFullForestG` (the `dregg_exec_full_forest_auth` 4-leg gate: credential ∧
cap-authority ∧ caveats-discharged ∧ not-revoked).

This app exercises the **`noteSpendA` / `noteCreateA`** effects, which were not yet covered by any
verified gated app. Unlike `PrivacyVotingGated` (whose no-double-vote rides a `WriteOnce` SLOT-caveat
DUAL of the nullifier discipline), this app spends against the REAL kernel nullifier SET — so the
no-double-spend headline is the GENUINE anti-replay keystone `RecordKernel.note_no_double_spend`
(`nf ∈ k.nullifiers ⇒ noteSpendNullifier = none`), the exact Zcash discipline, not a model surrogate.
It also exercises the welded §8 spending-PROOF gate (`noteSpendChainA_fails_without_proof`): a spend with
a missing/invalid proof fail-closes — the `apply.rs:929` "spending proof verification failed" rejection,
now captured IN the verified executor.

## The two shielded ops (each a SINGLE credential-gated leaf node through `execFullForestG`)

  * **deposit** — MINT a fresh note commitment for a recipient. `noteCreateA cm payer`: inserts the
    commitment `cm` into the note tree. Balance-NEUTRAL (the value backing is the §8 commitment carrier).
  * **spend**   — SPEND a note by publishing its nullifier. `noteSpendA nf payer spendProof`: requires
    the §8 spending proof to verify (`spendProof = true`) AND the nullifier `nf` to be FRESH (not in the
    kernel's spent set); on success inserts `nf` into the set (so a re-spend is rejected). FAIL-CLOSED on
    a missing proof OR a double-spend.

## The gated-executor keystones this app COMPOSES (it adds NO kernel theory)

  * `execFullForestG_leaf` — a childless gated forest runs EXACTLY its single gated node;
  * `execFullForestG_unauthorized_fails` — a false gate leg ⇒ whole-forest `none`;
  * `gateOK_forged_false` (local) — a forged credential's portal leg is `false`;
  * `gateOK_revoked_fails` — a revoked credential's nullifier in `s.kernel.revoked` ⇒ `none`;
  * `note_no_double_spend` / `note_spend_inserts` — the REAL nullifier-set anti-replay teeth;
  * `noteSpendChainA_fails_without_proof` / `noteSpendChainA_requires_proof` — the §8 spending-proof teeth;
  * `execFullForestG_conserves_per_asset` — note ops are balance-neutral, so each preserves supply.

## End-user theorems

  1. `sp_forged_rejected`           — a FORGED credential ⇒ the whole gated op rejects (`none`), ∀s, ∀op;
  2. `sp_revoked_rejected`         — a REVOKED credential ⇒ `none`, ∀s;
  3. `sp_spend_requires_proof`     — a SPEND with a missing/invalid §8 proof (`spendProof = false`) ⇒ `none`, ∀s;
  4. `sp_no_double_spend`          — a SPEND of an ALREADY-SPENT nullifier (`nf ∈ s.kernel.nullifiers`)
     ⇒ `none`, ∀s — the GENUINE Zcash anti-replay on the real kernel set (not a slot-caveat dual);
  5. `sp_spend_inserts_nullifier`  — a COMMITTED spend records `nf` in the spent set (so the NEXT spend
     of the same note is rejected — the anti-replay is self-reinforcing);
  6. `sp_spend_conserves` / `sp_deposit_conserves` — committed note ops preserve EVERY asset's supply.

Plus a concrete shielded-payment state (`sp0`) whose `#guard`s witness the lifecycle non-vacuously: a
DEPOSIT commits, a proof-backed fresh SPEND commits and records the nullifier, a re-spend ⇒ `none`, a
proofless spend ⇒ `none`, a forged credential ⇒ `none`, a revoked credential ⇒ `none`, all CONSERVE.

NEW file only — does NOT touch any existing app,
`FullForestAuth.lean`, `TurnExecutorFull.lean`, nor `Dregg2.lean`. Reuses ONLY the proved gated-executor
keystones + the proved nullifier-set / spending-proof teeth.
-/
import Dregg2.Exec.GatedForestCfg

namespace Dregg2.Apps.ShieldedPaymentGated

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Exec.EffectsState
open Dregg2.Exec.FullForestAuth
open Dregg2.Exec.StarbridgeGated

/-! ## §1 — The shielded-payment DOMAIN at the Demo carriers (the payer, a note commitment, a nullifier). -/

/-- The PAYER cell (the credential holder spending/creating notes). Cell `0`, so the note-op authority
gate holds trivially — the §8 CREDENTIAL gate is the load-bearing admission condition. -/
abbrev payer : CellId := 0

/-! ## §2 — Each shielded op as a GATED LEAF NODE through the production turn entry `execFullForestG`. -/

/-- A gated shielded node: credential `cred`, a note `action`, no children. -/
def spNode (cred : Authorization Dg Pf) (action : FullActionA) : DForest :=
  ⟨ mkAuth cred [], action, [] ⟩

/-- **deposit** — MINT a fresh note commitment. `noteCreateA cm payer`: insert `cm` into the note tree. -/
def depositNode (cred : Authorization Dg Pf) (cm : Nat) : DForest :=
  spNode cred (.noteCreateA cm payer)

/-- **spend** — SPEND a note. `noteSpendA nf payer spendProof`: requires the §8 spending proof to verify
(`spendProof = true`) AND the nullifier `nf` to be fresh; on success inserts `nf` into the spent set. -/
def spendNode (cred : Authorization Dg Pf) (nf : Nat) (spendProof : Bool) : DForest :=
  spNode cred (.noteSpendA nf payer spendProof)

/-! ## §3 — The leaf-collapse bridge: a childless gated forest runs EXACTLY its single gated node. -/

/-- **`execFullForestG_leaf`.** -/
theorem execFullForestG_leaf (s : RecChainedState) (na : DNodeAuth) (a : FullActionA) :
    execFullForestG s (⟨na, a, []⟩ : DForest) = execFullAGated s na a := by
  show (match execFullAGated s na a with
        | some s' => execFullChildrenG (targetOf a) s' ([] : List DChild)
        | none    => none) = execFullAGated s na a
  cases execFullAGated s na a with
  | none   => rfl
  | some _ => rfl

/-- **`execFullForestG_spNode` — the shielded-op collapse.** A note op runs `if gateOK then execFullA
action else none`. -/
theorem execFullForestG_spNode (s : RecChainedState) (cred : Authorization Dg Pf) (action : FullActionA) :
    execFullForestG s (spNode cred action)
      = (if gateOK (mkAuth cred []) s = true then execFullA s action else none) := by
  rw [spNode, execFullForestG_leaf, execFullAGated]

/-! ## §4 — The CREDENTIAL gate: `goodCred` admits, `forgedCred` fail-closed (state-independent). -/

/-- **`gateOK_forged_false` — the forged-credential gate leg is FALSE.** -/
theorem gateOK_forged_false (s : RecChainedState) : gateOK (mkAuth forgedCred []) s = false := by
  have hcred : credentialValidG (mkAuth forgedCred []) = false := by decide
  unfold gateOK
  rw [hcred]
  simp

/-! ## §5 — END-USER THEOREM 1: a FORGED credential ⇒ the whole gated op REJECTS. -/

/-- **`sp_forged_rejected` (END-USER THEOREM 1).** A shielded op (ANY note action) presented
with a FORGED credential is rejected by the production turn entry, for EVERY pre-state `s`. -/
theorem sp_forged_rejected (s : RecChainedState) (action : FullActionA) :
    execFullForestG s (spNode forgedCred action) = none := by
  rw [spNode]
  exact execFullForestG_unauthorized_fails s (mkAuth forgedCred []) action [] (gateOK_forged_false s)

theorem sp_forged_deposit_rejected (s : RecChainedState) (cm : Nat) :
    execFullForestG s (depositNode forgedCred cm) = none :=
  sp_forged_rejected s _
theorem sp_forged_spend_rejected (s : RecChainedState) (nf : Nat) (spendProof : Bool) :
    execFullForestG s (spendNode forgedCred nf spendProof) = none :=
  sp_forged_rejected s _

/-! ## §6 — END-USER THEOREM 2: a REVOKED credential ⇒ the whole gated op REJECTS. -/

/-- A NodeAuth identical to `mkAuth cred []` but carrying an explicit revocation nullifier `nul`. -/
def mkAuthRevoked (cred : Authorization Dg Pf) (nul : Nat) : DNodeAuth :=
  { mkAuth cred [] with credNul := nul }

/-- A shielded op whose credential carries the revocation nullifier `nul`. -/
def spNodeRevoked (cred : Authorization Dg Pf) (nul : Nat) (action : FullActionA) : DForest :=
  ⟨ mkAuthRevoked cred nul, action, [] ⟩

/-- **`sp_revoked_rejected` (END-USER THEOREM 2).** A shielded op whose credential nullifier
`nul` sits in the COMMITTED revocation registry `s.kernel.revoked` is rejected, for EVERY pre-state and
EVERY (even genuine) credential. A revoked key cannot deposit/spend, no matter how valid its signature.
(Note: this `nul` is the CREDENTIAL revocation serial in `s.kernel.revoked` — distinct from the note
nullifier `nf` checked in `s.kernel.nullifiers` by the spend's anti-replay gate.) -/
theorem sp_revoked_rejected (s : RecChainedState) (cred : Authorization Dg Pf) (nul : Nat)
    (action : FullActionA) (hrev : s.kernel.revoked.contains nul = true) :
    execFullForestG s (spNodeRevoked cred nul action) = none := by
  rw [spNodeRevoked]
  refine execFullForestG_unauthorized_fails s (mkAuthRevoked cred nul) action [] ?_
  exact gateOK_revoked_fails (mkAuthRevoked cred nul) s hrev

/-! ## §7 — The gate-passing collapse for `goodCred`: a SPEND runs `noteSpendChainA`.

When the genuine, non-revoked credential admits, a spend op IS its underlying `noteSpendChainA`. The
hinge for the spending-proof and no-double-spend theorems: any rejection of the underlying note-spend
rejects the whole gated turn. -/

/-- **`spend_runs_noteSpend` — the gate-passing collapse for a SPEND.** -/
theorem spend_runs_noteSpend (s : RecChainedState) (nf : Nat) (spendProof : Bool)
    (hgate : gateOK (mkAuth goodCred []) s = true) :
    execFullForestG s (spendNode goodCred nf spendProof)
      = noteSpendChainA s nf payer spendProof := by
  rw [spendNode, execFullForestG_spNode, if_pos hgate]; rfl

/-! ## §8 — END-USER THEOREM 3: a SPEND with a missing/invalid §8 proof ⇒ none (the spending-proof tooth). -/

/-- **`sp_spend_requires_proof` (END-USER THEOREM 3, THE §8 SPENDING-PROOF TOOTH).** A spend
whose §8 STARK spending proof did NOT verify (`spendProof = false`) is rejected by the executor:
`execFullForestG s (spendNode goodCred nf false) = none` — EVEN with a genuine, non-revoked credential.
This is exactly the `apply.rs:929` "NoteSpend spending proof verification failed" rejection — now CAPTURED
in the verified gated turn. NON-VACUOUS: a credential-valid, non-revoked spender is STILL rejected purely
because the note proof is missing — credential-validity and note-validity are orthogonal. -/
theorem sp_spend_requires_proof (s : RecChainedState) (nf : Nat)
    (hgate : gateOK (mkAuth goodCred []) s = true) :
    execFullForestG s (spendNode goodCred nf false) = none := by
  rw [spend_runs_noteSpend s nf false hgate]
  exact noteSpendChainA_fails_without_proof rfl

/-! ## §9 — END-USER THEOREM 4: a SPEND of an ALREADY-SPENT nullifier ⇒ none (the no-double-spend tooth). -/

/-- **`sp_no_double_spend` (END-USER THEOREM 4, THE GENUINE ZCASH ANTI-REPLAY).** A spend of a
note whose nullifier `nf` is ALREADY in the COMMITTED spent set `s.kernel.nullifiers` is rejected by the
executor: `execFullForestG s (spendNode goodCred nf spendProof) = none` — EVEN with a genuine credential
AND a valid §8 spending proof. This is the REAL nullifier-set anti-replay `RecordKernel.note_no_double_spend`
(`nf ∈ k.nullifiers ⇒ noteSpendNullifier = none`), the exact Zcash discipline — NOT a `WriteOnce`
slot-caveat surrogate. NON-VACUOUS: the rejection is keyed on the adversary-uncontrollable kernel set;
`hspent` is forced by a previously-spent note. -/
theorem sp_no_double_spend (s : RecChainedState) (nf : Nat) (spendProof : Bool)
    (hgate : gateOK (mkAuth goodCred []) s = true)
    (hspent : nf ∈ s.kernel.nullifiers) :
    execFullForestG s (spendNode goodCred nf spendProof) = none := by
  rw [spend_runs_noteSpend s nf spendProof hgate]
  unfold noteSpendChainA
  by_cases hp : spendProof = true
  · rw [if_pos hp, note_no_double_spend s.kernel nf hspent]
  · rw [if_neg hp]

/-! ## §10 — END-USER THEOREM 5: a COMMITTED spend RECORDS the nullifier (self-reinforcing anti-replay). -/

/-- **`sp_spend_inserts_nullifier` (END-USER THEOREM 5).** A COMMITTED spend actually INSERTS
`nf` into the kernel's spent set: `nf ∈ s'.kernel.nullifiers`. Composed with `sp_no_double_spend`, this
makes the anti-replay self-reinforcing — once a note is spent, the next spend of the same note is
rejected forever. (Reads off `RecordKernel.note_spend_inserts` through the gate-passing collapse.) -/
theorem sp_spend_inserts_nullifier (s s' : RecChainedState) (nf : Nat) (spendProof : Bool)
    (hgate : gateOK (mkAuth goodCred []) s = true)
    (h : execFullForestG s (spendNode goodCred nf spendProof) = some s') :
    nf ∈ s'.kernel.nullifiers := by
  rw [spend_runs_noteSpend s nf spendProof hgate] at h
  unfold noteSpendChainA at h
  by_cases hp : spendProof = true
  · rw [if_pos hp] at h
    cases hk : noteSpendNullifier s.kernel nf with
    | none   => rw [hk] at h; exact absurd h (by simp)
    | some k' =>
        rw [hk] at h; simp only [Option.some.injEq] at h; subst h
        exact note_spend_inserts hk
  · rw [if_neg hp] at h; exact absurd h (by simp)

/-! ## §11 — END-USER THEOREM 6: committed note ops CONSERVE every asset.

Both note ops are balance-neutral (`ledgerDeltaAsset = 0` for every asset) — they move SETs (the note
tree / nullifier set), not the `bal` ledger — so a single note leaf op's per-asset turn delta is `0`,
and `execFullForestG_conserves_per_asset` gives supply-preservation for free. -/

/-- The per-asset turn delta of a DEPOSIT is `0` for every asset. -/
theorem depositNode_delta_zero (cred : Authorization Dg Pf) (cm : Nat) (b : AssetId) :
    turnLedgerDeltaAsset ((lowerForestG (depositNode cred cm)).map Prod.snd) b = 0 := by
  simp [depositNode, spNode, lowerForestG, lowerChildrenG, turnLedgerDeltaAsset, ledgerDeltaAsset]

/-- The per-asset turn delta of a SPEND is `0` for every asset. -/
theorem spendNode_delta_zero (cred : Authorization Dg Pf) (nf : Nat) (spendProof : Bool) (b : AssetId) :
    turnLedgerDeltaAsset ((lowerForestG (spendNode cred nf spendProof)).map Prod.snd) b = 0 := by
  simp [spendNode, spNode, lowerForestG, lowerChildrenG, turnLedgerDeltaAsset, ledgerDeltaAsset]

/-- **`sp_deposit_conserves` (END-USER THEOREM 6a).** A COMMITTED note deposit preserves EVERY
asset's total supply: the commitment-tree insert touches no balance. -/
theorem sp_deposit_conserves (s s' : RecChainedState) (cred : Authorization Dg Pf) (cm : Nat)
    (b : AssetId) (h : execFullForestG s (depositNode cred cm) = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b :=
  execFullForestG_conserves_per_asset s s' (depositNode cred cm) b h (depositNode_delta_zero cred cm b)

/-- **`sp_spend_conserves` (END-USER THEOREM 6b).** A COMMITTED note spend preserves EVERY
asset's total supply: the nullifier-set insert touches no balance. -/
theorem sp_spend_conserves (s s' : RecChainedState) (cred : Authorization Dg Pf) (nf : Nat)
    (spendProof : Bool) (b : AssetId) (h : execFullForestG s (spendNode cred nf spendProof) = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b :=
  execFullForestG_conserves_per_asset s s' (spendNode cred nf spendProof) b h
    (spendNode_delta_zero cred nf spendProof b)

/-! ## §12 — NON-VACUITY: a concrete shielded-payment state + `#guard` witnesses (the gates are REAL).

`sp0` is a shielded-payment pre-state: the payer (cell 0) holds 100 of asset 0, the note tree is empty,
the spent-nullifier set has ALREADY recorded note `77` (a previously-spent note — a re-spend must fail),
an empty credential-revocation registry, default Live lifecycle. We exhibit: a DEPOSIT commits, a
proof-backed FRESH spend (`nf = 9`) commits and records the nullifier, a RE-spend of `77` ⇒ `none`, a
PROOFLESS spend ⇒ `none`, a forged credential ⇒ `none`, a revoked credential ⇒ `none`, all CONSERVE. -/

/-- A shielded-payment pre-state: payer (cell 0) holds 100 of asset 0; the note tree is empty; the
spent-nullifier set ALREADY contains note `77` (so a re-spend of `77` must fail); empty credential-
revocation registry; default Live lifecycle. -/
def sp0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun _ => []
        bal := fun c a => if c = 0 ∧ a = 0 then 100 else 0
        nullifiers := [77] }
    log := [] }

-- The gate passes for the genuine credential, fails for the forged one:
#guard (gateOK (mkAuth goodCred []) sp0)              --  true  (genuine credential admits)
#guard (gateOK (mkAuth forgedCred []) sp0) == false   --  false (forged ⇒ fail-closed)

-- (i) a DEPOSIT commits (inserts a fresh note commitment 5 into the tree):
#guard ((execFullForestG sp0 (depositNode goodCred 5)).isSome)                        --  true (deposited!)
-- ...and CONSERVES asset 0 (commitment insert is balance-neutral):
#guard ((execFullForestG sp0 (depositNode goodCred 5)).map (fun s => recTotalAsset s.kernel 0)) == some 100  --  some 100

-- (ii) a PROOF-BACKED FRESH spend (nf = 9, spendProof = true) commits and RECORDS the nullifier:
#guard ((execFullForestG sp0 (spendNode goodCred 9 true)).isSome)                     --  true (spent!)
#guard ((execFullForestG sp0 (spendNode goodCred 9 true)).map (fun s => s.kernel.nullifiers.contains 9)) == some true  --  recorded
-- ...and CONSERVES asset 0 (nullifier insert is balance-neutral):
#guard ((execFullForestG sp0 (spendNode goodCred 9 true)).map (fun s => recTotalAsset s.kernel 0)) == some 100  --  some 100

-- (iii) NO DOUBLE-SPEND: re-spending note 77 (already in the spent set) ⇒ none, EVEN with a valid proof:
#guard (sp0.kernel.nullifiers.contains 77)                                            --  true (77 already spent)
#guard ((execFullForestG sp0 (spendNode goodCred 77 true)).isSome) == false           --  false (re-spend rejected)

-- (iv) THE §8 PROOF TOOTH: a proofless spend (spendProof = false) of a FRESH note ⇒ none:
#guard ((execFullForestG sp0 (spendNode goodCred 9 false)).isSome) == false           --  false (no proof ⇒ rejected)

-- (v) a FORGED credential ⇒ none (credential gate fail-closes), even for a valid fresh spend:
#guard ((execFullForestG sp0 (spendNode forgedCred 9 true)).isSome) == false          --  false

-- (vi) REVOCATION: a revoked credential (serial 7 in the committed registry) ⇒ none, even genuine.
/-- A shielded-payment state whose credential-revocation registry contains serial 7. -/
def spRevoked : RecChainedState :=
  { kernel := { sp0.kernel with revoked := [7] }, log := [] }
#guard (spRevoked.kernel.revoked.contains 7)                                          --  true (7 is revoked)
#guard ((execFullForestG spRevoked (spNodeRevoked goodCred 7 (.noteSpendA 9 payer true))).isSome) == false  --  false

-- (vii) SELF-REINFORCING ANTI-REPLAY: spend note 9, then re-spend 9 ⇒ none (the insert made it permanent):
#guard (((execFullForestG sp0 (spendNode goodCred 9 true)).bind
          (fun s => execFullForestG s (spendNode goodCred 9 true))).isSome) == false  --  false (double-spend blocked)

/-! ## §13 — Axiom-hygiene tripwires (the honesty pins). Every keystone depends ONLY on the three
standard kernel axioms `{propext, Classical.choice, Quot.sound}` — no `sorryAx`. -/

#assert_axioms execFullForestG_leaf
#assert_axioms execFullForestG_spNode
#assert_axioms gateOK_forged_false
#assert_axioms sp_forged_rejected
#assert_axioms sp_revoked_rejected
#assert_axioms spend_runs_noteSpend
#assert_axioms sp_spend_requires_proof
#assert_axioms sp_no_double_spend
#assert_axioms sp_spend_inserts_nullifier
#assert_axioms depositNode_delta_zero
#assert_axioms spendNode_delta_zero
#assert_axioms sp_deposit_conserves
#assert_axioms sp_spend_conserves

end Dregg2.Apps.ShieldedPaymentGated
