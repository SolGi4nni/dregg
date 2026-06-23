/-
# Dregg2.Apps.Identity — the identity app as a verified cell-program: revoked stays revoked, forever.

dregg1's identity / verifiable-credential app (`credentials/src/{issuance,revocation,verification}.rs`)
is a three-verb protocol: **issue** mints a credential with a stable id; **revoke** inserts that id into
a grow-only `RevocationRegistry` (`HashSet<[u8;32]>`, insert-only, never removes); **verify** admits a
credential only when a non-membership check passes (`verify_non_revocation` — on presence returns
`NonRevocationError::Revoked`). The verifier never trusts a self-asserted boolean; it checks genuine
absence against the committed set.

The headline safety: permanent revocation — once revoked, a credential can never be re-validated. The
registry is modelled as `s.kernel.revoked : List Nat` (`RecordKernel.lean`), with the verifier's
negative-discharge leg as `FullForestAuth.revocationGate` and per-step teeth `gateOK_revoked_fails`.
This module carries that one-step fact to the coinductive living cell, forever.

The current 46-effect executor has no arm that grows `revoked` (the authority `revoke`/`dropRef`
effects edit only `caps` via `recCRevoke`, not this credential-revocation side-table). So the frame
is the sharpest possible: per-step equality `s'.kernel.revoked = s.kernel.revoked`.

Five theorems, ascending:
* `execFullA_revoked_eq` — per-effect registry frame: a committed effect leaves the registry unchanged.
* `execFullTurnA_revoked_eq` / `execFullForestA_revoked_eq` — turn- and forest-level lift by induction.
* `livingCellA_revoked_grow` — the crown: `rev0 ⊆ s.kernel.revoked` carried forever by
  `livingCellA_carries` against every adversarial schedule.
* `livingCellA_identity_revoked_forever` — the headline: if `credNul` is revoked initially, it is in
  the registry at every trajectory index — so `gateOK` fail-closes at every reachable state.
-/
import Dregg2.Exec.CellNullifier
import Dregg2.Exec.FullForestAuth

namespace Dregg2.Apps.Identity

open Dregg2.Boundary
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Authority
open Dregg2.Exec.EffectsState (stateStep stateStep_factors stateStepGuarded_eq
  stateStepDev_eq incrementNonceStep_eq)
open Dregg2.Tactics

/-! ## Step 0 — registry-frame lemmas for the deeply-nested kernel ops (swiss).

These kernel ops touch only `swiss` — never `revoked` — so a committed step leaves `revoked`
unchanged. Hoisted as `private` frame lemmas, the dual of `CellNullifier`'s `_nullifiers` helpers.
(F2b: the queue-family frame lemmas died with the queue verb family.) -/

/-! ## Step 1 — `execFullA_revoked_eq`: the per-effect registry frame (the full dispatch).

Every arm leaves `revoked` unchanged: no current effect grows the credential-revocation registry
(`noteSpend` grows `nullifiers`; the authority `revoke`/`dropRef`/`revokeDelegation` effects edit `caps`
via `recKRevokeTarget`). Each arm reduces `k'.revoked = s.kernel.revoked` by `rfl`. -/

mutual
/-- **`execFullA_revoked_eq`** — a committed `FullActionA` leaves the credential revocation registry
unchanged: `s'.kernel.revoked = s.kernel.revoked`. No current effect grows it; every kernel transform
writes a different field; `exerciseA` RECURSES (mutual `execInnerA_revoked_eq`). The sharpest dual of
`execFullA_ledger_per_asset`. -/
theorem execFullA_revoked_eq (s s' : RecChainedState) (fa : FullActionA)
    (h : execFullA s fa = some s') : s'.kernel.revoked = s.kernel.revoked := by
  cases fa with
  -- §catalog / supply / authority — chained `match kernelOp | some k' => some {kernel:=k',…}` wrappers.
  | balanceA t a =>
      obtain ⟨_, ⟨k', hk, hs'⟩⟩ := recCexecAsset_factors t a (by simpa only [execFullA] using h)
      subst hs'
      show k'.revoked = s.kernel.revoked
      unfold recKExecAsset at hk; split at hk
      · injection hk with hk; subst hk; rfl
      · exact absurd hk (by simp)
  | delegate del rec t =>
      simp only [execFullA, recCDelegate] at h
      cases hk : recKDelegate s.kernel del rec t with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          show k'.revoked = s.kernel.revoked
          unfold recKDelegate at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  | revoke holder t =>
      -- `recCRevoke`/`recKRevokeTarget` edit ONLY `caps` — the credential-revocation registry is a
      -- DISTINCT side-table, untouched (the projection through the `{caps := …}` update is `rfl`).
      simp only [execFullA, recCRevoke, Option.some.injEq] at h; subst h; rfl
  | mintA actor cell a amt =>
      simp only [execFullA, recCMintAsset] at h
      cases hk : recKMintAsset s.kernel actor cell a amt with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          show k'.revoked = s.kernel.revoked
          unfold recKMintAsset at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  | burnA actor cell a amt =>
      simp only [execFullA, recCBurnAsset] at h
      cases hk : recKBurnAsset s.kernel actor cell a amt with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          show k'.revoked = s.kernel.revoked
          unfold recKBurnAsset at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  -- §pure-state — `stateStep` (field write); factors through `stateStep_factors` (kernel = writeField,
  -- a `cell`-only update, `revoked` untouched ⇒ `rfl`). All four share the proof.
  | setFieldA actor cell f v =>
      -- §RESERVED-SLOT/§SLOT-CAVEAT: peel the reserved gate (`stateStepDev_eq`) then the caveat gate
      -- (`stateStepGuarded_eq`); the field write never edits `revoked`.
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors (stateStepGuarded_eq (stateStepDev_eq h)); subst hs'; rfl
  | emitEventA actor cell topic data =>
      -- Codex's emitStep is now live-cell guarded: peel the `if cell ∈ accounts`.
      simp only [execFullA] at h
      by_cases hlive : cell ∈ s.kernel.accounts ∧ acceptsEffects s.kernel cell = true
      · rw [if_pos hlive] at h; simp only [emitStep, Option.some.injEq] at h; subst h; rfl
      · rw [if_neg hlive] at h; exact absurd h (by simp)
  | incrementNonceA actor cell n =>
      -- §MONOTONE-NONCE: peel the monotone gate (`incrementNonceStep_eq`); the field write never edits `revoked`.
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors (incrementNonceStep_eq h); subst hs'; rfl
  | setPermissionsA actor cell p =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; rfl
  | setVKA actor cell vk =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; rfl
  | setProgramA actor cell prog =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; rfl
  -- §authority — introduce/validateHandoff route to recKDelegate; delegateAtten to recKDelegateAtten;
  -- attenuate commits in bounds (caps-only); dropRef/revokeDelegation to recCRevoke (caps-only);
  -- exercise factors (kernel UNCHANGED). NONE touches the credential-revocation registry.
  | introduceA intro rec t =>
      simp only [execFullA, recCDelegate] at h
      cases hk : recKDelegate s.kernel intro rec t with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          show k'.revoked = s.kernel.revoked
          unfold recKDelegate at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  | delegateAttenA del rec t keep =>
      simp only [execFullA, recCDelegateAtten] at h
      cases hk : recKDelegateAtten s.kernel del rec t keep with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          show k'.revoked = s.kernel.revoked
          unfold recKDelegateAtten at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  | attenuateA actor idx keep =>
      obtain ⟨_, rfl⟩ := attenuateA_factors h; rfl
  | revokeDelegationA holder t =>
      simp only [execFullA, recCRevoke, Option.some.injEq] at h; subst h; rfl
  | exerciseA actor t inner =>
      simp only [execFullA] at h
      by_cases hf : innerFacetsAdmittedA s actor t inner = true
      · rw [if_pos hf] at h
        cases hg : exerciseStepA s actor t with
        | none => rw [hg] at h; exact absurd h (by simp)
        | some s1 =>
            rw [hg] at h
            obtain ⟨_, hs1⟩ := exerciseStepA_factors hg
            -- the hold-gate frames `revoked`; the inner fold preserves it (no effect touches it).
            rw [execInnerA_revoked_eq s1 s' inner h, hs1]
      · rw [if_neg hf] at h; exact absurd h (by simp)
  -- §supply-growth — createCell/spawn factor through their gates (createCellIntoAsset / + a caps grant
  -- — neither touches `revoked`); bridgeMint reuses recCMintAsset.
  | createCellA actor newCell =>
      obtain ⟨_, _, hs'⟩ := createCellChainA_factors (by simpa only [execFullA] using h)
      subst hs'; rfl
  | createCellFromFactoryA actor newCell vk =>
      -- §MA-factory: the factory install edits `cell`/`slotCaveats`/`accounts`/`bal`, never `revoked`.
      obtain ⟨_, s1, _, _, hc, hs'⟩ :=
        createCellFromFactoryChainA_factors (by simpa only [execFullA] using h)
      obtain ⟨_, _, hs1⟩ := createCellChainA_factors hc
      subst hs' hs1; rfl
  | spawnA actor child target =>
      -- Codex's spawnChainA_factors gained the (held-edge ∧ live-target) authority conjunct.
      obtain ⟨s1, _, hc, hs'⟩ := spawnChainA_factors (by simpa only [execFullA] using h)
      subst hs'
      obtain ⟨_, _, hc'⟩ := createCellChainA_factors hc; subst hc'; rfl
  | bridgeMintA actor cell a value =>
      simp only [execFullA, recCMintAsset] at h
      cases hk : recKMintAsset s.kernel actor cell a value with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          show k'.revoked = s.kernel.revoked
          unfold recKMintAsset at hk; split at hk
          · injection hk with hk; subst hk; rfl
          · exact absurd hk (by simp)
  | noteSpendA nf actor spendProof =>
      simp only [execFullA, noteSpendChainA] at h
      by_cases hp : spendProof = true
      · rw [if_pos hp] at h
        cases hk : noteSpendNullifier s.kernel nf with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            commit_subst h hk
            show k'.revoked = s.kernel.revoked
            unfold noteSpendNullifier at hk; split at hk
            · exact absurd hk (by simp)
            · injection hk with hk; subst hk; rfl
      · rw [if_neg hp] at h; exact absurd h (by simp)
  -- §NOTE-CREATE — grows `commitments` (a DIFFERENT set), `revoked` untouched (always-commit).
  | noteCreateA cm actor =>
      simp only [execFullA, noteCreateChainA, noteCreateCommitment, Option.some.injEq] at h; subst h; rfl
  | makeSovereignA actor cell =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := makeSovereignStep_factors h; subst hs'; rfl
  | refusalA actor cell =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; rfl
  | receiptArchiveA actor cell =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := receiptArchiveChainA_factors h; subst hs'; rfl
  -- §swiss — four CapTP swiss-table effects, each `if stateAuthB … then match swissK … | some k' => …`
  -- (kernel updates `swiss`, never `revoked`). Gate-peel the outer `if`, then cases the kernel op.
  -- §lifecycle (Wave-3) — seal/unseal/destroy edit `lifecycle`/`deathCert`; refresh edits `delegations`
  -- — none touch `revoked` (frame: `rfl`).
  | cellSealA actor cell =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := cellSealChainA_factors h; subst hs'; rfl
  | cellUnsealA actor cell =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := cellUnsealChainA_factors h; subst hs'; rfl
  | cellDestroyA actor cell ch =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := cellDestroyChainA_factors h; subst hs'; rfl
  | refreshDelegationA actor child =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := refreshDelegationChainA_factors h; subst hs'; rfl
  -- pipelined-send leaves the kernel LITERALLY unchanged (only a clock row).
  | pipelinedSendA actor =>
      -- `kernel := s.kernel` LITERALLY — only `log` grows; `revoked` is read straight off `s.kernel`.
      simp only [execFullA, Option.some.injEq] at h; subst h; rfl
  | heapWriteA actor target addr v newRoot =>
      -- §MA-heap: the guarded `heap_root` write + `heaps` splice never touches `revoked`.
      simp only [execFullA] at h
      obtain ⟨s₁, hw, hs'⟩ := Dregg2.Substrate.HeapKernel.heapStepGuardedW_factors h
      obtain ⟨-, hs₁⟩ := stateStep_factors (stateStepGuarded_eq hw)
      subst hs'; subst hs₁; rfl

/-- **`execInnerA_revoked_eq`** — the inner-effect fold an `exerciseA` recurses through leaves the
credential revocation registry UNCHANGED. Mutual with `execFullA_revoked_eq`; chains `Eq.trans`. -/
theorem execInnerA_revoked_eq (s s' : RecChainedState) (inner : List FullActionA)
    (h : execInnerA s inner = some s') : s'.kernel.revoked = s.kernel.revoked := by
  cases inner with
  | nil => simp only [execInnerA, Option.some.injEq] at h; subst h; rfl
  | cons a rest =>
      simp only [execInnerA] at h
      cases ha : execFullA s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          rw [execInnerA_revoked_eq s1 s' rest h, execFullA_revoked_eq s s1 a ha]
end

/-! ## Step 2 — the turn- and forest-level lift (induction on the list + the pre-order bridge). -/

/-- **`execFullTurnA_revoked_eq`.** A committed per-asset full TURN leaves the credential
revocation registry UNCHANGED. By induction on the action list — each committed `execFullA` step frames
the registry (`execFullA_revoked_eq`), chained by `Eq.trans`; the empty turn is `rfl`. Mirrors
`CellNullifier.execFullTurnA_nullifiers_grow`'s structure (with `=` for `⊆`). -/
theorem execFullTurnA_revoked_eq :
    ∀ (s s' : RecChainedState) (tt : List FullActionA),
      execFullTurnA s tt = some s' → s'.kernel.revoked = s.kernel.revoked
  | s, s', [], h => by
      simp only [execFullTurnA, Option.some.injEq] at h; subst h; rfl
  | s, s', a :: rest, h => by
      simp only [execFullTurnA] at h
      cases ha : execFullA s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          exact (execFullTurnA_revoked_eq s1 s' rest h).trans (execFullA_revoked_eq s s1 a ha)

/-- **`execFullForestA_revoked_eq`.** A committed full FOREST leaves the credential revocation
registry UNCHANGED. Read straight through the pre-order bridge `execFullForestA_eq_execFullTurnA` into
the turn-level lemma — the route `CellNullifier.execFullForestA_nullifiers_grow` takes. -/
theorem execFullForestA_revoked_eq (s s' : RecChainedState) (f : FullForestA)
    (h : execFullForestA s f = some s') : s'.kernel.revoked = s.kernel.revoked := by
  rw [execFullForestA_eq_execFullTurnA] at h
  exact execFullTurnA_revoked_eq s s' (lowerForestA f) h

/-- **`execFullForestA_revoked_grow` — the grow-only COROLLARY.** Read off the equality:
`s.kernel.revoked ⊆ s'.kernel.revoked` (the permanent-revocation frame as the dregg1
`RevocationRegistry`'s insert-only `HashSet` sees it). Stated as `⊆` so the carry below is forward-
compatible with a future explicit `cap_revoke` effect that GROWS the registry. -/
theorem execFullForestA_revoked_grow (s s' : RecChainedState) (f : FullForestA)
    (h : execFullForestA s f = some s') : s.kernel.revoked ⊆ s'.kernel.revoked := by
  rw [execFullForestA_revoked_eq s s' f h]; exact List.Subset.refl _

/-! ## Step 3 — THE CROWN: `rev0 ⊆ s.kernel.revoked` carried FOREVER by `livingCellA_carries`. -/

/-- **`livingCellA_revoked_grow`** — the permanent-revocation crown: for any baseline `rev0 ⊆
s.kernel.revoked`, every id in `rev0` stays revoked at every index of every adversarial trajectory
`trajA s sched`. Carried by `livingCellA_carries` with `Good := (rev0 ⊆ ·.kernel.revoked)`, whose
one-step obligation is `execFullForestA_revoked_grow` on a commit and the stay-put self-loop on a reject.
A non-conservation safety: it reads the registry, never the per-asset measure. -/
theorem livingCellA_revoked_grow (rev0 : List Nat) (s : RecChainedState)
    (hinit : rev0 ⊆ s.kernel.revoked) (sched : SchedA) :
    ∀ n, rev0 ⊆ (trajA s sched n).kernel.revoked :=
  livingCellA_carries (fun s' => rev0 ⊆ s'.kernel.revoked)
    (fun a cf h => by
      -- One-step preservation. `cellNextA a cf = (execFullForestA a cf.1).getD a`: on a COMMIT the
      -- forest registry frame keeps (≥) the revocation registry (chain by `List.Subset.trans`); on a
      -- REJECT the state is the UNCHANGED `a`, so the baseline `⊆` is preserved trivially.
      show rev0 ⊆ (cellNextA a cf).kernel.revoked
      unfold cellNextA
      cases hc : execFullForestA a cf.1 with
      | some a' => simp only [Option.getD_some]
                   exact List.Subset.trans h (execFullForestA_revoked_grow a a' cf.1 hc)
      | none    => simp only [Option.getD_none]; exact h)
    s hinit sched

/-! ## Step 4 — THE HEADLINE: `identity_revoked_forever` — a revoked identity can NEVER be re-validated. -/

/-- **`livingCellA_identity_revoked_forever`** — if `credNul` is in the revocation registry initially,
it is in the registry at every index of every adversarial trajectory. The single-element instance of
the crown (`rev0 := [credNul]`). -/
theorem livingCellA_identity_revoked_forever (credNul : Nat) (s : RecChainedState)
    (hinit : credNul ∈ s.kernel.revoked) (sched : SchedA) :
    ∀ n, credNul ∈ (trajA s sched n).kernel.revoked := by
  intro n
  have h := livingCellA_revoked_grow [credNul] s (by
    intro x hx; rw [List.mem_singleton] at hx; subst hx; exact hinit) sched n
  exact h (List.mem_singleton.mpr rfl)

/-- **`identity_gate_revoked_forever`** — a revoked identity's auth gate fail-closes at every reachable
state of every trajectory: if `na.credNul` is revoked initially, then `gateOK na (trajA s sched n) =
false` for all `n`. Composes `livingCellA_identity_revoked_forever` with `gateOK_revoked_fails`.
The `NodeAuthC` type parameters `{Digest Proof … Tag}` are inferred from `na`; the proof reads only
`na.credNul` and the kernel registry. -/
theorem identity_gate_revoked_forever
    {Digest Proof Request Stmt Wit CellId Rights Ctx Gateway Bytes Tag : Type}
    [DecidableEq CellId] [SemilatticeInf Rights] [OrderTop Rights] [DecidableLE Rights]
    [Dregg2.Laws.Verifiable Stmt Wit]
    [DecidableEq Tag] [CaveatChain.MacKernel (CaveatChain.Key Tag) Bytes Tag]
    [FullForestAuth.AuthPortal (FullForestAuth.Authorization Digest Proof) Ctx]
    (na : FullForestAuth.NodeAuthC (Digest := Digest) (Proof := Proof) (Request := Request)
      (Stmt := Stmt) (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx)
      (Gateway := Gateway) (Bytes := Bytes) (Tag := Tag))
    (s : RecChainedState) (hinit : na.credNul ∈ s.kernel.revoked) (sched : SchedA) :
    ∀ n, FullForestAuth.gateOK na (trajA s sched n) = false := by
  intro n
  refine FullForestAuth.gateOK_revoked_fails na (trajA s sched n) ?_
  -- `credNul ∈ revoked` (carried forever) ⇒ `revoked.contains credNul = true`.
  rw [List.contains_iff_mem]
  exact livingCellA_identity_revoked_forever na.credNul s hinit sched n

/-! ## It runs (`#eval`) — the registry is non-empty and stable across a real committed turn.

We exhibit a kernel with `credNul = 42` already revoked, run a real conserving transfer, and observe
`42` is still revoked afterward. This witnesses non-vacuity: the carried invariant bounds a
non-empty, stable registry. -/

/-- A real kernel state with credential id `42` ALREADY revoked: `fma0` with `revoked := [42]`. -/
def fmaRevoked : RecChainedState :=
  { fma0 with kernel := { fma0.kernel with revoked := [42] } }

#guard fmaRevoked.kernel.revoked == [42]                                              -- [42] (42 is revoked)
#guard fmaRevoked.kernel.revoked.contains 42                                          -- true
-- run the real conserving transfer; the revocation registry is UNCHANGED (still [42]):
#guard (execFullForestA fmaRevoked transferCF.1).map (fun s' => s'.kernel.revoked) == some [42]            -- some [42]
#guard (execFullForestA fmaRevoked transferCF.1).map (fun s' => s'.kernel.revoked.contains 42) == some true  -- some true (STILL revoked)
#guard (execFullForestA fmaRevoked transferCF.1).map
        (fun s' => decide (([42] : List Nat) ⊆ s'.kernel.revoked)) == some true       -- some true (the carried ⊆)
-- a credential id NOT revoked (`99`) is absent — the registry has teeth, not all-true:
#guard fmaRevoked.kernel.revoked.contains 99 == false                                 -- false

/-! ## Axiom hygiene -/

#assert_axioms execFullA_revoked_eq
#assert_axioms execFullTurnA_revoked_eq
#assert_axioms execFullForestA_revoked_eq
#assert_axioms execFullForestA_revoked_grow
#assert_axioms livingCellA_revoked_grow
#assert_axioms livingCellA_identity_revoked_forever
#assert_axioms identity_gate_revoked_forever

end Dregg2.Apps.Identity
