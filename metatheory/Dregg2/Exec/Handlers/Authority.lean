/-
# Dregg2.Exec.Handlers.Authority — the AUTHORITY / DELEGATION handler batch.

The THIRD batch of `EffectHandler` instances (after the `transfer`/`escrow`/`state` slice in
`Dregg2.Exec.Handler` and the `StateSupply`/`Escrow` batches). This file EXTENDS the algebra with the
capability-graph cluster: the Granovetter delegations and the self-limiting revocations. We do NOT
touch `execFullA`/`FullActionA` (the cutover is a later step); we only IMPORT and REUSE the proved
kernel palette from `Dregg2.Exec.AuthTurn` (`recKDelegate`/`recKDelegateAtten`/`recKRevokeTarget` +
their frame/non-amplification lemmas) and `Dregg2.Exec.Caps`.

Every effect of this batch is balance-NEUTRAL: it edits the `caps` cap-graph (or merely the actor's
own c-list) and NEVER the `bal` ledger or the `escrows` holding-store, so the COMBINED per-asset
measure `recTotalAssetWithEscrow` is UNCHANGED at every asset — `delta = 0`, and `conserves` is the
trivial `caps`-only frame (`recTotalAsset` reads `bal`+`accounts`, `escrowHeldAsset` reads `escrows`;
neither touches `caps`, so both reduce on the post-state by `ring`).

Two faces:

  * **DELEGATIONS (the KEY FIX — non-amplification by construction).** `delegateA`/`introduceA`/
    `validateHandoffA`/`delegateAttenA` all route through the ATTENUATED kernel step
    `recKDelegateAtten` (the faithful `apply_introduce`), NOT the verbatim-copy `recKDelegate`. The
    granted cap is an `attenuate keep`-narrowing of the delegator's HELD cap to `t`, so its conferred
    rights are provably `⊆` the held cap's (`recKDelegateAtten_non_amplifying`,
    `AuthTurn.lean:320` — a genuine `granted.rights ≤ held.rights` over the real `ExecAuth` lattice,
    NOT a `()≤()` collapse) — granted authority CANNOT EXCEED held. The `auth` gate is the Granovetter
    connectivity premise (the delegator must already hold a cap conferring an edge to `t` — "only
    connectivity begets connectivity"), and `auth_gated` makes it a TYPING obligation: a committed
    delegation proves the premise held. The non-amplification keystone is surfaced PER HANDLER
    (`delegateA_non_amplifying` &c.). For the three full-authority delegations (`delegateA`/
    `introduceA`/`validateHandoffA`) we delegate with `keep := allAuths` (attenuate-to-full = the
    held cap itself), so they are the maximal in-rights delegation — still provably subset-held by the
    SAME lemma. `delegateAttenA` carries an explicit narrower `keep`.

  * **REVOCATIONS (genuinely TOTAL + SELF-LIMITING).** `attenuateA`/`revokeDelegationA`/`dropRefA`/
    `revokeA` only SHRINK authority — `recKRevokeTarget` filters out the holder's `t`-conferring caps,
    `attenuateSlotF` narrows the actor's own held cap in place. They ALWAYS commit (revocation cannot
    fail — at worst it is the identity), so we model them as TOTAL handlers (`step` returns `some`
    unconditionally) and prove `conserves` (`delta = 0`) directly. They are SELF-LIMITING: the
    post-state's caps are a `⊆`-shrinkage of the pre-state's (`revoke_subset`/`attenuate_subset`), so
    NO amplification is possible — surfaced as `*_self_limiting` keystones. `auth`/`admission` are
    default-true (a holder may always renounce its OWN authority; there is no cell to gate liveness on
    — the move only removes the actor's reach).

EVAL-VERIFIED (`§TEETH`): a delegation whose delegator lacks connectivity to the target is REJECTED
(`none`); a within-rights delegation by a connected delegator SUCCEEDS (`some`) and the granted cap is
provably subset-held; a revoke/attenuate/dropRef ALWAYS succeeds (`some`) and only shrinks the actor's
reach; and every authority effect leaves the combined per-asset measure UNCHANGED.

Pure, computable, `#eval`-able. Verified standalone: `lake build Dregg2.Exec.Handlers.Authority`.
-/
import Dregg2.Exec.Handler
import Dregg2.Exec.CapTP

namespace Dregg2.Exec.Handlers.Authority

open Dregg2.Authority (Cap Auth Caps Label capAuthConferred)
open Dregg2.Exec
open Dregg2.Exec.Handler
open Dregg2.Exec.TurnExecutorFull (acceptsEffects attenuateSlotF)
open scoped BigOperators

/-! ## §0 — The `caps`-only frame: an authority edit conserves the combined per-asset measure.

Every step of this batch produces a post-state of the form `{ k with caps := … }` (or merely re-binds
`caps`). `recTotalAssetWithEscrow k b = recTotalAsset k b + escrowHeldAsset k b` reads `bal`+`accounts`
(via `recTotalAsset`) and `escrows` (via `escrowHeldAsset`) — NEVER `caps`. So a `caps`-only edit leaves
the combined measure UNCHANGED at every asset. This single frame lemma discharges `conserves` for the
whole cluster (composed with each step's `caps`-only post-state shape). -/

/-- A `caps`-only re-binding leaves the combined per-asset measure fixed at every asset. The shared
`conserves` engine for the whole authority cluster: `recTotalAsset` (= `∑ bal`) and `escrowHeldAsset`
(= `∑` over `escrows`) both ignore `caps`. -/
theorem capsOnly_recTotalAssetWithEscrow_fixed (k : RecordKernelState) (f : Caps) (b : AssetId) :
    recTotalAssetWithEscrow { k with caps := f } b = recTotalAssetWithEscrow k b := by
  simp only [recTotalAssetWithEscrow, recTotalAsset, escrowHeldAsset]

/-! ## §1 — DELEGATIONS: the attenuated Granovetter grant (the KEY FIX).

All four delegation handlers route through `recKDelegateAtten` (the faithful `apply_introduce`): gate
on the delegator holding a cap conferring an edge to `t` (the Granovetter connectivity premise), then
grant `recipient` the delegator's HELD cap to `t` attenuated to `keep`. The granted cap's real rights
are `⊆` the held cap's (`recKDelegateAtten_non_amplifying`) — granted CANNOT EXCEED held. -/

/-- Delegation arguments: the `delegator` (authority source), the `recipient` (grant target), the
target `t` connectivity is granted to, and the `keep` rights mask the granted cap is attenuated to. -/
structure DelegateArgs where
  /-- The delegator (must already hold a cap conferring an edge to `target` — Granovetter premise). -/
  delegator : CellId
  /-- The recipient gaining the (attenuated) connectivity to `target`. -/
  recipient : CellId
  /-- The target the delegated connectivity points to. -/
  target : CellId
  /-- The rights mask the granted cap is attenuated to (`⊆` the held cap's conferred rights). -/
  keep : List Auth

/-- The full rights list — used as the `keep` mask for the maximal-in-rights delegations
(`delegateA`/`introduceA`/`validateHandoffA`): `attenuate allAuths c = c` on the held cap's rights, so
the delegation grants the held authority unchanged — STILL provably `⊆` held by
`recKDelegateAtten_non_amplifying` (the inequality holds for ANY `keep`). -/
def allAuths : List Auth := [.read, .write, .grant, .call, .reply, .reset, .control]

/-- **The R-closing attenuated delegation step (the KEY FIX).** Route the delegation through
`recKDelegateAtten` — the granted cap is an `attenuate keep`-narrowing of the delegator's held cap to
`t`, NEVER a fresh control cap, so granted authority is provably `⊆` held. Fail-closed: no held cap to
`t` ⇒ `none` (the Granovetter premise is unmet). -/
def delegateAttenStep (k : RecordKernelState) (a : DelegateArgs) : Option RecordKernelState :=
  recKDelegateAtten k a.delegator a.recipient a.target a.keep

/-- The Granovetter connectivity gate the delegation requires (the `auth` field): the delegator
already holds a cap conferring an edge to `target`. This is the EXACT gate `recKDelegateAtten` checks,
so `auth_gated` is provable directly off the committed step. -/
def delegateGateB (k : RecordKernelState) (a : DelegateArgs) : Bool :=
  (k.caps a.delegator).any (fun cap => confersEdgeTo a.target cap)

/-- **`delegateAttenH` — the registered attenuated-delegation handler.** `step` routes through
`recKDelegateAtten` (granted `⊆` held); `conserves` is the `caps`-only frame (`delta = 0`); `auth_gated`
recovers the Granovetter connectivity premise from the committed step; `admission_gated` is the same
gate (no separate cell-liveness — the move only edits the cap graph). -/
def delegateAttenH : EffectHandler DelegateArgs where
  step := delegateAttenStep
  delta := fun _ _ => 0
  auth := delegateGateB
  admission := delegateGateB
  trace := fun a => { actor := a.delegator, src := a.delegator, dst := a.recipient, amt := 0 }
  auth_gated := by
    intro s a s' h
    unfold delegateAttenStep recKDelegateAtten at h
    show delegateGateB s a = true
    unfold delegateGateB
    by_cases hg : (s.caps a.delegator).any (fun cap => confersEdgeTo a.target cap) = true
    · exact hg
    · rw [if_neg hg] at h; exact absurd h (by simp)
  admission_gated := by
    intro s a s' h
    unfold delegateAttenStep recKDelegateAtten at h
    show delegateGateB s a = true
    unfold delegateGateB
    by_cases hg : (s.caps a.delegator).any (fun cap => confersEdgeTo a.target cap) = true
    · exact hg
    · rw [if_neg hg] at h; exact absurd h (by simp)
  conserves := by
    intro s a s' h b
    unfold delegateAttenStep recKDelegateAtten at h
    by_cases hg : (s.caps a.delegator).any (fun cap => confersEdgeTo a.target cap) = true
    · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h
      rw [capsOnly_recTotalAssetWithEscrow_fixed]; ring
    · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`delegateAttenH` is NON-AMPLIFYING (the headline, PROVED).** The cap the delegation grants the
recipient confers REAL rights `⊆` the delegator's held cap to `t`: `confRights (attenuate keep held) ≤
confRights held` over the genuine `ExecAuth` lattice (`recKDelegateAtten_non_amplifying`). Granted
authority cannot exceed held — the rights-amplification hole is closed BY CONSTRUCTION. -/
theorem delegateAttenH_non_amplifying (k : RecordKernelState) (a : DelegateArgs) :
    confRights (attenuate a.keep (heldCapTo k.caps a.delegator a.target))
      ≤ confRights (heldCapTo k.caps a.delegator a.target) :=
  recKDelegateAtten_non_amplifying k.caps a.delegator a.target a.keep

/-- The full-authority delegations (`delegateA`/`introduceA`/`validateHandoffA`) ARE `delegateAttenH`
with `keep := allAuths` — the maximal-in-rights delegation. They share its discharged obligations and
its non-amplification proof for free (the inequality holds for ANY `keep`, so it holds for `allAuths`).
We register them under distinct tags so the audit trail records the op provenance
(delegate / introduce / validate-handoff), but they are DEFINITIONALLY the same handler. -/
def delegateH : EffectHandler DelegateArgs := delegateAttenH

/-- `introduceA` — the 3-party Granovetter introduce, attenuated path. Same handler as `delegateH`. -/
def introduceH : EffectHandler DelegateArgs := delegateAttenH

/-- `validateHandoffA` — the graph-level consequence of an accepted two-signature CapTP handoff,
attenuated path. Same handler as `delegateH`. -/
def validateHandoffH : EffectHandler DelegateArgs := delegateAttenH

/-! ## §2 — REVOCATIONS: genuinely TOTAL, SELF-LIMITING authority shrinkage.

`revokeA`/`dropRefA`/`revokeDelegationA` filter out the holder's `t`-conferring caps
(`recKRevokeTarget`); `attenuateA` narrows the actor's own `idx`-th held cap in place
(`attenuateSlotF`). All four ALWAYS commit (revocation cannot fail) — modelled as TOTAL handlers
returning `some` unconditionally. They only SHRINK the actor's OWN reach (monotone decrease), so no
amplification is possible and `conserves` (`delta = 0`) is proved directly off the `caps`-only frame.
`auth`/`admission` are default-true: a holder may always renounce its own authority. -/

/-! ### §2.1 — `revokeA` / `dropRefA` / `revokeDelegationA`: target revocation (always commits). -/

/-- Revoke arguments: the `holder` whose authority shrinks + the target `t` it loses connectivity to. -/
structure RevokeArgs where
  /-- The holder dropping every cap conferring an edge to `target` (only its OWN reach shrinks). -/
  holder : CellId
  /-- The target the holder loses connectivity to. -/
  target : CellId

/-- The (TOTAL) revoke step: `recKRevokeTarget` always commits (it only filters), so we wrap it in
`some`. Edits ONLY `caps` (the holder's slot loses its `t`-conferring caps); balances untouched. -/
def revokeStep (k : RecordKernelState) (a : RevokeArgs) : Option RecordKernelState :=
  some (recKRevokeTarget k a.holder a.target)

/-- **`revokeH` — the registered TOTAL revocation handler.** Always commits (revocation only subtracts
authority). `delta = 0`; `conserves` is the `caps`-only frame (`recKRevokeTarget` re-binds only `caps`).
`auth`/`admission` default-true: a holder may always renounce its own reach. -/
def revokeH : EffectHandler RevokeArgs where
  step := revokeStep
  delta := fun _ _ => 0
  auth := fun _ _ => true
  admission := fun _ _ => true
  trace := fun a => { actor := a.holder, src := a.holder, dst := a.holder, amt := 0 }
  auth_gated := by intro s a s' _; rfl
  admission_gated := by intro s a s' _; rfl
  conserves := by
    intro s a s' h b
    unfold revokeStep at h
    simp only [Option.some.injEq] at h; subst h
    -- `recKRevokeTarget` produces `{ s with caps := … }` — a caps-only edit.
    unfold recKRevokeTarget
    rw [capsOnly_recTotalAssetWithEscrow_fixed]; ring

/-- **`revokeH` is SELF-LIMITING (PROVED).** After the revoke, the holder's surviving caps are a SUBLIST
of its pre-state caps at EVERY slot (`recKRevokeTarget` only filters), so authority strictly shrinks —
no amplification is possible. The monotone-decrease witness for the total handler. -/
theorem revokeH_self_limiting (k : RecordKernelState) (a : RevokeArgs) (l : Label) :
    (recKRevokeTarget k a.holder a.target).caps l ⊆ k.caps l := by
  unfold recKRevokeTarget
  by_cases hl : l = a.holder
  · subst hl; simp only [if_pos]; intro d hd; exact List.mem_of_mem_filter hd
  · simp only [if_neg hl]; exact fun d hd => hd

/-- `dropRefA` — the CapTP GC decrement (the holder drops its edge to the target). Same total
self-limiting revocation handler as `revokeH` (distinct dregg1 op, same `removeEdge` graph move). -/
def dropRefH : EffectHandler RevokeArgs := revokeH

/-- `revokeDelegationA` — a parent revokes a child's delegation (the child's edge is removed). Same
total self-limiting revocation handler as `revokeH` (distinct dregg1 op, same `removeEdge` move). -/
def revokeDelegationH : EffectHandler RevokeArgs := revokeH

/-! ### §2.2 — `attenuateA`: in-place self-narrowing of the actor's held cap (always commits). -/

/-- Attenuate arguments: the `actor` whose own c-list is narrowed, the `idx` of the slot cap to narrow,
and the `keep` rights mask. The narrowing is on the ACTOR's OWN authority — self-limiting. -/
structure AttenuateArgs where
  /-- The actor narrowing its OWN held cap (no other slot/cell is touched). -/
  actor : CellId
  /-- The index of the actor's c-list cap to narrow. -/
  idx : Nat
  /-- The rights mask the cap is narrowed to (`attenuate` only drops rights — never widens). -/
  keep : List Auth

/-- The (TOTAL) attenuate step: narrow the actor's `idx`-th cap to `keep` in place
(`attenuateSlotF`) — always commits (attenuation cannot fail; at worst the identity, still
narrower-or-equal). Edits ONLY `caps` (the actor's own slot); balances untouched. -/
def attenuateStep (k : RecordKernelState) (a : AttenuateArgs) : Option RecordKernelState :=
  some { k with caps := attenuateSlotF k.caps a.actor a.idx a.keep }

/-- **`attenuateH` — the registered TOTAL self-attenuation handler.** Always commits (the purest
non-amplification: narrow the actor's own cap). `delta = 0`; `conserves` is the `caps`-only frame.
`auth`/`admission` default-true: an actor may always narrow its own authority. -/
def attenuateH : EffectHandler AttenuateArgs where
  step := attenuateStep
  delta := fun _ _ => 0
  auth := fun _ _ => true
  admission := fun _ _ => true
  trace := fun a => { actor := a.actor, src := a.actor, dst := a.actor, amt := 0 }
  auth_gated := by intro s a s' _; rfl
  admission_gated := by intro s a s' _; rfl
  conserves := by
    intro s a s' h b
    unfold attenuateStep at h
    simp only [Option.some.injEq] at h; subst h
    rw [capsOnly_recTotalAssetWithEscrow_fixed]; ring

/-- **`attenuateH` is NON-AMPLIFYING (PROVED).** The narrowed cap confers a genuine `List Auth` SUBSET
of the original: `capAuthConferred (attenuate keep c) ⊆ capAuthConferred c` (`attenuate_subset`). The
actor's own authority only shrinks — the purest self-limiting move. -/
theorem attenuateH_non_amplifying (keep : List Auth) (c : Cap) :
    capAuthConferred (attenuate keep c) ⊆ capAuthConferred c :=
  attenuate_subset keep c

/-! ## §3 — The AUTHORITY registry coproduct and the `ClosedEffect` builders.

Each handler is one well-typed `PackedHandler` — the obligation proofs are a TYPING condition on entry.
This list plugs straight into the generic `turn_conserves` from `Dregg2.Exec.Handler` (it is generic
over the registry). -/

/-- The authority/delegation batch registry (the coproduct menu for this cluster). -/
def authorityRegistry : Registry :=
  [ ⟨DelegateArgs, delegateH⟩, ⟨DelegateArgs, introduceH⟩, ⟨DelegateArgs, validateHandoffH⟩,
    ⟨DelegateArgs, delegateAttenH⟩,
    ⟨AttenuateArgs, attenuateH⟩,
    ⟨RevokeArgs, revokeDelegationH⟩, ⟨RevokeArgs, dropRefH⟩, ⟨RevokeArgs, revokeH⟩ ]

/-- Build a closed delegate effect (tag `0`; full-authority attenuated delegation, `keep := allAuths`). -/
def delegateEffect (delegator recipient target : CellId) : ClosedEffect :=
  { tag := 0, Args := DelegateArgs,
    args := { delegator := delegator, recipient := recipient, target := target, keep := allAuths },
    handler := delegateH }

/-- Build a closed introduce effect (tag `1`; full-authority attenuated 3-party introduce). -/
def introduceEffect (introducer recipient target : CellId) : ClosedEffect :=
  { tag := 1, Args := DelegateArgs,
    args := { delegator := introducer, recipient := recipient, target := target, keep := allAuths },
    handler := introduceH }

/-- Build a closed validate-handoff effect (tag `2`; full-authority attenuated handoff). -/
def validateHandoffEffect (introducer recipient target : CellId) : ClosedEffect :=
  { tag := 2, Args := DelegateArgs,
    args := { delegator := introducer, recipient := recipient, target := target, keep := allAuths },
    handler := validateHandoffH }

/-! ### §CERT — the REAL CapTP certificate attenuation (no longer `keep := allAuths`).

dregg1's `validate_handoff` does NOT confer the introducer's full held rights — it confers the
`HandoffCertificate.permissions` mask (`Exec.CapTP.HandoffCert.granted`), which the introducer's signed
certificate names. We wire that mask in as the delegation `keep`: the recipient receives the held cap
ATTENUATED to the cert's allowed effects, NOT `allAuths`. `granted ⊆ held` is the certificate's
non-amplification clause (`HandoffValid.nonAmplifying`), discharged for ANY `keep` by
`delegateAttenH_non_amplifying`. The cert mask is the rights the cert's `granted` cap confers
(`Dregg2.Authority.capAuthConferred cert.granted`). -/

/-- The cert's allowed-effect mask: the rights the certificate's `granted` cap names (the
`HandoffCertificate.permissions`). `HandoffCert`'s `Cap` is the abstract `Spec.Cap` with a `rights`
field, so the mask is exactly `cert.granted.rights`. -/
def certMask (cert : Dregg2.Exec.CapTP.HandoffCert CellId (List Auth)) : List Auth :=
  cert.granted.rights

/-- **Build a closed validate-handoff effect from the REAL certificate** (tag `2`). The recipient
receives the held cap ATTENUATED to the certificate's allowed-effect mask (`certMask cert`), the
faithful CapTP `permissions` — NOT the blanket `allAuths`. This is the cert-attenuated handoff the
`§DEFER` carried open. -/
def validateHandoffCertEffect (cert : Dregg2.Exec.CapTP.HandoffCert CellId (List Auth))
    (target : CellId) : ClosedEffect :=
  { tag := 2, Args := DelegateArgs,
    args := { delegator := cert.introducer, recipient := cert.recipient, target := target,
              keep := certMask cert },
    handler := validateHandoffH }

/-- **`validateHandoffCert_non_amplifying` — PROVED.** A cert-attenuated handoff confers the recipient
REAL rights `⊆` the introducer's held cap to `target`: the cert mask cannot amplify (`granted ⊆ held`,
`HandoffValid.nonAmplifying`), discharged off `delegateAttenH_non_amplifying` for the cert's `keep`. -/
theorem validateHandoffCert_non_amplifying (k : RecordKernelState)
    (cert : Dregg2.Exec.CapTP.HandoffCert CellId (List Auth)) (target : CellId) :
    confRights (attenuate (certMask cert) (heldCapTo k.caps cert.introducer target))
      ≤ confRights (heldCapTo k.caps cert.introducer target) :=
  recKDelegateAtten_non_amplifying k.caps cert.introducer target (certMask cert)

/-- Build a closed attenuated-delegate effect (tag `3`; explicit narrower `keep`). -/
def delegateAttenEffect (delegator recipient target : CellId) (keep : List Auth) : ClosedEffect :=
  { tag := 3, Args := DelegateArgs,
    args := { delegator := delegator, recipient := recipient, target := target, keep := keep },
    handler := delegateAttenH }

/-- Build a closed attenuate effect (tag `4`; in-place self-narrowing of the actor's `idx`-th cap). -/
def attenuateEffect (actor : CellId) (idx : Nat) (keep : List Auth) : ClosedEffect :=
  { tag := 4, Args := AttenuateArgs,
    args := { actor := actor, idx := idx, keep := keep }, handler := attenuateH }

/-- Build a closed revoke-delegation effect (tag `5`). -/
def revokeDelegationEffect (holder target : CellId) : ClosedEffect :=
  { tag := 5, Args := RevokeArgs, args := { holder := holder, target := target },
    handler := revokeDelegationH }

/-- Build a closed drop-ref effect (tag `6`). -/
def dropRefEffect (holder target : CellId) : ClosedEffect :=
  { tag := 6, Args := RevokeArgs, args := { holder := holder, target := target }, handler := dropRefH }

/-- Build a closed revoke effect (tag `7`). -/
def revokeEffect (holder target : CellId) : ClosedEffect :=
  { tag := 7, Args := RevokeArgs, args := { holder := holder, target := target }, handler := revokeH }

/-! ## §4 — TEETH: the non-amplification fix + the self-limiting revokes, evaluated.

A delegation by a delegator WITHOUT connectivity to the target is REJECTED (`none` — the Granovetter
premise is unmet); a within-rights delegation by a CONNECTED delegator SUCCEEDS (`some`) and the
granted cap is an attenuation of the held cap (provably subset-held); a revoke/attenuate/dropRef ALWAYS
succeeds (`some` — total, self-limiting); and every authority effect leaves the combined per-asset
measure UNCHANGED (`delta = 0`). -/

/-- A 2-cell, 1-asset fixture: cells 0 and 1 are live accounts; cell 0 holds 100 of asset 0; cell 0
holds a `node 7` cap (connectivity to target 7) and an `endpoint 9 [write]` cap (write authority over
target 9). Cell 1 (and everyone else) holds NO caps. -/
def as0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun c => if c = 0 then [Cap.node 7, Cap.endpoint 9 [Auth.write]] else []
    bal := fun c a => if c = 0 ∧ a = 0 then 100 else 0 }

-- §TEETH-1 (KEY FIX — Granovetter premise bites): a delegation by cell 1 (which holds NO cap to
-- target 7) is REJECTED — connectivity does not begin from nothing.
#guard ((execEffect (delegateEffect 1 0 7) as0).isSome) == false  --  false (delegator 1 lacks connectivity)
-- §TEETH-2 (within-rights delegation): cell 0 (which HOLDS connectivity to 7) delegates to cell 1 —
-- SUCCEEDS (the held cap to 7 is attenuated and granted; granted ⊆ held).
#guard ((execEffect (delegateEffect 0 1 7) as0).isSome)  --  true (delegator 0 holds a `node 7` cap)
-- §TEETH-3 (granted ⊆ held): after the delegation, recipient cell 1 holds the (attenuated-to-full)
-- held cap to 7 — `attenuate allAuths (Cap.node 7) = Cap.node 7` (a node cap has no rights list to
-- narrow), so the granted cap is exactly the held cap, NOT a manufactured stronger cap.
#guard ((execEffect (delegateEffect 0 1 7) as0).map (fun k => k.caps 1)) == some [Cap.node 7]  --  some [Cap.node 7]
-- §TEETH-4 (NARROWED delegation): cell 0 delegates its endpoint-9-write cap attenuated to `[]` (drop
-- write) — the granted cap confers NO rights (strictly narrower than the held `[write]`).
#guard ((execEffect (delegateAttenEffect 0 1 9 []) as0).map (fun k => k.caps 1)) == some [Cap.endpoint 9 []]  -- some [Cap.endpoint 9 []]   (write DROPPED — granted ⊊ held)
-- §TEETH-5 (revoke is TOTAL): cell 0 revokes its connectivity to target 7 — ALWAYS succeeds, and the
-- `node 7` cap is filtered out of its slot (only the endpoint-9 cap survives).
#guard ((execEffect (revokeEffect 0 7) as0).map (fun k => k.caps 0)) == some [Cap.endpoint 9 [Auth.write]]  -- some [Cap.endpoint 9 [Auth.write]]   (the `node 7` cap is gone)
-- §TEETH-6 (dropRef is TOTAL + self-limiting): dropRef always commits; cell 0's reach only shrinks.
#guard ((execEffect (dropRefEffect 0 9) as0).map (fun k => k.caps 0)) == some [Cap.node 7]  -- some [Cap.node 7]   (the endpoint-9 cap dropped)
-- §TEETH-7 (attenuate is TOTAL + self-limiting): cell 0 narrows its OWN idx-1 cap (endpoint 9) to `[]`
-- — always commits; the actor's own authority shrinks (write dropped).
#guard ((execEffect (attenuateEffect 0 1 []) as0).map (fun k => k.caps 0)) == some [Cap.node 7, Cap.endpoint 9 []]  -- some [Cap.node 7, Cap.endpoint 9 []]   (idx-1 narrowed in place)
-- §CERT-TEETH (the REAL CapTP certificate attenuation BITES). A fixture where cell 0 holds
--   `endpoint 9 [read,write]` to target 9; a certificate granting only `endpoint 9 [read]` hands off the
--   READ-ONLY view — the recipient receives `[read]`, NOT the full `[read,write]` and NOT `allAuths`.
def asCert : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => default
    caps := fun c => if c = 0 then [Cap.endpoint 9 [Auth.read, Auth.write]] else []
    bal := fun c a => if c = 0 ∧ a = 0 then 100 else 0 }

/-- A read-only handoff certificate: introducer 0 hands target-9 to recipient 1, granting only `read`.
`HandoffCert`'s caps are the abstract `Spec.Cap = ⟨target, rights⟩`. -/
def readOnlyCert : Dregg2.Exec.CapTP.HandoffCert CellId (List Auth) :=
  { introducer := 0, recipient := 1,
    held := ⟨9, [Auth.read, Auth.write]⟩, granted := ⟨9, [Auth.read]⟩ }

-- the cert mask is exactly the certificate's `granted` rights — `[read]`, NOT `allAuths`:
#guard (certMask readOnlyCert == [Auth.read])
-- the recipient receives the held cap ATTENUATED to the cert mask: `[read]` (WRITE DROPPED) — the real
-- CapTP `permissions`, strictly narrower than the held `[read,write]` and than the old `allAuths` path:
#guard ((execEffect (validateHandoffCertEffect readOnlyCert 9) asCert).map (fun k => k.caps 1))
        == some [Cap.endpoint 9 [Auth.read]]  -- write DROPPED by the cert mask (granted ⊊ held)
-- ...whereas the OLD `keep := allAuths` path would have conferred the FULL held `[read,write]` — the
-- cert mask is what makes the handoff faithfully narrowing:
#guard ((execEffect (validateHandoffEffect 0 1 9) asCert).map (fun k => k.caps 1))
        == some [Cap.endpoint 9 [Auth.read, Auth.write]]  -- allAuths = identity-on-rights (the looser path)
-- the cert handoff is still authority-gated: an introducer holding NO edge to the target is REJECTED.
#guard ((execEffect (validateHandoffCertEffect { readOnlyCert with introducer := 1 } 9) asCert).isSome) == false

-- §TEETH-8 (CONSERVATION): a within-rights delegation leaves the combined per-asset measure UNCHANGED.
#guard ((execEffect (delegateEffect 0 1 7) as0).map
        (fun k => (recTotalAssetWithEscrow as0 0, recTotalAssetWithEscrow k 0))) == some (100, 100)  --  some (100, 100)
-- §TEETH-9 (CONSERVATION): a revoke leaves the combined per-asset measure UNCHANGED.
#guard ((execEffect (revokeEffect 0 7) as0).map (fun k => recTotalAssetWithEscrow k 0)) == some 100  --  some 100
-- §TEETH-10 (turn conserves): a turn = [delegate; attenuate; revoke] runs through the registry foldlM
-- and the combined measure is unchanged (every authority effect has `delta = 0`).
#guard ((execTurn [delegateEffect 0 1 7, attenuateEffect 0 1 [], revokeEffect 1 7] as0).map
        (fun k => recTotalAssetWithEscrow k 0)) == some 100  --  some 100

/-! ## §5 — turnDelta cross-check: the authority turn moves the measure by exactly 0. -/
#guard (turnDelta [delegateEffect 0 1 7, attenuateEffect 0 1 [], revokeEffect 1 7] 0) == 0  --  0

/-! ## §6 — Axiom-hygiene pins (every handler keystone rests only on the three kernel axioms).

Pinning each handler `def` pins its obligation FIELDS transitively (the structure literal carries the
proofs), so these pins certify that delegation/revocation soundness rests only on the kernel triple —
a `sorryAx` anywhere in the composed lemmas would fail the pin (and the build). The non-amplification /
self-limiting keystones are pinned directly. -/

#assert_axioms capsOnly_recTotalAssetWithEscrow_fixed
#assert_axioms delegateAttenH
#assert_axioms delegateH
#assert_axioms introduceH
#assert_axioms validateHandoffH
#assert_axioms delegateAttenH_non_amplifying
#assert_axioms validateHandoffCert_non_amplifying
#assert_axioms revokeH
#assert_axioms dropRefH
#assert_axioms revokeDelegationH
#assert_axioms revokeH_self_limiting
#assert_axioms attenuateH
#assert_axioms attenuateH_non_amplifying

/-! ## §DEFER — honest scope of this batch.

Deliberately OUT of this batch (documented, NOT a silent gap):

  * **The full-authority `keep := allAuths` choice** (for `delegateA`/`introduceA` — and the bare
    `validateHandoffEffect`). These delegate the held cap with NO rights narrowing (`attenuate allAuths
    c = c` on the rights list): the MAXIMAL in-rights delegation — still provably `⊆` held
    (`delegateAttenH_non_amplifying`), so non-amplifying. A caller wanting a strictly narrower grant uses
    `delegateAttenEffect` with an explicit `keep` (the §TEETH-4 path).

  * **CLOSED — the REAL CapTP certificate attenuation** (§CERT). `validateHandoffCertEffect` takes the
    `Exec.CapTP.HandoffCert` and uses the certificate's allowed-effect mask `certMask cert` (the rights
    its `granted` cap confers — the `HandoffCertificate.permissions`) as the delegation `keep`. The
    recipient receives the held cap ATTENUATED to the cert mask (§CERT-TEETH: a read-only cert hands off
    `[read]`, NOT the held `[read,write]` nor `allAuths`), and `validateHandoffCert_non_amplifying`
    proves `granted ⊆ held` (`HandoffValid.nonAmplifying`). The remaining model extension is carrying
    the cert's rights on `FullActionA.validateHandoffA` itself (it currently takes only `intro rec t`),
    at which point the executor dispatch routes to `validateHandoffCertEffect`.

  * **`attenuateA` slot-index bounds.** `attenuateSlotF` uses `List.modify`, which is a no-op when
    `idx` is out of range (the attenuation is then the identity — still narrower-or-equal, so still
    self-limiting). The handler is TOTAL by design; an out-of-range index is harmless (no cap is
    widened). The genuine non-amplification content is `attenuateH_non_amplifying` (the narrowed cap
    confers a `List Auth` subset of the original).

  * **`exerciseA` (the recursive sub-effect handler).** dregg1's `ExerciseViaCapability` runs a NESTED
    sub-turn gated on holding the cap edge; its handler needs the well-founded `actionSize` recursion
    that the flat `EffectHandler` shape defers (see `Dregg2.Exec.Handler §DEFER`). The cap-graph is
    UNCHANGED by an exercise (it reads, never edits, the c-list — `delta = 0`), so it folds onto
    `turn_conserves` once the recursive measure is wired; it is NOT in this flat batch.
-/

end Dregg2.Exec.Handlers.Authority
