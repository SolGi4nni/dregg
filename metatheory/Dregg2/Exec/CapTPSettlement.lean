/-
# Dregg2.Exec.CapTPSettlement — distributed-authorization settlement over pipelined batches.

`Dregg2.Exec.CapTPPipeline` gives the EXECUTABLE pipelining core: queued eventual-sends drained
IN ORDER through the verified `Exec.Kernel.exec`, with no-amplification (`drainAll_preserves_caps`),
the anti-ghost tooth (`overAuthorized_send_rejected`), and break-cascade-freeze
(`break_freezes_state`). But pipelining at scale is not just "drain a list of pre-authorized
turns." Parties run **partial, suspended computations** — a pipelined chain of mutations is held
in `Pending` while a *distributed authorization exchange* runs over it: each required party
contributes its consent (an authority-bearing approval), the consents ACCUMULATE, and only once
the exchange has converged (every required party has approved) are the mutations FINALLY settled
and committed — **atomically, all-or-nothing**, through the verified executor.

This module builds that fabric:

  * **`SuspendedBatch`** — a pipelined chain of `QueuedSend` mutations held `Pending`, together
    with the parties whose consent the batch requires and the consents accumulated so far. This
    is the "partial, suspended thing parties are doing a complicated authorization exchange over."
  * **`Approval`** — a party's consent over the batch. The crypto signature is the §8 verify
    seam (an `approved : Bool` discharge); the PARTY-BINDING is enforced — an approval from a
    party the batch does not require does NOT count (`addApproval` discards it). So the exchange
    cannot be spoofed by a non-participant.
  * **`consentComplete`** — the convergence/threshold gate: every required party has approved.
  * **`settle`** — the FINAL settlement: atomically drain the whole batch through the verified
    executor IFF consent is complete; otherwise the batch stays suspended and NOTHING mutates.

The security properties, proved over the EXECUTABLE settle:

  1. **No premature settlement** (`unsettled_freezes_state`): a batch whose consent is incomplete
     settles to the UNCHANGED state — no mutation commits before the distributed exchange converges.
  2. **Settlement is atomic + executor-checked** (`settle_complete_is_drain`): once consent is
     complete, settling IS draining the whole batch through `drainAll` — so every mutation is STILL
     individually re-authorized by `exec` at commit (the multi-party consent does NOT bypass the
     per-mutation authority check; it GATES it).
  3. **No authority amplification through the exchange** (`settle_preserves_caps`): even a fully
     consented, settled batch never grows the capability table — reuses `drainAll_preserves_caps`.
     The distributed authorization exchange cannot bootstrap authority no party held.
  4. **Consent accumulates monotonically** (`addApproval_monotone`): adding an approval never
     retracts a prior one — the exchange only converges.
  5. **A missing or forged approval blocks settlement** (`missing_party_blocks_settlement`,
     `forged_approval_does_not_count`): if any required party has not approved, `consentComplete`
     is false and the batch stays suspended; an approval from a non-required party is discarded and
     does not move the batch toward settlement. The anti-ghost tooth at the consent layer.

NOT gated on succinct proofs: settlement re-drains through `exec`, which re-witnesses each
mutation's authority directly. Reserve succinct-proof attestation for proving a whole SETTLED
batch to a light client (the `settle`-produced post-state is the batch the circuit would witness).

REUSES `Exec.CapTPPipeline` (the verified drain) + `Authority.Positional` (caps); invents no new
executor and no new verify side. Does NOT touch `RecordKernel.lean` (another agent's lane).
-/
import Dregg2.Exec.CapTPPipeline
import Dregg2.Tactics

namespace Dregg2.Exec.CapTPSettlement

open Dregg2.Exec
open Dregg2.Exec.CapTPPipeline
open Dregg2.Authority (Label)

/-! ## §1 — Approvals: a party's authority-bearing consent over a suspended batch.

An `Approval` records WHO approved (`party : Label`) and the §8 verify-seam discharge that their
signature over the batch validated (`signed : Bool` — "this party's Ed25519 signature over the
batch digest verified," carried opaquely exactly as `CapTP`'s `attested`). The party-binding is
load-bearing and ENFORCED here: only approvals from parties the batch REQUIRES are admitted. -/

/-- **`Approval`** — a single party's consent over the suspended batch. `party` is the consenting
label (a vat/cell); `signed` is the §8 discharge (their signature over the batch verified). An
approval with `signed = false` is a malformed/forged consent — it never counts. -/
structure Approval where
  /-- The party (vat/cell label) contributing this consent. -/
  party  : Label
  /-- The §8 verify-seam discharge: this party's signature over the batch verified. -/
  signed : Bool
  deriving DecidableEq, Repr

/-! ## §2 — The suspended batch: a pipelined chain of mutations under a distributed exchange. -/

/-- **`SuspendedBatch`** — a partial, suspended pipelined computation that multiple parties run
a distributed authorization exchange over before final settlement:

  * `mutations`       — the pipelined chain of `QueuedSend`s (the mutations to commit on settle),
    delivered IN ORDER through the verified executor exactly as `CapTPPipeline.drainAll`;
  * `requiredParties` — the parties whose consent the batch requires (the participants of the
    distributed exchange — the settlement threshold is "all of them");
  * `approvals`       — the consents accumulated SO FAR (the in-flight state of the exchange). -/
structure SuspendedBatch where
  /-- The pipelined chain of mutations to commit atomically on settlement. -/
  mutations       : List QueuedSend
  /-- The parties whose consent the batch requires (the exchange participants). -/
  requiredParties : List Label
  /-- The consents accumulated so far (the in-flight authorization exchange). -/
  approvals       : List Approval

/-- **`partyApproved b p`** — has party `p` contributed a VALID (signed) approval to batch `b`?
A consent counts only if it is present AND its §8 signature discharge holds. -/
def SuspendedBatch.partyApproved (b : SuspendedBatch) (p : Label) : Bool :=
  b.approvals.any (fun a => a.party == p && a.signed)

/-- **`consentComplete b`** — the convergence/threshold gate: EVERY required party has contributed
a valid approval. This is the point at which the distributed authorization exchange has converged
and the batch may finally settle. Before this, the batch stays suspended. -/
def SuspendedBatch.consentComplete (b : SuspendedBatch) : Bool :=
  b.requiredParties.all (fun p => b.partyApproved p)

/-- **`addApproval b a`** — admit a party's consent into the in-flight exchange. The party-binding
is ENFORCED: an approval from a party the batch does NOT require is DISCARDED (the exchange cannot
be advanced by a non-participant — the consent-layer anti-ghost tooth). A required-party approval
is appended to the accumulated consents. -/
def SuspendedBatch.addApproval (b : SuspendedBatch) (a : Approval) : SuspendedBatch :=
  if a.party ∈ b.requiredParties then
    { b with approvals := a :: b.approvals }
  else
    b

/-! ## §3 — Settlement: atomic, all-or-nothing, gated on complete consent. -/

/-- **`settle k b`** — the FINAL settlement of a suspended batch. If the distributed authorization
exchange has converged (`consentComplete`), drain the WHOLE chain of mutations through the verified
executor (`drainAll`) — atomically: either every mutation commits (and each is re-authorized by
`exec`) or the drain returns `none` and nothing commits. If consent is INCOMPLETE, the batch stays
suspended: the state is returned UNCHANGED (`some k`). So mutations commit ONLY after the exchange
converges, and even then ONLY if the executor accepts each — consent gates, it does not bypass. -/
def settle (k : KernelState) (b : SuspendedBatch) : Option KernelState :=
  if b.consentComplete then
    drainAll k b.mutations
  else
    some k

/-! ## §4 — No premature settlement: an unsettled (under-consented) batch mutates NOTHING. -/

/-- **`unsettled_freezes_state` (PROVED)** — a batch whose distributed exchange has NOT converged
settles to the UNCHANGED state. No mutation commits before consent is complete: the partial,
suspended computation holds the mutations in escrow, touching neither `caps` nor `bal`, until every
required party has approved. This is the no-premature-settlement keystone. -/
theorem unsettled_freezes_state (k : KernelState) (b : SuspendedBatch)
    (hno : b.consentComplete = false) :
    settle k b = some k := by
  unfold settle
  rw [hno]; rfl

/-- **`missing_party_blocks_settlement` (PROVED)** — if any required party has NOT contributed a
valid approval, consent is incomplete and the batch stays suspended (no mutation). A single
withholding participant blocks the whole settlement — the threshold is unanimity over the required
parties, so the exchange cannot settle behind a party's back. -/
theorem missing_party_blocks_settlement (k : KernelState) (b : SuspendedBatch)
    {p : Label} (hp : p ∈ b.requiredParties) (hno : b.partyApproved p = false) :
    settle k b = some k := by
  apply unsettled_freezes_state
  unfold SuspendedBatch.consentComplete
  by_contra hall
  rw [Bool.not_eq_false, List.all_eq_true] at hall
  have := hall p hp
  rw [hno] at this
  exact absurd this (by simp)

/-! ## §5 — Settlement is the verified drain (atomic + per-mutation re-authorized). -/

/-- **`settle_complete_is_drain` (PROVED)** — once the distributed exchange converges, settling IS
draining the whole batch through the verified executor. So multi-party consent does NOT bypass the
per-mutation authority check: every mutation in the settled batch is STILL re-authorized by `exec`
at commit (consent GATES the drain; the drain re-witnesses each turn). Atomic: `drainAll` is all-
or-nothing — a single rejected mutation aborts the whole settlement to `none`. -/
theorem settle_complete_is_drain (k : KernelState) (b : SuspendedBatch)
    (hc : b.consentComplete = true) :
    settle k b = drainAll k b.mutations := by
  unfold settle; rw [hc]; rfl

/-- **`settle_atomic_aborts_on_unauthorized` (PROVED)** — even with COMPLETE consent, a forged
mutation buried in the batch aborts the WHOLE settlement. If the first mutation is unauthorized
(the executor will reject it), the consented settle returns `none` — nothing commits. So the
distributed authorization exchange's consent cannot launder an over-authorized mutation past the
executor: the per-turn `authorizedB` check still fires. -/
theorem settle_atomic_aborts_on_unauthorized (k : KernelState) (b : SuspendedBatch)
    {s : QueuedSend} {rest : List QueuedSend}
    (hc : b.consentComplete = true) (hmut : b.mutations = s :: rest)
    (hno : authorizedB k.caps s.turn = false) :
    settle k b = none := by
  rw [settle_complete_is_drain k b hc, hmut]
  exact drainAll_aborts_on_unauthorized_head hno

/-! ## §6 — No authority amplification through the multi-party exchange. -/

/-- **`settle_preserves_caps` (PROVED) — the headline: the distributed exchange cannot amplify
authority.** A settled batch — no matter how elaborate the multi-party authorization exchange that
gated it — never grows the capability table. We split: incomplete consent leaves the state (and so
`caps`) literally unchanged; complete consent settles via `drainAll`, which preserves `caps`
(`drainAll_preserves_caps`). So consent GATES which mutations commit, but the mutations themselves
are still bounded by the authority the parties already held — settlement re-shares, never conjures,
authority. The security property that holds at scale across a complicated distributed exchange. -/
theorem settle_preserves_caps (k k' : KernelState) (b : SuspendedBatch)
    (h : settle k b = some k') : k'.caps = k.caps := by
  unfold settle at h
  by_cases hc : b.consentComplete = true
  · rw [if_pos hc] at h
    exact drainAll_preserves_caps k k' b.mutations h
  · rw [if_neg hc] at h
    simp only [Option.some.injEq] at h; subst h; rfl

/-- **`settle_conserves` (PROVED)** — a settled batch conserves total supply: incomplete consent
is a no-op (trivially conserving), and a complete-consent settle drains through `exec`, which
conserves each turn (`drainAll_conserves`). The distributed exchange neither mints nor burns. -/
theorem settle_conserves (k k' : KernelState) (b : SuspendedBatch)
    (h : settle k b = some k') : total k' = total k := by
  unfold settle at h
  by_cases hc : b.consentComplete = true
  · rw [if_pos hc] at h
    exact drainAll_conserves k k' b.mutations h
  · rw [if_neg hc] at h
    simp only [Option.some.injEq] at h; subst h; rfl

/-! ## §7 — The consent layer's own anti-ghost tooth + monotone accumulation. -/

/-- **`forged_approval_does_not_count` (PROVED)** — an approval from a party the batch does NOT
require is DISCARDED: `addApproval` leaves the batch unchanged. So a non-participant cannot advance
the distributed exchange toward settlement by submitting a consent — only the required parties'
approvals accumulate. The anti-ghost tooth at the consent layer. -/
theorem forged_approval_does_not_count (b : SuspendedBatch) (a : Approval)
    (hno : a.party ∉ b.requiredParties) :
    b.addApproval a = b := by
  unfold SuspendedBatch.addApproval
  rw [if_neg hno]

/-- **`addApproval_monotone` (PROVED)** — consent accumulates monotonically: if a party `p` had
already approved the batch, it STILL has approved after admitting any further approval `a`. The
distributed exchange only converges — adding consent never retracts a prior one. -/
theorem addApproval_monotone (b : SuspendedBatch) (a : Approval) {p : Label}
    (hp : b.partyApproved p = true) :
    (b.addApproval a).partyApproved p = true := by
  unfold SuspendedBatch.addApproval
  by_cases hreq : a.party ∈ b.requiredParties
  · rw [if_pos hreq]
    unfold SuspendedBatch.partyApproved at hp ⊢
    simp only [List.any_cons, Bool.or_eq_true]
    exact Or.inr hp
  · rw [if_neg hreq]; exact hp

/-- **`consent_monotone` (PROVED)** — convergence is monotone at the THRESHOLD too: if the exchange
had already converged (`consentComplete`), it stays converged after any further approval. So once
all required parties have approved, no later message can un-settle the batch — the exchange is a
ratchet toward settlement. -/
theorem consent_monotone (b : SuspendedBatch) (a : Approval)
    (hc : b.consentComplete = true) :
    (b.addApproval a).consentComplete = true := by
  unfold SuspendedBatch.consentComplete at hc ⊢
  rw [List.all_eq_true] at hc ⊢
  intro p hp
  -- the required-party list is unchanged by addApproval, and each party's approval is monotone
  have hreq : (b.addApproval a).requiredParties = b.requiredParties := by
    unfold SuspendedBatch.addApproval; split <;> rfl
  rw [hreq] at hp
  exact addApproval_monotone b a (by have := hc p hp; simpa using this)

/-! ## §8 — Non-vacuity: a multi-party distributed exchange that suspends, accumulates consent,
and finally settles atomically through the verified executor. Real data. -/

section NonVacuity

/-- A concrete kernel: accounts {1,2}, bal 1 = 10, and a caps table where the actor (cell 0) holds
a `node` cap on cell 1 (authority to move cell 1's resource). -/
def demoState : KernelState where
  accounts := {1, 2}
  bal := fun c => if c = 1 then 10 else 0
  caps := fun a => if a = 0 then [Dregg2.Authority.Cap.node 1] else []

/-- An authorized mutation: actor 0 (holding the node cap on 1) moves 5 from cell 1 to cell 2. -/
def demoMutation : QueuedSend :=
  { turn := { actor := 0, src := 1, dst := 2, amt := 5 } }

/-- A two-party suspended batch: parties 7 and 9 must both consent before the mutation settles.
Initially NO approvals — the batch is fully suspended. -/
def demoBatch : SuspendedBatch :=
  { mutations := [demoMutation]
  , requiredParties := [7, 9]
  , approvals := [] }

/-- Suspended (no consent): settling is a no-op — the mutation does NOT commit. -/
example : settle demoState demoBatch = some demoState :=
  unsettled_freezes_state demoState demoBatch (by decide)

/-- Party 7 approves, then party 9 approves — the distributed exchange converges. -/
def demoBatchBothApproved : SuspendedBatch :=
  (demoBatch.addApproval { party := 7, signed := true }).addApproval { party := 9, signed := true }

/-- After both required parties approve, consent is COMPLETE — the batch may settle. -/
example : demoBatchBothApproved.consentComplete = true := by decide

/-- A forged approval from non-participant party 5 is DISCARDED — concrete anti-ghost. -/
example : demoBatch.addApproval { party := 5, signed := true } = demoBatch :=
  forged_approval_does_not_count demoBatch _ (by decide)

/-- With only party 7 (party 9 still withholding), settlement is BLOCKED — the mutation is held. -/
example : settle demoState (demoBatch.addApproval { party := 7, signed := true }) = some demoState := by
  apply missing_party_blocks_settlement (p := 9)
  · decide
  · decide

/-- With BOTH parties consented, settling DRAINS the mutation through the verified executor and
COMMITS it (the post-state is `some`, the mutation finally applied) — concrete atomic settlement. -/
example : (settle demoState demoBatchBothApproved).isSome = true := by
  rw [settle_complete_is_drain demoState demoBatchBothApproved (by decide)]
  unfold demoBatchBothApproved demoBatch demoMutation drainAll drainStep exec demoState
    SuspendedBatch.addApproval authorizedB
  decide

/-- The settled batch preserves caps — the multi-party exchange did NOT amplify authority. -/
example : ∀ k', settle demoState demoBatchBothApproved = some k' → k'.caps = demoState.caps :=
  fun k' h => settle_preserves_caps demoState k' demoBatchBothApproved h

#guard (s!"settlement: parties {demoBatch.requiredParties} must consent; suspended until both approve, \
then atomic commit through the verified executor"
        == "settlement: parties [7, 9] must consent; suspended until both approve, then atomic commit through the verified executor")

end NonVacuity

/-! ## §9 — Axiom-hygiene tripwires. Every PROVED keystone depends ONLY on the three standard
kernel axioms (no `sorryAx`). -/

#assert_axioms unsettled_freezes_state
#assert_axioms missing_party_blocks_settlement
#assert_axioms settle_complete_is_drain
#assert_axioms settle_atomic_aborts_on_unauthorized
#assert_axioms settle_preserves_caps
#assert_axioms settle_conserves
#assert_axioms forged_approval_does_not_count
#assert_axioms addApproval_monotone
#assert_axioms consent_monotone

end Dregg2.Exec.CapTPSettlement
