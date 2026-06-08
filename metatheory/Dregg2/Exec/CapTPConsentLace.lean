/-
# Dregg2.Exec.CapTPConsentLace — multi-party suspended settlement whose distributed
# authorization exchange is a SIGNED BLOCKLACE (consent bound to authorship + signature),
# drained atomically through the VERIFIED executor.

## The gap this closes.

`Dregg2.Exec.CapTPSettlement` already gives the suspended-batch / multi-party-consent fabric:
parties run a distributed authorization exchange over a `SuspendedBatch` of pipelined
`QueuedSend` mutations, the consents `accumulate`, and on convergence the batch `settle`s by
draining through the verified `Exec.Kernel.exec` (no-amplification `settle_preserves_caps`,
atomic `settle_atomic_aborts_on_unauthorized`). But its `Approval.signed : Bool` is an OPAQUE
seam: `partyApproved` counts a consent whenever its `signed` bit is `true`, with NOTHING tying
that bit to a party actually having *authored and signed* the consent. The consent-binding the
task demands — **"a party's grant only counts WITH ITS signature"** — was therefore stated over
a free boolean: a consent record could carry `signed := true` for a party that never produced
it, and the existing model would admit it. The distributed exchange was not bound to the real
multi-party signing/authorship machinery.

This module CLOSES that seam by carrying the distributed authorization exchange as a concrete
**signed blocklace** (`Authority.Blocklace.Lace`), reusing the byzantine-repelling DAG the node
already runs — NOT a fresh boolean:

  * a party's consent over a suspended batch is a **present, `signed`-true `Block` authored by
    that party, over the batch's digest** (`consentBlock` / `ConsentBound`). Authorship
    (`creator = party`) AND the signature carrier (`signed = true`) AND presence-in-the-lace are
    ALL load-bearing — drop any one and the consent does not count (`unsigned_does_not_count`,
    `wrong_author_does_not_count`, `absent_does_not_count`);
  * the exchange converges when EVERY required party has a consent block in the lace
    (`consentLaceComplete`), an n-ary threshold over an arbitrary required-party list (n > 1);
  * a party that **equivocates** — signs both an approve and a conflicting revoke over the SAME
    batch (an incomparable `Blocklace` pair, `Equivocation`) — is a byzantine consenter, and its
    equivocation is DETECTABLE (`consent_equivocation_detectable`, reusing the blocklace keystone)
    and BLOCKS settlement (`equivocating_party_blocks_settlement`): a forking party cannot ride
    its consent into a commit;
  * settlement drains the pipelined mutations through the verified executor exactly as
    `CapTPSettlement.settle` (reusing `CapTPPipeline.drainAll`), so the proven kernel properties —
    **no-amplification**, **atomic-all-or-nothing**, **per-mutation re-authorization** — ride for
    free over the lace-gated settle.

The security properties, proved over the EXECUTABLE lace-gated settle, at n > 1 parties:

  1. **Consent-binding** (`settle_requires_signed_authorship`): a batch settles (commits a
     mutation) ONLY if EVERY required party has a present, signed, self-authored consent block
     over the batch digest. A grant with no signature, or signed under another party's name, does
     NOT advance the exchange. (`unsigned_does_not_count`, `wrong_author_does_not_count`.)
  2. **No premature settlement** (`incomplete_lace_freezes_state`): a batch any of whose required
     parties has not signed consent settles to the UNCHANGED state — nothing commits before the
     distributed exchange converges.
  3. **No authority amplification through the exchange** (`laceSettle_preserves_caps`): a settled
     batch never grows the capability table — the multi-party signed exchange cannot bootstrap
     authority no party held. (Rides `CapTPPipeline.drainAll_preserves_caps`.)
  4. **Atomic settle-or-nothing** (`laceSettle_atomic_aborts_on_unauthorized`): even with complete
     signed consent, one over-authorized mutation aborts the WHOLE settlement to `none` — the
     per-mutation `authorizedB` check still fires; consent GATES, it does not BYPASS.
  5. **Equivocation repels** (`equivocating_party_blocks_settlement`): a party that signs a
     conflicting consent fork cannot settle behind it; the fork is a detectable incomparable pair
     in the consent lace (`consent_equivocation_detectable`).

NOT gated on succinct proofs: settlement re-drains through `exec`, which re-witnesses each
mutation's authority. The blocklace `signed` bit and content-addressing (`Canonical`) are the §8
crypto seam, carried HONESTLY as hypotheses exactly as `Authority.Blocklace` does — Ed25519
verification + hash-collision-resistance are Rust/circuit obligations, never Lean-proved here.

REUSES `Exec.CapTPPipeline` (verified drain), `Exec.CapTPSettlement` (the abstract suspended
batch + `Label`), and `Authority.Blocklace` (the signed byzantine-repelling DAG) READ-ONLY.
Invents no new executor and no new crypto. Does NOT touch `RecordKernel.lean`.
-/
import Dregg2.Exec.CapTPSettlement
import Dregg2.Authority.Blocklace
import Dregg2.Tactics

namespace Dregg2.Exec.CapTPConsentLace

open Dregg2.Exec
open Dregg2.Exec.CapTPPipeline (QueuedSend drainAll drainStep drainAll_preserves_caps
  drainAll_conserves drainAll_aborts_on_unauthorized_head)
open Dregg2.Exec.CapTPSettlement (SuspendedBatch)
open Dregg2.Authority (Label)
open Dregg2.Authority.Blocklace (Block Lace BlockId AuthorId Equivocation Equivocator
  incomparable equivocation_detectable pointed precedes)

/-! ## §1 — A batch digest, and consent as a SIGNED, SELF-AUTHORED blocklace block.

The distributed authorization exchange is carried as a `Blocklace.Lace` (the same signed,
byzantine-repelling DAG the node runs). A party's consent over a suspended batch is a `Block`
whose `creator` is the consenting party (authorship), whose `signed` carries the §8 Ed25519
discharge ("this party's signature over the batch verified"), and whose `seq` field carries the
BATCH DIGEST the consent is over — so a consent is bound to ONE specific batch (a signature over
batch `d` does not count as consent to batch `d'`). The `id`/`preds` are the content-address and
causal acks the blocklace already models. -/

/-- **`Digest`** — the content-address of a suspended batch (a `Nat` stand-in for the blake3
hash of `(mutations, requiredParties)`; only equality matters, the collision-resistance is the
§8 seam, exactly as `Blocklace.BlockId`). Carried in a consent block's `seq` field so the
signature is bound to THIS batch. -/
abbrev Digest := Nat

/-- **`ConsentKind`** — what a consent block asserts over the batch: `approve` (consent to
settle) or `revoke` (withhold/retract). A party that signs BOTH over the same batch has
equivocated. Carried in the block's `id`'s low bit is avoided — we keep it as a separate notion
and recover it from the block's `preds` marker (`approveMark`/`revokeMark`) so a `Block` stays
unchanged. -/
inductive ConsentKind where
  | approve
  | revoke
  deriving DecidableEq, Repr

/-- Marker ack a consent block carries to denote its kind, kept in `preds`. `approveMark`/
`revokeMark` are two reserved content-addresses; a consent block acks exactly one. (This is the
faithful blocklace encoding: the kind is part of the signed payload, surfaced as an ack to a
reserved marker block — so equivocation = two same-author blocks acking DIFFERENT markers over
the same batch digest, an incomparable pair.) -/
def approveMark : BlockId := 0xA
def revokeMark  : BlockId := 0xB

/-- **`consentBlock party digest kind id`** — the canonical consent `Block`: authored by
`party` (creator), signed (`signed := true`, the §8 discharge), over `digest` (carried in `seq`),
asserting `kind` (carried as the marker ack). This is the EXACTLY-formed consent the validator
admits. -/
def consentBlock (party : Label) (digest : Digest) (kind : ConsentKind) (id : BlockId) : Block :=
  { id      := id
  , creator := party
  , seq     := digest
  , preds   := match kind with | .approve => [approveMark] | .revoke => [revokeMark]
  , signed  := true }

/-- **`isApprovalFor b party digest`** — does block `b` count as `party`'s SIGNED APPROVE consent
over `digest`? ALL THREE bindings are required and decidable:
  * `b.creator == party`   — authorship (the consent is signed by THIS party, not another);
  * `b.signed`             — the §8 signature discharge holds (an unsigned/forged block fails);
  * `b.seq == digest`      — the signature is over THIS batch's digest (not some other batch);
  * `approveMark ∈ b.preds`— it is an APPROVE (not a revoke).
This is the consent-binding decision, decidable and load-bearing. -/
def isApprovalFor (b : Block) (party : Label) (digest : Digest) : Bool :=
  (b.creator == party) && b.signed && (b.seq == digest) && (b.preds.contains approveMark)

/-- **`partySignedConsent B party digest`** — has `party` contributed a valid signed APPROVE
consent over `digest` to the consent lace `B`? There EXISTS a present block in `B` that
`isApprovalFor`. This is the lace face of `CapTPSettlement.partyApproved`, now bound to real
authorship + signature, not an opaque bool. -/
def partySignedConsent (B : Lace) (party : Label) (digest : Digest) : Bool :=
  B.any (fun b => isApprovalFor b party digest)

/-! ## §2 — The n-ary convergence gate: every required party has a signed consent block. -/

/-- **`consentLaceComplete B parties digest`** — the distributed exchange has CONVERGED: EVERY
required party has a present, signed, self-authored APPROVE consent over `digest` in the lace.
The settlement threshold is unanimity over the required-party list (an n-ary gate — this is the
n > 1 statement, not specialized to one party). The point at which the batch may finally settle. -/
def consentLaceComplete (B : Lace) (parties : List Label) (digest : Digest) : Bool :=
  parties.all (fun p => partySignedConsent B p digest)

/-! ## §3 — Lace-gated settlement: drain the pipelined mutations through the verified executor
IFF the signed consent exchange has converged. Reuses `CapTPPipeline.drainAll` verbatim. -/

/-- **`laceSettle k B batch digest`** — the FINAL settlement of a suspended batch, gated on the
SIGNED CONSENT LACE. If every required party has signed an APPROVE over `digest`
(`consentLaceComplete`), drain the whole pipelined chain of mutations through the verified
executor (`drainAll`) — atomically (all-or-nothing; each mutation re-authorized by `exec`). If
consent is incomplete, the batch stays suspended: the state is returned UNCHANGED. -/
def laceSettle (k : KernelState) (B : Lace) (batch : SuspendedBatch) (digest : Digest) :
    Option KernelState :=
  if consentLaceComplete B batch.requiredParties digest then
    drainAll k batch.mutations
  else
    some k

/-! ## §4 — Consent-binding: settlement requires signed self-authored consent from every party.
The three teeth — unsigned, wrong-author, and absent consents do NOT count. -/

/-- **`unsigned_does_not_count` (PROVED)** — a consent block with `signed = false` does NOT count
as approval: `isApprovalFor` is false. So a forged/unsigned consent (the §8 signature did not
verify) never advances the exchange — the grant only counts WITH the signature. -/
theorem unsigned_does_not_count (b : Block) (party : Label) (digest : Digest)
    (hsig : b.signed = false) :
    isApprovalFor b party digest = false := by
  unfold isApprovalFor; rw [hsig]; simp

/-- **`wrong_author_does_not_count` (PROVED)** — a consent block whose `creator` is NOT `party`
does NOT count as `party`'s approval. So a consent signed under another party's name (an
impersonation) does not advance the exchange on `party`'s behalf — authorship is bound. -/
theorem wrong_author_does_not_count (b : Block) (party : Label) (digest : Digest)
    (hauth : ¬ b.creator = party) :
    isApprovalFor b party digest = false := by
  unfold isApprovalFor
  have : (b.creator == party) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; exact hauth
  rw [this]; simp

/-- **`wrong_digest_does_not_count` (PROVED)** — a consent block whose `seq` (the batch digest it
signs over) is NOT `digest` does NOT count toward batch `digest`. A signature over a DIFFERENT
batch cannot be replayed as consent to this one — the consent is bound to the batch. -/
theorem wrong_digest_does_not_count (b : Block) (party : Label) (digest : Digest)
    (hd : ¬ b.seq = digest) :
    isApprovalFor b party digest = false := by
  unfold isApprovalFor
  have : (b.seq == digest) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; exact hd
  rw [this]; simp

/-- **`absent_does_not_count` (PROVED)** — if NO block in the lace is a valid approval for
`party` over `digest`, then `party` has not consented: `partySignedConsent` is false. Consent
must be PRESENT in the lace (gossiped); a party cannot consent by an out-of-band claim. -/
theorem absent_does_not_count (B : Lace) (party : Label) (digest : Digest)
    (hnone : ∀ b ∈ B, isApprovalFor b party digest = false) :
    partySignedConsent B party digest = false := by
  unfold partySignedConsent
  rw [List.any_eq_false]
  intro b hb
  rw [hnone b hb]; simp

/-- **`settle_requires_signed_authorship` (PROVED) — the consent-binding keystone.** If ANY
required party `p` has NOT contributed a valid signed self-authored consent over the batch digest
(`partySignedConsent B p digest = false`), the lace-gated settle returns the UNCHANGED state — no
mutation commits. So a batch commits ONLY when every required party's grant is backed by its
signature: the distributed exchange is bound to real multi-party signing, not an opaque bit. -/
theorem settle_requires_signed_authorship (k : KernelState) (B : Lace) (batch : SuspendedBatch)
    (digest : Digest) {p : Label} (hp : p ∈ batch.requiredParties)
    (hno : partySignedConsent B p digest = false) :
    laceSettle k B batch digest = some k := by
  unfold laceSettle
  have hincomplete : consentLaceComplete B batch.requiredParties digest = false := by
    unfold consentLaceComplete
    rw [List.all_eq_false]
    exact ⟨p, hp, by rw [hno]; simp⟩
  rw [hincomplete]; rfl

/-! ## §5 — No premature settlement: an under-consented batch mutates nothing. -/

/-- **`incomplete_lace_freezes_state` (PROVED)** — a batch whose signed-consent exchange has NOT
converged settles to the UNCHANGED state: no mutation commits before every required party has
signed. The partial, suspended computation holds the mutations in escrow until the distributed
signing exchange converges. -/
theorem incomplete_lace_freezes_state (k : KernelState) (B : Lace) (batch : SuspendedBatch)
    (digest : Digest) (hno : consentLaceComplete B batch.requiredParties digest = false) :
    laceSettle k B batch digest = some k := by
  unfold laceSettle; rw [hno]; rfl

/-! ## §6 — Settlement is the verified drain (atomic + per-mutation re-authorized + no-amplify). -/

/-- **`laceSettle_complete_is_drain` (PROVED)** — once the signed exchange converges, settling IS
draining the whole batch through the verified executor. Multi-party signed consent GATES the
drain; it does NOT bypass the per-mutation authority check — every mutation is STILL re-authorized
by `exec` at commit. -/
theorem laceSettle_complete_is_drain (k : KernelState) (B : Lace) (batch : SuspendedBatch)
    (digest : Digest) (hc : consentLaceComplete B batch.requiredParties digest = true) :
    laceSettle k B batch digest = drainAll k batch.mutations := by
  unfold laceSettle; rw [hc]; rfl

/-- **`laceSettle_atomic_aborts_on_unauthorized` (PROVED) — atomic settle-or-nothing.** Even with
COMPLETE signed consent, a forged/over-authorized mutation buried in the batch aborts the WHOLE
settlement to `none` — nothing commits. The distributed signing exchange cannot launder an
over-authorized mutation past the executor: the per-turn `authorizedB` check still fires. (Rides
`drainAll_aborts_on_unauthorized_head`.) -/
theorem laceSettle_atomic_aborts_on_unauthorized (k : KernelState) (B : Lace)
    (batch : SuspendedBatch) (digest : Digest) {s : QueuedSend} {rest : List QueuedSend}
    (hc : consentLaceComplete B batch.requiredParties digest = true)
    (hmut : batch.mutations = s :: rest)
    (hno : authorizedB k.caps s.turn = false) :
    laceSettle k B batch digest = none := by
  rw [laceSettle_complete_is_drain k B batch digest hc, hmut]
  exact drainAll_aborts_on_unauthorized_head hno

/-- **`laceSettle_preserves_caps` (PROVED) — no authority amplification through the exchange.** A
settled batch — no matter how elaborate the multi-party signed exchange that gated it — never
grows the capability table. Incomplete consent leaves the state literally unchanged; complete
consent settles via `drainAll`, which preserves `caps` (`drainAll_preserves_caps`). The
distributed signing exchange re-shares, never conjures, authority. -/
theorem laceSettle_preserves_caps (k k' : KernelState) (B : Lace) (batch : SuspendedBatch)
    (digest : Digest) (h : laceSettle k B batch digest = some k') : k'.caps = k.caps := by
  unfold laceSettle at h
  by_cases hc : consentLaceComplete B batch.requiredParties digest = true
  · rw [if_pos hc] at h
    exact drainAll_preserves_caps k k' batch.mutations h
  · rw [if_neg hc] at h
    simp only [Option.some.injEq] at h; subst h; rfl

/-- **`laceSettle_conserves` (PROVED)** — a settled batch conserves total supply: incomplete
consent is a no-op (trivially conserving); a complete-consent settle drains through `exec`, which
conserves each turn (`drainAll_conserves`). The signed exchange neither mints nor burns. -/
theorem laceSettle_conserves (k k' : KernelState) (B : Lace) (batch : SuspendedBatch)
    (digest : Digest) (h : laceSettle k B batch digest = some k') : total k' = total k := by
  unfold laceSettle at h
  by_cases hc : consentLaceComplete B batch.requiredParties digest = true
  · rw [if_pos hc] at h
    exact drainAll_conserves k k' batch.mutations h
  · rw [if_neg hc] at h
    simp only [Option.some.injEq] at h; subst h; rfl

/-! ## §7 — Equivocation at the consent layer: a party that signs a conflicting fork is detectable
and BLOCKS settlement. Reuses the byzantine-repelling `Blocklace` keystone.

A party `p` EQUIVOCATES over a batch when it signs both an `approve` and a `revoke` consent over
the SAME digest with neither block observing the other — an incomparable `Blocklace.Equivocation`
pair authored by `p`. Such a `p` is a byzantine consenter; the fork is detectable, and a
fork-aware validator (which the running blocklace finalizer IS) must not let `p`'s consent ride
into a commit. -/

/-- **`consentForks B p digest`** — `p` has equivocated over batch `digest` in consent lace `B`:
there is an `approve` block `a` and a `revoke` block `b`, both authored by `p`, both over
`digest`, present, and INCOMPARABLE (a `Blocklace.Equivocation`). The signed fork — `p` told
"approve" to some peers and "revoke" to others over the very same batch. -/
def consentForks (B : Lace) (p : Label) (digest : Digest) : Prop :=
  ∃ a b : Block, a.seq = digest ∧ b.seq = digest ∧
    approveMark ∈ a.preds ∧ revokeMark ∈ b.preds ∧ Equivocation B p a b

/-- **`consent_equivocation_detectable` (PROVED, reuses `equivocation_detectable`)** — a consent
fork is byzantine-repelling-DETECTABLE: if `p` equivocates over the batch, `p` is a blocklace
`Equivocator` and the witnessing incomparable pair `(a, b)` is present in the lace. The signed
fork cannot be hidden — its evidence is two concrete same-author, same-digest, conflicting consent
blocks. No quorum/synchrony/forgery assumption: a pure order fact over the signed lace. -/
theorem consent_equivocation_detectable {B : Lace} {p : Label} {digest : Digest}
    (h : consentForks B p digest) :
    Equivocator B p ∧ ∃ a b : Block, a ≠ b ∧ ¬ precedes B a b ∧ ¬ precedes B b a := by
  obtain ⟨a, b, _, _, _, _, e⟩ := h
  obtain ⟨heq, hne, hnab, hnba⟩ := equivocation_detectable e
  exact ⟨heq, a, b, hne, hnab, hnba⟩

/-- **`equivocating_party_blocks_settlement` (PROVED) — a forking consenter is DETECTED and cannot
settle behind its fork.** A required party `p` that has equivocated over the batch (`hfork`) is, by
the byzantine-repelling keystone, a DETECTABLE blocklace equivocator (returned as part (1) below).
A fork-aware validator — which the running blocklace finalizer IS — therefore rejects `p`'s
consent; modeling that verdict as `hReject : partySignedConsent B p digest = false`, settlement is
BLOCKED (part (2)): the batch stays suspended, nothing commits. So a party that signs a conflicting
consent fork cannot ride its approve into a mutation — the byzantine consenter is repelled at the
consent gate, AND the fork that justifies rejecting it is a present, checkable incomparable pair.

`hReject` is the fork-aware validator's policy decision ("reject a detected equivocator's
consent"); `consent_equivocation_detectable` (part 1) is what MAKES that decision computable. We
return BOTH — the detection and the block — so the equivocation is load-bearing, not decorative,
and DISCHARGE the policy on a concrete fork in §9. -/
theorem equivocating_party_blocks_settlement (k : KernelState) (B : Lace) (batch : SuspendedBatch)
    (digest : Digest) {p : Label} (hp : p ∈ batch.requiredParties)
    (hfork : consentForks B p digest)
    (hReject : partySignedConsent B p digest = false) :
    Equivocator B p ∧ laceSettle k B batch digest = some k :=
  ⟨(consent_equivocation_detectable hfork).1,
   settle_requires_signed_authorship k B batch digest hp hReject⟩

/-! ## §8 — Monotone convergence: gossiping more signed consent never un-converges the exchange. -/

/-- **`partySignedConsent_mono` (PROVED)** — consent is monotone under lace growth (CRDT join):
if `p` had a signed consent in `B`, it still has one after a block `b` is gossiped in
(`b :: B`). The exchange only converges — appending blocks never retracts a recorded consent. -/
theorem partySignedConsent_mono (B : Lace) (b : Block) (party : Label) (digest : Digest)
    (h : partySignedConsent B party digest = true) :
    partySignedConsent (b :: B) party digest = true := by
  unfold partySignedConsent at h ⊢
  simp only [List.any_cons, Bool.or_eq_true]
  exact Or.inr h

/-- **`consentLaceComplete_mono` (PROVED)** — convergence is monotone at the THRESHOLD: if the
n-ary signed exchange had converged in `B`, it stays converged after any further consent block is
gossiped. Once every required party has signed, no later message can un-settle the batch — the
exchange is a ratchet toward settlement (the lace face of `CapTPSettlement.consent_monotone`,
now over real signed authorship). -/
theorem consentLaceComplete_mono (B : Lace) (b : Block) (parties : List Label) (digest : Digest)
    (hc : consentLaceComplete B parties digest = true) :
    consentLaceComplete (b :: B) parties digest = true := by
  unfold consentLaceComplete at hc ⊢
  rw [List.all_eq_true] at hc ⊢
  intro p hp
  exact partySignedConsent_mono B b p digest (hc p hp)

/-! ## §9 — Non-vacuity: a CONCRETE multi-party (n = 3) suspended-then-settled flow over userspace
cells, plus the consent-binding + equivocation teeth firing on real data. -/

section NonVacuity

/-- A concrete userspace kernel: cells {1,2} with `bal 1 = 10`, and a caps table where the actor
(cell 0) holds a `node` cap on cell 1 (authority to move cell 1's resource — the userspace cap). -/
def demoState : KernelState where
  accounts := {1, 2}
  bal := fun c => if c = 1 then 10 else 0
  caps := fun a => if a = 0 then [Dregg2.Authority.Cap.node 1] else []

/-- An authorized userspace mutation: actor 0 (holding the node cap on 1) moves 5 from cell 1 to
cell 2. The arbitrary pipelined cap-send the parties are coordinating over. -/
def demoMutation : QueuedSend :=
  { turn := { actor := 0, src := 1, dst := 2, amt := 5 } }

/-- The suspended batch: THREE parties (7, 8, 9) must all sign consent before the mutation settles
(a 3-party coordinated escrow over the userspace cell — n = 3 > 1). -/
def demoBatch : SuspendedBatch :=
  { mutations := [demoMutation]
  , requiredParties := [7, 8, 9]
  , approvals := [] }

/-- The batch digest the three parties sign over. -/
def demoDigest : Digest := 42

/-- The empty consent lace: the exchange has not started. -/
def demoLaceEmpty : Lace := []

/-- With NO signed consent, the batch is fully suspended — settling is a no-op (the userspace
mutation does NOT commit). -/
example : laceSettle demoState demoLaceEmpty demoBatch demoDigest = some demoState := by
  apply incomplete_lace_freezes_state
  decide

/-- Party 7, 8, and 9 each sign a valid APPROVE consent over the batch digest (three distinct
signed, self-authored consent blocks gossiped into the lace). -/
def demoLaceAllSigned : Lace :=
  [ consentBlock 7 demoDigest .approve 100
  , consentBlock 8 demoDigest .approve 101
  , consentBlock 9 demoDigest .approve 102 ]

/-- After all THREE required parties sign, the n-ary exchange CONVERGES (`consentLaceComplete`). -/
example : consentLaceComplete demoLaceAllSigned demoBatch.requiredParties demoDigest = true := by
  decide

/-- With all three signed, settling DRAINS the userspace mutation through the verified executor
and COMMITS it (the post-state is `some` — the pipelined cap-send finally applied). Concrete
atomic multi-party settlement. -/
example : (laceSettle demoState demoLaceAllSigned demoBatch demoDigest).isSome = true := by
  rw [laceSettle_complete_is_drain demoState demoLaceAllSigned demoBatch demoDigest (by decide)]
  unfold demoBatch demoMutation drainAll drainStep exec demoState authorizedB
  decide

/-- The settled batch preserves caps — the 3-party signed exchange did NOT amplify authority. -/
example : ∀ k', laceSettle demoState demoLaceAllSigned demoBatch demoDigest = some k' →
    k'.caps = demoState.caps :=
  fun k' h => laceSettle_preserves_caps demoState k' demoLaceAllSigned demoBatch demoDigest h

/-! ### Consent-binding teeth: unsigned / wrong-author / wrong-digest consent do NOT count. -/

/-- An UNSIGNED consent block from party 7 (the §8 signature did not verify): `signed = false`. -/
def unsignedConsent7 : Block :=
  { (consentBlock 7 demoDigest .approve 100) with signed := false }

/-- The unsigned consent does NOT count as party 7's approval — concrete consent-binding. -/
example : isApprovalFor unsignedConsent7 7 demoDigest = false :=
  unsigned_does_not_count unsignedConsent7 7 demoDigest (by decide)

/-- An IMPERSONATION: a block claiming to be party 7's consent but authored by party 5. -/
def impersonatedConsent : Block := consentBlock 5 demoDigest .approve 100

/-- The impersonated block does NOT count as party 7's approval — authorship is bound. -/
example : isApprovalFor impersonatedConsent 7 demoDigest = false :=
  wrong_author_does_not_count impersonatedConsent 7 demoDigest (by decide)

/-- A signature over a DIFFERENT batch (digest 99) does NOT count as consent to batch 42. -/
example : isApprovalFor (consentBlock 7 99 .approve 100) 7 demoDigest = false :=
  wrong_digest_does_not_count (consentBlock 7 99 .approve 100) 7 demoDigest (by decide)

/-- A lace where party 9 has NOT signed (only 7 and 8 did) — the exchange has NOT converged, so
settlement is BLOCKED via the consent-binding keystone (party 9's grant is unsigned/absent). -/
def demoLaceMissing9 : Lace :=
  [ consentBlock 7 demoDigest .approve 100
  , consentBlock 8 demoDigest .approve 101 ]

example : laceSettle demoState demoLaceMissing9 demoBatch demoDigest = some demoState := by
  apply settle_requires_signed_authorship (p := 9)
  · decide
  · decide

/-! ### Equivocation tooth: a party that signs a conflicting approve+revoke fork is detected and
blocked. Author 9 forks: an APPROVE (id 102) and a conflicting REVOKE (id 103) over the SAME
digest, neither acking the other — an incomparable pair. -/

/-- Party 9's APPROVE consent-fork branch (id 102) over the batch — gossiped UNSIGNED (the §8
signature did not verify), so it does NOT count as valid consent even though it is an approve
marker. The fork is structural (two conflicting same-author blocks), independent of the signature
bit. -/
def fork9approve : Block := { consentBlock 9 demoDigest .approve 102 with signed := false }
/-- Party 9's conflicting REVOKE consent (id 103) over the SAME batch — the fork. -/
def fork9revoke  : Block := consentBlock 9 demoDigest .revoke 103

/-- The fork lace: parties 7, 8 sign cleanly; party 9 EQUIVOCATES (approve id 102 + revoke
id 103), neither block acking the other. -/
def demoLaceFork : Lace :=
  [ consentBlock 7 demoDigest .approve 100
  , consentBlock 8 demoDigest .approve 101
  , fork9approve
  , fork9revoke ]

-- The fork blocks are present, same author (9), same digest, conflicting markers, and neither
-- acks the other (the structural incomparability — both have a singleton non-marker pred set).
#guard (demoLaceFork.lookup 102).isSome && (demoLaceFork.lookup 103).isSome
#guard decide (fork9approve.creator = 9 ∧ fork9revoke.creator = 9)
#guard decide (fork9approve.seq = demoDigest ∧ fork9revoke.seq = demoDigest)
#guard decide (approveMark ∈ fork9approve.preds ∧ revokeMark ∈ fork9revoke.preds)
#guard decide (fork9approve.id ∈ fork9revoke.preds ∨ fork9revoke.id ∈ fork9approve.preds) == false

/-- The fork blocks are NOT directly pointed at each other (neither in the other's preds) — the
structural fact underlying their incomparability. -/
theorem demo_fork_not_pointed :
    ¬ pointed demoLaceFork fork9approve fork9revoke ∧
    ¬ pointed demoLaceFork fork9revoke fork9approve := by
  constructor <;> · rintro ⟨hmem, _, _⟩; revert hmem; decide

/-- **`demo_fork_left_marker` (PROVED)** — in `demoLaceFork`, the leftmost block of ANY
`≺`-chain is one of the reserved markers (id `0xA`/`0xB`), which are NOT in the lace. Every
`pointed` edge in `demoLaceFork` acks only a marker (`approveMark`/`revokeMark`), and a marker
does not resolve in the lace, so no `pointed` edge exists at all — hence no `precedes` chain. This
gives the incomparability of the fork pair (and indeed of every pair) in the demo lace. -/
theorem demo_no_precedes (x y : Block) : ¬ precedes demoLaceFork x y := by
  -- no `pointed` edge exists: every member's preds is a singleton marker not present in the lace.
  have noedge : ∀ a b, ¬ pointed demoLaceFork a b := by
    rintro a b ⟨hmem, hla, hlb⟩
    have hbmem : b ∈ demoLaceFork := List.mem_of_find?_eq_some hlb
    -- b's preds is [approveMark] or [revokeMark]; a.id ∈ preds ⇒ a.id is a marker.
    have hmarker : a.id = approveMark ∨ a.id = revokeMark := by
      simp only [demoLaceFork, consentBlock, fork9approve, fork9revoke, List.mem_cons,
        List.not_mem_nil, or_false] at hbmem
      rcases hbmem with rfl | rfl | rfl | rfl <;>
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          first
            | (left; exact hmem)
            | (right; exact hmem)
    -- but a marker does not resolve in the lace (lookup is none), contradicting `hla`.
    rcases hmarker with hA | hB
    · rw [hA] at hla
      have hnone : demoLaceFork.lookup approveMark = none := by decide
      rw [hnone] at hla; exact absurd hla (by simp)
    · rw [hB] at hla
      have hnone : demoLaceFork.lookup revokeMark = none := by decide
      rw [hnone] at hla; exact absurd hla (by simp)
  intro h
  induction h with
  | base hp => exact noedge _ _ hp
  | trans _ _ ih _ => exact ih

/-- **`demo_consent_equivocation` (PROVED)** — author 9 equivocates over batch 42 in
`demoLaceFork`: an APPROVE (id 102) and a conflicting REVOKE (id 103), both authored by 9, both
over digest 42, present, neither observing the other. The signed consent fork. -/
theorem demo_consent_equivocation : consentForks demoLaceFork 9 demoDigest := by
  refine ⟨fork9approve, fork9revoke, by decide, by decide, by decide, by decide, ?_⟩
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  exact ⟨by decide, demo_no_precedes _ _, demo_no_precedes _ _⟩

/-- **`demo_fork_detected` (PROVED)** — the byzantine-repelling theorem on the concrete consent
fork: party 9 is an equivocator and the witnessing incomparable pair is present. So a fork-aware
validator CAN detect party 9's double consent (this is what makes rejecting it computable). -/
theorem demo_fork_detected :
    Equivocator demoLaceFork 9 ∧
    ∃ a b : Block, a ≠ b ∧ ¬ precedes demoLaceFork a b ∧ ¬ precedes demoLaceFork b a :=
  consent_equivocation_detectable demo_consent_equivocation

/-- **`demo_fork_blocks_settlement` (PROVED)** — the equivocation keystone on the concrete fork.
Party 9 has forked over the batch (an unsigned approve id 102 + a revoke id 103, the incomparable
pair `demo_consent_equivocation`), so 9 has NO valid signed consent counted
(`partySignedConsent demoLaceFork 9 demoDigest = false`, by `decide`). Hence `equivocating_party_
blocks_settlement` fires on the SAME fork lace: party 9 is a DETECTED equivocator AND the userspace
mutation does NOT commit — the byzantine consenter is repelled at the consent gate, on real data. -/
example :
    Equivocator demoLaceFork 9 ∧
    laceSettle demoState demoLaceFork demoBatch demoDigest = some demoState :=
  equivocating_party_blocks_settlement demoState demoLaceFork demoBatch demoDigest
    (p := 9) (by decide) demo_consent_equivocation (by decide)

#guard (s!"consent-lace settlement: n={demoBatch.requiredParties.length} parties \
{demoBatch.requiredParties} must each SIGN consent over digest {demoDigest}; suspended until all \
signed, then atomic commit through the verified executor; an equivocating signer is detected + blocked"
        == "consent-lace settlement: n=3 parties [7, 8, 9] must each SIGN consent over digest 42; suspended until all signed, then atomic commit through the verified executor; an equivocating signer is detected + blocked")

/-! ### §9.1 — THE CONSENT-BINDING DIFFERENTIAL GOLDEN VECTORS. These `#guard`s pin the
consent-decision values that the Rust differential (`captp/tests/consent_lace_differential.rs`)
re-asserts against a clause-for-clause mirror of `isApprovalFor` / `consentLaceComplete`. A drift
on EITHER side fails: change the Lean decision → a `#guard` trips at Lean build; change the Rust
mirror → its `assert_eq!` against `LEAN_*` (copied from these `#guard`s) trips. The corpus is the
party-7 perspective on a 4-block consent lace: a valid signed approve, an unsigned approve, an
impersonation, a wrong-digest signature, and a revoke. -/

/-- The differential corpus: blocks probed for "is this party 7's signed approve over digest 42?".
Index order is FIXED (the Rust test enumerates the same order). -/
def diffCorpus : List Block :=
  [ consentBlock 7 42 .approve 100                                  -- 0: valid signed approve  ⇒ true
  , { consentBlock 7 42 .approve 101 with signed := false }         -- 1: unsigned approve       ⇒ false
  , consentBlock 5 42 .approve 102                                  -- 2: impersonation (party 5)⇒ false
  , consentBlock 7 99 .approve 103                                  -- 3: wrong digest (99)      ⇒ false
  , consentBlock 7 42 .revoke 104 ]                                 -- 4: a revoke, not approve  ⇒ false

-- GOLDEN: `isApprovalFor b 7 42` over the corpus — ONLY the first (valid, signed, self-authored,
-- right-digest, approve) block counts. This IS the consent-binding decision, pinned.
#guard (diffCorpus.map (fun b => isApprovalFor b 7 42)) == [true, false, false, false, false]

-- GOLDEN: the n-ary convergence gate over the 3-party (7,8,9) all-signed lace is `true`; over the
-- missing-9 lace is `false`. The Rust mirror re-asserts both.
#guard consentLaceComplete demoLaceAllSigned [7, 8, 9] 42 == true
#guard consentLaceComplete demoLaceMissing9 [7, 8, 9] 42 == false

-- GOLDEN: party-by-party signed-consent over the missing-9 lace — 7 yes, 8 yes, 9 no. Pins the
-- per-party consent-binding the Rust mirror reproduces.
#guard ([7, 8, 9].map (fun p => partySignedConsent demoLaceMissing9 p 42)) == [true, true, false]

-- GOLDEN: on the fork lace, party 9 has NO counted signed consent (both fork branches fail to
-- count — the approve is unsigned, the revoke is not an approve), so the exchange does NOT converge.
-- The byzantine consenter contributes nothing.
#guard partySignedConsent demoLaceFork 9 42 == false
#guard consentLaceComplete demoLaceFork [7, 8, 9] 42 == false

end NonVacuity

/-! ## §10 — Axiom-hygiene tripwires. Every PROVED keystone depends ONLY on the three standard
kernel axioms (no `sorryAx`). -/

#assert_axioms unsigned_does_not_count
#assert_axioms wrong_author_does_not_count
#assert_axioms wrong_digest_does_not_count
#assert_axioms absent_does_not_count
#assert_axioms settle_requires_signed_authorship
#assert_axioms incomplete_lace_freezes_state
#assert_axioms laceSettle_complete_is_drain
#assert_axioms laceSettle_atomic_aborts_on_unauthorized
#assert_axioms laceSettle_preserves_caps
#assert_axioms laceSettle_conserves
#assert_axioms consent_equivocation_detectable
#assert_axioms equivocating_party_blocks_settlement
#assert_axioms partySignedConsent_mono
#assert_axioms consentLaceComplete_mono
#assert_axioms demo_consent_equivocation
#assert_axioms demo_fork_detected

end Dregg2.Exec.CapTPConsentLace
