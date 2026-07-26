# The Federation Knows a Secret No Member Knows

*On constructive knowledge, distributed knowledge, manufactured common knowledge, what
zero-knowledge does to all three, what other blockchains are entitled to conclude about any
of it, what breaks when a key leaks — and the rare case where emergence is a theorem instead
of a vibe.*

Take three validators. Give each one byte of a Shamir sharing: member *i* holds the point
`(i, 0x42 ⊕ 0xAB·i)` in GF(256). Ask each of them: what is the secret?

None of them knows. This is not a manner of speaking — it is proven twice over, once
structurally and once information-theoretically. Structurally: a share sits at `x ≠ 0` and
the secret lives at `x = 0`, so no share can ever verify the secret statement
(`share_alone_never_verifies`). Information-theoretically: any sub-threshold collection of
shares is consistent with *every possible secret* — for any two candidate secrets there
exist sharings agreeing on everything observed whose secrets differ by exactly that gap
(`shamir_below_t_undetermined`, riding Mathlib's Lagrange interpolation).

Now let any two of them cooperate. The Lagrange reconstruction of their two shares at
`x = 0` — the *real* reconstruction, the executable `reconstructByte` pinned byte-for-byte
to the deployed Rust — produces `0x42`, and the proof executes it inside the Lean kernel by
`decide`. So:

> **The group knows. No member knows.** `distributed_without_individual`
> (`Dregg2/Authority/Epistemic.lean:565`): `DistributedKnows … ∧ ∀ i, ¬ Knows i` — one
> theorem, both halves, over the federation's actual threshold-decryption algebra.

Epistemic logicians call this D-without-K: distributed knowledge strictly above every
individual's. It is usually a curiosity about possible-world models. dregg's version is
different in two ways. First, it is *constructive*: "knows" never means anything
mentalistic — it means *can exhibit a verifying witness*. Second, it is proven against the
running mechanism: the pooling operation is the federation's threshold decryption, the
shares are its shares, and the statement the coalition knows is the one its quorum gate
actually discharges.

This essay is about what that theorem — and the tower it anchors — says about *entities*.
Because "the group knows something no member knows" is the sentence people reach for when
they want to say a collective is real, over and above its members. Usually that claim is
atmosphere. Here it has a proof, a birth condition, a substance, a border, a uniqueness
law, and a documented failure mode when its secrets escape.

---

## 1. Knowledge is what you can exhibit

Everything below runs on one seam, and it is worth seeing exactly how small it is
(`Dregg2/Laws.lean:35`):

```
class Verifiable (P : Type*) (W : Type*) where
  Verify : P → W → Bool

def Discharged (p : P) (w : W) : Prop := Verifiable.Verify p w = true
```

`Verify` is a `Bool`-valued function — simultaneously the proof target and a runnable
oracle — and `Discharged` is decidable by construction. On top of it, one existential
(`Epistemic.lean:102`):

```
Knows pocket a φ  :=  ∃ w, pocket a w ∧ Discharged φ w
```

An agent's epistemic state is its **pocket** — the witnesses it can produce on demand. To
know `φ` is to be able to pull out a witness the verifier accepts. The foundational
document (`metatheory/CONSTRUCTIVE-KNOWLEDGE.md`) states the doctrine without hedging:
*"To know something here is to be able to produce a witness the kernel accepts,"* and its
twin for authority: *"You hold a capability iff you can produce the witness for it — never
merely assert it, never merely be named in a table. Authority is production under
non-forgeability."* The two are formally the same object: capability-holding (`Holds`,
`metatheory/Metatheory/ConstructiveKnowledge.lean:76`) is literally the full-pocket special case of
`Knows`, and `holds_iff_discharged_witness` is an `Iff.rfl` — *"knowledge = a verifiable
witness, full stop — no hidden assertion channel."* Possession and production are the same
act. The whole edifice is organized around one asymmetry, stated in the doc as its
engine: **proof-checking is cheap and trusted; proof-search is undecidable and
untrusted.** The `Knower` structure carries both halves — a trusted decidable `Verify` and
an opaque, possibly-adversarial `find` — and `find_realizes` proves the untrusted side can
only ever *establish* knowledge, never fake it, because everything it returns is funneled
through the trusted check.

Four consequences, each proven, each strange from the classical angle:

**Possession is not knowledge.** The designated-verifier machinery hands `v0`'s
zero-knowledge transcript to *every* agent — total forwarding, everyone holds the bytes.
`v0` knows; the others, holding the identical witness, provably do not
(`dv_forwarding_no_E`): the discharge relation is verifier-indexed, and for anyone else
the transcript could have been a simulation. Knowledge lives in the relation between a
witness and a verifier, not in the bytes.

**Knowledge is production, not descent.** Over the witness fibration, `Knows` *is* the
left-adjoint composite `∃_a ∘ q_a*` (`mem_knowsSet_iff`); the box reading — "everything
the agent holds verifies φ" — coincides with it exactly on single-credential pockets
(`knowsSet_eq_boxSet_of_functional`) and provably diverges at a mixed pocket
(`MixedPocket.knows_ne_box`). Knowing is ◇, an existential act. This mirrors, deliberately,
the authority doctrine's own correction: *"authority is not affine descent… it is
constituted by what you can prove, every time, at the point of use."*

**Copying knowledge is minting authority.** `knowledge_no_free_copy`
(`ConstructiveKnowledge.lean:444`): in a cancellative resource reading, an ordinary
(non-minting) duplication `A ⟶ A ⊗ A` forces the resource count to zero — only empty
knowledge copies freely. Substructural logic surfacing as a security law: no inflation of
authority, because authority *is* knowledge.

**Ignorance is not a type.** On the biorthogonal side of the tree, knowledge classes are
behaviours — closed under the double-orthogonal of a challenge relation — and behaviours
are evidence-monotone. "Does not know" is *not* a behaviour (`ignorance_not_behaviour`):
the closure floods non-knowledge upward. In a witness semantics you can prove that someone
knows; you can never carve out, by any family of tests, the set of those who don't.
Plausible deniability is not a policy here. It is a structural fact about what testing can
see. (Hold that thought until §6, where it becomes the leak analysis.)

## 2. The tower, and where it breaks

Four operators, one pocket semantics (`Epistemic.lean` §2):

- **K** — `Knows`: one agent can exhibit a witness.
- **E** — `EveryoneKnows`: every member of a group can exhibit a witness — *each possibly
  its own, private, mutually invisible witness*.
- **D** — `DistributedKnows`: the group's *pooled* witnesses — the closure of members'
  pockets under an explicit combining operation (`Pooled`: Lagrange interpolation,
  signature aggregation, concatenation) — contain a verifying witness.
- **C** — `CommonAt`: a verifying witness is *finalized*, hence visible to every agent by
  the finality floor's law.

Each operator is welded to a running mechanism rather than modeled beside it. E is the
polis council: an approval witness is necessarily the member's own turn
(`approval_witness_pins_sender`), so a full certificate is a tuple of per-member
witnesses, each in its member's pocket and provably in no other's
(`approval_not_exhibitable_by_other` — a stolen capability cannot claim another's vote). D
is the threshold gate, as above. C is finality: `CertValid` is the node's *real*
super-ratification rule over its real tau ordering, with an executable `#guard`-checked
certificate as non-vacuity.

The inclusions that hold are proven (`C → E → K → D`), and the ones that fail are
witnessed rather than waved at:

**D ⇏ K** is the threshold separation. The coalition's knowledge is not any member's and
not their union's — it exists only through the combining computation. The `Pooled` closure
is the exact formal content of "the whole is more than the parts": not a mystical surplus,
an *inductive datatype* — seeds (what members hold) plus mixes (what combining derives) —
with `pooled_invariant` as the no-conjuring law bounding the surplus.

**E ⇏ C** is the deepest single fact in the file (`no_common_for_private_pockets`): two
agents each privately, verifiably know `φ`, and *no possible finality floor consistent
with their pockets* can ever make `φ` common knowledge. Everyone knowing is compatible
with the group never knowing that it knows. The gap between E and C is not iteration
bookkeeping; it is a missing *object* — the one shared witness — and no amount of private
knowing manufactures it.

## 3. The entity that exists only above threshold

Below the threshold, the coalition-as-knower does not exist — not "knows less," but *is
consistent with every secret*. At the threshold it snaps into existence:
`threshold_knows_secret` exhibits the quorum — distinct members, each producing its share,
one combine, verification passes. The birth of the collective epistemic subject is a step
function, and both sides of the step are theorems. (The step is a cliff in the other
direction too, which is the dark half of §6.)

What is the entity *made of*? The biorthogonal analysis answers precisely. The
distributed-knowledge class is **not rectangular** — provably, no family of per-member
tests can carve it (`distributed_not_behaviour_rectangular`); it becomes a behaviour only
when the *pooled reconstruction challenge* is fielded as a test, and it then equals
exactly the closure of matched-randomness tensors
(`dclass_eq_closure_of_matched_tensors`). Compare conservation: not carvable per-turn,
exactly the closure of matched-delta tensors. The classification theorem
(`correlation_classifies_the_family`) says these are one phenomenon: a law that lives in
the *correlation* between components, invisible to every componentwise view.

So the emergent knower is made of correlation the way a conserved quantity is made of
matched deltas. The federation's knowledge is not stored anywhere. It is not distributed
*over* the members like files over disks. It is the correlation between their pockets plus
a combining computation — exactly as real as conservation, and real in the same formal
sense: both are behaviours, both are carved by tests, both provably do not reduce to their
components.

## 4. Common knowledge is manufactured, and the machine is the ledger

E ⇏ C says private knowledge never spontaneously becomes common. The coordinated-attack
folklore says messages can't close the gap either. So where does common knowledge come
from?

You *manufacture the shared witness*. `finality_is_common` (`Epistemic.lean:660`): a valid
finality certificate makes its finalized root common knowledge at its wave. The mechanism
is almost embarrassingly concrete. The infinite E^k tower collapses because there is *one*
witness, the cert, and its verification is agent-independent — `cert_visibility_uniform`
is an `Iff.rfl` because the check literally takes no agent argument. Every agent can
exhibit the very witness that establishes every other agent's knowledge, at every depth,
uniformly (`common_gives_mutual_witness`). Common knowledge is not an infinite conjunction
achieved; it is a single transferable artifact, engineered. A ledger, on this reading, is
a **common-knowledge prosthesis** — a machine whose product is the shared witness that
private pockets and message-passing provably cannot produce.

Note the load-bearing word *transferable*. Finality can seed common knowledge only
because a finality cert sits at the public endpoint of the designated-verifier dial —
identically checkable by everyone. A DV witness, convincing only its designated verifier,
could never do this (§7 of the file proves the separation). Transferability is the
dial-position that makes a witness *social*.

The manufactured subject has laws:

- **It cannot bifurcate.** `no_conflicting_common_per_wave`: two valid certificates over
  the same view anchor the same leader — common knowledge at a wave is unique. At most one
  "what we all know" per wave.
- **It cannot be forked by a partition.** A bridge that settles on locally-visible
  approval double-settles under partition (`unguarded_double_settles` — four validators
  split two and two, both sides mint). Guard settlement on the common-knowledge
  constructor — a super-majority of ratifiers — and *no partition of any committee size*
  can settle on both sides (`commonAt_guard_partition_safe`), because two disjoint
  super-majorities cannot fit in one committee. Safety unconditional; the price is
  waiting out the partition.

That price is typed. The epistemic guard atoms carry their coordination cost as part of
their design (`EpistemicAtom.cost`): K and DV-K are **free** (a local witness check); D
costs **one quorum round**; C costs **finality latency**. To be an individual knower is
cheap. To be a coalition costs a round-trip. To be a *public* costs finality — and the
partition-safety theorem is what that latency buys. The ontology has a price list.

## 5. The dial: what zero-knowledge does to the tower

Everything so far treats a witness as a lump: exhibit it and the verifier knows. Zero
knowledge is the discovery that the lump has *layers*, and dregg's metatheory carries the
layering as a first-class object — a **disclosure dial** — with the tower rebuilt around
it.

The foundational split (`ConstructiveKnowledge.lean:212`): `verifier_learns_only_acceptance`
and `content_not_reached_from_acceptance` — the verifier's position after a ZK
presentation is *strictly below* content. What a proof transfers is exactly the
∃-statement — *that* some witness discharges the predicate — never the witness. And the
dial theorem (`EpistemicDial.lean`): `accepts_invariant_under_dial` — turning the dial
changes *what else the verifier learns*, never *what is known to hold* — with
`leak_mono`: descending the dial never leaks more, and the ZK floor leaks least. Same
knowledge, tunable revelation, as theorems.

The deployed instances, each with teeth in both polarities:

**Selective disclosure** (`Authority/SelectiveDisclosure.lean`, modeling the real
`credentials/src/presentation.rs` path): a credential holder reveals chosen slots and
proves predicates over hidden ones. The observer's knowledge is bounded exactly:
`presentation_hides_undisclosed` — the observer-view is provably *constant* across all
credentials agreeing on disclosed slots (the view is a function of disclosed slots and
proven `(slot, predicate)` pairs, nothing else) — paired with `disclosed_slot_is_revealed`
— distinct disclosed values force distinct views, so the hiding theorem is not a
`True`-masquerade. What the verifier does learn is real: `proven_predicate_holds` gives
`evalPred pred (attr slot) = true` of the hidden value, and a false predicate is
*uninhabitable* (`predicate_proof_has_teeth` derives `False` from an alleged `≥ 18` proof
over a 17). And the verifier cannot even accumulate knowledge across encounters:
`multishow_unlinkable` — two presentations of the same credential under fresh blinding
produce equal views; the verifier cannot know it saw the same credential twice. Sameness
itself is undisclosed.

**Private conservation** (`Authority/PrivatePredicate.lean`) — the one to sit with,
because it feeds the emergence thesis directly.
`private_conservation_checks_homomorphically`: the executor's homomorphic check on
commitment sums holds *iff* the hidden values conserve — the verifier reads only
`insCommit`/`outsCommit`, never a value, never a blinding. The witnessed pair: a
conserving split passes; an inflating split (5 in, 9 out) *fails the commitment check
itself* — the executor rejects the inflation *without opening a single value*. The
disclosure accounting is exact: the affine fragment and the range fragment price at `⊥`
on the dial (`affine_reveals_nothing`, `range_reveals_only_truth_bit`), any cleartext
fragment prices at `⊤` (`cleartext_fragment_discloses_slots`), and at the floor the
verifier learns precisely the truth bit (`privPred_floor_reveals_only_truth`). The file's
own phrase is the right one: **enforcement without surveillance.** A collective can
enforce a law over values it structurally cannot see. The emergent subject of §3 gains a
stranger power: it can *know-that* — the law holds, the books balance — while no
component, and not even the collective verifier, *knows-what*.

**Shielded value** (`cell/src/note.rs` + `Exec/NullifierAccumulator.lean`): at
note-create, what becomes public is a Poseidon2 commitment (and, via batching, only
batch-granular timing); owner, amount, asset, randomness stay private. At note-spend, the
nullifier and the spent amount become public; *which commitment died* stays unlinkable —
the nullifier binds a ~248-bit spending key, so only the owner can compute it. And the
double-spend gate is an epistemic construction of its own: a valid spend witness *proves
non-membership* in the committed nullifier set (`witness_fresh`); after the spend, the
committed root makes any second witness for the same nullifier *nonexistent* —
`present_no_witness` is an `IsEmpty` instance, and `spend_then_no_rewitness` composes it:
the rejection of a double-spend is not a scan, it is **witness scarcity**. The STARK for
the second spend cannot be produced. Fail-closed security as the non-existence of a
constructive object.

**Deniability** (`Authority/DesignatedVerifier.lean`) — the dial's other axis:
*transferability*, orthogonal to disclosure. A designated-verifier proof convinces `V₀`
while being worthless as evidence to anyone else, because `V₀` could have simulated it
from its own trapdoor (`designated_is_deniable`; the simulator law is carried as a named
class obligation, the honest §8 posture). Under DV, acceptance stops being transferable
evidence: K without the ability to seed E. The file is equally plain that *shipped* dregg
sits at the opposite pole — the deployed presentation verifier takes no verifier index, so
every discharged transcript convinces everyone (`public_convinces_any_third_party`):
non-repudiation forced by the architecture, with DV the modeled road not yet taken.

Put §5 back against the tower and the refinement is clean: zero-knowledge splits every
operator into *knowledge-of-∃* and *knowledge-of-content*, and lets the system route them
separately. A federation can hold E or even C of the ∃-statement — everyone commonly
knows the payment cleared, the balance conserves, the credential holder is of age — while
content remains exactly one pocket's K, or no one's. The tower is not four rungs but four
rungs times a dial position, and the dial's invariance theorem guarantees the rungs don't
move when the dial does.

## 6. Interchain: what other chains are entitled to know

A federation's edges are where epistemics gets adversarial: other systems that share no
kernel, no finality floor, no combining operation. dregg's interchain posture, read
end-to-end, is a single principle applied in both directions: **knowledge is graded by
the witness that carries it, and the grade is stated, not laundered.**

**Outbound — what an EVM contract knows after `settle` succeeds.** The wrapped Groth16
proof binds a 25-lane public statement: `genesis_root[8] ‖ final_root[8] ‖ num_turns ‖
chain_digest[8]`. Its Lean meaning (`wellformed_attests_whole_history`): there exists a
sequence of `num_turns` finalized turns, each executed correctly by the verified executor,
correctly ordered with no reorder, drop, or insert, folding the state root from
`genesis_root` to `final_root`. That is a genuine ∃-statement about dregg's whole history,
checkable by a contract that re-witnesses nothing. Equally important is what the contract
does *not* know: no state contents (two 8-lane roots, no balances, no cells), no turn
contents (the digest commits ordered root-pairs only; even "this turn arrived encrypted"
is a single deliberate bit), and — a designed epistemic *refusal* — no outbound messages:
`isProvenMessageRoot` returns false for every input until the message commitment is
proof-bound, because the prior path would have let an operator attest an arbitrary root
and forge cross-chain inclusion. The contract is not allowed to know what the proof does
not carry. (The knowledge is relative to a named carrier stack — the FRI floor, the
Groth16 dev ceremony — inventoried in the ledger below, not footnoted away.)

**Inbound — what dregg knows about other chains, graded.** The chain-participation census
is effectively an epistemic ladder, and reading it as one is clarifying. The Stripe
zkTLS/DECO path is the K-grade design: `deco_authenticates_payment` certifies a four-link
chain — Stripe's key signed the session key, the transcript is MAC'd under it, the
commitment opens to exactly the disclosed facts, the amount is positive — as an
exhibitable, re-checkable witness (modulo named signature/MAC/hash carriers and the
Web-PKI floor). The Solana consensus path is E-grade: a *real* Tower-BFT verification —
stake-weighted Ed25519 supermajority, bank-hash recompute — that dregg itself runs and
could re-run, but off-circuit: re-executing-validator knowledge, not yet exportable as a
succinct proof. The Solana mirror is threshold-oracle attestation and the ETH/Base
listener is an RPC finality tag — graded in the census as exactly what they are:
testimony. And Mina is the cautionary tale the repo keeps on purpose: a recursion wrap
that claimed more than it checked was found vacuous and *removed* — a recorded refusal to
launder a fake K.

Two constructions sharpen the picture:

- **Knowledge without possession.** Proof-of-holdings: `weight_backed_and_noncustodial` —
  any voting weight granted from a foreign holding is backed by a consensus-proven,
  finalized, owner-bound balance of at least that amount, *and the foreign chain's
  post-state is definitionally the pre-state* (`grant_preserves_custody := rfl`). No
  vault, no lock, no wrapped token. dregg comes to know "this account held ≥ W at slot S"
  and the knowing moves nothing. The untrusted tier provably grants zero
  (`rpc_grants_no_weight`), and the deciding function is the exported Lean object itself,
  so the verdict is rendered by the proven code, not a Rust re-implementation.
- **A counterparty that lives nowhere.** The private-leg construction
  (`Distributed/PrivateLeg.lean`): a cell maintained entirely offline joins an atomic
  multi-cell turn contributing only `(commitPre, commitPost, proof)`. The keystone
  (`joint_turn_sound_with_private_legs`) gives the counterparties exactly this knowledge:
  the joint turn conserves publicly; *and for every private leg there exist hidden states,
  bound only under the ∃, that ran a real conserving, authorized offline step matching
  the published commitments* — "even though no one but the maintainer saw the authority
  check." The counterparty knows the ∃; the state never existed on any machine it could
  ask.

And the borders are epistemic objects too. Every receipt and every sovereign-witness
signature binds a `federation_id` under a domain-separated context, so a valid receipt
from federation A *discharges nothing* in federation B — knowledge is deliberately
non-transportable by replay across the boundary. Between sovereign systems there is no
shared finality floor, so there is no ambient C; anything commonly known across a border
has to be manufactured per-boundary, by exactly the §4 mechanism — which is why the
partitioned-bridge theorem is not a toy: a bridge *is* two systems trying to construct
common knowledge, and the double-settle counterexample is what "everyone locally knew" is
worth without the shared witness.

## 7. Leaks: you cannot un-know a secret; you can only make it stop being a key

Now the failure mode. A private key escapes; a threshold share is exfiltrated; a
credential's holder goes rogue. What does the epistemic frame say — and what does the
system actually do?

Start from the substance law. Evidence, in dregg's four-substance ontology, is the
monotone one: the constructive-knowledge doc states it as *"You may construct knowledge;
you may never quietly retract it,"* and the theorems enforce it everywhere the substance
lives — `spend_monotone` (the spent set only grows), `revocation_is_iconfluent` (once
revoked, forever revoked, merge-stable across partitions), `execFullForestA_logMono` (the
receipt log never shrinks). A leak is an irreversible K-event: the adversary's pocket now
contains the witness, and §1's `ignorance_not_behaviour` already told you there is no test
family that can certify they don't. **Un-knowing is not in the ontology.**

What *is* in the ontology is the other half of the `Knows` conjunction. `Knows = ∃ w,
pocket a w ∧ Discharged φ w` — the system cannot reach into pockets, but `Discharged` is
its to define. Every leak response in the codebase, without exception, is a rewrite of
what the stolen witness *discharges*:

- **Bound first.** Before any response fires, the blast radius is already a theorem:
  non-amplification means the thief's constructive knowledge is bounded by what it stole —
  `key_leak_attacker_blind`: *"possession of the key buys the held caps and NOTHING
  more,"* and `leak_blast_no_amplify`: no new targets, no widened authority, down
  arbitrary attenuation chains (`chain_narrows` — a leaked *derived* credential admits a
  subset of what the root admitted, and no restriction "adds back" authority,
  `amplification_impossible`).
- **Revoke.** `revoke_blocks_verify`: after revocation the credential no longer
  discharges — and note what did *not* happen: its signature is still cryptographically
  valid; the attestation still verifies. Only the negative leg flipped. Revocation is a
  grow-only G-Set needing only root-epoch agreement (revocations from partitioned issuers
  union losslessly), and the executor's teeth are fail-closed against committed,
  adversary-uncontrollable state: `gateOK_revoked_fails` — a revoked nullifier in the
  committed registry rejects the node and rolls back the entire forest, TOCTOU-free.
- **Win the race to the tip.** The leaked-cap race has exact semantics
  (`metatheory/Metatheory/SettlementSoundness.lean` + `KeyLeak.lean`). `LiveAtTip`: settled
  authority must be held *and* honored by the finalized revocation set at the settlement
  tip. `revoke_before_tip_unsettleable`: a revocation logged at origin `m` at time `τ`
  forecloses settlement at any tip with `τ + delay(m, tip) ≤ tip.time`. Both sides of the
  bound are inhabited: the demo tip *inside* the propagation window settles; the tip *at*
  the bound is unsettleable. At n = 1 the window vanishes — the revoke forecloses the
  instant it lands. And the failure shape is refuted, not just avoided: a settlement
  predicate that carries a stale branch-time view of authority provably fails the
  `BindsLiveAuthority` interface (`branchSettle_NOT_binds`). The corollary is named for
  this section: `leaked_then_revoked_cannot_settle` — the leak's blast radius is bounded
  *in settled state*, not merely in honored exercises.
- **Rotate.** A cell's verification key is itself governed: `set_verification_key` is a
  permission slot whose sovereign default is `Proof` — *the outgoing circuit must
  authorize its own replacement* — and the new VK digest is welded into the cell's
  committed state with `None` as an explicit all-zero revoke sentinel, so light clients
  compare against the pin and old-circuit proofs simply stop discharging the gate.
  Rotation re-keys the future; it does not, and cannot, edit the past.

What is *not* recoverable is exactly what the monotone substance says: whatever settled
inside the stale window; every spent nullifier; the receipt log (which is the forensic
upside — every exercise the thief made left a permanent attested receipt; the leak is
*knowable* forever); the revocation itself; and the stolen witness in the adversary's
pocket.

The threshold case is the purest statement of the whole frame, because there the leaked
object is not a credential *about* knowledge — it *is* knowledge, a bare Shamir point.
Below threshold, the grace is information-theoretic: `t−1` leaked shares are consistent
with every secret; the adversary's coalition, pooled, knows *nothing*
(`subthreshold_pool_blind` — the same theorem that made the federation an emergent knower
now bounds the adversary's emergent knowing). At `t`, the cliff: `t` shares determine the
secret uniquely, and a forked threshold certificate is formally *identical* to holding
the group secret. And here the system's honesty is total, because the resharing code says
out loud what no protocol can do: *"resharing does NOT revoke old shares. They remain
valid Shamir points of the same `f(0)` forever… deletion is a party-local act no protocol
can force."* What proactive resharing buys is a new *verification surface* per epoch — the
adversary must assemble `t` leaks within one epoch window rather than across the
committee's lifetime. There is no per-share revocation, and there cannot be: revocation
operates on discharge, and a raw share has no discharge to operate on. Where the leaked
thing is pure knowledge, the protocol concedes the epistemics and manages the *clock*
instead.

That is the leak doctrine in one line, and it is the essay's thesis applied under
adversity: **the witnesses cannot be moved, so the system moves the tests.** Attenuation
was already refutation-growth (`attenuation_is_refutation_growth` — adding caveats grows
the test set and shrinks the behaviour); revocation, rotation, and resharing are the same
operation performed in anger. You cannot un-know a secret. You can only make it stop
being a key.

## 8. What kind of thing is a federation, then?

The companion essay argued a cell is not a datastructure — it is pinned between two
fixpoints, its identity the unique unfold into a final coalgebra, its interface a
biorthogonally closed set. The epistemic tower runs the same maneuver on collectives, and
the three new sections each add a clause to the answer.

A federation, as an epistemic subject, is **a pocket assignment, plus a combining
operation, plus a finality floor** — and each ingredient is individually load-bearing.
The pockets say what members can exhibit. The combining operation says what the coalition
can derive: change it and you change what the group knows, members untouched. The floor
says what the group knows *in common* — and it is exactly the assumption a partition
suspends, which the file states rather than hides: C is relative to the floor law, and at
n = 1 the whole tower collapses onto K.

Now the refinements. The subject's knowledge has a *dial* (§5): it can know-that without
knowing-what — enforce conservation over values it cannot see, certify age without
learning birthdays, accept payments whose contents stay one pocket's private K. Its
*borders* are epistemic (§6): domain-separated replay boundaries; graded, named-witness
knowledge of foreign systems; common knowledge across a border only ever manufactured,
never ambient. Its *persistence* is epochal (§7): it cannot forget — its evidence
substance is monotone, its logs append-only — so it survives compromise not by erasing
but by re-keying, out-racing leaks to the settlement tip and re-becoming, each epoch, a
subject whose tests the old secrets no longer pass.

None of these ingredients is a member. None is a sum of members. The subject they compose
is real by the only standard this codebase accepts: it is *interrogable* — there are
tests it passes that nothing smaller passes — and its existence conditions are theorems.
Emergence talk usually asks you to squint. This is the other thing: a collective entity
with a proven birth condition (the threshold), a proven substance (correlation, in the
precise biorthogonal sense), a proven identity law (one "we" per wave), proven
non-reducibility (D-without-K, both halves), a posted price (free / quorum / finality), a
disclosure dial with an invariance theorem, replay-sealed borders, and a documented,
theorem-bounded way of surviving its own secrets escaping.

The federation knows a secret no member knows — and we can say exactly what the "it" in
that sentence is, what it costs, what it refuses to learn, and how it dies and doesn't.

---

### Resolution ledger

Stated at current resolution, as always. The mechanism instances are proven against real
machinery — the council's actor-bound approval slots, the deployed Shamir/GF(256) algebra
with its Rust-pinned `reconstructByte`, the node's real super-ratification rule — while
the small TRUE/FALSE demos in each file are labeled toys. The four epistemic guard atoms
(`knownBy / distributedAmong / commonAt / privateTo`) are **design only**: signatures,
denotations, and cost classification exist; installation into the executor's guard
surface has not happened. C is explicitly relative to the finality floor's delivery law —
what a partition suspends — which is precisely why the `commonAt` guard is the
partition-safe one. On the ZK front: the Lean content is the information-theoretic core
(perfect view-collapse on the modeled transcript, homomorphic algebra, disclosure-dial
order theory); computational hiding/binding/indistinguishability are named §8 carrier
obligations, never claimed as Lean laws; designated-verifier mode is *modeled with its
endpoints witnessed*, while shipped dregg sits entirely at the transferable pole; the
cell-layer `SelectivelyDisclosable` tag currently routes like `Committed` (the
predicate-proof machinery lives in the credentials path); a note-spend publishes the spent
*amount* (unlinkability covers identity, not value). On the interchain front: the census
grades are a dated snapshot; the Stripe DECO path is proven and wired end-to-end locally
while the *operationally live* money-in remains the labeled HMAC fallback; the Groth16
settlement runs real proofs against the real generated verifier but under a single-party
dev ceremony; the Solana consensus verify is off-circuit; the outbound message root is
fail-closed unproven by design; and per the project's own recorded posture, the deployed
FRI floor and the witness-generator perimeter are open inadequacies that bound every
"an external verifier knows" claim in this essay. On the leak front: `BindsLiveAuthority`
is a typed interface with the circuit-emit conformance residual named in-file; attenuation-
chain integrity rides the named MAC carrier; FROST resharing is implemented for the BLS
beacon committee and staged (not deployed) for FROST proper, with erase-old-share
attestation planned and honestly unenforceable. The epistemic tower itself — operators,
inclusions, separations, mechanism welds, adjoint triple, partition theorems, revocation
and settlement keystones, monotonicity laws — is sorry-free and `#assert_axioms`-clean
against `{propext, Classical.choice, Quot.sound}`.
