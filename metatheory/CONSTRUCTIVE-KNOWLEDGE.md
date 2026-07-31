# dregg, as a metatheory of constructive knowledge

> This file names the thing the directory has been *mis-calling* "Metatheory." There is an
> **actual metatheory** here — a distributed, intuitionistic logic of *constructive knowledge and
> authority* — and there is the **verification of dregg2** (the Lean proofs that the system realizes
> that logic). They interact, but they are not the same. This document is the former: the conceptual
> spine, with the authority model stated as the law the verification discharges, and the realization
> traced through every layer the system is built from.

The README opens by calling dregg "my experiment in the metatheory of constructive knowledge." This
document is what that phrase means, taken literally and all the way down. The claim is not a slogan
laid over a capability system; it is the organizing principle from which every substance, verb, proof,
surface, and desktop affordance is a projection. To *know* something here is to be able to *produce a
witness the kernel accepts* — and every layer below is that single move, refracted.

---

## 0. The thesis: authority is constructive knowledge

**A principal's authority over a resource is exactly its ability to constructively exhibit a witness
the kernel accepts.** You *hold* a capability iff you can *produce* the witness for it — never merely
assert it, never merely be named in a table. Authority is **production under non-forgeability**.

This is the corrected, current thesis, and the correction is load-bearing enough to state its negation
first:

> **Authority is *not* affine descent.** It is tempting to read a capability as a linear/affine resource
> that is *consumed* as it flows — held, then spent, monotonically narrowing down a meet-semilattice.
> That frame is **wrong**: it forbids exactly the generative patterns (introduction, sealer/unsealer
> amplification, mint/factory) that give object-capabilities their power, and it locates authority in a
> *quantity that drains* rather than in a *witness you can re-exhibit*. Authority does not deplete by
> being used; it is constituted by what you can prove, every time, at the point of use.

So the unit of authority is a **proof obligation you can discharge**, and four facets make that sound:

1. **non-forgeability** — the crypto floor makes the ability to produce a witness *un-counterfeitable*;
2. **monotone attenuation** (`granted ⊆ held`) — production is monotone-*decreasing* along delegation:
   a delegate can only produce what its delegator could, or less;
3. **kernel enforcement** — the gate that accepts the witness is the kernel's, run on every step;
4. **zk-checkability** — the production is witnessed by a proof a light client (holding no secrets)
   can check.

Everything else — cells, turns, effects, the constraint catalog, finality, privacy, the desktop — is a
*projection* of "authority = constructive knowledge = production-under-non-forgeability." This is the
[BHK / realizability](https://en.wikipedia.org/wiki/Realizability) reading of intuitionistic logic,
made operational and distributed: the whole edifice is organized around the asymmetry **proof-checking
is cheap and trusted; proof-*search* is undecidable and untrusted.** A proposition you can prove is a
piece of knowledge you can construct; a capability you hold is a proposition you can prove; a turn is
the act of proving one. The metatheory and the access-control system are the same object seen from two
sides.

---

## 1. The knowledge graph

The capability graph **is** a distributed knowledge graph:

- **nodes** are *cells* — the knowers / agents / objects, each with private state and a program;
- **edges** are *capabilities* — directed facts of the form "this cell can constructively produce a
  witness the kernel accepts for authority over that one," carrying *attenuated rights* (a facet:
  which acts the edge licenses);
- the graph is **partial and local**: no node sees the whole graph. You learn of an edge only when
  someone *produces a witness* for it. There is **no global registry of who-can-do-what** — the
  capability-derivation tree is at most a *retrospective* log (the de-jure record), never a live oracle
  you consult. Authority is established by *exhibiting a discharging witness at the point of use*, and
  checking it.

To *hold* a capability is therefore not to possess a key in a lock — it is to be able to **discharge a
proof obligation**. Possession and production are the same act. This is also why there is exactly one
predicate language across the whole system: caveat (on delegated power), program (on self), precondition
(required of a turn), and intent-demand (wanted of the world) are *one `Pred` algebra* with four
polarities (README-LLMs §2). A guard is a proposition; discharging it is constructing its proof; and the
kernel never takes the caller's word — it checks the witness.

---

## 2. The four substances are four kinds of knowledge

A cell holds **four substances** (README-LLMs §2; `cell/src/`), and each is a distinct *epistemic mode*
— a different thing it can mean to know something here:

- **value** (per-asset `i64` balances; an asset *is* its issuer cell, which carries −supply, so every
  asset's sum is identically 0) — **conserved knowledge**: knowledge that cannot be created or
  destroyed, only moved. The assurance case's guarantee B is its law: `recTotal` is invariant on every
  reachable state. You cannot *know yourself into more money*; conservation is the impossibility of
  forging this kind of fact.
- **state** (programmable slots + nonce) — **revisable knowledge**: a cell's own beliefs about itself,
  governed by its program (a predicate over its own transitions, enforced on every turn touching it).
  The nonce is the freshness coordinate of revisable knowledge.
- **authority** (a capability tree / c-list) — **productive knowledge**: precisely the §0 thesis — what
  this cell can *constructively produce a witness for*. The other three substances are *what is known*;
  authority is *what can be done with what is known*.
- **evidence** (monotone nullifier / commitment / epoch ledgers) — **the constructive-knowledge ledger
  itself**: the append-only record of *what has been constructed*. This is the substance that makes the
  whole thesis operational, and it deserves its own treatment.

### 2a. Evidence is the constructive-knowledge ledger

Evidence is the only **monotone** substance, and that monotonicity *is* the constructive reading. A
nullifier is the trace that a one-shot thing was spent; a commitment is the trace that a hidden thing was
created; an epoch is the trace that delegated authority was refreshed. Knowledge, once constructed, is
recorded and **never un-constructed** — the ledger grows and never forgets.

This is proven, not asserted. The evidence camera is the authoritative set `USet` ordered by `⊆`
(`metatheory/Dregg2/Substrate/FpuProbe.lean:256`), and its growth law is `auth_grow_fpu`
(`FpuProbe.lean:178`): the authoritative element grows from `a` to `a + t` while every fragment a third
party holds stays valid — *appending knowledge invalidates no prior knowledge*. The spend instance is
`spend_evidence_fpu` (`FpuProbe.lean:575`): a committed `noteSpendNullifier` is *exactly* an instance of
`auth_grow_fpu` — the spent-nullifier ledger grows by precisely `{nf}`, frame-preserving. And the
monotone *tooth* — the non-vacuity that makes this a real constraint — is `forget_evidence_not_fpu`
(`FpuProbe.lean:596`): *forgetting* a nullifier is **not** a frame-preserving update, because a frame
holding the full snapshot is invalidated by the erasure. You may construct knowledge; you may never
quietly retract it.

Operationally the evidence substance is the kernel-reserved side tables `NULLIFIER` / `COMMIT` (and
`DELEG` for epochs) in `cell/src/state.rs:46`. The nullifier set is an append-only sorted Merkle
structure with non-membership proofs by adjacent-neighbor bracketing (`cell/src/nullifier_set.rs`); the
double-spend prevention of the assurance case's guarantee D is the *non-membership* of a nullifier in
this monotone tree — you can only spend a thing whose spend has not yet been constructed.

---

## 3. A turn is an authorized inference step

A **turn** is one step of distributed inference: a forest of *actions*, each of which proposes to move
the knowledge graph from one state to a successor, **executed as a transaction** (all-or-nothing;
journalled, rolled back on any failure). An action carries:

- a **demand ⊣ supply** pair (the cell *demands* `AuthRequired`; the action *supplies* a witnessed
  `Authorization`) — this is exactly the **`Predicate ⊣ Witness` adjunction**: admissibility is "does
  the supplied witness realize the demanded predicate?", i.e. `Verify P w`. Read as a Lawvere
  hyperdoctrine, `Predicate ⊣ Witness` is the *base* adjunction; production (this section) is its left
  leg made operational — you supply the witness, the kernel checks the predicate. (Agreement across
  knowers is the *limit* in this hyperdoctrine; the witness escapes Arrow-style impossibility precisely
  by restricting to *certifiable* claims — but that is the agreement story, downstream of production,
  and not relied on here.)
- **guards** (preconditions / program-constraints / caveats) — *more* predicates over the proposed
  step, each again first-party (decidable now) or witnessed (a registry verifier discharges it);
- **effects** — the proposed graph mutation;
- a signed **binding** to a canonical message (federation, nonce, action, effects) — so an inference
  cannot be replayed into a context it was not proved for.

Soundness is not a property of one step but of the **unbounded life of the cell**: the cell is *codata*
(`νC. µI. StepProof I × (Turn ⇒ C)`), and "the cell stays correct forever" is a **▶-guarded
bisimulation** to a golden-oracle reference — "the knowledge never drifts from the truth it claims."
Step-completeness (each step really attests its full invariant) is what makes the coinduction
productive rather than a *drifting future* that type-checks while leaking.

### 3a. Witness modes: knowledge separated from its proof object

A turn applies its **state transition** (the abstract semantics — balances, caps, nonces) independently
of **materializing its witness** (Merkle roots, commitments, proofs). This is `WitnessMode`
(`turn/src/collapse.rs`): `Symbolic` *defers* the witness layer, so a local UI/terminal turn pays
effectively zero hashing; `collapse` re-runs deferred turns to materialize the *exact* witnesses on
demand. The epistemic content of this is precise: **the knowledge is constructed eagerly; the
publishable proof of it is constructed lazily.** A symbolic turn knows its effect but holds no
stranger-checkable artifact — it is structurally local and unpublishable; collapse is the only path to a
`verifyBatch`-acceptable receipt. Crucially the *admission gates* (authority, conservation, freshness)
are never deferred — only the proof object. You always *check* you may construct the knowledge; you
defer only the *evidence you constructed it*. This is grounded in the `Exec ⊑ Abstract` refinement
(`metatheory/Dregg2/Spec/ExecRefinement.lean`): the abstract state is witness-free, and the deferred
layer is exactly what the refinement throws away.

---

## 4. The production law

To *produce* authority is to **exhibit the witness the kernel's gate accepts** — and the gate is one
fail-closed conjunction, run on every action. In the Lean executor it is `gateOK`
(`Dregg2/Exec/FullForestAuth.lean:490`):

```
gateOK na s = credentialValidG na      -- WHO  : the credential's witness verifies (non-forgeability)
           && capAuthorityG na          -- WHAT : kernel cap narrowing,  granted ⊆ held
           && caveatsDischarged na s     -- HOW  : caveat chain + tiered caveats discharge
           && revocationGate na s        --        the edge is not revoked/expired
```

The four facets of §0, mapped to the real proofs:

**(1) non-forgeability — the credential's witness verifies.** `credentialValidG`
(`FullForestAuth.lean:433`) reduces through **`portalVerify`** (`FullForestAuth.lean:138`): the crypto
arms (signature / proof / bearer / capTpDelivered / custom / stealth / token) route through the
`CryptoKernel.verify` portal — a named crypto floor — and the structural arms are pure reads. The
ten-variant `Authorization` dispatcher is `authModeAdmits` (`Dregg2/Exec/AuthModes.lean:182`), which
proves per-mode that admission implies the abstract authority object holds. `portalVerify`'s
non-vacuity is pinned in-file: a genuine signature is accepted, a *forged* one fail-closes, and
`Unchecked` is rejected at the §8 anchor (`FullForestAuth.lean:192-198`). Forgery is what production
must be safe against; the portal is where that safety is named.

**(2) monotone attenuation — `granted ⊆ held`.** Production is monotone-decreasing along delegation.
This is *not* a `() ≤ ()` collapse: the rights lattice is `ExecAuth := Finset Auth`, ordered by genuine
`⊆`, with `{read}` and `{write}` **incomparable** (`Dregg2/Exec/Caps.lean:57`). Attenuation narrows in
that real lattice: `attenuate_confRights_le` (`Caps.lean:130`). The delegation verb
`recKDelegateAtten` (`Dregg2/Exec/AuthTurn.lean:97`) carries
`recKDelegateAtten_non_amplifying` (`:439`): when a delegation commits, the granted cap's conferred
rights are `⊆` the held cap's — *granted-vs-held, not self-vs-self*. The generative twin,
`introduce_non_amplifying` (`Dregg2/Exec/EffectsAuthority.lean:207`), proves a Granovetter introduction
confers no more than the introducer holds, and `handoff_non_amplifying` (`Dregg2/Exec/CapTP.lean:286`)
reuses it for the two-signature CapTP handoff.

**(3) kernel enforcement — the gate is the kernel's, every step.** `gateOK` is *the* admission gate;
there is no ungated escape hatch on the gated forest. Whole-turn non-amplification survives the gate:
`execFullForestG_no_amplify` (`FullForestAuth.lean:1014`) — **every delegation edge produced by a gated
turn confers `≤` what the actor holds** — is a one-line corollary of the ungated
`execFullForestA_no_amplify` via the erasure discipline (`eraseG`). The gate adds restrictions and
removes none, so the headline survives it for free.

**(4) zk-checkability — the production is witnessed in-circuit.** The same `granted ⊆ held` is decided
in the circuit IR by **`checkSubset`** (`Dregg2/Circuit/Argus/Stmt.lean:83`), which commits iff
`a k ≤ b k` over the genuine partial order — fail-closed on a strict superset *and* on an incomparable
pair (`interp_checkSubset`, `Stmt.lean:338`). The deployed turn proof carries it: `AttenuateCapability`
and `GrantCapability` are witnessed in-circuit against the **authenticated openable `capability_root`**
(`circuit/tests/effect_vm_attenuate_non_amp.rs`, `effect_vm_grant_non_amp.rs`,
`circuit/src/cap_root.rs`), seeded from the cell's canonical root rather than zero
(`circuit/tests/cap_root_cell_circuit_differential.rs`), and the consumed capability's full leaf is
proven a member of the holder's pre-state root (`CapMembershipWitness`, `sdk/src/full_turn_proof.rs:212`).

These four are AND-ed and **fail-closed on any leg**. Production is the act that makes all four true at
once: exhibit a witness that verifies (1), confers no more than you hold (2), passes the kernel gate
(3), and leaves a proof a stranger can check (4).

The production law is, in `metatheory/Metatheory/PolisNonConfusion.lean:39`, restated in the camera
algebra: `production_step_fpu` is the deployed substance discipline that *authorized production is an
Iris frame-preserving update on the authority camera, and unauthorized amplification is provably not a
production step.* Constructing authority you hold preserves every observer's frame; constructing
authority you don't is not a move the algebra admits.

---

## 5. The receipt is a verifiable witness of constructed knowledge

A turn leaves a **receipt**, and the receipt's defining property is that it **binds the whole
post-state** — *constructively*. This is the **anti-ghost property** (README-LLMs §4): tampering a field
the effect did not legitimately construct makes the turn **unprovable**. You cannot witness knowledge you
did not construct.

This is the assurance case's guarantee C, and it is a theorem, not a convention. The executor is a
**memory program**: every kernel field and the receipt log project onto one domain-tagged universal
address space `uproj` (`Dregg2/Exec/UniversalBridge.lean:201`), and a verb's effect *provably equals the
fold of its emitted memory trace* over the pre-state projection. The headline is `integrity_guarantee`
(`Dregg2/AssuranceCase.lean:361`):

```
uproj C s' = (moveTrace C s t).foldl step (uproj C s)
```

— the post-state projection is *exactly* the fold of the trace the verb emitted, computed from the
pre-state without the executor peeking at its own output (`move_is_memory_program`,
`UniversalBridge.lean:587`; the deployed per-asset arm `moveAsset_is_memory_program`,
`ForestMemoryProgram.lean:143`). Because the trace is emitted blind and the fold is deterministic,
*tampering any address the effect did not write makes the fold disagree, and the receipt does not bind.*
This composes to the whole turn: `integrity_guarantee_whole_turn` (`AssuranceCase.lean:401`) proves a
committed gated full-forest run — the body behind the `dregg_exec_full_forest_auth` FFI — is a memory
program over the concatenated per-node traces. A receipt is therefore a constructive witness in the
strictest sense: it *is* the proof that this state was reached by constructing exactly these facts and no
others.

---

## 6. The circuit is a knowledge-proof; the light client cannot be fooled

A turn's STARK is a proof that the turn was a *valid inference*. **Light-client unfoolability** is the
statement that you cannot be *fooled* about what knowledge was constructed: a light client holds no
secrets, re-runs no cell, and yet — checking only a succinct root — learns that every turn in the whole
history was a genuine kernel transition.

The apex is `ApexFloorFree.lightclient_unfoolable_free` (`Dregg2/Circuit/ApexFloorFree.lean`). Its only
data inputs are what a light client actually has — the public inputs `pi` and the proof `π`; it takes
*no* `pre`/`post` and *no* `StateDecode` as hypotheses (those would hide the hardest rung). From
`verifyBatch vk pi π = accept` plus named floors (`StarkSound` extracting a `Satisfied2` witness, the
per-effect refinement `descriptorRefinesFree`, and the carried existence rung `WitnessDecodesC`) it
*derives*:

```
∃ pre post, StateDecodeC C pi.toPublished pre post ∧ kstep pi.effect pre post
          ∧ pi.pre = C pre.kernel pi.turn ∧ pi.post = C post.kernel pi.turn
```

— *accept ⟹ there exists a genuine kernel transition committing to exactly these published roots.* The
light client ran nothing.

⚑ **Read the last sentence exactly, and no further (2026-07-31).** Two hypotheses that this paragraph
used to list are REFUTED IN THIS TREE, and the apex was restated to stop carrying them:

* `Poseidon2SpongeCR` is FALSE at deployed BabyBear (`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`).
  The older apex `CircuitSoundness.lightclient_unfoolable` carries it, but only to discharge a def-body
  antecedent of `descriptorRefines` that the closed route introduces and DROPS — vestigial, and now shed
  from the whole state-decode chain.
* `S : CommitSurface` carries five commitment floors as FIELDS and has NO INHABITANT at any parameter
  (`Verify.ApexPremiseVacuity.apexCommitFloor_unsatisfiable`, Cantor on `restFrame`). Every apex stated
  over it — including `lightclient_unfoolable_closed_final{,_genuine,_avail}` and
  `kernelConfigSound{,Avail}` — is therefore VACUOUS, whether or not it also carries the sponge floor.
  `lightclient_unfoolable_free` is stated over a bare commit map `C : RecordKernelState → Turn → ℤ`,
  which is inhabited by the deployed `recStateCommit`, and it is REFUTABLE: its per-effect rung is FALSE
  at the unsatisfiable step relation (`descriptorRefinesFree_false_at_False_kstep`), the test that both
  `descriptorRefines` and `descriptorRefinesR` pass for free.

⚠ **"Cannot be shown a forged history" is NOT what this apex says.** It says a real transition EXISTS
behind an accepted proof, with the published roots as its endpoints. It does NOT say the state behind a
published root is UNIQUE — that is `stateDecode_pre_faithful`/`_post_faithful` through
`CommitSurface.commit_binds`, which consumes exactly the refuted five and is unavailable until the
rest-hash is refined to finite support (`Verify.RestFrameFiniteSupportSuccessor`). Existence is
floor-free and true; uniqueness is open.

Over the *whole* history this is `light_client_verifies_whole_history`
(`Dregg2/Circuit/RecursiveAggregation.lean:192`): checking only `verify agg.root = true` yields
`AggregateAttests` — every turn executed correctly, the chain is correctly ordered (no reorder/drop/
insert), and the public final root is the genuine fold of the whole history. Conservation rides the same
root with no prover-supplied state-continuity hypothesis (`conserves_from_verification`,
`RecursiveAggregation.lean:264` — the critical-3 closure). And the anti-ghost tooth at the chain level is
`tampered_aggregate_cannot_bind` (`RecursiveAggregation.lean:404`): no sound aggregate can attest a
reordered chain — *the pale ghost (a forged history that type-checks) cannot be produced*, because the
witness it would need does not exist under non-forgeability. The verification of the succinct aggregate
*is* the trust in the whole history; this is the unfoolability of the assurance case's guarantee E
(`unfoolability_guarantee`, `AssuranceCase.lean:615`).

This is also why the **cipherclerk is a sovereign executor**: a sovereign cell keeps only a commitment
to its state and *proves* its own transitions; a far federation admits it knowing only how to *check a
proof*, never how to *re-run* it. Identity is production: the cell's authority over its own resources is
precisely its ability to exhibit accepted witnesses for its transitions. Inside a trust root authority is
positional ("caps-as-caps": holding the edge *is* the proof); across a boundary it becomes epistemic
("keys-as-keys": you must *present* a verifiable witness, because the far side shares no mediator) — the
crossing is a named-lossy functor Φ under which *permission survives, authority does not* (so a forwarded
capability becomes revocable by construction).

---

## 7. Knowledge over time and across adversaries

Non-amplification is the **monotonicity of constructive knowledge under delegation**: `granted ⊆ held`
is the statement that *you cannot produce a witness for authority you could not already produce*.
Miller's law — "only connectivity begets connectivity" — is exactly: you can only produce witnesses you
(transitively) hold the material to produce. Authority can still *grow* (introduction, sealer/unsealer
amplification, mint/factory, parenthood/endowment are all generative) — but every generative act is
itself authorized by held knowledge and receipt-disclosed. This is an epistemic non-forgeability
invariant, not a lattice descent.

Three theorems extend this past the single turn:

**Knowledge-live-at-settlement.** A revoked credential cannot construct *settled* knowledge. The keystone
is `settlement_soundness` (`metatheory/Metatheory/SettlementSoundness.lean:153`): under any settlement
predicate that binds live authority into the commitment, a *settled* turn necessarily exercised an
authority that was **live at the settlement tip** — an attenuation of something held (`reaches`) *and*
honored by the tip's finalized revocation set (`honors`). The operational face is the contrapositive
`revoke_before_tip_unsettleable` (`SettlementSoundness.lean:192`): if the credential was revoked at
origin `m` at time `τ` and that revocation propagated to the settlement tip by the tip time, *no turn
exercising it can settle* — fail-closed, the stale branch-time view notwithstanding. At the single
machine (`delay ≡ 0`) this collapses to *immediate*: `revoke_unsettleable_immediate`
(`SettlementSoundness.lean:212`). Constructed-but-not-settled knowledge can be revoked out from under;
settled knowledge was provably authorized at the moment it settled.

**The cage proves what an adversary can construct.** A leaked private key is a compromised principal —
an arbitrary opaque controller, exactly what `polis_safety` quantifies over. So the blast radius is
bounded by the *deployed* proofs, not new machinery: `key_leak_contained`
(`metatheory/Metatheory/KeyLeak.lean:202`) is `polis_safety` instantiated with the adversary as the
controller — the principal's authority floor (`held ⊆ bound`) is preserved at every step for every
attacker. The reachable set is *only* the attenuation-closure of the leaked c-list:
`leak_blast_no_amplify` (`KeyLeak.lean:123`) proves every cap the attacker can produce is an attenuation
of something held — *you cannot construct authority you do not hold*, even with the key. Conservation
forbids minting; confinement bounds the reach; and `revoke_kills_leak` (`KeyLeak.lean:300`) ends it
(immediate at n=1, `revoke_kills_leak_immediate:315`). Non-amplification is precisely "the adversary's
constructive knowledge is bounded by what it stole."

**The polis is multi-agent constructive knowledge.** `polis_safety` (`metatheory/Metatheory/Polis.lean:102`)
is the "verify the cage, not the animal" theorem: for a sound policy, safe shield, and safe start, the
enveloped system keeps the *shared floor* at every step for *every* opaque controller — the inhabitant is
the ∀-term the proof never reasons about (`polis_envelope_ctrl_blind:125` proves a naive and a maximally
adversarial controller are bounded identically). This grounds on the real l4v authority type in
`DreggPolis.lean`: `dreggReal_polis_safety` (`DreggPolis.lean:148`) — no dregg subject can be driven to
hold an authority outside its bound or lose its bounded recovery — and `dreggReal_envelope_no_foreclosure`
(`DreggPolis.lean:197`), the politician defeated by construction (bounded exit never foreclosed).
Legitimacy is *non-regression*, not provable justice: `amendment_stream_nonregression`
(`Polis.lean:306`) preserves every subject's frozen minimum floor along any adversarial amendment stream;
a polis forms only where the exported floors have non-empty meet (`disjoint_floors_no_polis`,
`Polis.lean:335`). `PolisNonConfusion.lean` re-pins the deployed kernel theorems — unfoolability,
non-amplification, certificate-is-not-capability (`transclusion_grants_no_unheld_authority`), one-shot
resolution (`commit_resumes_once`) — as CI-enforced constitutional invariants, so a regression breaks the
build. Shared constructive knowledge among arbitrary agents is bounded by the floor, never by trust in
the agents.

---

## 8. Knowledge cannot be hidden; transport keeps receipt-identity

**Reads are attested with a non-omission certificate.** You cannot *hide* knowledge any more than you can
forge it. A `dregg-query` answer ships with a `RangeCertificate` (`dregg-query/src/attested.rs:39`) — the
MMR range-opening of the receipt positions it was computed from — and the verifier re-derives the answer
locally against a trusted root. The guarantee is `server_cannot_omit_position`
(`metatheory/Dregg2/Lightclient/MMR.lean:478`): a verifying answer against any log recomposing the
committed root *is the unique exact range of the genuine log* — every committed in-range position present
at its dense slot (omission impossible), every value genuine (forgery impossible). The non-omission
keystone is `range_complete` (`MMR.lean:422`): density plus the root-pinned count is the whole argument —
a skipped position breaks the count. Omission is not a policy the server may choose; it is a
cryptographic impossibility.

**Transport distinguishes constructed from delivered.** Knowledge in motion keeps a *receipt-identity*:
"queued" is not "handled." The data plane's `Delivery` (`captp/src/data_plane.rs:235`) is a relay's
signed promise minted on `Bus::enqueue` (`data_plane.rs:446`); `is_handled` reads the *drain witness*
(`delivered_hashes`), not the promise — and `Bus::drain` (`data_plane.rs:627`) is where queued becomes
handled, appending each box's content-hash to the authenticated witness. A refused send (over-attenuated
or revoked cap) mints no receipt and queues nothing — *no phantom work*. Run through the node, this is
`channels_service.rs:184`: a POST is a real enqueue (returning the custody receipt), a drain the
receipt-identity witness; "queued-but-not-drained" is a distinct, observable, convictable state. Holding
the receipt of a transmitted fact does not make the fact known to its recipient — only the drain witness
does.

---

## 9. Persistence: knowledge that endures by default

Orthogonal persistence (`docs/deos/HOUYHNHNM-CONVERGENCE.md`) is the principle that *the image is the
accumulated knowledge* — there is no save button, because there is no distinction between the live world
and the durable one. The blocklace is the persistence journal; `World::open` recovers an image by
deterministic replay from recorded witness-cursors. Crucially, recovery is **verifiable, not asserted**:
`CrashRecovery.lean::recover_eq_replay` proves recovery equals replay from genesis, and a resume is valid
only if the reconstructed canonical root matches the recorded Merkle tooth (`starbridge-v2/src/replay.rs`
fail-closes with `RootMismatch`). Session resume reopens the *exact* durable image where it closed
(commit `2aeab369`) — the system cannot lie about whether a resumed world is authentic. Knowledge here
persists the way a proof persists: as a witnessed, cryptographically-bound object that you can re-check,
not as a claim a process holds in memory.

---

## 10. Hypothetical knowledge: promises, partial turns, and the stitch

The metatheory has a tense for *knowledge-to-be-constructed* and a discipline for *branched, hypothetical
worlds*. Both reduce to the same machinery as actual knowledge.

**A promise is a hole that binds its obligation.** A partial turn is an exercise with a hole: the *value*
it will consume is not yet known, but the *shape* — which field, whose write, under which predicate — is
fixed now (`docs/deos/PARTIAL-TURN-LIFT.md`). Determination is eager, witness is lazy. The hole is a
`GuardedHole`/`EventualRef` (`turn/src/eventual.rs`, `starbridge-v2/src/held_promise.rs`), and filling it
is `holeFill_binds_in_circuit` (`Dregg2/Exec/GuardedHole.lean`): a successful fill binds *both* its δ
(post-state is exactly the `stateStep` write, no hidden mutation) *and* its guard (every caveat
discharged) into the committed post-state; a value violating the guard does not fill
(`holeFill_rejects_guard_violation`, fail-closed, the hole stays open). A `ConditionalTurn`
(`turn/src/conditional.rs`) does not execute until a `ProofCondition` is presented, with timeout-abort
fail-closed. The deep identity: **a promise-hole is a nullifier, its resolution is a spend, and one-shot
linearity is the double-spend non-membership the circuit already enforces** — so promise pipelining
inherits light-client unfoolability. A held promise drains only when every hole is filled
(`HeldPromise::is_ready`); hypothetical knowledge cannot be cashed before it is constructed.

**The membrane is shared hypothetical knowledge; the stitch merges it soundly.** A rehydratable
frustum-snapshot is a *cap-bounded fork of the world a message can carry* (the membrane). A shared fork
(`docs/deos/SHARED-FORK-CONSENT.md`) hands a confined sub-world to another principal, graduated by rights
— `embedded` (exercise locally), `studyref` (read-only, exercise = an upgrade request), `networkboundary`
(exercise opens an owner-consent request, a `ConditionalTurn` whose hole is the owner's signed grant).
The guest's turns are *structurally imaginary* with respect to the real world (they hold no cap to it);
the only door is a gated settlement turn. Merging diverged forks is the **branch-and-stitch pushout**
(`docs/deos/BRANCH-AND-STITCH-PROTOCOL.md`): the I-confluent/monotone part merges clean (the union *is*
the colimit); conflicting parts yield a *first-class conflict object*, never a silent overwrite; and any
conservation/authority/nullifier clash forces an explicit linear-logic **drop**. Authority re-evaluates
*at settlement*, so a cap revoked since fork time cannot ride a stitch into the real world — this is
exactly `settlement_soundness` (§7). Branching is free constructive *speculation*; settlement is where
speculation must pay the production law.

**The document language is the same object in editor clothes.** A dregg document is a patch-theoretic
graph riding the cell substrate (`docs/deos/DOCUMENT-LANGUAGE.md`): a document is a cell, an edit is a
patch (a turn), the content is the fold of the patch-history. Patches are additive (add/delete-as-
tombstone/connect), so they commute on disjoint parts and merge by graph union — the colimit. A conflict
is not a failed merge; it is an *antichain in the merged graph*, a first-class state a later resolution
patch collapses. Merge correctness is the pushout, proved in `metatheory/Dregg2/Deos/DocMerge.lean`.
Writing is constructing knowledge; merging two authors' knowledge is the universal-property composition;
disagreement is a shape you carry, not a thing you discard.

---

## 11. deos: a constructive-knowledge workspace

deos adds **zero new trust** — every visual or interactive primitive reduces to a kernel theorem
(README-LLMs §8) — and read as constructive knowledge, the desktop is a workspace where *every action
constructs a verifiable fact*.

- **An affordance** — the "button" — is a cap-gated verified-turn template; who may press it is decided
  by held capabilities (`required ⊆ held`, the proven `is_attenuation` lattice). Pressing a button *is*
  producing a witness the kernel accepts; the UI is a surface over the production law.
- **Login is the root capability**; a session *is* the resulting c-list; logout is a transitive revoke
  (synchronous at n=1). An agent (Hermes) logging in is the *identical* ceremony with a narrower
  template — `polis_safety`'s controller-blindness makes the human and the agent the same case. Who is
  at the keyboard is the ∀-term the proofs never reason about.
- **A transclusion** is Xanadu shipped: a quote *is* a first-class provenanced, per-viewer, unforgeable
  citation of a source cell's committed field — and it confers *no* authority over the source
  (`transclusion_grants_no_unheld_authority`). Citing a fact is constructing an observed read, not
  acquiring a handle: certificate is not capability.
- **A deos app** is a cap-mandated, verified, durable workflow — runs to completion exactly once across
  crashes, each step admitted by a held capability, each step a verified turn, each step a fireable
  affordance: four surfaces of one kernel. An app's durable core is a *cell*, its mutations are *turns*,
  its documents speak the document language — so apps are *views over one cell graph*, every state they
  hold a piece of constructed, witnessed knowledge.
- **The MUD** (`docs/deos/DREGG-MUD.md`) is a shared constructive-knowledge *world*: a room *is* a cell,
  an inhabitant *is* a cap-rooted session whose reach is exactly their c-list, an item *is* a capability,
  an exit *is* a cap edge, an action *is* a verified turn leaving a signed receipt. You cannot cheat
  because conservation (Σδ=0) forbids duping, the attenuation lattice forbids unpermitted entry, and
  settlement soundness proves a settled action exercised only authority live at the tip. The clean part
  of a fork merges; the cheating part is *lossy-dropped as a visible conflict object*. A shared
  imaginary world made honest is the whole metatheory at play scale.
- **The membrane** (§10) is the desktop's primitive for *shared hypothetical knowledge*: a message can
  carry a cap-bounded fork of your computer into which you invite another principal, drive locally, and
  stitch back under the production law. Matrix is the multiplayer transport.

The two tests the desktop must pass are the same two the metatheory states: a five-year-old can click an
affordance with delight (the surface), and an adept can inspect/modify the live image (the malleability)
— *and in both cases the system can only show, and only do, what it can prove.*

---

## 12. The honest open frontier: the macaroon ↔ cap convergence

The production law is fully proven and in-circuit for **one** of the four credential aspects — the
kernel capability (`granted ⊆ held` via `recKDelegateAtten` / `capAuthorityG` / `checkSubset`,
witnessed against the authenticated `capability_root`). The credential is meant to be *one authority
seen four ways* — **biscuit** (Datalog policy: what is permitted) · **macaroon** (caveat-chain
transport: how it narrows hop by hop) · **cap** (kernel c-list: what the kernel enforces) · **zk**
(proof of honest narrowing) — all refining the single relation `granted ⊆ held`
(see `.docs-history-noclaude/AUTHORIZATION-MODEL.md`).

Today these are joined by **conjunction, not by a proven arrow**. `gateOK` reads *independent*
`NodeAuth` fields: `capAuthorityG` (`FullForestAuth.lean:443`) and `chainGateG` (`:452`, the macaroon
HMAC face) are AND-ed over disjoint state, and **there is no theorem `chainGateG na → capAuthorityG na`**
anywhere in `Dregg2/` — the kernel files do not even import the caveat-chain model. So at the delegation
verb, where the macaroon caveat chain and the kernel cap both narrow authority, non-amplification is
told *twice*, in two separately-modeled lattices welded by `&&`. It is a genuine fail-closed conjunction
(a macaroon can never widen *past* the kernel cap, so this is defense-in-depth, not a hole) — but it is
not *one* proven production-arrow.

**The live research edge is the `chainGateG → capAuthorityG` arrow:** prove that the macaroon caveat
chain's narrowing *is* (or refines) the kernel's `granted ⊆ held` narrowing on the verb where they
overlap, so the four aspects bind into a single proven production rather than four agreeing stories.
The smallest first step is a single Lean lemma over a shared `NodeAuth.narrowed : ExecAuth` field plus
the SDK projection of the caveat chain onto that lattice (`.docs-history-noclaude/AUTHORIZATION-MODEL.md` §4). Until that
arrow exists, the production law is *proven for the cap aspect and conjoined with the others*, not yet
*proven as one production* across all four. This is the place the four facets do not yet bind into one
proven production-arrow, and it is named, not papered over.

The companion open construction is **Settlement Soundness as a deployed composition** (§7): the keystone
is proved (`SettlementSoundness.lean:153`), but `BindsLiveAuthority` is a *typed hypothesis* — the
settlement predicate the deployed commitment uses must be shown to bind the finalized revocation set, not
carry branch-time authority forward. It is the same theorem the distributed-time-travel and
membrane-merge frontiers converge on; it is named, with its discharge lane open, in `docs/ASSURANCE.md`.

---

## 13. Metatheory vs. verification (why the rename)

- **The metatheory** (this document, and the small Lean core that genuinely encodes it) is the *logic*:
  what a capability/proof/turn *is*; the demand⊣supply adjunction; **authority as
  production-under-non-forgeability** and its four facets; the four substances as four kinds of
  knowledge; the receipt as a constructive witness; the circuit as a knowledge-proof; the generative/
  restrictive dynamics and the non-forgeability invariant; coinductive soundness. It is, deliberately,
  *candidate-independent* — it would be the metatheory of any system built this way.
- **The verification of dregg2** is the (much larger) body of Lean that proves *the dregg2 system*
  realizes that logic — the executable cells, the constraint catalog, the kernels, the protocols, the
  circuit bridges, the FFI cascade, the polis weld, the deos modeling.

They interact (verification *discharges* the metatheory's obligations against a real system) but are
**not the same thing**, and conflating them under one name "Metatheory" hid the actual metatheory. The
relationship is exactly the thesis turned on itself: the metatheory is the *predicate*, the verification
is the *witness*, and dregg2 is real precisely because it can produce the witness the predicate demands.

> The egg metaphor still holds: we are learning what is inside without cracking it. What is inside is a
> living, distributed, capability-secure organism that *knows things by being able to prove them* — whose
> four substances are four modes of knowledge, whose receipts are constructive witnesses, whose circuit
> makes a stranger unfoolable, whose persistence makes knowledge endure by default, whose membrane lets
> knowledge be shared as hypothesis and merged as proof — and whose authority is, all the way down, the
> disciplined production of authorized, non-forgeable witnesses over unbounded time. 🐉🥚
