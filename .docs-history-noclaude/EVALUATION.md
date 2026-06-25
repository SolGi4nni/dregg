# Evaluating dregg

This is the page for someone deciding whether dregg is worth their time: what it
*is*, what it actually guarantees (and where the honest edges are), and a
first-ten-minutes path that needs no one in the loop. If you want hands-on
commands instead, [QUICKSTART.md](../QUICKSTART.md) is the 15-minute tour; this
page is the "should I trust it, and why" companion.

## What dregg is

dregg (Dragon's Egg) is a **formally verified object-capability operating
substrate**. The whole kernel is one sentence:

> A turn is the exercise of an attenuable, proof-carrying token over owned
> state, leaving a verifiable receipt.

Concretely:

- **Cells** are isolated objects — per-asset balances, programmable state slots,
  a capability tree, and a **program**: a predicate over the cell's own
  transitions that the kernel enforces on *every* turn touching the cell.
- **Turns** are atomic, capability-gated state transitions across one or more
  cells. Authority is structural: a turn that cannot exhibit a valid,
  sufficiently-empowered, fresh token chain simply does not execute.
- **The kernel is eight verbs** — seven constructors with `shieldUnshield`
  carrying two directions (`create · write · move · grant · revoke ·
  shield/unshield · lifecycle`), specified in Lean 4 with machine-checked
  minimality and completeness theorems. Everything else a turn carries is
  *turn structure* (exercising a capability is a use, not a verb; refusal is an
  outcome; the nonce is prologue) or a *factory pattern* built from these verbs.
- **The verified executor *is* the executor.** The node's state producer is the
  Lean function `execFullForestG` — credential- and caveat-gated, proven sound —
  compiled and linked into the node over a C ABI (`dregg-lean-ffi/`). It is not a
  *model* of what the node does; it is the function the node calls.
- **Circuits are emitted from Lean.** Constraint systems are generated from
  proved Lean modules as byte-pinned descriptor artifacts; the Rust prover
  *interprets* them. Rust authors no constraints.
- **Receipts and proofs.** Every turn leaves a receipt; STARK proofs (Plonky3,
  BabyBear, Poseidon2, FRI — post-quantum assumptions only) attest turns
  *additively* — verifying a turn never requires re-executing history — and
  recursive aggregation folds a whole history into one root.

The thing that makes this more than a verified library: the proofs are *about
the running system*, because the running system calls the proved function.

## The guarantees, in human terms

dregg states its case as six guarantees to a light client (A–E below, plus **R**,
the running entry). They are assembled, by guarantee, in
[`metatheory/Dregg2/AssuranceCase.lean`](../metatheory/Dregg2/AssuranceCase.lean)
— each one a theorem-DAG over the keystones that discharge it. The precise
contract — exact terms, the full crypto floor by carrier name, and the
deployment correspondence at file:line — is [ASSURANCE.md](ASSURANCE.md). Here is
what each means if you are not reading Lean:

1. **Authority** — every state change is justified by an unforgeable,
   non-amplified, fresh token chain. *No effect ever confers more authority than
   the caller held.* You cannot grant a capability you don't have, and a
   delegated capability is always an attenuation (weaker or equal), never an
   amplification.

2. **Conservation** — per asset, the resource sum across a turn (and across a
   whole run) is *exactly zero*. Nothing is minted or burned outside the supply
   discipline. An asset *is* its issuer cell, so "who can mint" is a structural
   fact, not a policy knob.

3. **Integrity** — a receipt binds the *whole* post-state. The state commitment
   is determined by, and recovers, *every* state field — so a turn that tampers
   with a field the effect didn't legitimately touch is rejected. (This is the
   "anti-ghost" property: you cannot smuggle a change into an unrelated cell or
   capability and have the receipt still verify.)

4. **Freshness** — no replay, no double-spend. A committed spend's nullifier was
   fresh at commit time, and a repeat is rejected; revocation takes effect at
   finality (it is consensus-bound, not instantaneous-by-fiat).

5. **Unfoolability** — a light client that verifies a Q-chain learns guarantees
   1–4 for the *whole history* while re-witnessing nothing. A tampered aggregate
   cannot bind. This is the property the whole design exists to protect: a thin
   verifier cannot be fooled into accepting an incorrect protocol evolution.

**R. The running entry** — Authority, Conservation, and Integrity hold over
*what the node actually runs*, not over a model of it. The state producer is the
proved Lean function the node calls over a C ABI, so the guarantees above are
about execution itself, not a paper abstraction of it. This is why the case
names its deployment-side boundary (producer coverage) explicitly rather than
quietly assuming it away.

### What the guarantees rest on (the trust boundary)

The guarantees are unconditional in the Lean-kernel sense *modulo* a small,
explicit set of cryptographic assumptions. These enter as typed hypotheses, never
as `axiom`, and they are the *entire* trust boundary:

- collision-resistance of Poseidon2 (in-circuit hash) and BLAKE3 (out-of-circuit);
- ed25519 signature unforgeability (turns, strand blocks);
- HMAC/PRF unforgeability (macaroon caveat chains);
- AEAD confidentiality+integrity (sealed payloads);
- discrete-log hardness (Pedersen commitments);
- FRI / STARK soundness (a verifying proof attests its statement);
- post-GST synchrony (the consensus liveness carrier).

There is no trusted executor, no out-of-band "this turn was authorized" premise,
and no post-state field left uncommitted. A boundary the case does not name would
be a boundary the case launders — so the deployment-side seams (which prover
covers which turn shape, host-fed admission inputs, producer coverage) are named
explicitly in `AssuranceCase.lean` itself.

## Honest caveats (read these before you over-trust)

dregg is a real, running system, but it is a research-grade devnet, not a
hardened production network. The caveats that matter for evaluation:

- **Single-node devnet.** The public devnet runs in **solo federation mode** —
  one node, no peers. Consensus is *live* in the single-machine sense, but the
  Byzantine-fault-tolerant multi-node path, while modeled and proved, is not what
  the public devnet exercises. (Many of dregg's strong properties — immediate
  consistent checkpoints, sync commit — are *single-machine* properties; under
  real distribution they become the bounds the topology allows.)

- **Per-turn proving is staged, not cut over.** On the shared devnet the witness
  for each turn lands immediately, but the per-turn STARK attachment currently
  stays `proof_pending` — the async prove pool is not attaching proofs yet. The
  proving machinery is real (you can produce and self-verify an EffectVM STARK in
  the browser playground); the devnet's automatic per-turn attachment is the gap.

- **Producer coverage is a boundary, not "all effects."** The verified Lean
  producer covers a named subset of effects (the devnet reports
  `producer_covered_effects`; today ~19, the doctor surface reports the
  credential modes separately). Turns outside that boundary — e.g. thin-HTTP
  turns marshaled without `valid_until` — fall back to the unverified Rust
  executor, which the node logs explicitly. Execution is unaffected; those turns
  just don't ride the verified producer yet.

- **Circuit graduation is in progress.** Most effect selectors prove on the
  Lean-descriptor path; graduating the remainder and deleting the legacy fallback
  circuit entirely is active work.

- **The seeded apps depend on genesis.** The shared devnet's data dir predates
  starbridge genesis seeding, so the seeded app cells don't exist there; the
  app-specific CLI verbs need a freshly-initialized node.

None of these are hidden — they are the same items tracked in the project's
HORIZONLOG and surfaced in QUICKSTART's "rough edges". The point of listing them
here is so an evaluator can calibrate: the *proofs* are strong and load-bearing;
the *deployment* is a staged devnet with named gaps.

## The first ten minutes

No build, no account, no one in the loop — just `curl`:

1. **See a live node.** `curl -s https://devnet.dregg.fg-goose.online/status` —
   the JSON tells you it's healthy, solo-federation, with a verified Lean state
   producer and per-turn proving on.

2. **Watch a verified turn — faucet a cell.** A cell id is a commitment to a
   public key (`id == derive_raw(pubkey, token)`), so a bare random id is an
   **unspendable** address: the faucet credits it (a real verified turn) but no
   one holds its key to sign a spend. To fund a cell you OWN, pass a `public_key`
   you hold (what `dregg demo` does). This bare-address form just shows the turn:

   ```sh
   CELL=$(python3 -c "import secrets;print(secrets.token_hex(32))")
   curl -s -X POST https://devnet.dregg.fg-goose.online/api/faucet \
     -H 'content-type: application/json' \
     -d "{\"recipient\":\"$CELL\",\"amount\":1000}"
   ```

3. **Read it back** and watch it in the explorer:

   ```sh
   curl -s https://devnet.dregg.fg-goose.online/api/cell/$CELL
   # then open https://devnet.dregg.fg-goose.online/explorer/cell/$CELL
   ```

4. **Read the assurance case.** Open
   [`metatheory/Dregg2/AssuranceCase.lean`](../metatheory/Dregg2/AssuranceCase.lean)
   — the header states the five guarantees and the assumption floor in prose,
   then assembles the keystone DAG for each. This is the document that answers
   "why should I trust a Q-chain?".

When you're ready to build and drive real turns, the SDK, and the governance
ceremonies, go to [QUICKSTART.md](../QUICKSTART.md).

## A runnable two-agent story

The "two agents transacting" story — a line of credit, an encrypted group
channel, and an asynchronous mailbox handoff — is three SDK nouns that all ride
the *same* `.turn()` path through the verified executor (no new executor entry
for any of them). Each is an executable test you can run and read:

- **Trustline** — "issuer A extends holder B a line of N" as an attenuated,
  quantitative capability (granted ⊆ held made numeric). The cell's installed
  program enforces `drawn ≤ ceiling` for life. Run/read
  [`sdk/src/trustline.rs`](../sdk/src/trustline.rs) — the tests
  `open_escrows_the_line_and_grants_the_holder_capability`,
  `draw_within_line_succeeds_and_over_line_refuses`, and
  `settle_moves_net_position_and_conserves` are the story tooth-by-tooth, and
  `executor_program_rejects_over_line_draw_directly` shows the executor itself
  refusing an over-line draw.

- **Channel** — A and B form a group whose membership root, key epoch, and epoch
  key all live on-cell; the keystone is that a `remove(member)` darkens *both*
  the ciphertext plane and the capability plane in **one** atomic turn. Run/read
  [`sdk/src/channels.rs`](../sdk/src/channels.rs) —
  `remove_is_one_turn_and_darkens_both_planes` and
  `executor_rejects_partial_membership_turns` are the heart of it.

- **Mailbox** — A sends B a *sealed* turn-intent while B is offline; B's crank
  later drains B's hosted relay inbox over the real HTTP route, the
  executor-anchored sender gate admits A, and the intent executes as a turn on
  B's cell — with a checkable custody receipt. The negative path (an ungranted
  sender is refused, no state change) is in the same file. This is a genuine
  two-node async handoff:
  [`node/src/mailbox_crank_e2e.rs`](../node/src/mailbox_crank_e2e.rs).

Read top-to-bottom these three say: A and B can extend each other credit, talk
privately as a group, and hand off intents asynchronously — and every rule is
enforced by the cell program the factory installs, with the executor rejecting
the bad turns. The narrative design notes are in
[`docs/ORGANS.md`](ORGANS.md) (§1 trustlines, §2 mailbox, §4 channels) and
[`docs/TRUSTLINES.md`](TRUSTLINES.md).
