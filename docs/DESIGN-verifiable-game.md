# Verifiable Game Design

## Status and design stance

`attested-dm` already has the correct authority boundary: the AI proposes narration, while `resolve_action(map, world, typed_action)` deterministically resolves a closed `GameAction` (`Move`, `Take`, `Use`, `Examine`, or `Attack`). Every landed move becomes a previous-hash-linked `LedgerEntry` binding the sequence number, prior entry, narration, effect, prompt and game bindings, and attestation. `DmCaps` gates grants, `.dungeon` provides a readable world format, and `GameSession::verify()` authenticates the recorded chain.

The next design objective is stronger than tamper evidence: a verifier should be able to establish that every recorded transition was permitted by the bound rules, and that every random outcome came from an unbiased source neither participant could grind.

Two trust statements must remain explicit:

- The current attestation's authenticity leg is an in-tree fixture. Chain verification proves that recorded history is untampered; it is not yet production identity or hardware-backed authenticity.
- Dregg has real circuit, proving, folding, and WASM light-client machinery, but ultimate STARK soundness remains an assumption. The right claim is **verifiable under the deployed prover assumptions**, not “trustless from first principles.”

The product should expose these distinctions as verification levels rather than collapsing them into one green check.

## Receipt model

The ledger should evolve from a narration-oriented log into a canonical transition receipt. Each transition should commit to at least:

```text
TransitionReceipt {
    protocol_version,
    game_binding,
    seq,
    prev_receipt_hash,

    pre_state_root,
    action_bytes,
    actor_binding,
    capability_witness,

    randomness_request,
    randomness_evidence,

    effect_bytes,
    post_state_root,
    narration_hash,

    resolver_version,
    ruleset_root,
    proof_or_attestation,
}
```

Canonical serialization is consensus-critical. `action_bytes`, effects, state roots, randomness domains, and version identifiers must have one encoding with explicit domain separators. Narration remains bound to the move but outside the deterministic state transition: changing prose invalidates the receipt chain, while prose is never allowed to grant an item, alter hit points, choose randomness, or otherwise mutate the world.

Verification should report independent claims:

1. **Chain-valid:** hashes, sequence numbers, bindings, and attestations are internally valid.
2. **Replay-valid:** a local resolver re-executed every bound action and reproduced every effect and post-state root.
3. **Randomness-valid:** each random value has valid, correctly scoped evidence and was consumed exactly as specified.
4. **Proof-valid:** a deployed proof verifies the claimed transition invariants under the selected prover assumptions.
5. **Identity-valid:** the signer or execution environment is authenticated by a production trust root, when one exists.

This avoids presenting a fixture attestation or a hash-chain-only check as full rule correctness.

## Verifiable randomness

### Requirements

Randomness must be:

- unpredictable before all gameplay choices affecting it are irrevocably bound;
- non-selectable after the outcome is known;
- domain-separated by game, turn, event, and draw index;
- reproducible by verifiers from compact evidence;
- resistant to grinding by both server and player;
- equipped with an explicit timeout and abort policy.

Commit-reveal alone is insufficient as the final design. It prevents unilateral choice only when both sides reveal, and the last revealer can still abort selectively after learning an unfavorable result. Penalties can discourage that behavior but do not remove it.

### Recommended construction: VRF plus delayed public beacon

Use a hybrid source:

```text
event_id = H("attested-dm/random-event/v1",
             game_binding, seq, pre_state_root,
             action_hash, event_kind, draw_count)

server_output, vrf_proof = VRF_server(event_id)

random_seed = H("attested-dm/random-seed/v1",
                event_id, server_output,
                beacon_round, beacon_output)
```

The action, pre-state, event kind, and number of draws are committed before the chosen beacon round becomes available. The server VRF makes the server's contribution unique and publicly verifiable; the future public beacon makes the result unavailable when the player commits the action and prevents a malicious player from searching actions against a known seed. Mixing both sources also avoids placing liveness and unpredictability entirely in one operator.

This design is non-grindable only if the protocol closes several escape hatches:

- **Server key selection:** bind the VRF public key into the genesis `game_binding`, not per turn.
- **Beacon-round selection:** derive the round from a fixed schedule or the receipt sequence; do not let the server choose among published rounds.
- **Action grinding:** bind the player's canonical action before the beacon deadline. Re-submission with cosmetic differences must not create a new eligible event identifier.
- **Server grinding:** a VRF has one valid output per key and input. The server cannot try alternate nonces or keys.
- **Selective abort:** specify the result of non-publication. After a deadline, anyone may finalize using the public beacon plus a deterministic `server-missed` marker, and the receipt records the fault. A server must not gain a reroll by withholding its VRF proof.
- **Variable draw grinding:** bind `event_kind` and `draw_count` before the seed exists. Random consumers use an indexed XOF stream, so skipping or requesting extra draws is detectable.

The player need not contribute a secret for ordinary online play; the already-bound player action is their non-malleable contribution to the event identity. For adversarial wagered games, an optional player VRF may be mixed in, but it needs the same timeout rule so withholding cannot buy a reroll.

### Alternatives

#### Server VRF only

A server VRF is simple, low-latency, and has compact proofs. It proves that the published value is the unique output for a committed server key and event. It does **not** by itself prove the server did not predict favorable future outcomes and steer scheduling, content, or encounter creation around them. It is appropriate for low-stakes play or as one leg of the hybrid, not as the strongest fairness story.

#### Public randomness beacon only

A future beacon output is publicly auditable and removes server secret-key trust. It introduces latency, availability dependence, and careful round scheduling. A player who can submit after the output is known can grind actions; a server that can choose the round can grind scheduling. Therefore the action and round must both be bound beforehand.

#### Randomness checked in-circuit

The circuit should eventually verify the randomness transcript and its consumption: event-domain construction, beacon-round binding, seed derivation, draw indexing, and mapping to bounded outcomes. Verifying a heavyweight VRF or beacon signature inside a STARK circuit may be expensive. The pragmatic split is to verify cryptographic evidence outside the circuit initially, expose authenticated outputs as public inputs, and prove in-circuit that the resolver consumed those outputs correctly. Later, add a circuit-friendly VRF or recursive proof of the external verifier if its cost justifies the reduced trust surface.

“In-circuit randomness” is not itself a source of entropy. A circuit can prove correct derivation and use; unpredictability still comes from a VRF, beacon, threshold protocol, or comparable external source.

### Receipt-chain binding

Each random event records its request before its result:

```text
RandomnessRequest {
    event_id,
    scheme_id,
    vrf_public_key,
    beacon_id,
    beacon_round,
    event_kind,
    draw_count,
}

RandomnessEvidence {
    server_vrf_output,
    server_vrf_proof,
    beacon_output,
    beacon_proof,
    final_seed_commitment,
}
```

For beacon latency, use two linked receipt stages: an action-accepted receipt binds the request, then a finalized transition receipt binds the evidence and effect. No later action may depend on an unfinalized state. This makes scheduling and withholding visible in the same history that commits the game result.

## Verifiable rule execution

The present verifier authenticates what was recorded but does not establish that the resolver should have produced it. Close that gap in two complementary layers.

### Layer A: re-execution light client

The first correctness verifier should be deliberately boring: ship the deterministic resolver as a small native/WASM library and replay the game from the bound genesis state.

For each receipt, the verifier:

1. checks chain linkage, canonical encoding, versions, and game binding;
2. verifies the action actor and `DmCaps` witness;
3. verifies randomness evidence and reconstructs the indexed draw stream;
4. checks that its current state root equals `pre_state_root`;
5. calls the exact versioned `resolve_action` over the reconstructed state and canonical typed action;
6. compares the returned effect bytes and post-state root byte-for-byte with the receipt;
7. advances only on equality.

The replay package must bind the resolver binary or code artifact, ruleset root, `.dungeon` content root, schema version, and deterministic execution profile. Avoid ambient time, locale, host floating point, unordered map iteration, filesystem reads, or network access. Integer arithmetic must define overflow behavior. Any rule upgrade starts a new resolver epoch committed in the chain; it cannot silently reinterpret old receipts.

Replay is the highest-leverage correctness layer because it catches the whole class of “valid chain, invalid transition” failures without waiting for circuit coverage. Its limitation is verifier cost: a long session requires the verifier to possess the relevant world data and repeat all transitions. Checkpoints can reduce startup cost, but a checkpoint is trustworthy only when replayed from genesis or backed by a proof.

The UI should never label chain-only verification as replay verification. A useful result looks like:

```text
Chain: valid (842/842 receipts)
Rules: replayed (842/842 transitions, resolver v3)
Randomness: valid (37 events; 0 missed contributions)
Proof: not present
Identity: development fixture
```

### Layer B: resolver invariants through dregg folding

The proof lane should encode transition validity as a foldable state machine. Each step consumes a committed pre-state, canonical action, capability witness, and authenticated random inputs; it emits an effect and post-state. Dregg's fold machinery accumulates many step proofs into a compact session proof whose public inputs bind:

```text
(game_binding, resolver_version, ruleset_root,
 initial_state_root, final_state_root,
 first_seq, last_seq, receipt_chain_tip)
```

Do not begin by circuitizing the entire resolver or AI narration. Start with one small invariant whose inputs and state delta are easy to arithmetize, whose failure is economically meaningful, and whose proof composes across every action.

**Smallest invariant worth proving first: no item can be created or destroyed except by an explicitly authorized inventory-transfer effect.**

Concretely, commit to a multiset accumulator of item identities and quantities across room containers, characters, and authorized sinks/sources. For every step, prove either:

- the accumulator is unchanged and ownership changes exactly match a typed transfer effect; or
- a mint/burn delta is present, authorized by the required `DmCaps` grant and rule identifier, and included in the receipt.

This is a better first proof than “the state hash changed correctly,” which is tautological without transition semantics, and smaller than full combat correctness. It immediately rules out a powerful cheating class—fabricated loot, duplicated keys, and vanished quest items—while exercising state commitments, capability gates, effect decoding, and recursive folding.

After inventory conservation, extend proof coverage in this order:

1. movement preserves identity and only traverses an enabled edge;
2. bounded resources never underflow or exceed rule-defined maxima;
3. combat effects match initiative, target eligibility, random draws, and damage rules;
4. experience and level transitions follow the committed progression table;
5. the complete effect and post-state are the unique result of the bound action.

Until the last stage, proofs establish named invariants—not “the whole game was correctly executed.” Proof metadata must enumerate the circuit and invariant set verified. All claims remain conditional on the deployed prover and STARK-soundness assumptions.

### Replay and proofs are complementary

Replay gives broad semantic coverage quickly but costs linear work and requires executable rule code. Circuit proofs give succinct verification and support cross-session state, but are expensive to design and only cover the constraints actually encoded. The product should use replay as the reference oracle, then differential-test each circuit against it. A proof is accepted only for the exact resolver and ruleset commitments named in its public inputs.

## Ambitious capabilities

### Overworld

**What it is.** A large, possibly streamed graph of regions, points of interest, travel edges, clocks, weather, factions, and encounter tables. Local dungeons become subgraphs under a common world root.

**World-resolved and verifiable.** The AI may propose destinations, describe travel, or surface choices. The world engine alone advances time, checks reachability, consumes travel resources, selects encounters, and updates faction/world state. Use a Merkleized sparse world state: a transition carries proofs only for the regions and global indices it reads or writes. Procedural regions are derived from a committed generator version, world seed, coordinates, and verified randomness; authored regions bind their `.dungeon` or successor DSL content hashes.

Receipts must include read and write sets, so a verifier can establish that an unloaded region was not mutated invisibly. Global events use deterministic scheduling keyed by world tick and event identity, not wall-clock timing.

**Difficulty: high.** State commitment and partial-state witnesses are tractable. The hard parts are deterministic content generation, global-event ordering, migrations, and preventing hidden reads from becoming an authority channel.

### Turn-based combat engine

**What it is.** A closed state machine for encounter creation, initiative, legal actions, targeting, resources, status effects, damage, defeat, retreat, and rewards.

**World-resolved and verifiable.** Combat receives typed commands such as `Attack`, `Defend`, `UseAbility`, `UseItem`, and `Flee`. The engine computes legal targets, costs, cooldowns, hit and damage rolls, status transitions, and terminal outcomes. AI output is flavor text attached after the effect. Rules are data-driven but committed by a `combat_ruleset_root`; effect ordering and tie-breaking are explicit.

Random draws are declared before finalization by event kind and maximum count, then consumed from the verified indexed stream. Avoid rejection sampling with data-dependent draw counts unless the transcript commits every draw; fixed-width unbiased mappings or predeclared bounded retries are easier to audit.

Combat is an excellent circuit target after inventory conservation: its state is compact, turns are naturally foldable, and invariants—no action outside initiative, no negative resources, damage derived from committed stats and draws—are crisp.

**Difficulty: medium-high.** A deterministic replayable engine is moderate. A balanced extensible rules language and efficient proof constraints are substantially harder.

### Character progression

**What it is.** Persistent experience, levels, attributes, abilities, equipment constraints, quests, and respec rules.

**World-resolved and verifiable.** Narration may celebrate a level-up but cannot grant one. Rewards arise only from committed encounter, quest, or administrator-grant effects. Progression tables and ability prerequisites are versioned data under the ruleset root. A level-up transition proves that prior experience crosses a threshold, chosen upgrades are legal, derived stats recompute deterministically, and no points are duplicated.

Keep immutable character identity separate from mutable character state. Every progression receipt binds the identity, prior state root, source reward receipt, chosen typed upgrade, and new state root. Capabilities distinguish ordinary earned advancement from explicit administrative grants.

**Difficulty: medium.** Replay is straightforward if the rules remain closed. Compatibility across ruleset versions, respecs, and user-authored content is the main complexity; circuitizing table lookups and derived-stat recomputation adds cost but is manageable.

### Cross-session persistence with proofs

**What it is.** A character or world state can leave one session and enter another without trusting the destination server to accept an invented history or the source server to rewrite it later.

**World-resolved and verifiable.** End a session with a checkpoint certificate binding character identity, state root, inventory accumulator, progression state, world or campaign namespace, ruleset version, receipt-chain tip, and a folded proof or replay-verifiable history. A new session's genesis receipt consumes that certificate exactly once and records an import transition.

Preventing duplication requires more than a proof of valid state. A portable sword copied into three offline sessions is valid history three times unless there is a uniqueness mechanism. Choose explicitly between:

- **copyable branches:** forks are allowed and visibly derive distinct lineage identifiers;
- **single-owner assets:** transfers consume a globally ordered nullifier in a shared registry or consensus-backed log;
- **campaign-local uniqueness:** a campaign coordinator rejects reused import nullifiers, introducing a scoped availability/trust dependency.

For a first product, copyable branches with conspicuous provenance are honest and usable. Reserve global single-owner semantics for scarce or traded assets that justify a registry. Cross-ruleset imports require a typed, receipt-bound migration whose code and proof are independently versioned; never reinterpret an old state under new rules.

**Difficulty: very high.** Succinct state validity is achievable with folding. Double-spend resistance, finality, privacy, recovery, schema migration, and governance across independent operators are the genuinely hard parts.

## Phased roadmap

### Phase 0 — canonical transition receipts

- Add canonical typed-action bytes, pre/post state roots, resolver version, and ruleset root to each ledger transition.
- Split verification results into chain, replay, randomness, proof, and identity claims.
- Specify deterministic serialization and domain separation as protocol fixtures.

Exit criterion: a receipt uniquely identifies the state, action, rules, claimed effect, and resulting state.

### Phase 1 — replay correctness

- Implement `verify_replay` in the native library and WASM light client.
- Reconstruct genesis state, re-run `resolve_action`, and compare every effect and state root.
- Add adversarial fixtures in which hashes and attestations are valid but an effect violates the resolver; chain verification must pass and replay verification must fail.
- Publish resolver artifacts by version and bind their digest into `game_binding`.

Exit criterion: an independent client detects every tested rule-invalid but internally well-formed history.

### Phase 2 — hybrid verifiable randomness

- Define random-event domains, fixed draw accounting, and two-stage receipts.
- Bind a server VRF key at genesis and a future beacon round at action acceptance.
- Implement timeout finalization so withholding cannot reroll outcomes.
- Verify evidence in native and WASM clients; expose randomness status separately.

Exit criterion: neither party can choose among multiple valid outputs, and abort behavior yields no favorable reroll.

### Phase 3 — first folded invariant

- Commit inventory as a multiset accumulator within the state root.
- Prove conservation or capability-authorized mint/burn for one transition.
- Fold proofs across a session and bind the final proof to the ledger tip.
- Differential-test circuit witnesses against replay results.

Exit criterion: a light client verifies a compact session proof for the named inventory invariant under the deployed prover assumptions.

### Phase 4 — combat and progression

- Introduce the closed combat state machine and committed combat ruleset.
- Add progression rewards and typed level-up transitions.
- Expand folded constraints through movement, resources, combat, and advancement.

Exit criterion: complete combat encounters and character upgrades are replay-verifiable, with explicit proof coverage for the implemented invariant set.

### Phase 5 — overworld and succinct checkpoints

- Merkleize region state and require transition read/write witnesses.
- Add deterministic travel, time, encounters, and committed content generation.
- Produce folded checkpoint proofs suitable for fast session startup.

Exit criterion: a client can verify a long-running world from a trusted genesis using compact checkpoints plus the recent receipt suffix.

### Phase 6 — cross-session portability

- Define export certificates, lineage identifiers, import transitions, and migrations.
- Ship copyable, visibly forked character branches first.
- Add a nullifier registry only for assets requiring single-owner semantics.

Exit criterion: a destination session can verify provenance and rules validity without trusting the source operator, subject to explicit prover, identity, and finality assumptions.

## The one-day, highest-leverage first step

**Add a replay-verification fixture that proves the current gap, then make it pass with one-action re-execution.**

Concretely, extend a transition receipt with canonical `action_bytes`, `pre_state_root`, `post_state_root`, and `resolver_version`. Construct a one-move session whose chain and fixture attestation are valid but whose recorded effect or post-state is deliberately wrong. Preserve the existing expectation that `GameSession::verify()` reports the chain as valid, and add `verify_replay()` that re-runs `resolve_action` and rejects the forged transition with a precise mismatch.

Scope the first implementation to a single deterministic `Move` fixture and one resolver version. Do not wait for WASM packaging, VRFs, or circuits. This small vertical slice establishes the receipt fields every later feature needs, makes the honest verification distinction executable rather than documentary, and creates the reference oracle against which randomness handling and dregg constraints can be tested.

## Security and product claims

The verifier must describe evidence, not imply absolutes:

- Today: “This session's recorded history is internally consistent and untampered under the fixture attestation.”
- After replay: “This client re-executed the bound resolver and reproduced the recorded transitions.”
- After randomness: “Random outcomes match the bound VRF/beacon transcript and draw schedule.”
- After folding: “The named invariants verify under the deployed dregg prover and STARK-soundness assumptions.”
- After production attestation: “The execution identity chains to the configured production trust root.”

No single badge should silently merge those claims. A verifiable game earns trust by making the exact boundary of each proof leg as legible as the game itself.
