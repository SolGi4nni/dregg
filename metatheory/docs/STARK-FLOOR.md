# The STARK floor: what `StarkSound` / `StarkComplete` assume

The circuit-soundness apex (`lightclient_unfoolable_circuit_sound`) rests on exactly
one cryptographic trust boundary that Lean cannot discharge: the soundness of the
deployed p3 batch-STARK verifier. That boundary is named, in full, by two Lean
classes — `StarkSound` (extraction) and `StarkComplete` (its dual). This document
states precisely what those classes assume, against the actual deployed verifier and
its concrete FRI parameters, and what is PROVED above the floor.

## The floor, stated

`StarkSound hash R` (`Dregg2/Circuit/CircuitSoundness.lean` §5) carries one field:

    extract : verifyBatch (vkOfRegistry R) pi π = accept →
      ∃ minit mfin maddrs t,
        Satisfied2 hash (R pi.effect) minit mfin maddrs t ∧
          tracePublishedCommit t = pi.toPublished

In words: a batch proof that the deployed verifier ACCEPTS against the live
registry's verifying key yields, for the descriptor the public inputs name
(`R pi.effect`), a circuit witness `t` that SATISFIES that descriptor's AIR
relations and whose published OLD/NEW state commitments are EXACTLY the public
inputs' `pi.pre` / `pi.post` at the boundary turn `pi.turn`.

`StarkComplete hash R` (`Dregg2/Circuit/CircuitCompleteness.lean` §3) is the dual:
a `Satisfied2` witness of the claimed descriptor, publishing `pi`, yields some proof
`π` the verifier accepts. The honest prover, holding a satisfying instance, can
always produce an accepting proof.

These are the FRI / p3 verify⟹∃-witness extraction and its converse. They are
realizable and standard, but not provable inside Lean — so they are carried as named
classes, not silently assumed.

## The deployed verifier this floor mirrors

The Lean `verifyBatch` / `vkOfRegistry` / `BatchPublicInputs` interface is a faithful
abstraction of the deployed verify path:

- **Verifier.** `verify_vm_descriptor2(desc, proof, public_inputs)`
  (`circuit/src/descriptor_ir2.rs:4121`) → `verify_vm_descriptor2_with_config(...,
  &ir2_config())`. It rebuilds the AIR set from the descriptor alone, checks the
  proof's instance count against the descriptor's present-table set, pins the
  range-table height (`degree_bits[byte_idx] == LIMB_BITS`), and then calls p3
  `verify_batch(config, &airs, proof, &pvs, &common)`. `Ok(())` is `accept`; any
  `Err` is `reject`. The Lean `verifyBatch ... = accept` subsumes these structural
  pre-checks plus the FRI check under one opaque verdict.

- **Verifying key ↔ registry binding.** The AIRs are reconstructed FROM the
  descriptor (`R pi.effect`); the descriptor / registry IS the object the verifier
  is pinned to. Lean's `vkOfRegistry R = ⟨registryCommit R⟩` models this binding: the
  VK commits exactly to the registry, and the apex needs only that equality.

- **Public-input layout.** The verifier consumes a flat `&[BabyBear]` whose layout is
  fixed in `circuit/src/effect_vm/pi.rs`:
  - `OLD_COMMIT_BASE = 0` (4 felts) — the published pre-state commitment ⇒ Lean
    `pi.pre`.
  - `NEW_COMMIT_BASE = 4` (4 felts) — the published post-state commitment ⇒ Lean
    `pi.post`.
  - `TURN_HASH_BASE = 25` (4 felts) — the turn binding ⇒ Lean `pi.turn`.
  - the descriptor selector ⇒ Lean `pi.effect`.

  The Lean `BatchPublicInputs { effect, pre, post, turn }` mirrors exactly the slots
  the apex reasons about. (The deployed PI vector additionally carries effects-hash,
  balance-limb, slot-caveat-manifest and bilateral-binding fields; those are bound by
  AIR constraints and by the off-AIR `effect_vm/verify.rs` re-checks, and are
  subsumed into "the descriptor's AIR relations" that `Satisfied2` encodes — they do
  not weaken the OLD/NEW/turn binding the floor exports.)

The conjunct `tracePublishedCommit t = pi.toPublished` is precisely the FRI
public-input binding: the verifier's accepted PI vector pins `OLD_COMMIT` /
`NEW_COMMIT` / `TURN_HASH`, and a satisfying trace's chained-root column publishes
exactly those. It is pure-FRI extraction binding, not a smuggled decode or
refinement fact.

## The concrete FRI parameters

The production STARK configuration is `ir2_config()`
(`circuit/src/descriptor_ir2.rs:3830`) =
`create_config_with_fri(log_blowup = 6, log_final_poly_len = 0, max_log_arity = 3,
num_queries = 19, query_proof_of_work_bits = 16)`
(builder at `circuit/src/plonky3_prover.rs:119`):

- **Field.** BabyBear (`p = 2^31 − 2^27 + 1`), challenges drawn from the degree-4
  extension `BinomialExtensionField<BabyBear, 4>` (`|EF| ≈ 2^124`).
- **Hash / Merkle.** Poseidon2 width 16 (α = 7, 4+4 external + 13 internal rounds),
  `PaddingFreeSponge` leaf hash + `TruncatedPermutation` compression, `MerkleTreeMmcs`.
- **FRI.** rate `1/2^log_blowup = 1/64`; `num_queries = 19`; `query_proof_of_work_bits
  = 16`; `commit_proof_of_work_bits = 0`.

The v1 monolithic path (`create_config`, `circuit/src/plonky3_prover.rs:92`) uses
`(log_blowup = 3, 38 queries, 16 PoW)` at the same conjectured/proven security as
`ir2_config` — the IR-v2 path RAISES blowup and CUTS queries at parity to shrink the
wire. The deployed descriptor proofs run under `ir2_config`. (The module header
comment in `plonky3_prover.rs` says "log_blowup=2, 50 queries" — that is STALE;
`create_config` itself constructs `(3, …, 38, 16)`.)

### Soundness error

FRI query soundness contributes, per query, roughly `log_blowup` bits under the
conjectured capacity (proximity-gap) bound, or `log_blowup / 2` bits under the proven
Johnson / list-decoding-to-`√rate` bound. With grinding (`query_proof_of_work_bits`)
added once:

- **Conjectured (capacity bound):** `19 × 6 + 16 = 130` bits.
- **Proven (Johnson bound):** `19 × 3 + 16 = 73` bits.

Both are additionally capped by the soundness of the extension-field challenge space
(`≈ 2^124`) and by the collision/preimage resistance of the Poseidon2 commitment
hash. The symbolic statement: for `q` queries at blowup `2^b` with `w` grinding bits,
the soundness error is bounded by `2^-(q·b + w)` (conjectured) / `2^-(q·b/2 + w)`
(proven), plus the FRI batching, field, and hash terms. The v1 path
`(b=3, q=38, w=16)` lands at the same `130 / 73` bit envelope. See
`circuit/docs/PROOF-ECONOMICS.md` for the measured size/time tradeoff behind the
`(6, 19)` choice.

### Audit status

There is NO third-party / external audit of the deployed verifier or its
configuration. The o1vm audit referenced in `circuit/src/effect_vm/verify.rs` (e.g.
"audit finding #1", the balance-limb overflow mitigation) is an internal,
self-conducted review; its findings are reflected as executor-side range re-checks
in that file. The honest status of this floor is therefore: **the soundness of p3
`verify_batch` at the `ir2_config` FRI parameters, under conjectured FRI security,
self-reviewed and UNAUDITED by a third party.** Hardening this line means a
third-party audit of the p3 batch-STARK and the descriptor AIR set, and/or pinning
the proven (Johnson-bound) parameter envelope on the wire.

## What is PROVED above the floor

`StarkSound` is the SINGLE pure-FRI rung. Everything between "a witness exists" and
"a genuine kernel transition committing to the public inputs exists" is proved in
Lean, on top of this one floor:

1. **`StarkSound.extract`** (this floor) — `verify accept ⟹ ∃ a Satisfied2 witness `
   `t` publishing `pi`.
2. **Faithful decode** — `Poseidon2SpongeCR hash` + the `CommitSurface` /
   `S_live` collision-resistance fields give an injective commitment surface, so the
   published roots determine the kernel states behind them
   (`WitnessDecodes` supplies their EXISTENCE; the CR fields supply uniqueness).
3. **Per-effect refinement** — `descriptorRefines` / the genuine per-effect
   dischargers in `Dregg2/Circuit/ClosureFanoutGenuine.lean` turn a `Satisfied2`
   witness + a faithful decode into a real kernel step `kstep pi.effect pre post`.
   The 36-way `actionTag` case-split keeps every proven `<e>_closedLog` rung
   load-bearing (`closedWitness_of_readouts`).
4. **The apex** — `lightclient_unfoolable_circuit_sound`
   (`Dregg2/Circuit/ClosureFinal.lean` §3) composes these: from `(pi, π)` and the
   named crypto floors ALONE, there exist decoded endpoints and a genuine FULL
   kernel+log transition `kstepAll pi.effect pre post` whose endpoints commit to the
   published `(pi.pre, pi.post)`. The light client ran nothing. The whole-turn lift
   (`lightclient_turn_unfoolable_forest`, §8) chains per-step apexes along a turn via
   the `DecodedStep` frame.

The carried set at the apex is exactly: `{ StarkSound, Poseidon2SpongeCR + the S_live
CR fields, logHashInjective, ClosedWitness }`. `StarkSound` is one of these — the
irreducible FRI line. The completeness apex `lightclient_complete`
(`CircuitCompleteness.lean` §4) is the dual: a valid kernel transition HAS an
accepting proof, resting on `StarkComplete` symmetrically.

`#assert_axioms` on the apex theorems confines their axiom dependence to
`{ propext, Classical.choice, Quot.sound }` — the STARK floor enters as a typeclass
HYPOTHESIS (`[StarkSound hash R]`), not as an axiom, so it is explicit at every use
site rather than baked into the ambient logic.
