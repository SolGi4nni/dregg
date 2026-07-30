# The descriptor circuit & light client

What this subsystem IS at HEAD. Three crates, one chain of trust: a turn's
execution becomes a STARK proof (`dregg-circuit` / `dregg-circuit-prove`), turns
fold into one succinct whole-history aggregate, and a light client verifies that
aggregate — re-witnessing nothing (`dregg-lightclient`). Every load-bearing claim
below is cited to a file:line (Rust) or `Module.decl` (Lean).

## The three crates and the prove/verify split

- **`dregg-circuit`** (`circuit/`) — the **verify floor**. It carries only the
  recursion-FREE Plonky3 deps (`p3-batch-stark`'s `prove_batch`/`verify_batch`,
  `p3-uni-stark`) and is always-on; the three recursion-only crates are NOT here
  (`circuit/Cargo.toml:9-23`). A verify-only consumer depends on this crate
  alone.
- **`dregg-circuit-prove`** (`circuit-prove/`) — the **heavy prove surface**: the
  `p3-recursion` tower (IVC turn chain, joint-turn recursive aggregation,
  recursive witness bundle), the custom proof-bind engine, the shielded-action
  prover, the LogUp lookup AIR (`circuit-prove/src/lib.rs:1-29`). This partition
  is what keeps `cargo tree -p dregg-circuit` free of the recursion prover
  (`circuit-prove/src/lib.rs:10-15`).
- **`dregg-lightclient`** (`lightclient/`) — verify ONE succinct IVC aggregate
  (`WholeChainProof`) and obtain the verdict, re-witnessing nothing
  (`lightclient/Cargo.toml` description; `lightclient/src/lib.rs:1-10`).

## The trust model

The crate operates at the **TRUSTLESS** level: a valid proof guarantees the
prover knows a witness satisfying the circuit constraints, independently
verifiable by anyone with the public inputs and verification key; the assumptions
are cryptographic hardness of the hash (Poseidon2/BLAKE3), correct constraint
encoding, and honest verifier randomness (Fiat–Shamir) — no trust in any
federation member or operator (`circuit/src/lib.rs:26-43`).

## Two circuit layers: hand-written AIRs vs the Lean-emitted descriptor

`circuit/src/lib.rs:1-24` states the load-bearing distinction explicitly: **most
AIRs in `dregg-circuit` are hand-written, UNVERIFIED dregg1 circuits, NOT the
source of truth.** The verified circuit semantics live in Lean under
`metatheory/Dregg2/Circuit/`; the Lean is verified at the digest /
state-transition layer and abstracts Poseidon2 / Merkle / selector-dispatch as a
hypothesis. The hand-written AIRs (`effect_vm/`, `note_spending_witness`,
`poseidon2_air`, `effect_action_air`) are the layer that actually computes those
hashes / Merkle paths in-circuit — a different abstraction layer. They retire one
frontier at a time as the Lean-emitted descriptor interpreter gains gates.

The verified path:

1. **Lean is the source of truth.** Each `circuit/descriptors/*.json` is the
   output of `Dregg2/Circuit/Emit/EmitAllJson.lean`, NOT hand-written; the
   checked-in JSON is a cache of Lean's emission, drift-gated by
   `scripts/check-descriptor-drift.sh` which re-runs the emitters and diffs
   (`circuit/src/effect_vm_descriptors.rs:10-26`).
2. **The registry** (`effect_vm_descriptors`) keys every verified-by-construction
   descriptor JSON by per-effect selector index
   (`circuit/src/effect_vm_descriptors.rs:30-44` documents the v1 layer, where the
   `attenuateA` cap-root-move object was shared by attenuate/delegate). The
   DEPLOYED rotated path is the **v3 staged registry** — 60 descriptor rows in
   `circuit/descriptors/rotation-v3-staged-registry.tsv` (+ its wide and
   umem-welded twins); the Lean registry object is `v3RegistryHeap`
   (`metatheory/Dregg2/Circuit/CircuitSoundnessAssembled.lean:141`), 61 entries,
   length pinned by `v3RegistryHeap_length` (`:285`) — where the cap-writing
   effects no longer share one object: each rides
   a shape-matched keystone (`effCapInsertV3` / `effCapRemoveV3` /
   `effCapOpenWriteV3`) and the six committed Merkle roots are faithful 8-felt —
   see [`faithful-commitment.md`](faithful-commitment.md).

## Descriptor IR v2 — the multi-table batch STARK (the "emit")

The current effect-VM circuit is `descriptor_ir2` — the EPOCH multi-table batch
STARK interpreter. It parses Lean's versioned `"ir":2` wire
(`Dregg2.Circuit.DescriptorIR2.emitVmJson2`) and assembles a multi-table batch
STARK over the fork's `p3-batch-stark` + the `p3-lookup` LogUp argument
(`circuit/src/descriptor_ir2.rs:1-13`). Hashing becomes a *boundary* phenomenon —
the descriptor declares tables and relations, the Rust side realizes them. The
instances (`circuit/src/descriptor_ir2.rs:10-43`):

- **main** — one row per effect row; interprets the v1 constraint forms
  (`gate`/`transition`/`boundary`/`pi_binding`) and realizes each declared
  `lookup`/`mem_op`/`map_op` as a bus interaction;
- **poseidon2 chip** — one row per permutation, pinned to the real Poseidon2
  round constraints (Lean `ChipTableSound`); hash-site lookups ride the `ir2_p2`
  bus;
- **range** — the shared `[0,256)` byte table; a `lookup` is byte-limb
  decomposition + LogUp byte queries (Lean `range_row_mem_iff`);
- **memory** — one row per state access, offline-memory-checking (Blum); soundness
  is Lean `Dregg2.Crypto.MemoryChecking.memcheck_sound`;
- **map-ops** — one row per boundary reconciliation, each verifying a real
  sorted-Poseidon2-Merkle opening (depth 16, byte-identical to
  `heap_root::CanonicalHeapTree` for the scalar chains; the deployed after-spine /
  insert descriptors carry the faithful **8-felt** roots via the arity-16 node8
  chip lanes and `CanonicalHeapTree8` witnesses — `circuit/src/heap_root.rs:728`,
  `circuit/src/descriptor_ir2.rs:1823`; see
  [`faithful-commitment.md`](faithful-commitment.md)).

**The law: Rust authors NO constraints** — every enforced relation is the
realization of a declared descriptor element; which wires are constrained is
entirely Lean's choice (`circuit/src/descriptor_ir2.rs:53-58`).
Descriptor-empty tables are NOT committed; the batch is assembled over only the
tables the descriptor uses, a function of the constraint list alone so prover and
verifier agree (`circuit/src/descriptor_ir2.rs:45-51`).

The proof: `prove_vm_descriptor2` produces a `BatchProof<DreggStarkConfig>` over
`(base_trace, public_inputs, mem_boundary, map_heaps)`
(`circuit/src/descriptor_ir2.rs:5630`).
Verify: `verify_vm_descriptor2` (`circuit/src/descriptor_ir2.rs:5785`)
checks the proof against the descriptor and public inputs, ultimately via
`p3_batch_stark::verify_batch` (`circuit/src/descriptor_ir2.rs:200`). The verify
core rejects a proof whose instance count differs from the descriptor's
present-table set (`circuit/src/descriptor_ir2.rs:5814`).

## A finalized turn → its per-cell proof

A turn's per-cell proof is carried as a `RotatedParticipantLeg`: the rotated
multi-table `Ir2BatchProof`, the `EffectVmDescriptor2` it satisfies, and the
38-PI vector (`circuit-prove/src/joint_turn_aggregation.rs:105-115`). A
`FinalizedTurn` wraps a `DescriptorParticipant` carrying that rotated leg
(`circuit-prove/src/ivc_turn_chain.rs:527`); its `old_root`/`new_root` are
read from the rotated commitments at PI 34/35
(`circuit-prove/src/ivc_turn_chain.rs:538`).

**Host admission** is `verify_descriptor_participant`
(`circuit-prove/src/joint_turn_aggregation.rs:1327`): it re-verifies the
rotated proof standalone via `verify_vm_descriptor2_with_config` and maps the
descriptor name back to its effect selector. This host gate is an *admission
discipline, NOT the soundness boundary* — the leaf is re-verified in-circuit at
the wrap (`circuit-prove/src/joint_turn_aggregation.rs:1322-1326`).

## The whole-chain IVC fold

`ivc_turn_chain` folds a sequence of finalized turns — in the node's finalized
(`tau`/blocklace) order — into ONE running recursive proof attesting "all turns
1..K executed correctly AND the finalized state root advanced correctly from
genesis to final, in that order" (`circuit-prove/src/ivc_turn_chain.rs:1-23`).
The binding is *temporal*: turn N's post-state root must be turn N+1's pre-state
root (`circuit-prove/src/ivc_turn_chain.rs:20-23`).

Two pieces (`circuit-prove/src/ivc_turn_chain.rs:25-64`):

1. **The Lean-emitted chain-binding descriptor** — `dregg-turn-chain-binding-v2`
   (`TURN_CHAIN_BINDING_NAME` from `dregg_circuit::turn_chain_witness`,
   `circuit-prove/src/ivc_turn_chain.rs:230`) — one row per folded position,
   carrying `[old_root, new_root, acc_in, acc_out, idx, is_real, real_count]`
   with its Poseidon2 relation served by the shared chip lookup. Its constraints
   are emitted by Lean: chain continuity `new_root[i] == old_root[i+1]` (the
   temporal tooth); first row `old_root == genesis_root`, last row `new_root ==
   final_root`; the running digest `acc_out == hash_4_to_1([acc_in, old_root,
   new_root, idx])` ENFORCED in-circuit (a genuine Poseidon2, not a free
   column); and `num_turns` pinned to `real_count[last]`, the cumulative count
   of non-padding rows (`circuit-prove/src/ivc_turn_chain.rs:26-49`). Rust
   builds only the chip-lane witness and interprets the descriptor — no
   Rust-authored turn-chain algebra is on this path. A
   reordered/dropped/inserted turn breaks continuity (UNSAT); a forged
   `chain_digest` has no satisfying Poseidon2 witness; a forged `num_turns`
   mismatches the real-row count.
2. **The recursion tree with REAL leaves + the ordered SEGMENT ACCUMULATOR.**
   Each finalized turn's leaf is the rotated multi-table `Ir2BatchProof` itself,
   re-proven and wrapped in its own in-circuit verifier layer; all batch leaves
   are pairwise aggregated up a binary tree to ONE root batch-STARK proof. The
   verifier checks ONLY the root; its cost is independent of K
   (`circuit-prove/src/ivc_turn_chain.rs:51-64`). The in-circuit chain linkage
   is the segment: every DESCRIPTOR leaf exposes
   `[first_old, last_new, count, acc]` through the `expose_claim` table, with
   `first_old`/`last_new` bound to that leaf's verified rotated roots
   (`prove_descriptor_leaf_rotated_with_segment`,
   `circuit-prove/src/ivc_turn_chain.rs:1098`); each aggregation combine
   constrains state continuity (`L.last_new == R.first_old`), count additivity,
   and the ordered digest fold (`acc = H(L.acc, R.acc)`), re-exposing the
   parent segment up to the root (`aggregate_tree`,
   `circuit-prove/src/ivc_turn_chain.rs:3498`; the closure record:
   `circuit-prove/src/ivc_turn_chain.rs:107-140`). There is NO separate binding
   leaf on the soundness path.

The soundness argument (`circuit-prove/src/ivc_turn_chain.rs:66-81`): the leaf
wrap re-proves the IDENTICAL constraint set as a recursion-compatible STARK; a
claimed `(old_root, new_root)` with no satisfying execution trace has no
satisfying leaf, so a prover that SKIPS the host gate still CANNOT produce a
verifying root for a forged turn — the tooth
`ungated_prover_with_forged_post_commit_cannot_produce_a_root` bites on this
(`circuit-prove/tests/ivc_turn_chain_rotated.rs:551`). The deliberately
host-gate-less entry `prove_turn_chain_recursive_without_host_gate`
(`circuit-prove/src/ivc_turn_chain.rs:1739`) makes that claim falsifiable.

`prove_turn_chain_recursive` is the public fold
(`circuit-prove/src/ivc_turn_chain.rs:1714`): host-admit every turn
selector-bound, check ≥2 turns + sequential continuity, prove the Lean-emitted
chain-binding descriptor, re-prove + wrap each descriptor leaf with its
segment, then aggregate to one root. The result is a `WholeChainProof` carrying
the root, the chain-binding descriptor proof, and the wide publics —
`genesis_root`/`final_root` as 8-felt (~124-bit faithful) anchors
(`[BabyBear; SEG_ANCHOR_WIDTH]`), `chain_digest` as
`[BabyBear; SEG_DIGEST_WIDTH]` (8 lanes), and the scalar `num_turns`
(`circuit-prove/src/ivc_turn_chain.rs:1383-1402`).

## `verify_turn_chain_recursive` — the four teeth

`verify_turn_chain_recursive(proof, expected_vk)`
(`circuit-prove/src/ivc_turn_chain.rs:3551`) forwards to
`verify_turn_chain_recursive_from_parts`
(`circuit-prove/src/ivc_turn_chain.rs:3587`), which the in-memory AND over-wire
paths share. The teeth, in order:

1. **VK pin** — recompute the root's verifier-key fingerprint and compare to the
   caller's `expected_vk` trust anchor; a root proof of a DIFFERENT circuit is
   refused before any check trusts its self-described circuit data
   (`circuit-prove/src/ivc_turn_chain.rs:3596`).
2. **Binding-descriptor attestation** — the carried Lean-emitted turn-chain
   descriptor proof verifies via `verify_vm_descriptor2` against the registered
   `TURN_CHAIN_BINDING_NAME` descriptor with its exact four PIs, and its scalar
   genesis/final/count PIs must match the head-lane projection of the carried
   wide claim (`circuit-prove/src/ivc_turn_chain.rs:3605-3638`). The verifier
   doc states it plainly: the carried binding proof is NOT a soundness
   dependency for the root↔claim link — the segment tooth is
   (`circuit-prove/src/ivc_turn_chain.rs:3577-3585`).
3. **The root** — `verify_recursive_batch_proof_with_config` on the single root
   batch-STARK proof under the rotated leaf-wrap config
   (`circuit-prove/src/ivc_turn_chain.rs:3639-3646`).
4. **The segment tooth** — `root_exposed_claims(root_proof)` reads the root's
   exposed ordered segment `[first_old, last_new, count, acc]` (built BY
   CONSTRUCTION from the real descriptor leaves and combined up the tree) and
   requires it to equal the carried
   `[genesis_root, final_root, num_turns, chain_digest]`; absence of the
   segment table is itself a rejection
   (`circuit-prove/src/ivc_turn_chain.rs:3647`). This closes the mixed-root
   hole: a root that executed history A cannot expose history B's endpoints,
   so a B-claim against an A-execution fails here.

The `expose_claim` channel is emitted at every descriptor leaf
(`prove_descriptor_leaf_rotated_with_segment`,
`circuit-prove/src/ivc_turn_chain.rs:1098`) and re-exposed + combine-constrained
up every aggregation layer (`aggregate_tree`,
`circuit-prove/src/ivc_turn_chain.rs:3498`). The module header records the
segment-accumulator closure of the binding↔root linkage (CRITICAL HOLES
#1/#2/#6, `circuit-prove/src/ivc_turn_chain.rs:107-140`), and the active
rejection test `carried_binding_proof_unlinked_to_root_is_rejected`
(`circuit-prove/tests/ivc_turn_chain_rotated.rs:732`) bites on the out-of-band
binding-proof swap. The honest open residual is the engine-soundness floor,
below.

`TurnChainError` (`circuit-prove/src/ivc_turn_chain.rs:556`) names each
rejection: `TooFewTurns`, `ChainBreak` (the temporal tooth), `WideChainBreak`
(the 8-felt temporal tooth for WIDE welded legs), `MissingWideAnchor` (a narrow
leg presented to the wide fold), `TurnProofInvalid`, `RecursionFailed`,
`VkFingerprintMismatch` (tooth 1), `ClaimedPublicsUnattested` (teeth 2 and 4),
`EnvelopeDecode`.

## Over-wire envelope

A whole `WholeChainProof` is NOT byte-encodable (its `root.1` is prover-only
`Rc<CircuitProverData>`); `WholeChainProofBytes`
(`circuit-prove/src/ivc_turn_chain.rs`, `WHOLE_CHAIN_PROOF_ENVELOPE_V1 = 6`)
carries the verify-sufficient subset (the root `BatchStarkProof`, the binding
descriptor proof with its four PIs, and the wide publics as canonical `u32`
lanes). `verify_whole_chain_proof_bytes` and
`verify_turn_chain_recursive_from_blobs` run the same teeth on a decoded
envelope, fail-closed on a non-decoding envelope (a stale-version envelope is
refused, `EnvelopeDecode`).

**v6 — the count-lane alias close (2026-07-30).** `num_turns` is a `u32`, not a
`u64`, and `from_postcard` refuses `num_turns >= BABY_BEAR_MODULUS`. The count
rides as ONE BabyBear lane, so through v5 a relayer could edit that single field
to any modular alias (`n + p`, `n + 2^32`, …) — no key, no proving, no witness —
and the artifact still passed every tooth while reporting the inflated count: a
measured 2-turn history attested as `num_turns = 6,308,233,219`
(`circuit-prove/tests/num_turns_alias_probe.rs`,
`lightclient/tests/num_turns_alias_reaches_attested_history.rs`, and
`wasm/tests/wasm32_count_gate_is_not_truncated_past.rs` for the 32-bit-`usize`
target). Every fold entry already refused `>= p`; no verify path did. The
verifier core (`verify_turn_chain_recursive_from_parts_with_board_window`) and
the non-funnelling `verify_wide_turn_chain_recursive` now refuse it too. **A v5
artifact refuses to load; re-emit the envelope from the same fold — no VK
rotation, no re-proving, no descriptor re-emit.**

## The light client

`dregg-lightclient` is the executable counterpart of the Lean theorem
`Dregg2.Circuit.RecursiveAggregation.light_client_verifies_whole_history`
(`lightclient/src/lib.rs:12-13`).

- **`verify_history(agg, expected_vk)`**
  (`lightclient/src/lib.rs:189`) — THE light-client check. It calls
  `verify_turn_chain_recursive` (the teeth above), then reads off the
  `AttestedHistory` (`lightclient/src/lib.rs:134`):
  `genesis_root`/`final_root` (8-felt anchors), `chain_digest` (8 lanes),
  `num_turns`. `expected_vk` is the client's trust anchor — the root circuit's
  VK fingerprint, obtained ONCE from an honest setup fold and NEVER read off
  the artifact under verification (`lightclient/src/lib.rs:175-178`). The
  byte-path dual is `verify_history_bytes` (`lightclient/src/lib.rs:217`).
- **`fold_and_attest(turns)`** (`lightclient/src/lib.rs:243`) — the
  setup/relayer convenience: fold a chain (expensive, once) then self-anchor +
  light-verify.
- **The third leg — finality.** `verify_history` proves a *correct-looking*
  history, but an equivocating prover can fold a valid aggregate over a fork the
  network never finalized (`lightclient/src/lib.rs:255-262`).
  `FinalityCert` (`lightclient/src/lib.rs:351`) carries the distinct signer
  ids, the participant count, and the finalized root. `has_quorum`
  (`lightclient/src/lib.rs:422`) counts DISTINCT signers against the REAL
  node threshold `dregg_blocklace::ordering::supermajority_threshold` = `2n/3 + 1`
  (`lightclient/src/lib.rs:273`); duplicate signers collapse to one
  (`lightclient/src/lib.rs:415-424`). `verify_finalized_history`
  (`lightclient/src/lib.rs:652`) runs three legs: (1) `verify_history`; (2)
  the root seam `agg.final_root == finalized_root == cert.finalized_root`; (3)
  `cert.has_quorum()`. It is the Rust embodiment of
  `Dregg2.Distributed.FinalizedLightClient.light_client_accepts_finalized_history`
  (`lightclient/src/lib.rs:262`), returning a `FinalizedAttestation`
  (`lightclient/src/lib.rs:599`).

Light-client rejections are tested: a mismatched VK anchor
(`VkFingerprintMismatch`), a spliced public claim (`ClaimedPublicsUnattested`), a
sub-quorum cert (`NoQuorum`), a cert for the wrong root (`CertRootMismatch`),
duplicate-signer Sybil-by-repeat (`lightclient/src/lib.rs:1494-1800`). The headline
test `light_client_attests_whole_history` folds a real K=3 chain and light-verifies
it (`lightclient/src/lib.rs:1211`); `whole_history_demo`
(`lightclient/src/bin/whole_history_demo.rs:1-15`) is the runnable demo.

## The Lean anchors

The Rust mirrors named Lean theorems in `metatheory/Dregg2/Circuit/`:

- `RecursiveAggregation.AggregateAttests`
  (`metatheory/Dregg2/Circuit/RecursiveAggregation.lean:179`) — the verdict
  structure: (1) every turn executed correctly per the verified executor, (2) the
  chain is correctly ordered (the temporal tooth), (3) the public final root IS
  the genuine fold, (4) the genesis root is the chain's start.
- `RecursiveAggregation.light_client_verifies_whole_history`
  (`metatheory/Dregg2/Circuit/RecursiveAggregation.lean:200-211`) — checking only
  `verify agg.root = true`, re-witnessing nothing, yields `AggregateAttests`,
  UNDER the named `EngineSound` hypotheses.
- `EngineSound`
  (`metatheory/Dregg2/Circuit/RecursiveAggregation.lean:115-133`) — the named,
  realizable hypotheses: `recursive_sound` (root verifies ⇒ leaves + binding
  verify), `leaf_sound` (positional pairing ⇒ each step executed), `binding_sound`
  (ordering + genesis + final-is-fold).

These theorems are `#assert_axioms`-clean (⊆ `{propext, Classical.choice,
Quot.sound}`) — the file pins
`light_client_verifies_whole_history`,
`tampered_aggregate_cannot_bind`, `leaf_pairing_defeats_swap`,
`conserves_from_verification`, and `real_engine_sound` among others
(`metatheory/Dregg2/Circuit/RecursiveAggregation.lean:694-703`).

## The honest engine-soundness floor (named, not hidden)

The light client guarantees the COMPOSITION gap-free — IF the aggregate verifies,
THEN the whole history is attested — but NAMES the FRI engine soundness it does
not re-prove (`lightclient/src/lib.rs:45-50`): `recursive_sound` is the plonky3
recursion fork's FRI obligation, the same named crypto carrier as the Lean model's
`EngineSound.recursive_sound`. You cannot prove plonky3 FRI soundness in Lean, and
this crate does not pretend to (`lightclient/src/lib.rs:46-49`). The two
fork follow-ups the module docs name — child-circuit identity under the VK pin
and leaf public-value re-exposure at the root — are CLOSED
(`circuit-prove/src/ivc_turn_chain.rs:172-193`), so recursion soundness rests on
`recursive_sound` alone.
