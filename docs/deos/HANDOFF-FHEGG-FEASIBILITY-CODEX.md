# HANDOFF — fhEgg / Dark Bazaar current implementation ledger

*Current at HEAD on 2026-07-21. This is the durable implementation handoff, not a
roadmap. Verify every claim against the named source, theorem, test, and captured
gate result before repeating it.*

## 0. Status language

- **GATED** — the named artifact exists and the named gate passed after the
  relevant implementation landed.
- **BUILT, UNGATED** — the implementation exists, but no successful run of the
  relevant current target has been captured.
- **PENDING GATE** — the HEAD source and exact target exist, but no result has
  yet been supplied for this implementation revision. This says nothing about
  whether the target compiles or passes.
- **MIXED** — a target or composed lane has both captured greens and a captured
  red/pending member; only the individually named results carry authority.
- **PARTIALLY GATED** — every named result is green, but at least one composed
  member remains pending or the evidence is split across focused invocations.
- **OPERATIONAL** — the execution substrate is available for the named work.
  Hardware discovery alone is not a code verdict; only attached gates count.
- **OPEN** — the construction, proof, or production boundary does not exist yet.

Do not turn an earlier, compiled-out, or predecessor test into a current green
claim. A Lean theorem proves the model stated in that module; it does not silently
prove the Rust codec, cryptography, transport, or refinement hidden behind an
explicit backend premise.

## 1. The honest current sentence

The repository has a transferable, source-row-bound BFV/Poseidon same-opening
proof; a composite quorum + HidingFRI + same-opening verifier; public-only hosted
verifier reconstruction; and a green full-profile integration wiring the exact
encrypted rows through a live authenticated PartyMPC crossing into atomic
Bazaar/game consequences. The same-opening proof, composite verifier, hosted
registry, live crossing, custody envelope, fhIR raid allocation, and the
full-profile apex gate are green. The Warden's Keep crown consequence is also
green at its exact heavy-release gate.
The decisive hbox run passed 1/1 under the full nextest profile with both
DREGG_REQUIRE_LEAN=1 and DREGG_REQUIRE_PQ_CORES=1 and no authority-core
fallback.
The newer composed-game evidence has also advanced: narrated Dungeon is 3/3,
relic oath is 2/2 after repair, the narrated private-raid relic capstone is 1/1,
and all eight private-raid surface tests have current evidence across the seven
prior greens plus the repaired focused final path. Four other composed targets
remain pending.

This is **not** a no-single-viewer system. The deployed same-opening prover still
receives the complete private witness and BFV openings in one process; source
verification sees plaintext orders and encryption randomness; PartyMPC arithmetic
is semi-honest with trusted Beaver preprocessing; and the distributed-custody
surface does not yet produce the real Bulletproof/R1CS proof.

This is also **not an end-to-end post-quantum apex**. Native clearing quorum and
PartyMPC transport now have separately green ML-DSA and ML-KEM-backed profiles,
and BFV is lattice-based, but the full apex has not been rerun since those
transport cutovers. More importantly, its exact ciphertext/root relation is a
Bulletproof over Ristretto/Pedersen with a discrete-log + Fiat–Shamir security
floor, and distributed custody still uses Ristretto/Pedersen. HidingFRI,
Poseidon, BFV, and the wide Lean/Rust bindings have their own stated
soundness/security floors; their presence does not convert the remaining
classical seams into a post-quantum composition.

## 2. Current status at a glance

| Surface | State | Exact authority |
|---|---|---|
| BFV/Poseidon same-opening proof | **GATED** | private_book_bfv_zk: 2/2 release green; hostile proof test 65.765s |
| Composite private clearing verifier | **GATED** | private_bfv_attested_clearing: 1/1 release green; 62.958s |
| Exact source rows and ingress weld | **GATED in Lean and the full-profile apex** | DarkBazaarPrivateIngressCutover: 11 clean; apex 1/1 green |
| Public-only hosted verifier registry | **GATED** | two hostile registry tests: 2/2 green |
| Authenticated live PartyMPC crossing | **GATED; NATIVE PQ PROFILE SEPARATELY GATED** | original crossing 2/2 release; native ML-DSA + ML-KEM/X25519 integration 5/5 and transport units 5/5 |
| Native clearing quorum | **GATED** | full canonical ClearingClaim under roster-pinned ML-DSA + Ed25519: 1/1 hostile native gate; classical compatibility 6/6 |
| Restartable live private-clearing apex | **GATED, NOT END-TO-END PQ** | exact timed hbox full-profile run 1/1 green in 124.159s; verified authority cores required; capture predates native quorum/transport cutovers and still uses the classical Bulletproof relation |
| Distributed input custody | **GATED** | custody-hardened private_book_distributed_inputs: 4/4 green |
| Distributed prover envelope | **GATED, FIXTURE BACKEND ONLY** | private_book_distributed_prover: 2/2 green; no distributed Bulletproof/R1CS backend |
| Distributed real same-opening prover | **OPEN** | no backend consumes shares to produce the apex Bulletproof/R1CS proof |
| Bazaar crown consequence | **GATED** | one both-polarity heavy-release test, 1/1 green |
| fhIR exact raid allocation | **GATED** | Rust integration 6/6 release green; FhIRRaidAllocationBinding: 7 clean |
| Narrated Dungeon and relic-oath composition | **GATED BY TARGET** | narrated Dungeon 3/3; repaired relic oath 2/2 |
| Private-raid capability/Arena and narrated-relic composition | **PARTIALLY GATED** | relic capstone 1/1; surface evidence 7 prior + 1 focused current; lower forest pending |
| Chutes → Dungeon closed-command weld | **PENDING GATE** | HEAD target contains 3 tests; no result supplied |
| Lean-native Descent offering/campaign | **PENDING GATE** | HEAD targets contain 3 + 3 tests; no result supplied |
| hbox build substrate | **CONSTRAINED** | current filesystem probe: 19GiB free; prior full-profile apex and real Vulkan GPU gates remain valid captures |
| Collective GPU additive fold | **GATED** | 1/1 on real RX 6750 XT; GpuResident via wgpu/Vulkan, not HIP |
| Portable HidingFRI GPU path | **GATED** | exact CPU proof parity 2/2; retained LDE buffers through salted leaves; 6 resident blits; GPU 1.306s vs CPU 3.072s at depth 2048 |
| Portable encrypted TFHE CMUX | **GATED PROTOTYPE** | CPU/hostile 4/4 and strict GPU 2/2 on hbox; degree-N external product is O(N²), not programmable bootstrapping |
| Exact BFV + wide PQ Lean boundaries | **GATED AT THE MODEL BOUNDARY** | PrivateBookBfvBindingAir checks 98,304 exact equations; WideNativePqCommitment binds 16 canonical lanes; neither alone is a deployed prover cutover |
| Wide shielded value binding | **GATED, TRANSITIONAL** | Turn shielded 7/7 and circuit wire/alias 4/4; live no-mint still retains the classical conservation proof and old note/root seam |
| Hostile external fhIR optimizer protocol | **GATED** | 69/69 focused: problem/session/nonce/manifest/certificate/checksum/replay are bound before the exact checker |
| Lean handler-cutover export | **GATED** | credential-preserving export accepted genuine/rejected forged; archive symbol present, zero unresolved non-toolchain initializers; 44.60s warm closure rebuild |
| Aggregate Market metatheory | **GATED** | lake build Market green at 8747 jobs after the live-host/optimizer additions |

## 3. Transferable BFV/private-root same-opening proof

### What is implemented

**fhegg-fhe/src/private_book_bfv_zk.rs** implements a fixed
\(N=4, K=4, n=4096\) Bulletproof R1CS relation. This proof seam has a
**classical-security** floor: it uses Bulletproofs over Ristretto/Pedersen and
the discrete-log + Fiat–Shamir assumptions. One proof binds the same hidden
order selectors, quantities, and private-root blinding to both:

1. the deployed Poseidon2 private-book root; and
2. the exact four public-key BFV ciphertext rows, using the pinned RNS equations
   and bounded short witnesses in [-32, 31].

The relation uses the actual fhe.rs SIMD encoding. It applies 128
transcript-derived Rademacher compressions per modulus after commitment. The
2^-128 statement applies only to that equation-compression error; it is not a
claim about total protocol security. Total security also depends on BLAKE3,
Poseidon2, and the implementation. The yoloproofs dependency is an
experimental/reference implementation, not a production certification. The
lattice basis of the BFV ciphertext relation does not make its Bulletproof
carrier post-quantum.

The proof does **not** establish:

- exact membership in a seeded sampler image, seed entropy, seed distinctness,
  or a CBD distribution;
- DKG correctness or collective-key well-formedness;
- owner-separated witness custody;
- maliciously secure distributed proving.

### Exact Rust gate

**fhegg-fhe/tests/private_book_bfv_zk.rs**:

- proof_wire_is_bounded_versioned_and_fail_closed
- exact_pk_bfv_and_poseidon_relation_refuses_every_public_substitution

Captured result: **2/2 green in release**. The hostile proof/substitution test
took **65.765s**. It refuses substitutions of the public key, ciphertext
coefficient, private root, session, modulus, and layout.

## 4. Composite receipt and exact source-row binding

### Composite verifier

**dreggnet-market/src/private_bfv_attested_clearing.rs** defines
PrivateBfvAttestedClearingVerifier. Acceptance is the conjunction of:

1. the pinned authenticated committee quorum;
2. the HidingFRI clearing proof; and
3. the BFV/private-root same-opening proof.

new_source_bound pins the full claim nonce, public clearing statement,
parameters, collective public key, four exact ciphertext rows, and canonical
source input pairs. The verifier derives the packed fold from those exact rows.
The claim layout includes:

- the exact four proof ciphertext rows and private root;
- each live source message commitment paired with its exact proof-row
  ciphertext;
- the packed fold ciphertext; and
- the board commitment.

Digest-only verification is intentionally insufficient: verify() returns false
and relying code must call statement-directed verify_claim.

**dreggnet-market/tests/private_bfv_attested_clearing.rs** contains:

- receipt_requires_quorum_hidingfri_and_exact_bfv_root_proof

Captured result: **1/1 green in release**, **62.958s**. This gate validates the
composite proof and hostile public substitutions, but its clearing transcript is
still produced with simulate_public_transcript; it is not the live PartyMPC gate.

### Exact ingress rows

The current **dreggnet-market/tests/private_clearing_apex_e2e.rs** constructs four
canonical PrivateBookCiphertexts. The three live seller/bid board inputs use
those same proof rows; the fourth is canonical padding. Source
messages/signatures and exact row ciphertexts occupy WriteOnce board slots, and
the packed fold in the receipt is computed from those exact rows. There is no
second re-encryption whose equality is merely asserted by committee signatures.

This closes the detached-dual-encoding bug at the public statement boundary. It
does not make ingress private from the process performing source verification:
that process still sees the order and encryption randomness.

Relevant Lean authority:

- **metatheory/Market/PrivateBookEncryptionBinding.lean** states the exact-opening
  law and preserves the RED detached-statement counterexample.
- **metatheory/Market/DarkBazaarPrivateIngressCutover.lean** proves the exact
  ingress/proof/claim weld and refuses row, order, auxiliary-value, root,
  session, and quorum substitutions. Direct gate: **11 clean**.
- **metatheory/Market/DarkBazaarAttestation.lean** retains the older RED result
  showing why digest-only composition did not bind BFV rows. That
  counterexample describes the weak boundary, not the repaired proof path.

## 5. Hosted verifier registry and restart boundary

**dreggnet-market/src/fhegg_verifier_registry.rs** replaces a quorum-only hosted
verifier slot with FheggVerifierRegistry, which dispatches both:

- legacy AuthenticatedQuorum; and
- PrivateBfvAttested.

The registry carries verifier_id, verify, and the load-bearing
statement-directed verify_claim. PrivateBfvHostedVerifierConfig owns public
deployment material only:

- an independently pinned verifier ID;
- the ordered quorum verification-key roster and threshold;
- value bits;
- BFV public identity;
- claim nonce and clearing statement;
- BFV parameters and collective public key;
- the exact ciphertext rows; and
- the canonical source inputs.

It owns no private-book witness, BFV seeds, secret key, or decryption shares.
Installation reconstructs the complete verifier, checks that the BFV-opening
roster agrees with the signature roster, recomputes the verifier ID, and
compares it to the independent pin. DarkBazaarOffering preserves the legacy
with_fhegg_quorum path and adds registry/private-attested constructors.

**dreggnet-market/tests/fhegg_private_verifier_registry.rs** contains:

- exact_public_config_installs_full_private_verifier_in_hosted_operation_registry
- pinned_reconstruction_refuses_every_public_substitution

The hostile test changes the pin, nonce, clearing session/root/result/rule, BFV
identity, source message/row/coefficient, roster order/threshold, value bits,
and BFV-opening roster. Captured result: **2/2 green**.

**metatheory/Market/DarkBazaarLiveApexHost.lean** proves that exact pinned public
configuration reconstruction is required and that verifier-ID equality alone is
not sufficient. Its direct gate is **16 clean**. Its live-MPC conclusion still
depends on the explicit LiveMpcBackend.sound premise.

## 6. Live PartyMPC crossing

### Transport and crossing code

**fhegg-fhe/src/mpc_party/transport.rs** now implements two explicit transport
profiles:

- `NativePostQuantum` roster-pins ML-DSA-65 identities and authenticates every
  frame under the native profile;
- each native frame combines a fresh ML-KEM-768 encapsulation with the existing
  X25519 contribution through dregg's canonical hybrid combiner before
  XChaCha20-Poly1305 protects the peer payload;
- `ClassicalCompatibility` is explicit rather than an implicit downgrade;
- signatures bind the profile, identity, session, circuit role, route,
  sequence, payload, and roster key;
- CrossingPartyMachine and CrossingCoordinatorMachine drive the crossing;
- prepare_private_book_crossing_input validates the exact packed private-book
  shape;
- verify_public_crossing_transcript reconstructs and verifies the public reveal
  transcript; and
- fresh_crossing_preprocessing_seed separates invocations.

The native profile removes Curve25519-only confidentiality and Ed25519-only
frame authentication from this boundary, but it makes no forward-secrecy claim:
recipient ML-KEM and identity-DH keys are long-lived. More importantly,
authenticated transport does not imply honest arithmetic. The crossing
protocol is semi-honest and uses trusted Beaver preprocessing; it has no proof
of honest share formation, correct gate evaluation, or maliciously secure
preprocessing.

**fhegg-fhe/tests/party_mpc_crossing_transport.rs** starts with the exact four BFV
proof rows, folds them, masks and threshold-opens only a one-time-padded
carrier, gives each party its local nine-slot share, and checks that
authenticated machines reveal only (p*, V*). It contains:

- exact_packed_rows_drive_authenticated_crossing_and_bind_every_public_bit
- packed_private_input_refuses_wrong_shape_or_noncanonical_share

The original exact-crossing target passed **2/2 in release**, **1.099s**. After
the native profile cutover, the focused end-to-end native integration passed
**5/5**, including exact packed private crossing and hostile replay, downgrade,
and roster-key substitution cases; transport units passed **5/5**. Those native
PQ tests used the explicit unaudited test backend because the remote lane lacked
the verified Lean cores, so they are control-flow/transcript evidence rather
than verified-core evidence.

### Apex cutover

The current **dreggnet-market/tests/private_clearing_apex_e2e.rs** no longer calls
simulate_public_transcript. It:

1. retains the threshold parties from collective key generation;
2. derives shares from the packed exact proof rows;
3. runs the authenticated crossing machines;
4. verifies the public crossing transcript; and
5. requires the resulting (p*, V*) to equal the HidingFRI statement before the
   committee signs the composite receipt.

This is the correct code-level crossing. The decisive hbox invocation used
**--profile full**, **DREGG_REQUIRE_LEAN=1**, and
**DREGG_REQUIRE_PQ_CORES=1**. The first verified run passed **1/1 in 114.033s**.
The exact-attribution rerun passed **1/1 in 124.159s nextest elapsed**
(**124.116s** on the test's internal timer) with the current-source Lean splice
and required verified ML-KEM/ML-DSA authority cores; no unaudited authority-core
fallback was enabled. The BFV same-opening proof, HidingFRI proof, live PartyMPC
crossing, hosted verifier reconstruction/restart, verified ML-DSA
turn-authority core, atomic consequence, and replay refusal all ran.

That is a verification statement about the required authority cores, not an
end-to-end post-quantum claim. The captured full-apex run predates the later
native quorum and PartyMPC transport cutovers and therefore exercised the then
current Ed25519/Curve25519 boundary. Their replacement profiles are separately
green but have not yet been recaptured inside this heavy apex. In every case the
apex still depends on the classical Bulletproof/Ristretto/Pedersen
exact-relation seam and the separately stated HidingFRI/Poseidon soundness
floors. BFV's lattice security does not remove those assumptions.

The first hbox invocation used the default nextest profile. It built the current
Lean material but ran **0 tests** because the apex binary is deliberately
excluded as heavy. That invocation is build evidence only, not a gate. The
full-profile invocation is the authoritative green.

The archive used by the apex run emitted warnings for **five unresolved
initializers** and did not export **dregg_exec_handler_turn**. That later
residual is now closed independently: the replacement export retains
`lowerForestG` credentials, runs the four-leg gate on the exact pre-state before
handler dispatch, and fails closed in strict test mode. On hbox the ABI tooth
accepted the genuine credential and rejected the forged one in 0.188s; the
archive defines the export and has zero unresolved non-toolchain initializers.
The resumable bounded-parallel closure rebuild is 44.60s warm. Earlier
unaudited-fallback, local archive-closure, remote install-abort, and compiled-out
runs remain historical diagnostics only.

### Timed attribution and GPU priority

The exact timed run is captured in
**/tmp/private-clearing-apex-cpu-timed.log**. WGPU precompute was unset, so this
is the current CPU baseline for the exact relation seam:

- BFV/Bulletproof prove: **63.153s**;
- four full BFV proof verifications: **28.998s** total;
- prove + four verifies: **92.151s**, or **74.2%** of the 124.116s internal
  end-to-end time;
- generic Bulletproof cryptography after subtracting relation synthesis:
  approximately **60.838s proving + 19.959s verifying = 80.8s**;
- HidingFRI: **22ms**; and
- packed fold + PartyMPC: **621ms**.

The immediate GPU priority is therefore the classical Bulletproof/Ristretto
MSM path, followed by any relation-specific acceleration that preserves exact
semantics. The already-GpuResident additive fold is not the apex bottleneck in
this fixture, and accelerating it cannot turn the classical Bulletproof seam
into post-quantum security.

The Lean companion, DarkBazaarLiveApexHost.lean, models the weld from exact
ingress through same-opening evidence, live MPC output, claim, hosted verifier,
and consequence. Its 16 clean theorems do not discharge
LiveMpcBackend.sound; that premise is precisely where malicious arithmetic,
codec, and implementation refinement remain.

## 7. Custody and the no-single-viewer residual

### What the custody surface does

**fhegg-fhe/src/private_book_distributed_inputs.rs** lets four owners expand only
their own local witness vector: order kind, quantity, BFV u/e1/e2, and the
owner-0 root blinding. Owners distribute n-of-n additive Ristretto shares to
workers, commit with vector Pedersen commitments, receive local packet
acknowledgements, and produce a canonical public certificate. Under the stated
confidential-channel and distinct-principal assumptions, any strict subset of
workers has uniformly hidden shares.

This layer assumes confidential authenticated private packet transport. Packets
deliberately have no production wire codec. The public certificate binds custody
events; it is not the R1CS proof and does not establish the same-opening
constraints.

**fhegg-fhe/src/private_book_distributed_prover.rs** adds worker-process and
coordinator APIs, but the current test backend returns public digests only.
LocalOnlyBackend and FixtureVerifier test the custody/envelope boundary; they do
not generate or verify the production Bulletproof.

### Exact test inventory

**fhegg-fhe/tests/private_book_relation.rs** currently contains:

- exact_bfv_rows_open_the_same_private_root_and_refuse_every_substitution
- metadata_slot_keeps_zero_quantity_side_and_limit_injective
- duplicate_bfv_randomness_is_refused_before_encryption
- packed_fold_consumes_the_exact_proof_rows_and_refuses_a_detached_shape
- authenticated_ingress_emits_the_exact_proof_ciphertext_not_a_second_encoding

**fhegg-fhe/tests/private_book_distributed_inputs.rs** currently contains:

- reused_rng_stream_is_session_separated_before_any_worker_sees_a_share
- all_local_openings_bind_one_public_certificate_without_reconstruction
- private_packet_equivocation_and_public_signature_forgery_fail_closed
- exact_production_layout_and_session_separation_are_pinned

The captured relation/distributed-input run was **8/8 green before later custody
hardening**. The current custody-hardened distributed-input target has now also
passed **4/4**. HEAD has nine tests across the relation and distributed-input
targets; the two captures together cover the relation baseline and the current
four-test custody target without pretending they were one nine-test invocation.

**fhegg-fhe/tests/private_book_distributed_prover.rs** contains:

- each_process_consumes_one_share_and_coordinator_sees_only_public_digests
- duplicate_missing_misbound_and_forged_worker_material_fail_closed

Captured result: **2/2 green**. This gates the process/custody envelope and its
fixture backend, not a real distributed Bulletproof/R1CS prover.

### Exact residual before any no-single-viewer claim

A production distributed R1CS/Bulletproof backend must consume shares without
reconstructing the witness. It must then be used by the actual apex instead of
prove_private_book_bfv_zk, whose API receives the complete witness and openings.
The system also still needs malicious share-formation and MPC-gate proofs,
production authenticated private-packet wire transport, DKG/key-domain
validation, and rollback/replay treatment. A colluding decryption threshold can
decrypt. Until those boundaries are closed and gated, “no single viewer” is
false for the deployed path.

## 8. Consequences in the game

### Atomic Bazaar settlement

The current private apex builds a real provenance-carrying Descent loot asset
and gives the winning buyer 3 DREGG. Its intended full path:

1. records the exact source-bound private receipt;
2. reconstructs the public-only verifier after replaying a pre-operation
   FileResumeStore;
3. invokes the same frontend-neutral fhEgg operation used by hosted adapters;
4. journals the operation result;
5. atomically transfers the exact Descent asset and 3 DREGG; and
6. refuses replay.

The implementation is in
**dreggnet-market/tests/private_clearing_apex_e2e.rs**:

- private_bfv_receipt_survives_restart_and_authorizes_the_real_bazaar_consequence

Captured result: **1/1 full-stack integration green in 124.159s nextest
elapsed** under the full profile with the verified ML-KEM/ML-DSA authority
cores required and no fallback. This is not an end-to-end post-quantum result:
the game path still crosses the classical exact-relation, authentication, and
peer-DH seams in section 6. The handler-export caveat also remains load-bearing
without negating the exact authority cores this target required and executed.

### Warden's Keep crown

**dreggnet-market/src/private_clearing_consequence.rs** defines a process-local
corroborated gate from a settled private-clearing receipt to one cap-bounded game
turn, with a derived replay ID and recovery observer.

**dreggnet-market/tests/private_clearing_crown_consequence.rs** contains:

- proven_bazaar_winner_claims_the_writeonce_keep_crown_exactly_once

The test targets the real Warden's Keep WriteOnce crown and includes hostile
target, root, turn, receipt, replay, and recovery cases. It uses the older Tier-1
private-clearing producer, which sees the order witness; the consequence gate is
process-local and is not the transferable BFV composite verifier. It is
**GATED: 1/1 green in the heavy release profile**. Only the pinned receipt may
authorize the crown; target/root/turn/receipt substitution, replay, and crash
splice cases refuse.

### fhIR raid allocation

The green optimizer/game consequence is separate from the private BFV apex.
**circuit-prove/tests/fhir_verified_raid_allocation.rs** verifies a canonical
FHQPB001 artifact, derives the certificate-selected one-hot roster assignment,
binds the exact objective and ordered roster into a witnessed cell claim, and
lets the ordinary executor mutate the actual relic-carrier slot only for that
assignment.

Its six exact tests are:

- exact_fhir_certificate_commits_the_certificate_selected_raid_assignment
- host_cannot_spend_a_valid_certificate_on_a_different_raid_assignment
- corrupted_or_different_program_certificates_cannot_authorize_the_outcome
- same_winner_with_a_different_objective_cannot_reuse_the_cell_claim
- objective_and_ordered_game_roster_are_part_of_the_cell_claim_and_vk
- approximate_tolerance_cannot_authorize_the_exact_game_allocation

Captured result: **6/6 green in release**.

## 9. Composed Dungeon, raid, Chutes, and Descent burn-down

Every path in this section is verified present at HEAD. Results are attached to
their exact targets only: these lanes are not promoted by the private-clearing
apex 1/1 or fhIR raid-allocation 6/6 results.

### Narrated Dungeon and relic-oath substrate — mixed

**dreggnet-offerings/tests/dungeon_narrated_operation.rs** exercises the typed
closed-command narrator boundary over the real hosted Dungeon. Prose is bound
into the receipt but is not state authority; stale-room, injection-shaped, and
world-exposure attempts are refusal teeth. Its exact three tests are:

- opt_in_narrated_turn_records_the_real_receipt_and_prose_is_not_power
- stale_wrong_room_and_injecting_proposals_are_anti_ghost_refusals
- narrator_view_tracks_the_hosted_session_without_exposing_the_world

**dungeon-on-dregg/tests/relic_oath_branch.rs** supplies the consequential
two-oath relic branch that later composition consumes. Its exact two tests are:

- the_sunblade_oath_refuses_the_crown_route_and_replays_to_mercy
- the_thorn_crown_oath_refuses_mercy_and_replays_to_a_cursed_tribute

Captured status:

- dungeon_narrated_operation — **3/3 GREEN**.
- relic_oath_branch — the prior 0/2 LinkageBroken run was repaired; the current
  target is **2/2 GREEN**.

### Private raid, party capability, Arena, and narrated relic — mixed

**dungeon-on-dregg/tests/private_raid_atomic_forest.rs** is the lower-level
executor composition of a real HidingFRI raid-assignment receipt, proof sigil,
party role/focus cells, and a tactical Arena as one journaled forest. Its tests:

- real_proof_sigil_party_and_arena_commit_as_one_four_root_forest
- custom_vk_refuses_a_non_receipt_without_leaking_any_raid_prefix

Its own module comment keeps the boundary honest: the Party cells reproduce the
public executor semantics rather than importing the privately owned production
World, and executor-local atomicity is not distributed-consensus finality.

**dreggnet-surfaces/tests/private_raid.rs** is the broader hosted/player surface:
fhIR allocation or hiding assignment selects exact roster capabilities, the
party forms and spends them in a real Arena, operation and move timelines
restart, and web/chat encodings traverse the same flow. Its exact eight tests
are:

- fhir_optimum_selects_a_real_party_member_and_role_with_executor_and_replay_teeth
- fhir_member_role_allocation_survives_host_operation_and_move_replay
- hiding_assignment_authorizes_exact_capability_claims_and_a_real_arena_turn
- operation_and_moves_restart_exactly_while_roster_order_substitution_fails_closed
- catalog_lobby_forms_the_exact_roster_then_restarts_through_proof_and_capability_claim
- web_binary_and_chat_streaming_reach_one_join_proof_claim_burn_act_game
- chat_proof_stream_refuses_oversize_chunks_and_has_a_finite_turn_budget
- live_adapter_sources_keep_the_text_and_binary_routes_the_flow_requires

**dungeon-on-dregg/tests/relic_raid_narrated_forest.rs** is the new cross-lane
capstone: oath and guardian consequences precede one atomic two-root forest in
which the private raid proof materializes the exact Mender and a receipt-bound
narration awakens the relic. Its exact test is:

- relic_raid_allocation_and_narration_compose_in_one_receipt_chain_and_forest

Captured status:

- private_raid_atomic_forest — **PENDING GATE**; no result supplied.
- dreggnet-surfaces private_raid — seven tests were green in the prior suite;
  the repaired focused
  web_binary_and_chat_streaming_reach_one_join_proof_claim_burn_act_game path is
  now **GREEN**. Current evidence is **7 prior + 1 focused current**, not one
  newly captured 8/8 invocation. The prior 310,767-byte proof replay failure is
  closed by the focused result.
- relic_raid_narrated_forest — **1/1 GREEN**.

The already-green fhIR allocation checker and private-book apex remain separate
evidence.

### Chutes → Dungeon weld — pending

**discord-bot/tests/dungeon_chutes_weld.rs** uses the production
OpenAI-compatible client against a loopback server carrying the response shape
served by Chutes. The model proposes only a typed closed-channel Dungeon
command; the real Dungeon executor remains authority, narration is
receipt-bound, and refused/failed proposals must release player credit without
mutation. Its exact tests are:

- chutes_tool_call_resolves_as_one_real_dungeon_turn
- failed_or_refused_narration_releases_player_credit_and_never_mutates
- provider_schema_is_not_authority_wrong_room_and_injection_still_refuse

Status: **PENDING GATE**. This is an adapter/protocol test using a loopback
provider fixture, not evidence of an external Chutes service deployment.

### Lean-native Descent offering and campaign — pending

**dreggnet-offerings/tests/native_descent_offering.rs** checks the generic
Offering seam over Lean-authored native Descent, including the complete crowned
line, receipt replay/tamper refusal, actor binding, and anti-ghost affordances.
Its exact tests are:

- complete_crowned_run_banks_on_a_real_terminal_receipt
- public_record_resumes_by_reexecution_and_rejects_tampering
- affordances_follow_the_native_mover_and_refusals_are_anti_ghost

**dreggnet-offerings/tests/descent_campaign.rs** composes that native run with
the real region-cell campaign. Only a manually played crown may clear the Keep
and open travel; terminal-without-crown and hostile replay/substitution paths
must not mint campaign progress. Its exact tests are:

- crown_is_manually_played_and_is_the_only_region_unlock
- terminal_run_without_crown_cannot_mint_campaign_progress
- restart_and_hostile_substitutions_reexecute_exactly

Status for both targets: **PENDING GATE**. These are distinct from the green
private-clearing apex, which transfers a Descent loot asset, and from the green
fhIR raid-allocation target.

### hbox and artifact custody — operational facts, not build evidence

Current hbox ground truth:

- Intel i9-12900, 24 hardware threads;
- 123 GiB RAM;
- AMD RX 6750 XT visible through Vulkan;
- no ROCm/HIP installation; and
- **19 GiB free** on the filesystem used for the work at the latest direct
  probe.

The hbox required-authority-core apex gate above and the collective GPU fold
below are now successful
execution evidence. The current free-space floor is again too narrow for casual
parallel heavy builds, so keep Rust CPU gates on persvati and reserve hbox for
GPU-specific work until its build artifacts are pruned.

**fhegg-fhe/tests/collective_gpu_additive.rs**:

- collective_rows_fold_with_explicit_backend_and_feed_masked_threshold_boundary

Captured result: **1/1 GREEN** on the real RX 6750 XT. Both fold phases reported
GpuResident and matched the CPU byte-level oracle before feeding the
party-owned masked threshold boundary. The current implementation stack is
**wgpu/Vulkan**, not ROCm/HIP. This is a real retained collective additive fold,
not a claim that every BFV/MPC operation is GPU-resident.

The portable GPU frontier is now broader and exactly scoped:

- the hard correctness matrix is **8/8 core + 3/3 private**, covering 20
  deterministic parity shapes and 22 adversarial refusals for resident BFV
  folds, the degree-2048 TFHE torus negacyclic MAC, the degree-4096 three-prime
  BFV NTT, and the exact private-book signed-dot workload;
- the private-book relation's 196,608 signed dots cover 805,306,368 exact
  sign/add operations and run in 0.014s warm versus 0.683s CPU (**48.62×**), but
  the unchanged CPU verifier remains authoritative and the complete hostile
  production test is green;
- one-shot BFV upload/readback does not beat CPU through N=256 in the frozen
  hbox qualification; persistent residency wins at larger repeated shapes, so
  batching/residency—not magical dispatch—is the optimization contract; and
- the current Bulletproof fork has a real portable extended-Edwards group-add
  tooth: 7/7 point pairs match dalek compression on the RX 6750 XT and malformed
  coordinates are refused. This is **not yet a complete MSM** and, even when it
  is, only accelerates the transitional classical Bulletproof proof.

The HidingFRI GPU path now retains LDE buffers device-to-device through salted
leaf construction. At depth 2048 it produced the exact CPU proof with six
resident blits and measured **1.306s GPU vs 3.072s CPU**; Merkle-layer readback
remains, so this is not full proof residency. The TFHE path also has a portable
encrypted CMUX/external-product prototype with 4/4 CPU/hostile and 2/2 strict-GPU
gates. Its current kernel is quadratic in the polynomial degree and is not a
programmable-bootstrap implementation.

Lean arithmetic specifications for the BFV NTT and TFHE torus MAC are
axiom-clean; they specify arithmetic/refinement boundaries, not hardware
execution. Frozen details live in `FHEGG-WGPU-VALIDATION-MATRIX.md`,
`HBOX-WGPU-QUALIFICATION-2026-07-21.md`, and
`BULLETPROOFS-MSM-DISPATCH-INVENTORY.md`.

No build, verified artifact, or gate is promoted merely from custody activity.
The PQ lane supplied the apex-required verified ML-KEM/ML-DSA authority cores;
the separate credential-polarity ABI tooth and static archive audit are the
evidence that closed the handler/initializer residual.

### Wide post-quantum binding and the live shielded boundary

Two narrower-but-load-bearing replacements now exist:

- `metatheory/Market/PrivateBookBfvBindingAir.lean` checks the fixed private-book
  relation as **98,304 exact BFV equations** at the Lean model boundary.
- `metatheory/Dregg2/Shielded/WideNativePqCommitment.lean` commits the native
  shielded statement through **16 canonical BabyBear lanes**, rather than one
  field that aliases `x` with `x + p`.

The Rust `ShieldedInputPayload` now carries a mandatory 16-lane wide value
binding plus its hiding proof. The effect hash binds every lane, and executor
admission verifies both the existing spend/conservation evidence and the wide
proof before absorbing those lanes into the conservation transcript. Focused
gates are **7/7 Turn shielded** and **4/4 circuit wire/alias**.

This is a transitional weld, not the final PQ no-mint theorem. Note creation and
the live tree still commit the older modulo-field leaf, and the authoritative
conservation proof remains Ristretto/Pedersen/Bulletproof-based. The next exact
cut is a wide note/root format and one combined Lean AIR for membership and
conservation, followed by replacement of the classical acceptance leg.

## 10. What the fhIR optimizer proof does and does not say

The optimizer is an untrusted finder. Acceptance authority is the exact
certificate/checker path:

- `fhir/src/optimizer_protocol.rs` now makes the out-of-process worker boundary
  hostile by construction: the complete problem digest, solver manifest,
  session, nonce, certificate bytes, length, exact EOF, checksum, and replay id
  are bound before the existing checker and Cert-F authority are invoked. The
  focused protocol/checker target is **69/69 green**. A worker returning a valid
  certificate for a different problem, session, or solver context has supplied
  no authority.

- Market.SddPsd proves that an arbitrary finite rational SDD matrix with
  nonnegative diagonal is PSD. The exact checker constructs and verifies that
  witness. SDD is sufficient, not complete: the module includes a PSD rank-one
  matrix outside SDD.
- Rust ExactSddPsdCertificate is embedded in the compiled QP, rechecked at
  consumption, and bound bit-exactly to the backend's P matrix. Its strict wire
  family is FHSDD001.
- FHQPB001 joins the PSD admission with an exact KKT certificate and binds the
  complete public fixed-point problem (P,q,A,l,u).
- Exact-zero KKT plus the same admitted matrix proves global optimality for the
  bound convex QP. Market.QpExternalProgramBinding prevents reuse under a
  changed public field, including the dangerous same-P, different-q case.
- A positive tolerance is not exact optimality.
  Market.QpApproximateBound proves a quantitative objective-loss/feasibility
  bound only from the stated residual and displacement/radius assumptions. Rust
  connects its reported maximum residual coordinate-by-coordinate.
- The raid mechanic deliberately requires the zero-tolerance capability and a
  one-hot certified assignment. A valid positive-tolerance artifact cannot
  authorize the exact game allocation.

Residuals:

- source f64 to exact fixed-point scale refinement is not generally proved;
- a product using the positive-tolerance theorem must supply its own valid
  feasible-set radius or L1-displacement bound;
- SDD rejects some PSD matrices;
- wire checksums detect corruption but are not authentication;
- the broader fhIR Rust grammar is not wholly refined into Lean;
- the fixed clearing/raid claims are narrower than “the optimizer is proved.”

**metatheory/Market/FhIRRaidAllocationBinding.lean** is the game-facing
composition law. It binds the exact QP, ordered roster, one-copy assignment,
selected seat and actor, and recomputed objective. It proves feasibility and
global optimality through an explicit backend extraction premise and refuses
roster, P, q, reported-objective, and selected-actor substitutions. Direct gate:
**7 clean**.

## 11. Lean authority ledger

The aggregate command lake build Market is green at **8747 jobs** after adding
the live-host and optimizer/game modules. The immediately relevant direct gates
are:

- Market/DarkBazaarPrivateIngressCutover.lean — **11 clean**
- Market/DarkBazaarLiveApexHost.lean — **16 clean**
- Market/FhIRRaidAllocationBinding.lean — **7 clean**

Additional imported authority includes:

- Dregg2/Shielded/WideNativePqCommitment.lean — canonical 16-lane native PQ
  commitment and anti-aliasing laws;
- Market/PrivateBookBfvBindingAir.lean — exact fixed-shape BFV binding equations
  and extraction boundary;
- Market/PrivateBookEncryptionBinding.lean — exact opening law and detached
  encoding counterexample;
- Market/PartyMpcTransportBoundary.lean — authenticated transport does not
  imply arithmetic honesty;
- Market/SddPsd.lean — exact SDD-to-PSD theorem and incomplete-cone
  counterexample;
- Market/QpCertificateBundle.lean — same-matrix exact KKT composition;
- Market/QpExternalProgramBinding.lean — complete public-program binding; and
- Market/QpApproximateBound.lean — bounded-residual quantitative result, not
  exact optimality.

These modules make the missing premises visible. They do not prove the
Bulletproof implementation, BFV/DKG security, PartyMPC malicious security,
canonical wire decoding, GPU execution, or the complete Rust-to-Lean refinement
from first principles.

## 12. Exact captured verification ledger

### Green

- private_book_bfv_zk — **2/2 release green**; hostile proof test **65.765s**.
- private_bfv_attested_clearing — **1/1 release green**; **62.958s**.
- then-current private_book_relation + private_book_distributed_inputs —
  **8/8 green before later hardening**.
- custody-hardened private_book_distributed_inputs — **4/4 green**.
- private_book_distributed_prover — **2/2 green** for the fixture-backed
  process/custody envelope.
- fhegg_private_verifier_registry — **2/2 green**.
- party_mpc_crossing_transport — **2/2 release green**, **1.099s**.
- native PartyMPC PQ transport — **5/5 integration + 5/5 units green**;
  explicit unaudited test backend, so transcript/control-flow evidence only.
- native clearing quorum — **1/1 hostile native + 6/6 classical compatibility
  green**; the native authority transcript covers the complete canonical claim.
- private_clearing_apex_e2e — **1/1 full-stack integration green**, exact timed
  run **124.159s nextest / 124.116s internal**, under --profile full with
  DREGG_REQUIRE_LEAN=1 and DREGG_REQUIRE_PQ_CORES=1; no authority-core
  fallback. This verifies the required ML-KEM/ML-DSA cores, not end-to-end PQ.
- fhir_verified_raid_allocation — **6/6 release green**.
- hostile external fhIR optimizer protocol — **69/69 focused green**.
- private_clearing_crown_consequence — **1/1 heavy-release green**.
- dungeon_narrated_operation — **3/3 green**.
- relic_oath_branch — repaired target **2/2 green**.
- relic_raid_narrated_forest — **1/1 green**.
- dreggnet-surfaces private_raid — current test evidence is **7 prior greens +
  1 repaired focused-path green**; no single current 8/8 invocation captured.
- collective_gpu_additive — **1/1 green** on the real RX 6750 XT with
  GpuResident via wgpu/Vulkan.
- portable HidingFRI GPU — **2/2 exact parity green**, with the depth-2048 path
  measuring **1.306s GPU vs 3.072s CPU** and retaining six device blits.
- portable TFHE encrypted CMUX — **4/4 CPU/hostile + 2/2 strict GPU green**;
  quadratic external-product prototype, not PBS.
- wide shielded binding — **7/7 Turn + 4/4 circuit wire/alias green**; the old
  note/root and classical conservation leg remain.
- lake build Market — **8745 jobs green** before the final live-host/optimizer
  additions, then **8747 jobs green** afterward.
- direct Lean: private ingress **11 clean**, live apex host **16 clean**, fhIR
  raid allocation **7 clean**.

### Not green

- any earlier full-apex result that omitted the target because its manifest
  feature was absent — **not evidence**.
- No remaining handler-cutover archive residual: the exact strict ABI tooth and
  static symbol/U-minus-D audit are green. This does not alter the separate PQ
  identity-binding residual.

### Superseded or non-gate captures

- The earlier apex 1/1 in 63.951s with DREGG_ALLOW_UNAUDITED_PQ=1 remains useful
  semantic history but is superseded by the required-authority-core full-profile
  gate.
- The first current-source hbox invocation built Lean material but selected
  **0 tests** under the default profile because the heavy apex was excluded. It
  is not a test green.
- The prior relic-oath 0/2 LinkageBroken run and private-raid 7/8 chat replay red
  are repair history; their replacement focused gates are green.

### Pending composed-game gates

- private_raid_atomic_forest — 2 tests present; result pending.
- dungeon_chutes_weld — 3 tests present; result pending.
- native_descent_offering — 3 tests present; result pending.
- descent_campaign — 3 tests present; result pending.

## 13. Executable closure gates

These are the next truth-producing gates:

1. Recapture the full private-clearing apex with the native PQ quorum and native
   PartyMPC transport profiles installed together; their independent greens do
   not retroactively alter the older apex capture.
2. Capture the four still-pending composed-game targets in section 9; do not
   merge their counts or inherit greens from their organs.
3. If a single-invocation suite claim is needed for dreggnet-surfaces private
   raid, capture one current 8/8 run instead of collapsing 7 prior + 1 focused.
4. Replace the fixture-only distributed prover backend with a real distributed
   same-opening prover and make the apex consume it before revisiting any
   no-single-viewer language.
5. Add malicious arithmetic/share-formation and preprocessing evidence; signed,
   encrypted routing alone cannot satisfy LiveMpcBackend.sound.

Heavy Rust proof gates belong in the release-only nextest heavy profile and on
the build node. Lean stays local with the warm metatheory/.lake cache.
