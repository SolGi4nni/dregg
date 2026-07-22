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
The decisive current hbox run passed 1/1 under the full nextest profile with
both DREGG_REQUIRE_LEAN=1 and DREGG_REQUIRE_PQ_CORES=1 and no authority-core
fallback: 85.923s proof, 7.956s sealed PartyMPC crossing, and 167.008s internal
total.
The exact relation prover has since been accelerated without changing its proof
format or verifier: the fixed production relation now proves in **23.445s** in
its hostile standalone gate, about **3.66×** faster than that strict-apex
capture. A new full-apex timing has not yet replaced the 167.008s authority run.
The newer composed-game evidence has also advanced: the complete offerings
target is 117/117, the private-raid surface is 8/8 in one current invocation,
the narrated private-raid relic capstone is 1/1, the incarnation-bound common
game spine is 21/21, Telegram's combined game journey is 77 tests, and the viewer-safe web rail is
green at its exact focused gates. The lower private-raid forest is now 2/2 at
its focused engine gate; the Discord Chutes weld remains pending at this ledger
checkpoint.

This is **not** a no-single-viewer system. The deployed same-opening prover still
receives the complete private witness and BFV openings in one process; source
verification sees plaintext orders and encryption randomness; PartyMPC arithmetic
now refuses uncertified or malformed Beaver rows but still trusts the certifying
preprocessing authority; and the distributed-custody
surface now proves committed-share custody, the first three share-native linear
zero constraints, and owner-local kind/quantity ranges, 128-way one-hot
selection, nine-slot semantic message derivation, and all 12,288 BFV short
coefficients in `[-32,31]`, linked to the exact distributed commitments without
reconstructing the witness. The exact fhe.rs polynomial message-table/BFV
equations, Poseidon/root, and clearing constraints still run inside the
monolithic Bulletproof/R1CS backend.

This is also **not an end-to-end post-quantum apex**. Native clearing quorum and
PartyMPC transport now have separately green ML-DSA and ML-KEM-backed profiles,
and BFV is lattice-based. The sealed route-root replacement is now full-apex
green with six transport signs and six verifies rather than thousands of per-
frame operations. More importantly, the exact ciphertext/root relation is a
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
| Sealed native-PQ PartyMPC crossing | **GATED IN STRICT FULL APEX** | protocol teeth above plus strict full apex 1/1; 7.956s crossing vs v4 1,202.240s timeout, exactly six transport signs + six verifies independent of 1,302 gates |
| Certified PartyMPC preprocessing | **GATED, TRUSTED AUTHORITY** | mandatory hybrid `FHTRI003` binds exact Beaver rows/base session/batch under verified-core ML-DSA-65 + Ed25519 and the hosted verifier independently pins it; hostile 5/5 in 14.43s; generation remains trusted-dealer |
| Binary triple sacrifice | **STAGED, NOT LIVE MALICIOUS PREPROCESSING** | exact GF(2) 128-round committed-candidate sacrifice + Lean algebra, focused 6/6; executable lying-response tooth shows authenticated shares/MAC/ZK are still required before FHTRI003 integration |
| Native clearing quorum | **GATED** | full canonical ClearingClaim under roster-pinned ML-DSA + Ed25519: 1/1 hostile native gate; classical compatibility 6/6 |
| Cell-owned PQ turn identity | **GATED CLASSICAL RUNTIME; LEAN ROW GATED; COMPOSED PROOF PATH FAILS CLOSED** | runtime gates above plus Lean-authored 127-column rotation descriptor, exact 108-PI/120-constraint/111-range shape and Rust parse canary; outer ML-DSA composition remains unwired |
| Restartable live private-clearing apex | **GATED, NOT END-TO-END PQ** | strict v5 authority run 1/1 in 167.054s nextest / 167.008s internal; its proof was 85.923s, while the subsequently accelerated identical fixed relation is 23.445s in its hostile gate; sealed crossing 7.956s, audited Lean PQ cores required; exact relation still classical Bulletproof |
| Distributed input custody | **GATED** | custody/semantic/shortness private_book_distributed_inputs: 5/5 release green |
| Distributed private-order proof | **GATED THROUGH BOUNDED SHORTS + QUOTIENT CUSTODY** | base proof establishes share openings/root zero/order selectors/all 12,288 bounded BFV shorts; post-certificate phase commits, range-proves, shares, links, signs, and acknowledges 384 bounded RNS quotients per owner, 2/2 in 12.620s; exact quotient derivation and final worker equation remain |
| Distributed real same-opening prover | **OPEN** | no backend consumes shares to produce the apex Bulletproof/R1CS proof |
| Bazaar crown consequence | **GATED** | one both-polarity heavy-release test, 1/1 green |
| fhIR exact raid allocation | **GATED** | Rust integration 6/6 release green; FhIRRaidAllocationBinding: 7 clean |
| Narrated Dungeon and relic-oath composition | **GATED BY TARGET** | narrated Dungeon 3/3; repaired relic oath 2/2 |
| Common game-operation spine | **DURABLE EPOCH CUSTODY GATED FOR CATALOG + TELEGRAM** | bound routing 21/21; atomic/fsynced incarnation + monotone per-session generations 4/4; Telegram hostile epoch callbacks 2/2; web/Discord/WeChat/native migration remains |
| Telegram and viewer-safe web journey | **GATED BY TARGET** | Telegram combined 77 tests plus durable-epoch 2/2; web session rail 2/2 and no-viewer 2/2 |
| Private Bazaar → Dungeon consequence | **GATED AT FOCUSED PROOF/GAME PATH** | verifier-minted apex authority → exact winner-signed epoch-bound Mender turn; focused 2/2, real HidingFRI path 76.070s, HP 30→50/restart/replay teeth; full strict-apex recapture of the new block remains pending |
| Private-raid capability/Arena and narrated-relic composition | **GATED BY TARGET** | relic capstone 1/1; surface 8/8; lower atomic forest 2/2 (engine semantics only; its persvati fixture opted into the unaudited PQ test backend) |
| Chutes → Dungeon closed-command weld | **PENDING GATE** | HEAD target contains 3 tests; no result supplied |
| Lean-native Descent offering/campaign | **GATED** | both targets are green inside the current dreggnet-offerings 117/117 invocation |
| hbox build substrate | **QUALIFIED FOR GPU LANES** | current filesystem probe: 64GiB free after pruning four inactive, reconstructible build targets; active GPU/game/node/PQ lanes and deployed services were preserved |
| Collective GPU additive fold | **GATED** | 1/1 on real RX 6750 XT; GpuResident via wgpu/Vulkan, not HIP |
| Portable HidingFRI GPU path | **GATED** | exact CPU proof parity 2/2; retained LDE buffers through salted leaves; five Merkle commits materialize 77 layers in five whole-tree batches; 6 resident blits; GPU 0.717s vs CPU 3.081s at depth 2048 |
| Portable Ristretto verifier MSM | **GATED FOR CORRECTNESS, PERFORMANCE RED** | exact radix-16 Pippenger required-mode matrix 1/1 through 4096 terms; 4096 was 9.918ms CPU vs 7.508s GPU, so disabled by default |
| Portable encrypted TFHE PBS | **TRANSFORM-RESIDENT DENSE ENVELOPE GATED** | real encrypted 918-bit input, all 918 noisy GGSWs/nonzero rotations and all 919 tfhe-rs outputs; strict 1/1, 115.746ms warm transform GPU vs 422.847ms coefficient GPU / 1,380.391ms CPU; high-level integers/live clearing wiring remain |
| Exact BFV + wide PQ Lean boundaries | **FIRST NATIVE BFV SLICE LIVE; FULL FAMILY OPEN** | model checks all 98,304 equations; the first complete 4,096-term equation now has a real HidingFRI proof 1/1, while 98,303 slices remain; WideNativePqCommitment binds 16 canonical lanes |
| Wide shielded value binding | **GATED, TRANSITIONAL** | Turn shielded 7/7 and circuit wire/alias 4/4; live no-mint still retains the classical conservation proof and old note/root seam |
| Faithful wide note tree and history | **LIVE CREATE + LIVE HIDING SPEND + ATOMIC CUSTODY** | finalized create/history plus exact `(height, root8)` spend admission, real HidingFRI FNO2/FNC2/FNF2 membership/nullifier proof, durable exact nullifier records, successor root, receipt, and cursors; accumulator insertion is host-planned rather than recomputed in AIR |
| Hostile external fhIR optimizer protocol | **GATED** | fhir 69/69 and fhegg-solver 118/118; problem/session/nonce/manifest/certificate/checksum/replay bound; exact problem/KKT streams and typed zero-KKT authority borrows the single owned certificate without a dense clone |
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
protocol remains semi-honest. Its Beaver rows are now authority-certified and
globally checked, which closes the earlier unauthenticated malformed-triple
acceptance wound; it is not a distributed maliciously secure preprocessing
protocol and still has no proof of honest private-input share formation.

### Certified preprocessing boundary

**fhegg-fhe/src/mpc_party.rs** now hard-swaps certified custody to `FHTRI003`.
Before any multiplication gate consumes a row, the authority checks the exact
GF(2) Beaver relation and both ML-DSA-65 and Ed25519 sign the same canonical raw
statement: paired authority keys, exact salted row commitments/batch, base
session/circuit digest, roster size, and gate count. Keygen, sign, and verify
require the installed verified Lean cores even if `DREGG_ALLOW_UNAUDITED_PQ=1`
is set. The full canonical binding enters transport/KDF domains and the clearing
claim; the hosted verifier independently pins it across restart rather than
trusting a self-carried authority.

The archive-linked hostile target is **5/5 green in 14.43s**. It rejects row,
Ed-signature, ML-DSA-signature, v2 downgrade, relabel, context, batch, authority,
authenticated-frame, receipt, and replay substitutions, including explicit
unaudited-runtime refusal. This is mandatory hybrid authentication of audited
material, not malicious preprocessing: one trusted dealer still sees and
chooses every triple; input provenance, sacrifice/VSS/OT/VOLE/PCG, durable
rollback tombstones, and the SHA-256 commitment floor remain named.

The first additive sacrifice primitive now exists beside that trusted path but
is intentionally not wired into it. `mpc_party::sacrifice` commits exact
per-party GF(2) candidate rows before a post-commit beacon derives 128 challenge
bits per kept gate, reconstructs full-quorum rho/sigma openings and check
shares, and releases only an opaque verified batch. Lean proves
`check = r·error(kept) ⊕ error(sacrifice)`, honest completeness, both-challenge
detection, and the exact one-bit-per-round ceiling. The focused Rust target is
**6/6 green** and the Lean module/root build is green.

This is algebraic sacrifice under honest response computation, not a malicious-
MPC theorem. An executable hostile test shows that a lying check response can
cancel the public residual and force acceptance. Authenticated share responses,
MAC/ZK, one-time custody, durable replay treatment, and live `FHTRI003`
integration remain mandatory.

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
The pre-v5 exact-attribution rerun passed **1/1 in 124.159s nextest elapsed**
(**124.116s** on the test's internal timer) with the current-source Lean splice
and required verified ML-KEM/ML-DSA authority cores; no unaudited authority-core
fallback was enabled. The BFV same-opening proof, HidingFRI proof, live PartyMPC
crossing, hosted verifier reconstruction/restart, verified ML-DSA
turn-authority core, atomic consequence, and replay refusal all ran.

The current sealed-v5 recapture passed **1/1 in 167.054s nextest elapsed**
(**167.008s** internal) under the same strict Lean/PQ-core requirements and
unchanged 1200-second ceiling. Proof construction took **85.923s** and the
packed fold plus complete sealed PartyMPC crossing **7.956s**, versus the v4
per-frame-signature crossing's 1202.240-second timeout. The n=2 transport used
exactly six ML-DSA signs and six verifies independent of 1,302 gates; the two
quorum signatures were each checked in four composite verifier contexts.

The same proof format and verifier now have an exact host-parallel prover path.
Rayon schedules independent constant-time dalek commitment-MSM chunks, sibling
R1CS commitments, and inner-product rounds without changing transcript order or
group arithmetic. The production fixed-N hostile relation gate passed **1/1 in
64.631s**: proof construction was **23.445s** (23.074s inside R1CS), honest
verification was **8.213s**, and all four cryptographic substitutions plus two
structural substitutions still rejected. An independent 131,073-term exact MSM
differential measured **1.226s serial / 0.396s parallel** on 16 threads. This is
about **3.66×** faster than the 85.923s proof in the strict apex recapture; the
full strict apex has not yet been recaptured with this optimization.

That is a verification statement about the required authority cores, not an
end-to-end post-quantum claim. The apex still depends on the classical
Bulletproof/Ristretto/Pedersen
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

The exact host-parallel path has now taken the first large cut out of that
bottleneck. The portable WGPU public Pippenger remains disabled because its
measured group MSM is dramatically slower than dalek; the retained WGPU
scalar-preparation context is not presented as the source of the 3.66× result.

The Lean companion, DarkBazaarLiveApexHost.lean, models the weld from exact
ingress through same-opening evidence, live MPC output, claim, hosted verifier,
and consequence. Its 16 clean theorems do not discharge
LiveMpcBackend.sound; that premise is precisely where malicious arithmetic,
codec, and implementation refinement remain.

## 7. Custody and the no-single-viewer residual

### What the custody surface does

**fhegg-fhe/src/private_book_distributed_inputs.rs** lets four owners expand only
their own local witness vector: order kind, quantity, 128 option-selector
coordinates, nine semantic message coordinates, BFV u/e1/e2, and the owner-0
root blinding. Owners distribute n-of-n additive Ristretto shares to workers,
commit with vector Pedersen commitments, receive local packet
acknowledgements, and produce a canonical public certificate. Under the stated
confidential-channel and distinct-principal assumptions, any strict subset of
workers has uniformly masked shares under the CSPRNG/BLAKE3 scalar-sampling
assumption.

This layer assumes confidential authenticated private packet transport. Packets
deliberately have no production wire codec. The public certificate binds custody
events; it is not the R1CS proof and does not establish the same-opening
constraints.

**fhegg-fhe/src/private_book_distributed_prover.rs** adds worker-process and
coordinator APIs. The coordinator API never accepts scalar shares or openings.
The generic fixture backend still returns public digests only, but it is no
longer the strongest backend.

**fhegg-fhe/src/private_book_canonical_backend.rs** uses the owned Bulletproof
fork's logarithmic `LinearProof` to prove four exact committed-share openings
per worker. At degree 4096 each owner proof is 992 bytes rather than 12,436
opening scalars (12,435 vector coordinates plus the blinding). The same
artifacts prove the first share-native constraint
layer: for each owner 1..3, request-derived random coefficients compress the
eight root-blinding coordinates and the verifier checks that the workers'
committed linear images reconstruct to zero. The challenge is derived only
after the complete request, certificate, ordered commitment vector, roster,
worker/owner order, widths, and generator namespace are bound; prover nonces are
fresh CSPRNG output committed before that challenge.

Each owner certificate now also carries:

1. one four-value Bulletproof range proof over
   `[kind, 7-kind, quantity, 15-quantity]`;
2. one Bulletproof R1CS proof with 73,856 multiplication gates at production
   degree: 128 gates make the option coordinates boolean and exactly one-hot,
   select `16*kind + quantity`, and derive the private relation's eight unary
   demand/supply slots plus its injective `kind + 8*quantity` root-code slot;
   the other 73,728 gates range every `u/e1/e2` coefficient in `[-32,31]`; and
3. one transcript-derived random-linear `LinearProof` linking all 12,427
   non-root scalar commitments used by those proofs to the exact first 12,427
   coordinates of the same owner vector commitment whose worker commitments
   sum to it.

Thus the exact finite semantic order row is proved without disclosing it or
asking a worker/coordinator to reconstruct it. The batch link has
`1 / |Scalar|` random-linear-compression soundness error in the random-oracle
model. The proof digest is covered by the owner signature and the v4
session/deal/certificate domains. The strict per-owner artifact is 400,869
bytes at production width (8,293 bytes in the degree-16 fixture); the complete
four-owner/three-worker certificate is 1,605,710 bytes.
The commitments, proofs, and owner/worker signatures remain classical, not
post-quantum.

The banked v5 continuation (`fhegg-fhe/src/private_book_distributed_bfv.rs`)
starts only after that complete certificate and joint commitment. Its first
Fiat--Shamir challenge fixes 384 signed RNS quotient coordinates per owner.
Each owner supplies additive worker shares whose continuation-generator vector
commitments reconstruct to its owner commitment, proves every quotient in the
24-bit shifted interval with the conservative exact bound
`|q| ≤ 1,130,496`, and random-linearly links the R1CS commitments back to those
coordinates. The owner signature is verified before proof work, every worker
must acknowledge the private packet, and the public certificate contains no
shares. Production geometry is fixed at 16,384 coordinates per owner and
65,536 for the final worker proof. Focused release gates are **2/2 in 12.620s**.

This is custody/range/link, not yet the exact BFV proof. Quotients are currently
caller-supplied bounded integers. The shared exact `fhe.rs` coefficient API,
divisibility-derived quotient creation, second challenge, 65,536-coordinate
worker equation, canonical quotient wire, production relation-digest
constructor, Poseidon/root, clearing, sampler image, and PQ replacement remain.

### Exact test inventory

**fhegg-fhe/tests/private_book_relation.rs** currently contains:

- exact_bfv_rows_open_the_same_private_root_and_refuse_every_substitution
- metadata_slot_keeps_zero_quantity_side_and_limit_injective
- duplicate_bfv_randomness_is_refused_before_encryption
- packed_fold_consumes_the_exact_proof_rows_and_refuses_a_detached_shape
- authenticated_ingress_emits_the_exact_proof_ciphertext_not_a_second_encoding

**fhegg-fhe/tests/private_book_distributed_inputs.rs** currently contains:

- reused_rng_stream_is_session_separated_before_any_worker_sees_a_share
- every_semantic_option_row_is_exact_and_constraint_omissions_fail_closed
- all_local_openings_bind_one_public_certificate_without_reconstruction
- private_packet_equivocation_and_public_signature_forgery_fail_closed
- exact_production_layout_and_session_separation_are_pinned

The captured relation/distributed-input run was **8/8 green before later custody
hardening**. The current custody-hardened distributed-input target has now also
passed **5/5 release**, including the exhaustive 128-row semantic table and
deliberately malformed-but-well-shaped assignments for every load-bearing
selector/message/shortness constraint. HEAD has ten tests across the relation
and distributed-input targets; the captures cover the relation baseline and
the current five-test custody target without pretending they were one combined
invocation.

**fhegg-fhe/tests/private_book_distributed_prover.rs** contains:

- each_process_consumes_one_share_and_coordinator_sees_only_public_digests
- duplicate_missing_misbound_and_forged_worker_material_fail_closed

Captured result: **2/2 green**. This gates the process/custody envelope and its
fixture backend, not a real distributed Bulletproof/R1CS prover.

**fhegg-fhe/tests/private_book_canonical_backend.rs** exercises exact local
openings, rejection of arbitrary digests and cross-certificate reuse,
roster-signed corrupt-share proofs, and cross-worker/request/owner-order replay.
The canonical target passed **5/5 release in 0.359s**; the generic distributed
target passed **3/3 release in 0.236s** after the request-wire tooth was added.
With the selector/message/shortness layer, the three distributed targets passed
**13/13 release in 8.952s**. That run exercises the full production-width
73,856-gate owner proof, not only the reduced-degree fixture. Hostile cases
change canonical range and selector proof responses, recompute the artifact
checksum, and re-sign with the legitimate owner; verification still rejects
`OrderRangeProofRejected`. Valid selector proof bytes transplanted across
owners or ceremony requests also reject after checksum refresh and legitimate
re-signing. A forged owner signature rejects before any expensive proof
verification; the test-only verifier counter stays exactly zero.

### Exact residual before any no-single-viewer claim

A production distributed nonlinear backend must extend these same committed
shares from custody, linear constraints, owner ranges, finite semantic
selection, and bounded BFV shorts through the exact fhe.rs polynomial
message-table/BFV equations, Poseidon/root, and clearing relations. It must
then be used by the actual apex instead of prove_private_book_bfv_zk, whose API
receives the complete witness and openings.
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

Captured current result: **1/1 full-stack sealed-v5 integration green in
167.054s nextest / 167.008s internal** under the full profile with verified
ML-KEM/ML-DSA authority cores required and no fallback. This is not an end-to-
end post-quantum result: the exact same-opening proof remains classical, and
the game consequence is one-host atomic rather than distributed atomic commit.

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

### Private raid, party capability, Arena, and narrated relic — gated by target

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

- private_raid_atomic_forest — **2/2 GREEN** in one focused persvati invocation.
  That fixture uses `AuthRequired::None`; persvati lacked the verified ML-DSA
  archive, so the run explicitly set `DREGG_REQUIRE_LEAN=0` and
  `DREGG_ALLOW_UNAUDITED_PQ=1`. It qualifies the executor/HidingFRI/customVK/
  journal composition, not a strict PQ production runtime or distributed
  finality.
- dreggnet-surfaces private_raid — **8/8 GREEN** in one current feature-enabled
  invocation. The prior 310,767-byte proof replay failure is closed.
- relic_raid_narrated_forest — **1/1 GREEN**.

The already-green fhIR allocation checker and private-book apex remain separate
evidence.

### Durable game epochs and the first private-fhEgg game consequence

`dreggnet-catalog::GameEpochLedger` now owns a random host incarnation and a
monotone generation for each `(offering, session)`. Persistence is atomic and
fsynced; corruption fails closed; close/reopen advances the generation while an
exact process restart preserves incarnation, generation, state head, and valid
callbacks. The catalog gate is **4/4 green**. Production Telegram requires this
ledger plus its move-log store, encodes a 45-byte opaque digest of the complete
bound `GameActionRef`, and re-inspects the live bound view before execution. Its
hostile epoch gate is **2/2 green**. This is single-writer custody, not an
active/active lease system, and the other frontend adapters still need the same
migration.

The feature-gated private-fhEgg consequence accepts no caller-fabricated public
authority. It projects only from a verifier-minted native-PQ-quorum
`PrivateBfvLiveApexReceipt`, revalidates the atomic settlement audit, and binds
the exact verifier, claim/certificate/authority, root/session, roster,
settlement turn, sold asset, public winner/result, configured winner-to-game-key
route, epoch, action preimage, and current head. It then invokes the signed
common spine itself for one Warden's Keep raid-Mender recovery. The focused
release gate is **2/2 green**; the real HidingFRI raid path took **76.070s**,
landed HP **30→50**, survived durable restart, and refused wrong signer,
cross-incarnation substitution, and replay. Private order/opening/score/viewer
data never crosses this API.

The Bazaar asset settlement and later game turn are not one distributed
transaction. Deployments must durably record the authorization id after
success; the Keep's field and host signed-counter journal independently make
the concrete Mender action one-shot across the persistence window. The existing
strict-v5 apex remains the full-stack authority evidence, but its newly authored
game block has not yet completed a fresh strict recapture: that attempt stopped
before market code at a concurrent distributed-BFV test-cfg compile error. The
production feature itself passed its release check.

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

### Lean-native Descent offering and campaign — gated

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

Both targets are green inside the current **dreggnet-offerings 117/117** default
invocation. They remain distinct from the private-clearing apex, which transfers
a Descent loot asset, and from the fhIR raid-allocation target.

### Common session and frontend transport rail — gated with authority residuals

`dreggnet-catalog::game_spine` gives Dungeon, Descent, private raid, and Bazaar
operations one resumable descriptor/receipt shape. It binds the exact session,
actor, operation, payload, prior head, result, and successor head, rechecks the
operation descriptor/capability, and preflights replay material. The later
authority-bound route additionally carries a nonzero host/federation
incarnation and monotone session generation through action preimages and outer
receipts. Cross-incarnation replay, close/reopen generation rollback, and
receipt/session substitution refuse; same-incarnation restart replay remains
exact. The expanded hostile target is **21/21**. `dreggnet-telegram` carries the same game journeys, including
the canonical private-raid proof through Telegram's document/getFile path; its
combined current evidence is **77 tests**. The web session rail and reviewed
no-viewer projection are **2/2 + 2/2**.

These are coherent routing/presentation and replay boundaries, not actor
authentication. Current chat actor values are asserted, the presentation head
is not the canonical ledger root, and the consequence book is process-local.
Deployment custody and monotone allocation of the new incarnation/generation
values remain external; existing Telegram/web callers are explicitly
`LegacyUnbound` until migrated. Discord's direct binary path is being moved to
the same durable journal rather than promoted from its current in-memory/stamp-
only behavior.

### hbox and artifact custody — operational facts, not build evidence

Current hbox ground truth:

- Intel i9-12900, 24 hardware threads;
- 123 GiB RAM;
- AMD RX 6750 XT visible through Vulkan;
- no ROCm/HIP installation; and
- **86 GiB free** on the filesystem used for the work at the latest direct
  probe. Four inactive, reconstructible build-lane copies were removed; the
  current GPU lane, games deployment, private node, and service binaries were
  preserved.

The hbox required-authority-core apex gate above and the collective GPU fold
below are now successful
execution evidence. Keep ordinary Rust CPU gates on persvati for cache and
contention economy; hbox now has enough headroom for the GPU-specific gates it
is meant to run.

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
- the current Bulletproof fork now has a complete portable public-scalar
  verifier mega-MSM path as well as the extended-Edwards group-add tooth. Its
  exact radix-16 Pippenger follow-up uses 64 windows, four ordered dispatches,
  and one readback and passed the required-mode 17/256/1024/4096 matrix plus a
  real R1CS verification. Dalek independently recomputes the returned point.
  This remains a performance red: at 4096 terms CPU was **9.918ms** and GPU
  **7.508s**, with roughly 103–120s process-cold shader compilation. The backend
  therefore remains disabled by default. In every case this only accelerates
  the transitional classical Bulletproof proof.

The HidingFRI GPU path now retains LDE buffers device-to-device through salted
leaf construction and keeps every Merkle digest layer resident until the root
is complete. At depth 2048 it produced the exact CPU proof with six resident
blits; five Merkle commits materialized 77 opening layers in exactly five
whole-tree readback batches, and measured **0.717s GPU vs 3.081s CPU**. The FRI
query/fold phase still consumes the materialized host tree, so this is not full
proof residency. The TFHE path also has a portable
encrypted CMUX/external-product implementation with signed gadget decomposition
and an exact four-prime (~120-bit) RNS NTT. Portable WGSL performs exact
16-bit-split Montgomery arithmetic; the forced coefficient/NTT matrix through
N=4096 and a hostile base-log-31/two-level case passed **3/3**. At N=2048 the
warm medians were **2.401ms CPU / 4.160ms quadratic GPU / 2.721ms NTT GPU**; at
N=4096 exact NTT was **4.816ms GPU vs 10.052ms CPU**. The next exact rung keeps
two accumulators and a coefficient-domain standard BSK resident across one
dependent blind-rotation chain: native modulus switch, LUT/monomial rotation,
signed gadget decomposition, and four noisy GGSW selector steps use one command
submission and one final readback. The combined N=2048 strict hbox suite passed
**4/4** against an independent tfhe-rs oracle and decrypted semantic check;
warm GPU was **2.865ms vs 5.914ms CPU** (71.087ms cold). The next PBS-shaped
path continues in the same submission through exact degree-zero GLWE sample
extraction and a standard native-torus LWE key switch, with one final
post-key-switch LWE readback. The strict independent-tfhe-rs combined target
passed **5/5**. At N=2048, GLWE size 2, full 2048-coordinate extracted input,
and an 8-coordinate output, retained-context first execution was 57.652ms and
the warm GPU path was **4.673ms vs 5.763ms CPU**; the standalone warm median was
**6.474ms vs 13.377ms CPU**. A prepared plan owns the full envelope's actual
memory and addressing geometry: all 918 input-mask slots, a 57.38 MiB standard
BSK, the exact 2048→918 standard key switch with a 57.44 MiB KSK, and all 919
output coefficients. Its dense deployed gate now uses a real encrypted input
under a generated 918-bit LWE secret, a noisy GGSW for every BSK bit, and
rejection-samples until every modulus-switched mask rotation is nonzero. The
strict hbox target passed **1/1**; one-time plan/upload was **125.152ms**, first
dense execution **449.309ms**, and the three-sample warm median **421.617ms**
versus **1,493.795ms CPU**. All 919 outputs equal tfhe-rs; the far BSK slot is
load-bearing, host mutation cannot change the uploaded plan, and a 917-slot mask
is refused. The complete 1,836-dispatch command exceeds the deployed Vulkan
command/descriptor allocation, so the exact route submits at most 256 ordered
CMUX steps at a time while both accumulators, scratch, BSK, and KSK remain
device-resident and only the final LWE is read back. This is the honest linear
coefficient-domain baseline. Transform-form accumulator/BSK residency remains
the next performance cut, followed by high-level integer integration.

Lean arithmetic specifications for the BFV NTT and TFHE torus MAC are
axiom-clean; they specify arithmetic/refinement boundaries, not hardware
execution. `Dregg2.Circuit.TfhePbsRefinement` now additionally fixes the exact
native-torus GLWE/LWE semantics, degree-zero extraction signs, subtractive key
switch, fail-closed shape, and narrow plus 918×918 production coefficient
geometry. Its composed WGPU theorem requires an explicit external
implementation-equality premise; WGSL buffers, limbs, and dispatch are not
silently declared verified. Frozen details live in `FHEGG-WGPU-VALIDATION-MATRIX.md`,
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

The model boundary now has its first executable native-field member.
`Market.PrivateBookBfvSliceDescriptor` proves one complete 4,096-term
negacyclic equation—order 0, ciphertext polynomial 0, RNS modulus 0,
coefficient 0—together with the same hidden Dark Bazaar order/root relation and
an eight-lane commitment to all 4,096 ordered public-key coefficients. It is
not a random scalar projection. The real `fhe.rs` message-table differential is
**128/128 green**; the real HidingFRI proof/serialization/verification hostile
gate is **1/1 green in 22.414s** and rejects wrong key, ciphertext, and private
root. The checked 394,129-byte artifact has SHA-256
`459fa946690540ef0142c5feba0f8d03c1ace116ec3e42bca3c9b6b6a7b8526f`.
The remaining 98,303 exact equations are still open, so this first slice is not
accepted as a complete BFV opening or a replacement for the classical apex.

The Rust `ShieldedInputPayload` now carries a mandatory 16-lane wide value
binding plus its hiding proof. The effect hash binds every lane, and executor
admission verifies both the existing spend/conservation evidence and the wide
proof before absorbing those lanes into the conservation transcript. Focused
gates are **7/7 Turn shielded** and **4/4 circuit wire/alias**.

The faithful note-tree substrate now exists beside that value binding.
`Dregg2.Circuit.CommitmentTreeWide` proves that the exact 32-byte → sixteen-u16
codec has a left inverse and is injective, defines the KAT-real domain-separated
eight-lane Poseidon2 leaf/node/root and fail-closed 4-ary membership semantics,
and pins Lean-computed protocol vectors. The Rust tree and persistence wrapper
match those vectors **8/8**, `dregg-commit` is **141/141**, and the focused
persistence recovery/hostile target is **6/6**. The legacy and faithful trees
advance together during the transition. A strict authenticated history now
also binds exact session/federation/epoch, predecessor/successor faithful roots,
height, note count, and block id; hybrid Ed25519-and-ML-DSA verification plus
restart/replay/fork/truncation teeth are **6/6**.

The live finalization path now reconstructs all nested `NoteCreate` leaves,
advances the faithful tree, plans and hybrid-signs the exact successor edge, and
commits the finalized record/indexes, receipt, leaves, authenticated history
edge, exact eight-felt `StoredAttestedRoot`, and cursors in one redb
transaction. The node signs/publishes only after that transaction succeeds;
restart rebuilds the depth-16 tree and replays the authenticated history.
Forks, truncations, mismatched roots, unauthenticated records, and legacy scalar
aliases fail closed. The spend-side custody cut now adds a strict versioned
`FNSP` carrier for a bounded proof and historical `u64` height, replays the
hybrid-authenticated root history, and requires the exact `(height, root8)`
pair. Finalized commit, note leaves, exact `(nullifier, value, sequence)`
records, receipt, faithful history, attested roots, and cursors share one redb
transaction; duplicate/replayed nullifiers and wrong successor roots fail
before mutation, and restart seeds the executor from the durable records. Lean
proves refusal is state identity and success publishes exactly the persisted
successor root.

The faithful `NoteSpend` proof is now composed and live (`6cd2ddca2`). The
Lean-authored `faithful-note-spend-v2` relation uses the complete 16-lane
Poseidon2 bus and checks exact FNO2 spending-key-to-owner-address, FNC2 note
commitment, faithful depth-16 membership, and FNF2 nullifier derivation. Owner
address, spending key, nonce, randomness, leaf, position, and Merkle path remain
hidden; height, historical root8, nullifier, value, asset, and successor root8
are public. The 96,535-byte checked artifact has 1,623 main columns, 44 public
inputs, 393 constraints, and four tables. Its real HidingFRI hostile gate is
**1/1 green** (0.76s after build), and the production executor installs the
strict verifier without a legacy/non-hiding fallback.

This is still not the final PQ no-mint theorem. The circuit binds the planned
successor root but does not recompute accumulator insertion in AIR; the
deployed nullifier root still folds the nullifier to one felt, and value/asset
are public. The authoritative conservation proof remains
Ristretto/Pedersen/Bulletproof-based. Solo-mode already-applied finalization,
committee rollover, and O(all-leaves) recovery also remain.

### Cell-owned PQ identity and rotation

`Cell` now commits an ML-DSA-65 public-key commitment plus a dedicated monotone
key epoch. `CreateHybridCell` is sponsor-mediated but requires epoch-zero
new-key possession; `RotatePqIdentity` must be authorized by the current hybrid
identity and separately proves possession by the next key. The canonical cell
commitment and all faithful authority-digest lanes move on install/rotation,
the journal restores the exact prior anchor on failure, restart preserves it,
and SignedTurn admission treats the carried ML-DSA bytes only as an opening of
the live committed anchor. A host registry exists only as an independently
configured pre-v10 migration bridge and never learns from the envelope.

Exact gates: create/rotate/hostile later-effect rollback **1/1**; node restart
**1/1**; enrollment/no-TOFU/substitution **3/3**; hostile SignedTurn validator
**4/4**; cell identity/commitment/wire **3/3**; Rust registry **3/3 + 1/1** and
Lean registry green. Both proof producer and verifier projection explicitly
refuse these effects **3/3** because the PQ-authority row is not yet composed
with its outer cryptographic boundary; they are committed classical-runtime
transitions, never a silent `NoOp`. The Lean-authored rotation descriptor now
exists and is gated: it losslessly carries every 32-byte object as sixteen
canonical u16 limbs, every epoch as four limbs, and proves exact target/
expected-epoch continuity, overflow-free +1, and key change over a 127-column,
108-public-input row. ML-DSA authorization and new-key possession remain
explicit outer predicates, not a prover-chosen verified bit.
Pre-v10 postcard snapshots need a store migration, and unknown agents cannot
self-admit their first outer SignedTurn without a sponsor.

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
- custody-and-shortness-hardened private_book_distributed_inputs — **5/5
  release green**, including all 128 valid semantic rows and explicit omitted-
  constraint witnesses.
- private_book_distributed_prover — generic request/envelope **3/3 release
  green**; canonical committed-share backend **5/5 release green** with four
  opening PoKs and three share-native linear constraints per worker; owner
  range/selector/message/shortness/link layer brings the combined distributed
  targets to **13/13 release green in 8.952s**, including the production-width
  73,856-gate proof. Exact fhe.rs polynomial opening, Poseidon, clearing, and
  live apex proof generation remain monolithic.
- fhegg_private_verifier_registry — **2/2 green**.
- party_mpc_crossing_transport — **2/2 release green**, **1.099s**.
- native PartyMPC PQ transport — **5/5 integration + 5/5 units green**;
  explicit unaudited test backend, so transcript/control-flow evidence only.
- sealed native-PQ PartyMPC crossing — small full crossing/token/barrier hostile
  **1/1**, route asymmetry + coordinator-key-alias **2/2**, strict claim-source
  **1/1**, typed-apex structural build green, and strict full apex **1/1**.
- native clearing quorum — **1/1 hostile native + 6/6 classical compatibility
  green**; the native authority transcript covers the complete canonical claim.
- private_clearing_apex_e2e — **1/1 strict v5 full-stack integration green**,
  **167.054s nextest / 167.008s internal**, including 85.923s classical proof
  and 7.956s sealed crossing; DREGG_REQUIRE_LEAN=1 and
  DREGG_REQUIRE_PQ_CORES=1, unaudited fallback unset. This requires the real
  ML-KEM/ML-DSA cores, not end-to-end PQ.
- accelerated fixed-N private-book relation — **1/1 hostile green in 64.631s**;
  proof **23.445s**, honest verify **8.213s**, exact 131,073-term commitment MSM
  **1.226s serial / 0.396s parallel**. Same proof/verifier; full strict-apex
  timing not yet recaptured.
- fhir_verified_raid_allocation — **6/6 release green**.
- hostile external fhIR optimizer protocol — **69/69 fhir + 118/118
  fhegg-solver green**; streamed problem binding is zero-allocation at the
  comparison boundary; exact KKT `Ax` revalidation is also zero-allocation and
  preserves hostile lift-error/overflow precedence. The typed exact-zero view
  borrows the bundle-owned certificate, eliminating the 2,117,632-byte dense
  clone measured at n=256.
- private_clearing_crown_consequence — **1/1 heavy-release green**.
- dungeon_narrated_operation — **3/3 green**.
- relic_oath_branch — repaired target **2/2 green**.
- relic_raid_narrated_forest — **1/1 green**.
- dreggnet-surfaces private_raid — **8/8 green** in one current feature-enabled
  invocation.
- dreggnet-offerings — **117/117 green**, including native Descent/campaign and
  typed private-game consequences.
- incarnation-bound common game spine — **21/21 green**; Telegram combined journey **77 tests**;
  web session/no-viewer rails **2/2 + 2/2**.
- collective_gpu_additive — **1/1 green** on the real RX 6750 XT with
  GpuResident via wgpu/Vulkan.
- portable HidingFRI GPU — **2/2 exact parity green**, with the depth-2048 path
  measuring **0.717s GPU vs 3.081s CPU**, retaining six device blits, and
  reducing five Merkle trees to five whole-tree readback batches.
- portable Ristretto verifier MSM — exact radix-16 Pippenger required-mode
  matrix **1/1 green** with dalek authority through 4096 terms; 4096-term GPU
  is 7.508s versus 9.918ms CPU and therefore disabled by default.
- portable TFHE encrypted PBS — exact coefficient/RNS-NTT and
  four-selector device-resident blind rotation combined strict GPU **4/4**,
  exact extraction/key-switch combined strict GPU **5/5**, and the genuine
  dense 918-CMUX deployed envelope **1/1**; all 919 outputs match tfhe-rs and
  transform-resident warm GPU was **115.746ms** versus **422.847ms** coefficient
  GPU and **1,380.391ms CPU**. High-level integers/live clearing wiring remain.
- wide shielded binding — **7/7 Turn + 4/4 circuit wire/alias green**; the old
  note/root and classical conservation leg remain.
- native exact-BFV HidingFRI slice — exact 4,096-term coefficient equation plus
  the same hidden order/root relation **1/1 green in 22.414s**; real encoder
  table **128/128**; 98,303 production equations remain.
- faithful wide note tree/history — Lean authority green, Rust correspondence
  **8/8**, dregg-commit **141/141**, tree persistence **6/6**, authenticated
  history **6/6**; live finalized `NoteCreate` leaves, history edge, exact
  eight-felt attestation, receipt, and cursors commit atomically. Historical
  `(height,root8)` admission and exact nullifier/value/sequence plus successor
  persistence are atomic. The new faithful IR2 relation and strict production
  verifier produce/verify a real HidingFRI proof **1/1** while hiding owner,
  key, nonce, randomness, leaf, position, and path; accumulator insertion is
  still host-computed and public value/asset are an explicit boundary.
- cell-owned PQ identity — create/rotate/rollback **1/1**, restart **1/1**,
  enrollment/substitution **3/3**, SignedTurn hostile **4/4**, cell wire/
  commitment **3/3**, EffectVM fail-closed refusal **3/3**; Lean-authored
  rotation authority row and Rust parser canary green, outer ML-DSA composition
  still absent.
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

- dungeon_chutes_weld — 3 tests present; result pending.

## 13. Executable closure gates

These are the next truth-producing gates:

1. Capture the still-pending Discord Chutes→Dungeon target in section 9; do
   not inherit a green from its Dungeon/narrator organs.
2. Extend the committed-share backend beyond its opening PoKs, first linear
   constraints, owner ranges, finite semantic selectors, and bounded BFV
   shorts through exact fhe.rs polynomial opening/BFV, Poseidon/root, and
   clearing. Reuse the live exact native-field slice, materialize or prove the
   other 98,303 equations, then make the apex consume the family before
   revisiting any no-single-viewer language.
3. Compose the staged 128-round binary sacrifice with authenticated response
   shares/MAC-or-ZK and one-time custody, then replace trusted-authority Beaver
   generation and add private-input share-formation evidence. Signed, encrypted
   routing alone cannot satisfy LiveMpcBackend.sound.
4. Move successor-nullifier accumulator insertion and conservation authority
   into the now-live faithful hidden-spend relation, then widen the deployed
   one-felt nullifier root. Separately compose the landed PQ-identity AIR row
   with both outer ML-DSA predicates before removing either proof-path refusal.

Heavy Rust proof gates belong in the release-only nextest heavy profile and on
the build node. Lean stays local with the warm metatheory/.lake cache.
