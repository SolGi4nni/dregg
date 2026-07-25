# fhEgg maturity roadmap — current cut

*Rewritten 2026-07-22 at `6d0e024f19`. This is a capability and assurance
roadmap, not a calendar or cost estimate. Current implementation detail lives
in `HANDOFF-FHEGG-FEASIBILITY-CODEX.md`; the game/product view lives in
`THE-DARK-BAZAAR.md`.*

## 0. The ambition

fhEgg is the private-computation organ of Dregg:

> Evaluate a declared rule over hidden inputs, reveal only its permitted
> result, and leave a proof-carrying receipt that ordinary Dregg state and
> consensus can enact.

The mature system must simultaneously provide:

1. Lean-authored or Lean-refined semantics;
2. exact typed relation identity;
3. privacy from public observers and proof verifiers;
4. no single dealer, prover, custodian, or operator with the complete secret;
5. malicious and replay-safe distributed protocols;
6. durable atomic integration with cells, receipts, and finality; and
7. fast-enough portable execution, including WGPU where the complete operation
   benefits.

Passing one layer never silently grants the others.

## 1. Current maturity ledger

| Capability | Grade | Current truth |
|---|---|---|
| Plaintext uniform clearing and Cert-F | **WORKING** | Versioned Rust SDK/CLI, deterministic settlement, verification, fixed proof families, and allocation certificates exist. This carries no privacy claim. |
| fhIR product language | **WORKING / PARTIAL FORMAL CUTOVER** | Typed admission, explicit refusals, convex/direct-logic families, and several Lean-authored emitted relations exist. The whole Rust compiler/runtime is not yet covered by one Lean refinement. |
| Exact FNSP-v3 | **LIVE / NON-DARK** | HidingFRI acceptance, durable exact state, replay, finalizer selection, FRC1/CTM1, and private dependent wake are live. Public value/asset/nullifier coordinates make v3 exact continuity, not dark value. |
| Shared private-game rail | **LIVE / BOUNDED PRODUCT** | One authority-bound game spine serves web, Telegram, and Discord; public cards are viewer-blind; a private durable worker applies one exactly-once Dungeon consequence. |
| Exact fields and Descent census | **GATED SUBSTRATE** | V11 faithfully commits raw keys/full values; the fixed-eight HidingFRI census binds the exact fields root and declared writes through a canonical-v2 custom VK. It is not a general heap-aggregate proof. |
| Hidden-reserve Dark AMM | **RUNNING HOUSE-BLIND (SIMULATED) / UNREGISTERED** | `DarkPoolOffering` runs a full viewer-blind constant-product hall: `x·y=k` verified under an n-of-n collective key + n-of-n relin, n−1 refused, unfair swaps caught, oracle-validated vs `fhe.rs`. But the ceremony is SIMULATED in one process (not distributed), the offering is not in `CATALOG_KEYS` (surfaces only in tests), it is honest-party only (no active-malice proof), and the swap-*output* still needs division. |
| Whole-note shielded proof | **GATED SUBSTRATE** | FWS1 proves a hidden two-input/two-output swap with exact nullifier, conservation, output notes, and state endpoints. It is narrower than semantic v4. |
| Semantic shielded v4 | **BOUNDARY / OPEN LIVE AUTHORITY** | The no-clear-value 100-lane boundary and FXC4 shape exist. Full 19+27 same-witness proof, persistence, output-note mutation, selector, and committee finality remain. |
| No-single-viewer BFV/MPC | **RUNNING (SIMULATED, SEMI-HONEST) / DISTRIBUTION + ACTIVE-MALICE OPEN** | All four halls run house-blind under an n-of-n collective key (n−1 refused), with three security teeth RUNNING as witnesses of proved Lean theory: smudge floor (hiding), share binding, quorum necessity. The extension CAN hold a share (`fhe`→wasm32 confirmed 2026-07-25). Open: every ceremony is SIMULATED in one process (parties are threads, not clients); decrypt + relin are honest-party only (a party using its *wrong* secret is NOT caught — §3.2 VSS same-opening is proved in Lean but UNENFORCED in the running combine); the MPC crossing (`mpc.rs`) is semi-honest over a simulated dealer. Real distribution + active-malice robustness are the build. |
| Dealerless preprocessing | **SUBSTRATE** | FHTRI005 party-local candidate generation, beacon, MAC manifests, cross-term algebra, and one-use custody exist. Production stops at `AwaitingCrossTermProvider`. |
| Complete private BFV terminal | **PARTIAL / FAIL-CLOSED** | Exact carrier identities, root-order proofs, LogUp KATs, terminal binding theorem, and one fused private coordinate exist. The public unlinked terminal remains quarantined and the full N=4096 family is open. |
| Portable GPU | **WORKING KERNELS + MEASURED WINS / PARTIAL PIPELINE** | Exact WGPU BFV/TFHE/HidingFRI kernels + CPU differentials exist, and the compute-bound wins are now MEASURED bit-exact on real AMD (2026-07-24): the ct×ct multiply wins 3.35× (persvati iGPU) / 5.13× (hbox 6750 XT), the TFHE bootstrap crosses over at the deployed N=4096 (2.5–2.9×); the fold LOSES (memory-bound, run it on CPU). But no GPU BFV ct×ct exists yet (`bfv_gpu_mul` spec'd, unbuilt), so the halls run on CPU; not one resident schedule; not every path wins at small geometry. |
| Post-quantum end to end | **PARTIAL** | Hash/STARK/lattice/PQ-signature components exist. Classical Ristretto/Pedersen/Bulletproof and missing malicious-PQ distributed protocol seams prevent an “everything Dregg is PQ” claim. |

## 2. What crossed from research into system

### 2.1 Protocol consequence

The private result is no longer detached from the game:

- exact proof acceptance reaches ordinary block finality;
- FRC1 identities and typed terminal dispositions survive restart;
- private dependent turns enter through ordinary SignedTurn validation;
- finalized private Bazaar receipts feed a supervised durable worker;
- worker actions target signed, checkpoint-anchored character worlds; and
- all hosted surfaces consume one authority-bound game/session protocol.

This is the most important maturity transition of the sprint. The remaining
privacy work can now harden a real consequence path instead of a laboratory
demo.

### 2.2 Faithful commitments

The fields-root flag day removed a concrete mod-p source alias. Exact nullifier,
fields, heap, capability, note, and state commitments must continue to obey the
same law: committed source structure is encoded faithfully before any field
hash. A convenient one-felt fold is not identity.

### 2.3 Honest proof naming

The former “shielded exact apex v4” proof was renamed FWS1 because it proved a
narrower whole-note relation. A real smaller proof is valuable; a larger name
is not.

## 3. The five load-bearing closure programs

### 3.1 Full shared-witness v4

One relation must bind the hidden note opening, full nullifier, wide
value/asset commitment, BFV/TFHE market computation, all 19 Dark-AMM and 27
ring lanes, conservation/range facts, output notes, exact accumulator, and
outer before/after state. The accepted result must then install atomically and
finalize under signer-independent federation authority.

**Exit criterion:** substitution of any proof, opening, consequence, output
note, state endpoint, validator envelope, or predecessor refuses.

### 3.2 Trusted-dealer removal

Implement a malicious-secure PQ cross-term provider for the exact FHTRI005
`α_i · x_j` relation. Bind ordered parties, direction, roster, candidate
manifest, correlation profile, session, and one-use custody. Complete
authenticated q0 broadcast and prove same-opening between the live VSS and q0
commitments.

**Exit criterion:** no process sees both inputs; omission, direction swap,
chosen-input substitution, selective failure, replay, split view, and
recertification refuse or are attributable.

### 3.3 Distributed proving

HidingFRI hides named witnesses from the verifier. The apex needs
collaborative witness/proof production so no single prover reconstructs the
complete book, note opening, or game state.

The current research direction is a Dregg-owned share-native tensor-RS /
BaseFold-compatible backend beside—not blindly replacing—the Plonky3
HidingFRI differential reference.

**Exit criterion:** the selected worker threshold learns no witness, corrupt
partial folds are refused/attributed, and the public proof is
statement-equivalent to the monolithic reference.

### 3.4 Resident portable acceleration

Keep ciphertexts, transforms, comparisons, selection, and proof commitments on
device across the whole operation. Batch independent books/shares, fuse stages
where exact dataflow permits, and count uploads, dispatches, waits, and
readbacks.

**Exit criterion:** release-mode hbox measurements show an exact
residue-for-residue whole-operation win over CPU, with cold, warm, fallback,
and failure behavior.

### 3.5 Formal refinement through the host boundary

Lean should own product admission/denotation, descriptor identity, exact
arithmetic, commitment encodings, state-machine laws, and value-deciding
composition. Rust/WGPU should implement those relations behind strict
interpreters and exact differentials, not become a second unconnected spec.

**Exit criterion:** every value-deciding production path points to a named
semantic theorem, emitted typed relation, strict interpreter, and
differential/refinement gate; crypto/network assumptions remain explicit.

## 4. Product expansion after the apex

The shared private-game organ should grow from the current bounded Bazaar into:

1. hidden-reserve Dark-AMM swaps;
2. private shuffle/deal and hidden-hand legality;
3. guild/party voting and preference aggregation;
4. private matchmaking and raid formation;
5. sealed loot councils and DKP/need-greed allocation;
6. multilateral netting; and
7. confidential prediction/quest markets.

These mechanics should share identity, session epochs, viewer-blind receipts,
world cells, predicates, exact consequences, and finality. A new relation does
not require a new frontend-specific mini-engine.

## 5. What not to claim

- Hiding from the verifier is not hiding from the prover.
- Threshold-shaped code is not malicious security.
- Party-local contributions are not authenticated broadcast.
- A context digest is not a same-opening proof.
- A fixed public LogUp KAT is not a private runtime carrier.
- One fused BFV coordinate is not the full terminal family.
- Exact-v3 continuity is not dark value.
- A WGPU kernel is not a resident fhEgg pipeline.
- A Lean model beside Rust is not a proved Rust refinement.
- Classical Bulletproof/Ristretto acceleration is not post-quantum security.
- A committed WIP checkpoint is not a captured green.

## 6. Verification economy

Follow `AGENTS.md`:

- Lean stays local; `lake env lean Dregg2/Claims.lean` and registered lint
  gates are proof authority.
- Rust uses narrow `cargo nextest` targets.
- Proof-heavy work runs in release on persvati/hbox.
- Required-GPU tests identify the real adapter and compare exactly to CPU.
- Do not rerun the whole workspace to edit this roadmap.

The roadmap advances when a named boundary becomes both *true* and *consumed by
the next boundary*, not when the repository gains another isolated component.
