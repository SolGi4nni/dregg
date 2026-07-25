# fhEgg dark/fhe/mpc — the no-fakes + malicious-secure build roadmap (2026-07-25)

*Output of a 13-agent adversarial audit+design swarmcycle over the six dark/fhe/mpc components (keygen,
decrypt, relin, the MPC crossing, the same-opening apex binding, the distributed transport). Every claim is
grounded in code (file:line in the swarm transcript). This is the build plan for driving the crypto/protocol
suite to **no fakes + robust to active malice** — and the honest line on what genuinely cannot be finished.*

## The finishable line (state it plainly, to me and to ember)

**CAN reach no-fakes + malicious-secure-with-(identifiable)-abort NOW:** the **decryption path + its bindings**.
The exact ZK decrypt-share certificate + Ed25519 authenticated combiner + `InvalidDecryptShareProof{party}`
identifiable-abort **already RUN** in `threshold/quorum.rs` (t-of-n, verified on disk). So the fastest real
win is migrating the dark pool onto that already-running t-of-n stack (Build 10 fork), which subsumes most of
the n-of-n decrypt build AND adds dropout tolerance. This kills the top active-malice gap: the
**wrong-secret / retarget attack** that today returns `Ok(attacker-chosen slots)` SILENTLY and
UNATTRIBUTABLY becomes an `Err` attributed to a party. The ciphertext↔root equivocation closes now by pure
wiring of an already-machine-checked-but-DEAD Lean gadget (Build 3). The MPC online phase becomes
malicious-secure-with-abort by wiring the in-tree, already-tested SPDZ MAC through the AND gate + output reveal
(Build 7). keygen commit-then-open, relin detection, the Lean gates, and the real distributed transport + wasm
party are all tractable with **classical primitives already vendored in `quorum.rs`** (Ristretto/Bulletproofs/
Schnorr/Ed25519).

## Ordered builds (all tractable now)

| # | component | effort | what | unblocks |
|---|---|---|---|---|
| 1 | **shared/lean-gates** | med | Author the load-bearing Lean bound/relation gates (AIR-in-Lean rule): `KeygenNoise.lean` (`collective_key_decrypt_exact` + export `B_e`), `DarkBazaarShareValidity` RNS lift (over real RNS rows, not the scalar-ℤ toy), `Relin.lean` share relation + AIR. | every Rust range/well-formedness bound in keygen/decrypt/relin/apex/MPC. Rust never re-authors the relation. |
| 2 | **shared/rns-relation** | med | Factor the ℤ_p-Pedersen ↔ mod-q RLWE bridge out of `quorum.rs` into one audited `rns_relation.rs` (coeff-wise Pedersen, batched Schnorr, exact-RNS-quotient split, Bulletproof range). Already SOLVED+RUNNING for decrypt — just extract. | keygen ZK proof + decrypt/apex share-validity on the n-of-n path; keeps the delicate RNS-quotient point singly-audited. |
| 3 | **apex-binding (Piece B)** | med | Wire the proved-but-DEAD same-opening gadget: the non-imported ROOT runner (`Market.EmitSameOpeningGadget.emitMain`), regenerate the byte-pinned descriptor JSON, add `circuit-prove/src/same_opening_gadget.rs` (mirror `dark_bazaar_private.rs`), register an `InstalledVerifier` on `(session,root)`, cross-weld to `darkBazaarPrivateN4K4` via `RootCollision`. | closes ciphertext↔root equivocation on an already-machine-checked relation. **Highest security-per-effort; independent of 1-2.** |
| 4 ✅ | **relin (Tier 0) — DONE + ENFORCED** | **small** | Mandatory acceptance gate before caching any relin key: fresh trial products (`MulEngine::multiply`+relin → collective decrypt) must equal `m1*m2`; `RelinError::AcceptanceFailed`. No new crypto. **Landed `cd04bf34b0` (gate+`_verified`), enforced at `threshold_committee` `b9043e31c9`; test `relin_acceptance_gate.rs` 2✓.** | immediate fail-closed DETECTION of a silently-corrupt relin key. Stopgap (detection, not attribution); subsumed by 6. |
| 5 | **keygen** | large (Tier-0 ✅) | **Tier-0 detection DONE + ENFORCED** (`collective_key_acceptance_gate`, landed `1c99ff7c1f`, enforced at committee genesis `d879c5d5d3`; test `keygen_acceptance_gate.rs` 2✓) — a round-trip gate (encrypt→quorum-decrypt back to self) catches a malformed contribution fail-closed at genesis, closing gap A by DETECTION. **Full (attribution) remains:** bind each party's secret — extend `PublicKeyContribution` with a commitment to `s_i` + a ZK well-formedness proof bound to the CRP (`c0_i=-(a·s_i)+e_i`, `s_i` ternary, `‖e_i‖≤B_e`, PoK); commit-then-open over Ed25519 reliable/echo broadcast (reuse `AuthenticatedQuorumRoster`); CRP from a `joint_beacon` commit-reveal, not a unilateral OS seed. | the root of the whole share-binding chain (decrypt/relin/apex bind to the keygen commitment). Kills rogue-key/last-mover bias, equivocation, biased CRP, malformed shares — each attributable. |
| 6 | **decrypt (= apex Piece A)** | large | Port the decrypt-share validity certificate to the n-of-n path: `DecryptShareProof` (`h_i=s_i·c1+smudge` vs the keygen commitment; Bulletproof range on the ±2^80 smudge + RNS quotients + batched Schnorr), verified inside `combine` BEFORE the sum, `InvalidShareProof{party}`. Machinery RUNS today in `quorum.rs`. Classical-first for a running artifact. | **closes THE top active-malice decrypt gap** (wrong-secret/retarget → attributed Err). Malicious-secure decryption-with-identifiable-abort. Also closes apex share-equivocation + the MPC mask-holder gap (11). |
| 7 | **crossing (online)** | large | Wire the in-tree SPDZ GF(2^128) MAC (`authenticated_bits.rs`) through the ONLINE phase (today zero auth): add the one missing `add_public_constant`, authenticate every wire, route Beaver opens + p*/V* reveal through commit-reveal MAC-checked opens, batch into one `MACCheck` (challenge from `joint_beacon`), authenticated range-check on `reduce_mod_t`. `MaliciousAbort`. | crossing → malicious-secure-WITH-ABORT (deviation caught w.p. 1−2^−128). **CONDITIONAL** on authenticated triples + distributed α (see research). |
| 8 | **crossing (Lean AIR)** | med | Author the comparator/min/argmax + authenticated range-check circuit relation in Lean (the hand-written Rust `mpc.rs:268-509` is DEBT). | makes the MPC circuit a verified emitted object; prerequisite for any correctness theorem over the crossing. |
| 9 | **relin (Tier 1)** | large | Commit-and-prove binding every R1/R2 relin share to the keygen-committed `s_i` (NIZK on the exact fhe.rs relations). Needs fhe.rs field access (vendor/fork). Classical Ristretto route tractable; the PQ-lattice variant (BDLOP/LNP22/LaBRADOR) is borderline research. | malicious-secure relin key → correct ct×ct under active malice. Heaviest per-component lift. |
| 10 | **transport** | large | Make it RUNNING not SIMULATED: kill the single-root shared dealer (per-host custody root); build the authenticated network layer (mTLS/AKE `quorum_transport.rs` — does not exist); wasm32 extension-share party; persist combiner replay. **STRATEGIC FORK:** migrate the market onto the already-running t-of-n `quorum.rs` stack (inherits the certificate + identifiable abort + dropout tolerance) vs distributing the n-of-n path. | the gate between "malicious-secure algorithm in one process" and "malicious-secure running ceremony." |
| 11 | **crossing (BFV boundary)** | med | Run the DKG + decrypt-share certificate (5+6) over `distributed_bfv_correlation.rs` so no authority holds all masks. | removes the last trusted-viewer at the MPC↔FHE boundary. Rides on 5+6. |

**Suggested first wave (highest security-per-effort, least collision):** Build 4 (small, pure Rust, immediate
detection) → Build 3 (wire the dead apex gadget — closes equivocation) → Build 2 (extract the running bridge)
→ then the keygen/decrypt certificate stack (5,6) → transport migration (10). Builds 1/3/8 are Lean-authored
(AIR-in-Lean) and touch codex's active metatheory/circuit turf — **coordinate**.

## Genuine research — NOT tractable now, must never be claimed

1. **House-blind proof production** (share-native / collaborative proving). Every binding proof still needs
   SOME party to reconstruct the plaintext book to build the witness — the same-opening proof is honestly
   **Tier-1 VIEWER-FULL**. No-single-viewer *proving* needs collaborative code-based SNARKs / MPC-in-the-head
   over shares (ePrint 2026/729). The deepest open problem: the dark pool's *proof step* is not house-blind
   against a malicious prover, however good the decryption binding is.
2. **Dealer-free authenticated MPC triples at malicious security.** On disk: `mpc_distributed_mac.rs` uses a
   test-only ideal OT; `dealerless_preprocessing.rs` dead-ends at `AwaitingCrossTermProvider`. Needs a real
   malicious-secure PQ VOLE/OT (LogVOLE 2026/925, PQ-OPRF aVOLE 2026/533). Until then the MPC offline phase is
   SIMULATED and Build 7's soundness is CONDITIONAL on triples + a distributed α that do not yet exist.
3. **Full malicious-secure DKG (lattice shortness proof in the VSS setting).** No ZK proof that a dealer's
   hidden secret is ternary/CBD-short in the t-of-n VSS exists — secrecy rests on ≥1 honest dealer. (The
   n-of-n classical ternary Bulletproof is tractable-but-slow; the VSS-native lattice shortness proof is open.)
4. **Post-quantum INTEGRITY.** The route that RUNS (Ristretto/Bulletproofs/Schnorr/Ed25519) is classical
   discrete-log — a quantum adversary could forge a well-formedness/decryption/authenticity proof.
   CONFIDENTIALITY is already PQ (RLWE); INTEGRITY is not. PQ-correct routes are heavier / inherit the FRI floor.
5. **Robustness / guaranteed output / fairness.** n-of-n is security-WITH-ABORT only; the t-of-n path adds
   dropout tolerance + identifiable abort but NOT GOD. True robustness needs an honest-majority protocol. Never
   claim GOD for the n-of-n paths.
6. **The cryptographic floor stays UNDISCHARGED.** The Lean gates prove the RELATION/AIR (arithmetic over the
   emitted object); proof-SYSTEM soundness (FRI/STARK, M-SIS/M-LWE, Fiat-Shamir ROM, discrete-log) is an
   assumption, and the Bulletproofs/Schnorr/Ed25519 glue carries no machine-checked proof. **"It verifies on a
   box" is NOT verified.** A machine-checked malicious-security theorem over the emitted circuit is future work.
7. **Deployment-grade batched/compressed proving.** The certificates are CORRECTNESS-GRADE: tens of thousands
   of scalar witnesses per share at N=4096 × n parties. Known technique, unbuilt — and until a compressed
   proving path exists the ceremony stays SIMULATED-in-process at demo scale. **Honestly this gates the
   "running" claim for the whole malicious-secure stack even though the algorithm is sound.**
   **VERIFIED EMPIRICALLY 2026-07-25:** the running `quorum.rs` malicious-detection test
   (`vss_tests::authenticated_encrypted_orders_gate_real_game_asset_settlement_crypto_tooth`, which tampers
   `share.proof.relation_response[0]` and asserts `Err(InvalidDecryptShareProof{party})`) **exists and the
   detection logic is real**, but did NOT complete in ~10 min of release-mode execution — so the certificate's
   malicious-secure DECRYPTION is algorithmically DONE + in-tree, but is throughput-blocked at correctness
   grade. Conclusion for the build: migrating the halls onto `quorum.rs` (Build 6/10) buys real active-malice
   detection+attribution NOW, but "playable-fast" needs the batched-proving work — do the migration for
   correctness, schedule batched proving before claiming a running distributed ceremony.

## The one-line honest verdict
Active-malice robustness for the **decrypt + binding + keygen + relin + MPC-online** stack is **buildable now**
(identifiable-abort, classical-integrity, reusing running `quorum.rs` machinery) — a real, un-faked win. But
**house-blind proving, PQ integrity, dealer-free triples, GOD, the discharged floor, and throughput-grade
proving are genuine research** and must not be claimed. The game gauntlet exercises the buildable stack; those
six stay named open problems.
