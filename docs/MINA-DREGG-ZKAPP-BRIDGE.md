# Mina ↔ dregg: a mutually-proof-based bridge across two proof systems — feasibility + PoC

*Research / feasibility, 2026-07-27. Two proof systems that verify each other are rare, and rarer
still ACROSS families. This maps what is actually buildable between **Mina** (Kimchi/Pickles over
the Pasta cycle, IPA polynomial commitments) and **dregg** (BabyBear FRI-STARK, wrapped to a gnark
Groth16 on BN254). It states each direction at its CURRENT resolution — what is a real
proof-checking-a-proof, what is a hash attestation, and what is out of reach — and ships a runnable
PoC of the minimal real mutual step.*

---

## 0. Verdict up front

| Direction | What it would be | Status TODAY |
|---|---|---|
| **1. dregg verifies Mina** | a Lean-authored Kimchi verifier checks a real Mina proof | **mostly built** — checks a real Kimchi proof's arithmetic over the real Pasta field, non-vacuously, **modulo 3 named crypto carriers**. A real (partial) proof-checking-a-proof. |
| **2. Mina verifies dregg** (the hard, novel one) | a Mina zkApp verifies dregg's proof in-circuit | **infeasible in-circuit today** — dregg's proof is a **BN254 Groth16**; Kimchi has **no pairing gate**, and emulating one blows past the 2^16-row step ceiling by orders of magnitude. |
| **Tractable mutual step** | a Mina zkApp verifies a dregg **Poseidon-over-Pasta attestation** | **BUILT + RUN here** (PoC §6). Native Poseidon (11 rows/perm); the Rust and o1js hashers agree bit-for-bit. |

So the honest shape of a Mina↔dregg bridge that is buildable now is **asymmetric**: direction 1 is a
real (incomplete) proof-check; direction 2 is a hash-attestation, not yet a proof-check. A *symmetric*
mutual-proof bridge needs one of two heavy lifts (§5). "Mutually-proof-based across proof systems"
is reachable, but only direction 1 is a proof-check today; direction 2's proof-check is future work
with a named, non-vacuous path.

Everything below is at current resolution. Where a prior plan claimed more, that is flagged as a
**dead premise** (§4) — the Pasta-native dregg proving path it rested on was deleted as vacuous.

---

## 1. Direction 1 — dregg verifies Mina (mostly built, in Lean)

dregg already carries a **Lean-authored Kimchi/Mina verifier**, built check-by-check against
o1-labs `proof-systems` v0.7.0 (`36a8b510`). This is the House Law path: the verify decision is
EMITTED from Lean, Rust only calls it.

**The gadget floor (K1–K4), `metatheory/Dregg2/Circuit/Emit/`:**
- `PastaField.lean` — forced Fp/Fq arithmetic (the 255-bit Pasta 2-cycle).
- `PastaCurve.lean` / `PastaCurveComplete.lean` — Pallas/Vesta point ops + the unified RCB add.
- `PastaPoseidon.lean` — the Fiat–Shamir transcript sponge (`perm_forces`), KAT'd exact to o1js.
- `PastaScalarMul.lean` — the forced `[k]P` ladder + endomorphism.
- `PastaIPA.lean` — the IPA-opening DEFERRAL + the `sVec_eq_bPoly` soundness identity.

**The verify assembly (K5), `KimchiVerify.lean`:** composes the o1-labs verifier's checks in
verifier order (`oracles → to_batch → OpeningProof::verify`): C1 shape, C3 transcript order,
C4 public eval, C5 `ft(ζ)` / permutation, C6 linearization (generic gate emitted; custom gates a
carrier), C7 Maller `ft_comm`, C8 `combined_inner_product`, C9 IPA deferral.

**The reality gate, `KimchiRealProofGate.lean`** (+ `docs/MINA-REALITY-GATE.md`): a **real** Kimchi
proof (real prover, real SRS, ACCEPTED by o1-labs' own `kimchi::verifier::verify`, dumped to
`metatheory/kimchi_real_proof.json`) is run through the shipped formulas. Result: `kimchiVerifyDecisionField`
accepts over the real Pasta scalar field `ZMod pN` — C1 (shape) ∧ C8 (`cip = combinedInnerProduct`)
∧ a witnessed inverse ∧ C5 (`ft_eval0`) — and **every single tamper rejects**. Axiom-clean, no
`native_decide`.

**The honest boundary (what it does NOT do):** it does not *verify Mina*. Three named crypto carriers
remain: **C3** phase-2 Fr-sponge values, **C6** custom-gate token streams, **C9** the IPA `msm==0`
opening check (the terminal FRI/IPA soundness floor, inherited not discharged), plus C4's `p(ζ)` fed
as an input and C7's commitment-side MSM. Precisely: *the decision checks a real proof's arithmetic
over the real field, modulo those carriers.* This is a genuine, non-vacuous proof-checking-a-proof at
that resolution — the strong half of the mutual bridge.

**State-query (K6), `MinaStateQuery.lean`:** on top of a verified Mina ledger root, a **Poseidon
Merkle path** into an account/zkApp-state field (`merkleFold`, `leafHash_commits_balance/_nonce/_zkappRoot`).
SOURCED from the real Mina account structure (`~/dev/mina` `mina_base/account.ml`, `ledger_hash.ml`,
`hash_prefixes.ml`). `mina_verify_then_query` states the seam: (K5) verify-root ∘ (K6) query-under-root.
This is what makes Mina a **dregg light client** — the internet-of-proofs bet.

---

## 2. Direction 2 — Mina verifies dregg (the hard direction): what dregg actually emits

To verify dregg on Mina you must verify the artifact dregg actually produces. It is **not** a
Pasta/Pickles proof. The pipeline (`circuit-prove/`):

1. **Inner** — BabyBear STARK, Plonky3-style FRI, hashed with **Poseidon2-over-BabyBear**
   (`plonky3_recursion_impl.rs`); turn chain folded to an apex (`ivc_turn_chain.rs`, `apex_shrink.rs`).
2. **Outer "shrink" STARK** — `dregg_outer_config.rs` (`DreggOuterConfig`): trace arithmetic stays
   BabyBear, but the transcript/Merkle hash switches to **Poseidon2-over-BN254** (t=3, α=5, R_F=8,
   R_P=56) so the final SNARK hashes natively (the measured ~40.9M → ~1.0M R1CS collapse). dregg's
   analogue of RISC0 `identity_p254` / SP1 `shrink`.
3. **Final wrap = gnark Groth16 on BN254** — the shrink proof is verified inside a gnark circuit
   (`chain/gnark/settlement_circuit.go`, ~12.2M R1CS over BN254), Groth16-proven (`chain/gnark/groth16_cache.go`:
   `groth16.Setup`, `ecc.BN254`). On EVM it is consumed by `chain/contracts/DreggGroth16Verifier25.sol`
   — an explicit BN254 verifier using the **alt_bn128 pairing precompile `0x08`** over 25 BabyBear
   public inputs, gated by `DreggSettlement.sol`'s continuity/monotonicity state machine.

The dregg **state root** itself (`genesis_root`/`final_root`, 8 lanes) is a **Poseidon2-over-BabyBear**
commitment (`ivc_turn_chain.rs`), and `chain_digest` is a Poseidon2-BabyBear sponge. So there are
**three hashes in play, none of them Mina-Poseidon**: canonical state = Poseidon2-BabyBear; proof
transport = Poseidon2-BN254; EVM index = keccak.

### Why in-circuit verification on Mina is infeasible today

Ground truth from `~/dev/mina` (Pickles) and `~/dev/proof-systems` (Kimchi):

- **Budget.** One o1js `@method` compiles to one Pickles **step** circuit = **2^16 = 65,536 rows**
  (`mina/src/lib/pickles/common.ml`, `kimchi_pasta_basic.ml`: `Step = Nat.N16`), 15 columns/row. Wrap
  = 2^15. Pickles does **not** chunk step circuits — 65,536 is the hard ceiling per method.
- **No pairing, anywhere.** The complete Kimchi gate set is `{Zero, Generic, Poseidon, CompleteAdd,
  VarBaseMul, EndoMul, EndoMulScalar, Lookup, RangeCheck0/1, ForeignFieldAdd, ForeignFieldMul, Xor16,
  Rot64}` (`kimchi/src/circuits/gate.rs`). **No Fp12/Fp6/Fp2, no Miller loop, no final exponentiation,
  no G2.** The only "pairing" in the tree is a native Rust arkworks KZG backend (`poly-commitment/src/kzg.rs`)
  — an alternate *native* proof system, not an in-circuit verifier.
- **Foreign field fits the modulus but not the pairing.** `ForeignFieldMul` (11 constraints/gate,
  ~a dozen rows with range-checks) supports moduli ≤ 2^259, so BN254 Fq (254-bit) is representable
  (`foreign_field_common.rs`). But a Groth16 check is a **multi-pairing**: one Fp12 multiply ≈ dozens
  of Fq muls; a Miller loop + final exponentiation ≈ thousands of Fp12 ops. That is orders of magnitude
  past 65,536 rows — and the entire Fp12/pairing gadget stack **does not exist** in o1js/Kimchi; it
  would be built from scratch out of `ForeignFieldMul`.
- **No proof-system escape hatch.** o1js `.verify()` / `SelfProof` consume **only Pickles/Kimchi-over-Pasta
  proofs** (`inductive_rule.ml`: the previous proof is typed `Pickles.Proof.t`). **DynamicProof /
  side-loaded VK** exists (`pickles.ml` `module Side_loaded`) but it swaps *which Pickles VK* you check
  at runtime — a dynamic VK, **not** a dynamic proof system. There is no path to feed a Groth16 or a
  BabyBear STARK into `.verify()`.

**Conclusion: a Mina zkApp cannot verify dregg's Groth16 proof in-circuit today.** Not a tuning
problem — a missing-primitive problem (no pairing) compounded by a hard budget wall (step circuits
don't chunk).

---

## 3. The current Rust bridge is observation-only (not proof-carrying)

`bridge/src/mina.rs` + `bridge/src/mina_observer.rs`, and the existing o1js zkApp `bridge/mina-zkapp/`,
are honest about this once you read the accept path:

- `wrap_stark_for_mina` produces a **BLAKE3 binding commitment** over the STARK bytes — *"a BINDING
  COMMITMENT, not on-chain verification."* No proof is verified on Mina.
- `mina_observer.rs` speaks real Mina GraphQL, gates finality by Ouroboros-Samasika depth (~290
  confirmations), and decodes the dregg `provenRoot` from the zkApp's app-state Fields. Its own verify
  is **`StructureOnly`-grade** — *"a re-executing validator that trusts the node's canonical chain."*
  Safety rests on the dregg-side verifier; the relay is for **liveness only**.
- The o1js `DreggVerifier.verifyTransition` (`bridge/mina-zkapp/src/verifier.ts`) asserts only
  *structural* invariants (roots non-zero, height increasing, roots differ). It does **not** verify a
  dregg proof — the comment says the verification is "implicit." `DreggFederation.advanceState` gates
  on the account's `editState: proof` permission, i.e. the o1js method proof — a **trusted-relay**
  anchor, not a dregg-proof check. Notably `types.ts` ships a real 32-deep Poseidon-Merkle fold
  (`CellMerkleWitness.computeRoot`) that is **never wired into a method** — the PoC (§6) wires exactly
  this in.

---

## 4. Dead premise (flagged): the "STARK-in-Pickles already built" plan

`plans/mina-bridge-design.md` argues the Mina bridge can be fully proof-carrying at "Level 2 today"
because dregg allegedly already emits a Pasta-native Pickles proof (`poseidon_stark_verifier_circuit.rs`,
`pickles.rs`, `step_verifier.rs`, `wrap_verifier.rs`, `ipa_verifier.rs`, `circuit/src/backends/mina/mod.rs`).

**Every one of those files is gone.** They were deleted in *"the great deletion: ~29K lines of legacy
backends"* (`be83eceae`). The current `circuit/src/backends/mod.rs` states why: *"The former
Mina/Kimchi/Pickles backend family was REMOVED: its pickles wrap never verified the Kimchi proof
in-circuit (the recursive step was vacuous scaffolding)."* So the plan's premise — that dregg's proof
is already a Mina-verifiable Pickles proof — is **false today**. Treat that document as historical;
this one supersedes its feasibility claim. (The plan's *product* vision — sovereign cells on Mina,
zkApp-to-zkApp composition — remains valid once a real proof path exists.)

---

## 5. The two real-verification routes (to make direction 2 a proof-check)

Ranked by tractability. Both are large; both are honest paths, unlike the dead premise.

**Route A — foreign-field BabyBear-Poseidon2 recompute in the Mina circuit (most promising).**
Verify the *inner* dregg commitment, not the outer Groth16. BabyBear (p = 2^31−2^27+1, **31-bit**)
fits *natively* inside a Pasta Field, so BabyBear field arithmetic in a Kimchi circuit is cheap (a
mul + a witnessed reduction mod a 31-bit prime). The cost is re-implementing **Poseidon2-over-BabyBear**
(dregg's exact round constants) as a gadget and walking a Merkle/FRI path — hash-dominated, no pairing.
A full FRI verify (38 queries, dozens of folds) is a big circuit and likely needs splitting across
recursive Pickles steps, but it is *made of primitives Kimchi has*, unlike a pairing. This is the
route that turns the §6 hash-attestation into a real check of dregg's **canonical** root.

**Route B — dregg emits a Pasta-native Kimchi/Pickles proof.** Re-introduce a Kimchi *prover* over
Pasta whose recursive step ACTUALLY verifies (the deleted one did not). Then `.verify()` consumes it
natively and the bridge is symmetric and cheap on-chain. This is essentially standing up a Pickles
prover for dregg's statement — the heaviest lift, and the one whose prior attempt was deleted as
vacuous. High value (it also gives free Mina-side recursion), high cost.

**Route C — full BN254 Groth16 pairing emulation in-circuit. Infeasible** (§2): the Fp12/Miller/final-exp
gadget stack does not exist and blows the budget. Not recommended.

Until Route A or B lands, direction 2 is a **hash attestation** with a stated trust boundary (§6).

---

## 6. The tractable minimal mutual step + PoC — a Poseidon-over-Pasta attestation

**The one primitive both systems compute bit-for-bit is Mina-Poseidon over Pasta Fp.** o1js's native
`Poseidon.hash` is 11 rows/permutation (`kimchi/.../poseidon.rs`: `POS_ROWS_PER_HASH = 11`) — a
depth-32 Merkle path is ~350 rows, trivially inside the 65,536 budget. And dregg can produce the
*identical* hash in Rust: `circuit-prove/sketches/mina-pasta-hash-probe` (`mina_poseidon_hash`,
o1-labs `mina-poseidon`, kimchi params) is **gold-KAT-pinned to o1js `Poseidon.hash`** for single
hashes AND a depth-2 Merkle root.

So the minimal real mutual-proof step is: **dregg emits a Mina-Poseidon-over-Pasta commitment to a
value (or state root); a Mina zkApp verifies, in-circuit, a Poseidon Merkle path into that dregg
commitment and returns the opened leaf as a proof-carrying output.** Two languages, two proof systems,
one shared commitment.

### The PoC (built + run)

- **Verifier circuit:** `bridge/mina-zkapp/scripts/attestation-poc.mjs` — a ZkProgram
  `DreggMembershipAttestation` (`publicInput` = the dregg-emitted Pasta root, `publicOutput` = the
  proven leaf) whose method walks a Poseidon Merkle path and `assertEquals`es the reconstructed root.
  This is exactly the `CellMerkleWitness.computeRoot` fold that `types.ts` ships but never wired into a
  method. A committed `.ts` version lives beside it: `bridge/mina-zkapp/src/DreggPoseidonAttestation.ts`.
- **The cross-system handshake is live, not hardcoded:** the root it checks,
  `0x0f82b06f11a6dea422082c77668f6ac9fd97a5f21b81525cb61a46c335bbb777`, is the **live stdout of the
  Rust probe binary** (`merkle_root_1234`), and the PoC asserts o1js's own recomputation equals it.
  Rust (dregg's Poseidon) produces the root; o1js (Mina's proof system) proves membership under it.
- **Result (o1js 2.15.0, Node 26):**
  ```
  [1] o1js Poseidon Merkle root == Rust mina_poseidon_hash root (bit-for-bit)   ✓
  [2] compiled the Mina-side attestation circuit                          (8.1s) ✓
  [3] proof produced (7.3s), Mina-side proof VERIFIES, output == opened leaf     ✓
  [4] soundness: a wrong sibling is REJECTED at proving time                     ✓
  === PASS ===
  ```
  A real Kimchi/Pickles proof, non-vacuous (tamper rejects). (Runtime note: the project's pinned
  o1js **1.9.1** prover bindings crash on Node ≥26; run on Node 20–22 with 1.9.1, or `npm i o1js@2`
  on Node 26 — the hashing path in step 1 runs anywhere. The PoC was verified via the latter.)

### The honest boundary of the attestation

This verifies dregg's **commitment**, not dregg's **proof**. It is proof-carrying end-to-end only when
the checked root is one dregg's proof actually attests. Two gaps to close, in order:

1. dregg's canonical root is **Poseidon2-over-BabyBear**, not Mina-Poseidon — so the attested
   Pasta root is today a *re-commitment* the probe computes in **plain Rust, outside the STARK**. Until
   dregg's STARK (or the Groth16 public output) binds the Pasta re-commitment, the relay that computes
   it is trusted for that hash. Closing this = have the prover expose a Mina-Poseidon root as a public
   output, or do Route A (recompute the real BabyBear root in-circuit).
2. Even then, the Mina side attests *a value under a root*, and trusts that *the root itself* is a
   valid dregg state (the current `StructureOnly` relay). Full trustlessness = Route A/B.

So the PoC is the real, minimal, buildable mutual step — with a precisely named residual, not a
laundered one.

---

## 7. Rich interaction — what a Mina↔dregg zkApp enables

| Use-case | What it is | Tractable NOW? |
|---|---|---|
| **Cross-chain state read / capability attestation** | a Mina contract gates on "this cell / capability / balance is committed under dregg's root" | **Yes** — the §6 attestation + the K6 Merkle-query shape. Trust boundary = §6.1 (relay attests the Pasta root until Route A). |
| **Proof-carrying deposit/withdraw (shared asset)** | lock MINA → mint a dregg note; burn on dregg → unlock MINA, nullifier-gated | **Partial** — `DreggFederation` deposit/withdraw + nullifier machinery exist and run, but state advance is **trusted-relay** anchored. Trustless mint/unlock needs Route A/B. |
| **Mina as a dregg light client** (direction 1) | dregg verifies a Mina Kimchi proof + reads a zkApp-state field under the verified root | **Mostly built** in Lean (K5 + K6), modulo the 3 crypto carriers. This is the genuinely novel, mostly-real half. |
| **Sovereign cell on Mina** | a zkApp whose transitions REQUIRE a dregg authorization proof (`plans/…` Phase 3) | **No** — needs Route B (`.verify()` a real dregg Pickles proof). The product shape is right; the proof path is future. |
| **Symmetric mutual settlement ("true peers" on Mina)** | each chain verifies the other's proof; asset/message finality both ways | **No on Mina** — today "true peers" is **EVM Groth16/BN254** (`DreggPeerRegistry.sol` `submitPeerFinality`). Mina peers need direction 2 as a real check (Route A/B) to match the direction-1 half. |

The through-line: **direction 1 is real and mostly built; direction 2 is a hash-attestation now and a
real check after Route A.** The rich, symmetric, mutually-proof-checking bridge — the thing ember means
by "not many mutually-proof-based systems, especially across proof systems" — is reachable, and this
doc names the exact one lift (Route A: foreign-field BabyBear-Poseidon2, no pairing) that gets there.

---

## 8. Scorecard

| Claim | Resolution |
|---|---|
| dregg verifies a real Mina Kimchi proof | **arithmetic checked over the real Pasta field, non-vacuous, modulo C3/C6/C9 carriers** (Lean, axiom-clean). Not "verifies Mina." |
| Mina verifies dregg's Groth16 in-circuit | **infeasible today** — no pairing gate; emulation ≫ 2^16-row step ceiling; step circuits don't chunk. |
| Mina `.verify()` a dregg STARK/Groth16 | **no path** — `.verify()` is Pickles-proofs-only; DynamicProof = dynamic VK, not dynamic proof system. |
| Mina verifies a dregg Poseidon attestation | **built + run** (PoC §6): real Pickles proof, tamper-rejecting; Rust/o1js hashers agree bit-for-bit. |
| dregg emits a Mina-native Pickles proof ("Level 2 today") | **dead premise** — those backends were deleted as vacuous scaffolding (§4). |
| Path to a symmetric mutual-proof bridge | **Route A** (foreign-field BabyBear-Poseidon2 recompute; BabyBear is 31-bit → cheap, no pairing) or **Route B** (a real Pasta-native dregg prover). |

**Artifacts:** `bridge/mina-zkapp/scripts/attestation-poc.mjs` (runnable PoC),
`bridge/mina-zkapp/src/DreggPoseidonAttestation.ts` (committed circuit),
`metatheory/Dregg2/Circuit/Emit/{KimchiVerify,KimchiRealProofGate,MinaStateQuery}.lean` (direction 1),
`circuit-prove/sketches/mina-pasta-hash-probe/` (the Rust↔o1js Poseidon pin),
`docs/MINA-REALITY-GATE.md` (direction-1 boundary). Supersedes `plans/mina-bridge-design.md` §"already built".
