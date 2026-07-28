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
| **Tractable mutual step** | a Mina **zkApp** consumes a `ZkProgram` proof of a **Poseidon-over-Pasta KAT attestation** | **BUILT + RUN, ON-PIN, GATED** (PoC §6). Native Poseidon (11 rows/perm); the Rust and o1js hashers agree bit-for-bit — real, and it survived adversarial probing. **[CORRECTED 2026-07-27]** the original row overstated the packaging: no zkApp ran (F-B9), the attested value is a **hash KAT over the literals `[1,2,3,4]`**, not dregg state (F-B8), and it did not run on the repo's pinned o1js (F-B6). **[REPAIRED 2026-07-28]** F-B6/F-B9/F-B10 are closed — o1js pinned at 2.15.0, runs from the tree, and `DreggAttestedGate` really does deploy and consume the proof recursively, under `scripts/check-mina-attestation.sh`. ⚑ **F-B8 stands: the attested value is still a KAT, not dregg state.** **[DEPLOYED 2026-07-28]** the contract is now LIVE on **Mina Devnet** and both polarities are on chain — see `docs/MINA-DEVNET-DEPLOYMENT.md`. The attested root there is **freshly emitted by the Rust side** (not the `[1,2,3,4]` fixture), which narrows F-B8 to its real residual: the leaves are deploy-time metadata, still **not dregg cell state**. |

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

**State-query (K6), `MinaStateQuery.lean`:** a **Poseidon Merkle path** into an account/zkApp-state
field (`merkleFold`, `leafHash_commits_balance/_nonce/_zkappRoot`), as a `Nat` COMMITMENT MODEL —
the file emits zero constraints. SOURCED from the real Mina account structure (`~/dev/mina`
`mina_base/account.ml`, `ledger_hash.ml`, `hash_prefixes.ml`).

⚑ **Corrected 2026-07-27.** This paragraph used to say "`mina_verify_then_query` states the seam:
(K5) verify-root ∘ (K6) query-under-root." That theorem is **deleted**: its seam conjunct was
`P → P` over a free predicate and its other conjunct was vacuous through three collision-resistance
floors that were **provably false** (they asserted injectivity of a concrete Poseidon over all of
`Nat`, while the sponge absorbs mod `pN`). The binding results are re-proved on per-instance
non-equivocation conditions and stand; **the K5→K6 seam does not exist in Lean** — the two files
share no object. See `docs/AUDIT-MINA-KIMCHI.md` F2/F4 and `MinaStateQuery` §3/§7/§10.

So Mina is not yet a **dregg light client** at this leg; the state-query commitment structure is
built and KAT-anchored to the real hash, and the composition with the verifier is the open step.

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
`pickles.rs`, `step_verifier.rs`, `wrap_verifier.rs`, `ipa_verifier.rs`, and the `circuit` crate's
`src/backends/mina/mod.rs`).

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

### The PoC (built + run — with four corrections below)

> **⚑ [CORRECTED 2026-07-27]** This section overstated in four ways, each verified against the code
> during this pass (audit F-B6/B7/B8/B9/B10). **The cryptographic core is real** — a genuine
> `ZkProgram.compile()` producing real Pickles keys, a real proof that verifies, a genuinely
> in-circuit Merkle fold (`analyzeMethods` = 32 rows, `{"Generic":8,"Poseidon":22,"Zero":2}`), and
> tamper rejection *at the constraint level* (`Constraint unsatisfied (unreduced): rule_main /
> Equal(Var 443)(Var 1)` inside the Pickles prover, not a JS throw). **What was overstated is the
> packaging.** Nothing below weakens the hash agreement, which I re-confirmed.

- **Verifier circuit:** `bridge/mina-zkapp/scripts/attestation-poc.mjs` — a **`ZkProgram`**
  `DreggMembershipAttestation` (`publicInput` = the attested Pasta root, `publicOutput` = the
  proven leaf) whose method walks a Poseidon Merkle path and `assertEquals`es the reconstructed root.
  This is exactly the `CellMerkleWitness.computeRoot` fold that `types.ts` ships but never wired into a
  method. A `.ts` version is committed beside it: `bridge/mina-zkapp/src/DreggPoseidonAttestation.ts`.
  **[CORRECTED 2026-07-27]** — that committed `.ts` **does not compile**: `npx tsc --noEmit` gives 3
  errors (`:55`, `:108`, `:111`), because it is written against the o1js **2.x** API while
  `package.json:11` pins `"o1js": "^1.0.0"`. It fails `npm run build`. Describing it as a working
  "committed circuit" was wrong.
- **[CORRECTED 2026-07-27 — "live, not hardcoded" was FALSE, and the attribution was BACKWARDS.]**
  The earlier text read: *"the root it checks … is the **live stdout** of the Rust probe binary
  (`merkle_root_1234`) … Rust (dregg's Poseidon) produces the root; o1js (Mina's proof system) proves
  membership under it."* The actual code (`attestation-poc.mjs:40-42`) is a pasted literal:
  ```js
  const RUST_GOLD_ROOT =
    0x0f82b06f11a6dea422082c77668f6ac9fd97a5f21b81525cb61a46c335bbb777n;
  ```
  There is **no `child_process`, no `spawn`, no FFI anywhere in the file** (I grepped: zero hits).
  The number is **truthful** — the Rust binary does print exactly that — but it is pasted, not live.
  And the **direction is inverted**: `mina-pasta-hash-probe/src/main.rs:10-12` states the gold vectors
  *"were produced by `bridge/mina-zkapp/scripts/poseidon-kat.mjs` (o1js 1.9.1) … pasted verbatim"*,
  and the test that pins this exact root, `merkle_compress_matches_o1js_merkletree` (`:206-221`),
  says *"Gold value from poseidon-kat.mjs's MerkleTree case"* and asserts *"depth-2 Merkle root
  diverges from o1js MerkleTree"* on failure. **o1js is the authority and Rust checks against it** —
  the reverse of what this doc said. The bit-for-bit agreement is real and worth keeping; the words
  "live" and the direction were not.
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

  **[CORRECTED 2026-07-27 — "runnable PoC" describes something that does not run from the repo.]**
  With the repo's own pin (`package.json:11` → `"o1js": "^1.0.0"`, 1.9.1 installed),
  `node scripts/attestation-poc.mjs` dies during `[2] compiling` with
  `TypeError: Cannot read properties of undefined (reading '0')` at `absorb`
  (`o1js_node.bc.cjs:296574`), **`EXIT_CODE=7`**. Reproducing the result above required installing
  **o1js 2.15.0 into a scratch directory**. The version gap *is* disclosed in the runtime note
  directly above — that part was handled correctly — but "runnable" is not the right word for a
  script with no npm entry point that exits 7 on the pinned dependency. **Either pin o1js 2.x or say
  the PoC runs off-pin.** Until then, read every result in this section as **off-pin**.

- **[CORRECTED 2026-07-27 — a `ZkProgram` ran; the zkApp never did.]** What compiled and proved is a
  bare `ZkProgram` — **no account, no on-chain state, no `SmartContract`**. The actual zkApp,
  `DreggAttestedGate` (`src/DreggPoseidonAttestation.ts:89-113`), is **never compiled, deployed or
  exercised, and has zero importers.** The prose above that names a `ZkProgram` is accurate; the
  headline row in §0 and the scorecard in §8 said "a Mina **zkApp** verifies" and were not.

- **[CORRECTED 2026-07-27 — the attested root is a hash test vector, not "a dregg-emitted root".]**
  The root is a depth-2 Merkle tree over the literals **`[1,2,3,4]`** (`attestation-poc.mjs:87-90`;
  Rust `main.rs:92-96`). **No dregg state, cell, turn or chain value touches it**, and nothing in
  dregg emits a Mina-Poseidon root at all — `mina_poseidon_hash` appears only inside the sketch
  crate. Everywhere this document says "the dregg-emitted Pasta root" or "a dregg-emitted root",
  read: **a Mina-Poseidon KAT over `[1,2,3,4]`**. §6.1 below already draws the right boundary for the
  *re-commitment* case; what it did not say is that today there is no dregg value in the picture at all.

- **[CORRECTED 2026-07-27 — this result cannot go red.]** `grep -rn "mina-zkapp|attestation-poc|
  poseidon-kat|merkle-constraints" .github/ scripts/` returns **zero hits** across all 26 workflows
  and `scripts/local-gates.sh`. The Rust probe opts *out* of the workspace
  (`mina-pasta-hash-probe/Cargo.toml:16` has a bare `[workspace]`) and is absent from the root
  `Cargo.toml` members and from `Cargo.lock`; there is no root `package.json`/npm workspace and no
  jest config, so `npm test` has nothing to run. The two crates also draw `mina-poseidon` from
  **different sources** — root pins `emberian/proof-systems@c5305e63`, the probe pins
  `o1-labs/proof-systems@36a8b510` — and the KAT is pinned against the latter only. The good
  cryptographic result above is real **and nothing would ever report if it stopped being true.**

- **[REPAIRED 2026-07-28.]** Four of the five corrections above are closed; one is not.
  `package.json` now pins **`o1js` 2.15.0 exactly** (1.9.1's prover bindings abort during
  `compile()` on Node ≥ 26, and its `ZkProgram` typing rejects the committed source), `tsc` is
  clean, and everything runs **from the tree**: `tsc` emits to `dist/` and the driver imports the
  emitted JS, so `attestation-poc.mjs` — a second copy of `src/` — is **deleted**. The gate is
  `bridge/mina-zkapp/scripts/attestation-gate.ts`, run by `scripts/check-mina-attestation.sh`,
  which is a `scripts/local-gates.sh` row *and* a `ci.yml` job, and whose `--self-test` injects
  eight faults and requires each to turn it red.
  - **F-B6 "runnable" — closed.** `npm run gate`, 22 checks, ~37 s, on the pinned toolchain.
  - **F-B9 "a Mina zkApp verifies" — closed.** `DreggAttestedGate` now compiles, deploys on a
    local chain with proofs ENABLED, **consumes the attestation proof recursively** (340 rows),
    records the leaf on-chain, and **refuses** a proof bound to a different root.
  - **F-B7 direction — closed as documentation.** `src/rust-gold-vectors.ts` mirrors the Rust
    probe's table verbatim and states in place that o1js generated the vectors, so the agreement
    is a two-way check on two implementations of the same sponge — not evidence of provenance.
  - **F-B10 "cannot go red" — closed.** See above.
  - ⚑ **F-B8 is NOT closed, by design.** The attested root is still a fixed-leaf Mina-Poseidon
    test vector over `[1,2,3,4]`, not a commitment to dregg state. That fact now lives in the
    module header of `src/DreggPoseidonAttestation.ts`, where the next reader meets it, instead of
    only here. Closing it is the §6.1 work below, not a wording change.

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
| **Cross-chain state read / capability attestation** | a Mina contract gates on "this cell / capability / balance is committed under dregg's root" | **Shape demonstrated, not the use-case** — the §6 attestation proves membership under a **Poseidon KAT root over `[1,2,3,4]`**, in a `ZkProgram`, off-pin; **no cell, capability or balance has ever been attested**. Plus the K6 Merkle-query shape. Trust boundary = §6.1 (relay attests the Pasta root until Route A). **[CORRECTED 2026-07-27 — this row read "**Yes**".]** |
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

**[CORRECTED 2026-07-27 — two rows overstated; see the PoC section for evidence.]**

| Claim | Resolution |
|---|---|
| dregg verifies a real Mina Kimchi proof | **arithmetic checked over the real Pasta field, non-vacuous, modulo the named carriers** (Lean, axiom-clean; `MINA-REALITY-GATE.md` is authoritative on the current carrier set). Not "verifies Mina." |
| Mina verifies dregg's Groth16 in-circuit | **infeasible today** — no pairing gate; emulation ≫ 2^16-row step ceiling. *"Step circuits don't chunk"* is **[UNVERIFIED]**: the 2^16/2^15 figures are exact, but no code asserting non-chunking was located (audit §6.8). |
| Mina `.verify()` a dregg STARK/Groth16 | **no path claimed, but [UNVERIFIED]** — *".verify() is Pickles-proofs-only"* and *"DynamicProof = dynamic VK, not dynamic proof system"* are claims about o1js **2.x**, while `~/dev/o1js` is **v0.16.2 (2024-02-23)** and contains **no `DynamicProof` class at all**. Not refuted; **unchecked** (audit §6.7). |
| Mina verifies a dregg Poseidon attestation | **[SUPERSEDED 2026-07-28 — was "a bare `ZkProgram`, not a zkApp, over `[1,2,3,4]`, off-pin". Re-deployed the same day at a new address when `setDreggRoot` gained a real authorization check, which moved the zkApp VK.]** A **deployed zkApp on Mina Devnet** (`B62qkiRhX1tKdkYSXRHFASHQHj1tPf5VcLzgUhqkL3kuFViX9ckcSaN`; the first deployment `B62qo54w6YftnPHCXTrcEYDcKYwg8CCeW5wiTsW9x8Tp1Hm5BS5xCeD` is superseded and left on chain) consumed a **recursive** attestation over a root the **Rust side emitted fresh**, and the network **refused** the same proof once the anchored root moved (`Account_app_state_0_precondition_unsatisfied`). Still a **commitment attestation, not a proof check**, and the leaves are deploy-time metadata rather than dregg state. `docs/MINA-DEVNET-DEPLOYMENT.md` is authoritative, including on what it does NOT show. |
| dregg emits a Mina-native Pickles proof ("Level 2 today") | **dead premise** — those backends were deleted as vacuous scaffolding (§4). |
| Path to a symmetric mutual-proof bridge | **Route A** (foreign-field BabyBear-Poseidon2 recompute; BabyBear is 31-bit → cheap, no pairing) or **Route B** (a real Pasta-native dregg prover). |
| Does any of this go red on its own? | **Yes — [CORRECTED twice: this row read "No … a complete orphan", then "Partly … the Rust side runs in NO gate".]** `scripts/check-mina-attestation.sh` is a `local-gates.sh` row **and** a `ci.yml` job, with a `--self-test` that injects thirteen faults and requires each to turn it red. The Node-only hole is **closed**: a third leg runs `cargo test --locked` in `circuit-prove/sketches/mina-pasta-hash-probe` (its own workspace, so no other cargo job reached it) and then the `merkle` subcommand end to end, cross-checked against o1js elementwise — a missing `cargo` is now a failure, not a skip. The devnet scripts are still not gated and must not be (network, faucet budget, block times). |

**Artifacts:** `bridge/mina-zkapp/scripts/attestation-poc.mjs` (PoC — **runs off-pin only; exits 7 on
the repo's pinned o1js**), `bridge/mina-zkapp/src/DreggPoseidonAttestation.ts` (committed circuit —
**does not compile: 3 `tsc` errors, written against o1js 2.x under a 1.x pin**),
`metatheory/Dregg2/Circuit/Emit/{KimchiVerify,KimchiRealProofGate,MinaStateQuery}.lean` (direction 1),
`circuit-prove/sketches/mina-pasta-hash-probe/` (the Rust↔o1js Poseidon pin),
`docs/MINA-REALITY-GATE.md` (direction-1 boundary). Supersedes `plans/mina-bridge-design.md` §"already built".
