# FRI-verifier proof engineering: a Lean-specified verifier, a Lean-derived wrap circuit

The ETH-native wrap (`docs/deos/ETH-NATIVE-WRAP.md`) must reimplement dregg's
BabyBear batch-STARK FRI verifier as a gnark/BN254 arithmetic circuit. The wrap's
single load-bearing unknown is **bit-exact transcript / Fiat-Shamir fidelity**: if
the in-circuit `DuplexChallenger` squeezes even one challenge differently from the
Rust verifier, the circuit silently accepts proofs the Rust verifier rejects (a
soundness hole) or vice versa. Today that fidelity would be established only by
differential testing against the Rust verifier — the same hand-write-and-diff
discipline dregg's "ONE Lean-derived circuit/VK" principle exists to retire.

This document scopes turning that unknown into a **refinement theorem**. The
verifier *algorithm* gets a Lean specification; the gnark circuit is shown to
**refine** that spec; and the spec bottoms out on exactly two named terminal
crypto carriers (FRI low-degree soundness, Poseidon2 collision-resistance) — the
same floor the rest of dregg's circuit-soundness apex already rests on.

## 0. The honest line: carrier vs proven

This is the discipline of `feedback-named-seam-is-not-a-hole` and
`metatheory/docs/STARK-FLOOR.md` applied to the wrap. Two layers, kept distinct:

- **FRI soundness is a NAMED TERMINAL CRYPTO CARRIER.** "An accepting FRI proof ⟹
  the committed codeword is within decoding distance of a low-degree polynomial,
  up to the soundness error" is a property of FRI we **assume**, exactly as
  `StarkSound` / `Poseidon2SpongeCR` / `StarkComplete` are assumed today. We do
  NOT re-derive FRI soundness in Lean. It enters as a typeclass hypothesis, never
  an `axiom`, so `#assert_axioms` stays `⊆ {propext, Classical.choice, Quot.sound}`.

- **The verifier ALGORITHM is CODE, so it gets a spec + a refinement proof.** The
  `DuplexChallenger<Poseidon2-w16>` transcript squeezes, the FRI commit-phase
  beta derivation, the query-index sampling (`sample_bits` + grinding PoW), the
  per-query Merkle-path / fold-consistency checks, the batch-STARK
  `verify_all_tables` surface, and the three teeth of
  `verify_turn_chain_recursive_from_parts` are a deterministic algorithm. That
  algorithm gets a Lean function `verifyAlgo`; the gnark circuit is proven to
  compute the *same Boolean*; and `verifyAlgo accept` is fed to the FRI-soundness
  carrier to extract a genuine witness.

The wrap soundness theorem is then a one-line composition: `gnark accepts`
`= verifyAlgo accepts` (refinement) `→ ∃ genuine transition` (carrier). The
"silent soundness break" is exactly the refinement equality; making it a theorem
(eventually discharged bit-exactly, fixture-anchored) is the whole point.

## 1. Census — what Lean modeling exists today (the gap, precisely)

Verified against HEAD.

| Object | Where | What it is |
|---|---|---|
| `StarkSound` / `verifyBatch` | `Dregg2/Circuit/CircuitSoundness.lean §5` | `opaque verifyBatch : VerifyKey → BatchPublicInputs → BatchProof → Verdict` + a class field `extract : verifyBatch … = accept → ∃ Satisfied2 witness`. The verifier is a **black box verdict**; soundness is **assumed**. |
| `StarkComplete` | `Dregg2/Circuit/CircuitCompleteness.lean §3` | the dual carrier (honest prover ⟹ accepting proof). Also over the opaque `verifyBatch`. |
| `EngineSound` (`InnerProofSound`, `BindingAirSound`, `RecursiveVerifierSound`) | `Dregg2/Circuit/RecursiveAggregation.lean §0–1` | `verify : Proof → Bool` **opaque**; three named recursion-soundness `structure` fields. The whole-chain fold's soundness, again over an **opaque verifier**. |
| `Poseidon2SpongeCR` | `Dregg2/Circuit/Poseidon2Binding.lean` | the hash CR carrier (injectivity portal). Realizable, carried as a Prop hypothesis. |
| STARK floor doc | `metatheory/docs/STARK-FLOOR.md` | states plainly that `verify_batch` at `ir2_config` is the irreducible FRI line, self-reviewed, unaudited. |

**The gap, stated precisely:** there is **no Lean spec of the verifier
algorithm**. Every Lean object models the verifier as `opaque verifyBatch …` /
`verify : Proof → Bool` reduced to an accept/reject verdict, plus a soundness
carrier asserting "accept ⟹ ∃ witness". **Nothing models HOW `accept` is
computed** — not the challenger/transcript, not the FRI fold, not the Merkle
paths, not the query sampling, not `verify_all_tables`. For the existing
light-client apex that is *correct and sufficient*: the light client calls the
Rust verifier and trusts the carrier. But the ETH wrap must *re-implement* the
verifier in a foreign system (gnark), so an opaque verdict gives **nothing to
refine against**. The new work is to lift the algorithm from opaque-verdict to
specified-function, so "the gnark circuit is correct" becomes a statement with a
referent.

## 2. The Rust verifier surface being specified

Grounded at HEAD:

- **Top verifier** — `verify_turn_chain_recursive_from_parts`
  (`circuit-prove/src/ivc_turn_chain.rs:2845`), three teeth: (1) VK fingerprint
  pin `recursion_vk_fingerprint` (`plonky3_recursion_impl.rs:646`, blake3 over the
  root circuit's table shape); (2) the root verify
  `verify_recursive_batch_proof_with_config(root, ir2_leaf_wrap_config())` →
  `BatchStarkProver::verify_all_tables`
  (`~/dev/plonky3-recursion/circuit-prover/src/batch_stark_prover.rs:978`); (3)
  the segment tooth — the `expose_claim` table's
  `[first_old, last_new, count, acc_0..3]` must equal
  `[genesis_root, final_root, num_turns, chain_digest]`
  (`ivc_turn_chain.rs:2887–2905`).
- **The challenger** — `DuplexChallenger<F=BabyBear, Perm=Poseidon2BabyBear<16>,
  WIDTH=16, RATE=8>` (`plonky3_recursion_impl.rs:88`). The transcript semantics
  are fully captured by `observe` / `duplexing` / `sample` / `sample_bits`
  (p3-challenger `duplex_challenger.rs`): observe buffers into a rate-width input
  buffer and duplexes (overwrite-first-`len`, permute, refill output from
  `state[..RATE]`) when the buffer fills; `sample` pops the output buffer **from
  the end**, duplexing on empty/pending; `sample_bits(b)` is
  `sample().as_canonical_u64() & ((1<<b)-1)`.
- **FRI knobs** — `ir2_leaf_wrap_config`: `log_blowup 6`, `num_queries 19`,
  `query_proof_of_work_bits 16`, `max_log_arity 3`, `log_final_poly_len 0`
  (`ivc_turn_chain.rs:1137`). Conjectured soundness `19·6 + 16 = 130` bits.
- **The batch surface** — `verify_all_tables` is not one AIR: per-table
  `degree_bits`, a logup interaction bus across tables, and four non-primitive op
  tables (Poseidon2-w16, Poseidon2-w24, recompose, expose_claim;
  `plonky3_recursion_impl.rs:739–748`).

## 3. The Lean spec structure (design)

Module trunk: `Dregg2/Circuit/FriVerifier.lean` (this commit starts it), splitting
later into `FriVerifier/{Challenger,Fold,Batch,Refinement}.lean` as it grows.

**(a) The Fiat-Shamir transcript model — `Challenger` (the keystone).** A pure
functional model of `DuplexChallenger`: `spongeState`/`inputBuffer`/`outputBuffer`
over an abstract field `F`, parameterized by the permutation `perm : List F →
List F` and a canonical projection `toNat : F → ℕ`. `observe`, `observeList`
(left fold), `duplexing`, `sampleBase`, `sampleExt`, `sampleBits` mirror the Rust
byte-for-byte (overwrite-first-`len`, pop-from-end, the empty/pending duplex
trigger). This is the highest-leverage object: it is the load-bearing unknown, and
it is the thing the gnark in-circuit challenger must match exactly.

**(b) The FRI commit-phase / query derivation — `deriveFri`.** Given the proof's
fold-layer commitments, the specified observe-each-commitment-then-sample-a-beta
fold; the final-poly observe; the `num_queries` query-index draws via `sampleBits`
under the grinding PoW. This is the part where a transcript bug hides; it is
**concretely specified**, not opaque.

**(b′) The FRI query core — `merkleRecompute` + `friChainGo` + `friQueryCheck`
(CONCRETE, landed).** The per-query FRI low-degree test is NOT an opaque check: it
is the Poseidon2 Merkle-path recompute (fold the opened leaf up through siblings,
branching on the index bit, compare to the layer commitment), the fold-chain (each
layer's opening equals the value the previous layer folded to via `foldCombine beta
x e0 e1`, bottoming out at the FRI final-poly constant under `log_final_poly_len =
0`), and the query-position evolution (`idx/2` per layer). All specified. The
`concreteFriChecks` bundle additionally **BINDS the query positions to the
transcript-derived indices** — the soundness-critical link that makes Fiat-Shamir
load-bearing (a prover cannot choose favorable query points). The Poseidon2
`compress` and the exact arity-2 `foldCombine` (the coset `1/(2x)` twiddle) are the
two calibration constants the fixture pins; the verifier structure around them is
concrete Lean. The **Merkle binding tooth** `merkleRecompute_binds` is proven: under
the Poseidon2-CR carrier (`compress` injective) the opening binds the leaf — the
anti-forgery property. Executable `#guard` non-vacuity exercises honest-accept /
tampered-reject / index-mismatch / wrong-count.

**(c) The batch-STARK `verify_all_tables` surface (the genuine remainder).** The
per-table degree-bits/quotient/logup-bus checks and the four NPO tables. These —
plus the grinding PoW — are what remains as explicit `FriChecks` fields
(`batchTables`, `queryPow`), to be specified next; honestly scaffolded as record
fields, never `sorry`. The transcript derivation (a, b) AND the FRI query core (b′)
are concrete; the per-table arithmetic is the remaining specification.

**(d) The three teeth.** Tooth 3 (segment equality) is specified concretely now (a
list equality). Tooth 1 (VK fingerprint) follows the doc's design — bake the VK
shape as a circuit constant, so the per-instance check is structural equality and
blake3 stays out of band; modeled as a `vkShapeMatches` predicate. Tooth 2 is (b)+(c).

**(e) The carriers + the refinement statement.**
- `FriLowDegreeSound` — the NAMED TERMINAL CARRIER: `verifyAlgo … = accept → ∃
  genuine witness` (the FRI extraction, now stated over the *specified*
  `verifyAlgo` instead of the opaque `verifyBatch`). The bridge from
  `verifyAlgo` to the existing `StarkSound` is a later lemma; the carrier shape is
  identical.
- `GnarkRefines` — the refinement obligation: a Lean model of the gnark circuit's
  accept predicate `gnark : BatchProofData → Bool` equals `verifyAlgo` on every
  proof. The **transcript-fidelity sub-obligation** `TranscriptRefines` is the
  bit-exact squeeze equality — the load-bearing keystone, discharged
  fixture-anchored once the gnark challenger exists.
- `wrap_sound` — the payoff: `GnarkRefines → [FriLowDegreeSound] → (gnark accept →
  ∃ genuine transition)`. Provable now by rewriting `gnark = verifyAlgo` and
  applying the carrier. The gnark circuit *inherits* the spec's soundness the
  moment it refines the spec.

## 4. The refinement-to-gnark framing

The gnark `frontend.Circuit` (`chain/gnark/fri_verifier.go`) is the implementation;
`verifyAlgo` is the spec. Refinement is established in two tiers:

1. **Transcript fidelity (the keystone).** The gnark in-circuit challenger and the
   Lean `Challenger` must agree on every squeezed challenge for every observation
   script. Anchored by a Poseidon2-w16 sponge fixture (ETH-NATIVE-WRAP §4 / §3
   milestone 2: "validate the Fiat-Shamir transcript byte-for-byte against the
   Rust challenger first"). In Lean this is `TranscriptRefines`; the gnark side is
   discharged by exhibiting the fixture agreement and the structural argument that
   the gnark gadget implements `observe`/`sample`/`sample_bits` operation-for-
   operation.
2. **Whole-verifier refinement.** With transcript fidelity established, each
   per-query / fold / Merkle / logup check is a fixed arithmetic computation; the
   gnark gadget for it refines the corresponding `FriChecks` component by the same
   operation-for-operation argument over BabyBear field ops (one BabyBear mul ≈ one
   constrained product + a canonical-reduction gadget). The segment tooth is a
   public-input equality (trivial refinement).

The carriers the wrap rests on are **exactly** `{ FriLowDegreeSound,
Poseidon2SpongeCR }` — the same FRI + hash floor as the existing apex, plus the
gnark Groth16/pairing soundness (vetted external tooling, not a dregg obligation).
No new cryptographic assumption is introduced by the wrap; the wrap converts a
differential-testing trust into a refinement proof resting on the established floor.

## 5. The honest multi-week roadmap

This is a multi-week proof-engineering effort. Ordered by leverage:

1. **(LANDED) The transcript keystone + the FRI query core + the refinement
   skeleton.** The `Challenger` model + `observeList_append`, `deriveFri`
   commit-phase derivation + `deriveQueryIndices`, **the concrete FRI query core**
   (`merkleRecompute` + `merkleRecompute_binds` Merkle-binding tooth + `friChainGo`
   fold-chain + `friQueryCheck` + `concreteFriChecks` with transcript-bound query
   positions + executable `#guard` non-vacuity), the `verifyAlgo` assembly, the
   carriers as hypotheses, and `wrap_sound` proven (axiom-free). `lake build`-green,
   `sorry`-free, carriers named.
2. **(LANDED, hash half) Transcript fidelity against the real hash.** The Lean
   `Challenger` is cross-checked against p3-challenger's OWN reference vectors
   (`FriVerifier §6`, over a `reverse` stand-in — the Challenger LOGIC). The REAL
   `Poseidon2BabyBear<16>` permutation — the actual `RC_16_EXTERNAL_INITIAL/FINAL` +
   `INTERNAL` round constants, the `MDSMat4` external layer, the `(1+Diag(V))` internal
   shift-diagonal, the `x^7` S-box — is now implemented over canonical ℕ-mod-`p` in
   `Dregg2.Circuit.Poseidon2BabyBearW16` and **KAT-validated bit-exact** against the
   deployed Rust `default_babybear_poseidon2_16().permute(·)` (the `permute [0..15]` +
   all-zero KATs + the `TruncatedPermutation` `compress`). REMAINING: a Rust
   `DuplexChallenger`-with-real-Poseidon2 transcript KAT to weld the two (pin
   `TranscriptRefines` against the real hash); the gnark challenger gadget + diff.
3. **(LANDED) The batch surface.** The per-table quotient identity
   `C(ζ) = Z_H(ζ)·q(ζ)` (with the vanishing genuinely recomputed), the logup
   interaction-bus balance, the degree-bit pin, and the grinding PoW are SPECIFIED as
   real algorithms (`FriVerifier §3b` `batchTablesCheck` / `queryPowCheck` /
   `fullChecks`), filling the `FriChecks.batchTables`/`queryPow` fields. Reject-teeth
   proven (`batchTablesCheck_rejects_tampered_quotient`,
   `batchTablesCheck_rejects_unbalanced_bus`, `tableOk_rejects_wrong_degree`,
   `queryPowCheck_rejects_bad_pow`, and `verifyAlgo_full_rejects_tampered_quotient`
   through the whole verifier) + `#guard` non-vacuity over ℤ. REMAINING: the exact AIR
   constraint polynomial of each of the four NPO tables (the `constraintEval` is
   carried as the opened value; binding it to the actual per-table AIR is the next
   refinement) and the OOD-point's transcript binding.
4. **(LANDED) The `verifyAlgo → StarkSound` bridge.** `Dregg2.Circuit.FriVerifierBridge`
   makes `CircuitSoundness.StarkSound` a THEOREM (`starkSound_of_verifyAlgo`) over the
   SPECIFIED `verifyAlgo` instead of the opaque `verifyBatch`. `AlgoStarkSound` = the
   FRI/STARK extraction floor re-stated over `verifyAlgo` (the irreducible FRI-LDT +
   Poseidon2-CR floor, now sitting ON TOP of the proven algorithm); `DeployedRefines` =
   the deployed Rust `verify_batch` computes the same accept Boolean as `verifyAlgo`
   (the Rust analogue of `GnarkRefines`, the sole remaining code-trust).
   `lightclient_unfoolable_via_algo` rests the apex on the bridge;
   `deployed_rejects_tampered_quotient` shows the proven tooth biting the deployed
   verifier with no appeal to the floor. `#assert_axioms`-clean.
5. **gnark refinement discharge.** The operation-for-operation gnark↔`verifyAlgo`
   equality, fixture-anchored, accept/reject agreement over genuine + adversarial
   fixtures (ETH-NATIVE-WRAP §3 milestone 3).

Milestones 1, 3, 4 LANDED (transcript keystone + concrete FRI query core; the concrete
batch-table/PoW surface; the `verifyAlgo → StarkSound` bridge). Milestone 2 LANDED for
the HASH (real Poseidon2-w16, KAT-validated bit-exact). The remaining TCB residual is
exactly: (a) `AlgoStarkSound` (the FRI-LDT + Poseidon2-CR math floor — IRREDUCIBLE, the
same floor every STARK assumes), (b) `DeployedRefines` (Rust `verify_batch` = the Lean
`verifyAlgo` spec — discharged by the differential-testing rung + the per-table AIR
binding), and (c) the gnark refinement (milestone 5). The verifier ALGORITHM — the
transcript derivation, the FRI fold/Merkle core, the batch quotient/logup/PoW checks —
is now SPECIFIED and its teeth PROVEN, out of the opaque-verdict TCB.
