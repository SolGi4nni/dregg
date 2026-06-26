// Package friverifier is the SKELETON of dregg's native Ethereum wrap circuit.
//
// It defines, as a gnark frontend.Circuit over BN254, the three teeth of
//
//	verify_turn_chain_recursive_from_parts
//	  (circuit-prove/src/ivc_turn_chain.rs:2845)
//
// proven NATIVELY — one BabyBear field op per circuit constraint, no RISC-V
// emulation (contrast the legacy SP1 guest, chain/program/src/main.rs). The
// resulting Groth16/BN254 proof is checked by IDreggSettlement.settle for
// ~250-300k gas. See docs/deos/ETH-NATIVE-WRAP.md.
//
// STATUS: interface spec. The gadget bodies are the load-bearing work
// (docs/deos/ETH-NATIVE-WRAP.md §4) and are intentionally unimplemented here.
package friverifier

import "github.com/consensys/gnark/frontend"

// BabyBear is the prime p = 2^31 - 2^27 + 1 = 2013265921. Each BabyBear element
// embeds losslessly into one BN254 scalar variable (31 << 254); the only
// in-circuit cost is keeping values canonical (reduce mod p), a few range-checks
// + a conditional subtract — the cheap "small modulus in a big field" regime.
const BabyBearP = uint64(2013265921)

// SegDigestWidth mirrors circuit-prove/src/ivc_turn_chain.rs:249 (SEG_DIGEST_WIDTH).
const SegDigestWidth = 4

// Publics are the four WholeChainProof public inputs
// (circuit-prove/src/ivc_turn_chain.rs:1296-1304), each a BabyBear element
// carried as a BN254 variable and exposed as a Groth16 public input. They match
// EthPublicInputs (bridge/src/ethereum.rs:260) word-for-word.
type Publics struct {
	GenesisRoot frontend.Variable                  `gnark:",public"`
	FinalRoot   frontend.Variable                  `gnark:",public"`
	NumTurns    frontend.Variable                  `gnark:",public"`
	ChainDigest [SegDigestWidth]frontend.Variable  `gnark:",public"`
}

// RootProofWitness is the flat field-element view of a
// BatchStarkProof<DreggRecursionConfig> root, exported from circuit-prove
// (ETH-NATIVE-WRAP.md milestone 1). Verified at ir2_leaf_wrap_config —
// log_blowup 6, 19 queries, 16 query-PoW, max_log_arity 3
// (circuit-prove/src/ivc_turn_chain.rs:1137 fn ir2_leaf_wrap_config), ~130-bit
// conjectured soundness.
//
// Field set is a placeholder for the real batch-STARK layout that
// verify_all_tables walks (plonky3_recursion_impl.rs:732): per-table degree
// bits, trace/quotient commitments, the logup interaction bus, FRI commitments +
// per-query openings + final poly, and the four non-primitive op tables
// (Poseidon2-w16, Poseidon2-w24, recompose, expose_claim).
type RootProofWitness struct {
	// FRI commitments (Merkle roots), one per fold layer.
	FriCommitments []frontend.Variable
	// Per-query openings: [19 queries] x (value + Merkle path siblings + folding
	// data) across all batched tables. Shape fixed by ir2_leaf_wrap_config.
	QueryOpenings []frontend.Variable
	// FRI final polynomial coefficients.
	FriFinalPoly []frontend.Variable
	// The expose_claim table's exposed segment [first_old, last_new, count,
	// acc_0..acc_3] (tooth 3 compares this to Publics).
	ExposedSegment [3 + SegDigestWidth]frontend.Variable
	// (… trace/quotient openings, logup bus values, NPO Poseidon2 rows, etc.)
}

// Circuit is the native wrap statement: "this root proof verifies AND exposes
// exactly these four public inputs."
type Circuit struct {
	Publics
	Root RootProofWitness
}

// Define lays out the three teeth. The VK (tooth 1) is best baked as a circuit
// CONSTANT at setup (the circuit is built for one proof shape), so the
// per-instance check reduces to structural equality and the blake3 fingerprint
// stays out of band — see ETH-NATIVE-WRAP.md §4.
func (c *Circuit) Define(api frontend.API) error {
	// --- gadgets (the load-bearing work; ETH-NATIVE-WRAP.md §4) ---
	//   bbReduce(api, x)            canonicalize a product mod BabyBearP
	//   bbMul/bbAdd/bbSub           BabyBear field ops
	//   extMul (deg-4)              BinomialExtensionField<BabyBear,4>
	//   poseidon2W16 / poseidon2W24 the fork permutations (fixed RC + MDS consts)
	//   challenger                  DuplexChallenger<Poseidon2-w16> — MUST squeeze
	//                               byte-identical betas/indices/alpha as Rust
	//                               (transcript fidelity = soundness; validate
	//                               against a fixture FIRST)
	//   merklePath                  Poseidon2 Merkle-path check
	//
	// TOOTH 1 — VK pin. recursion_vk_fingerprint (plonky3_recursion_impl.rs:646).
	//   Bake the trusted RecursionVk shape as a constant; assert the witness's
	//   structural fields match it. (No in-circuit blake3.)
	//
	// TOOTH 2 — the root. verify_recursive_batch_proof_with_config under
	//   ir2_leaf_wrap_config → verify_all_tables (plonky3_recursion_impl.rs:732):
	//     a. rebuild the Fiat-Shamir transcript; squeeze alpha, the FRI betas,
	//        and the 19 query indices;
	//     b. for each of the 19 queries: Poseidon2 Merkle-path openings for
	//        trace/quotient/FRI layers, the per-table constraint+quotient
	//        evaluation, the logup interaction-bus check, and the NPO tables
	//        (Poseidon2-w16/w24, recompose, expose_claim);
	//     c. FRI low-degree test: per-layer folding consistency + final-poly check.
	//
	// TOOTH 3 — the segment tooth (ivc_turn_chain.rs:2887-2905).
	//   api.AssertIsEqual(c.Root.ExposedSegment[0], c.GenesisRoot)
	//   api.AssertIsEqual(c.Root.ExposedSegment[1], c.FinalRoot)
	//   api.AssertIsEqual(c.Root.ExposedSegment[2], c.NumTurns)
	//   for i := 0; i < SegDigestWidth; i++ {
	//       api.AssertIsEqual(c.Root.ExposedSegment[3+i], c.ChainDigest[i])
	//   }
	_ = api
	return nil
}
</content>
