// Package friverifier is dregg's native Ethereum wrap circuit.
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
// STATUS: gadget layer landed (babybear.go, babybear_ext.go,
// poseidon2_w16.go) + the pinned public-input contract and tooth 3 wired
// below. Teeth 1-2 (VK pin, the batch-STARK/FRI verification itself) are the
// remaining milestone-2 work.
package friverifier

import "github.com/consensys/gnark/frontend"

// DigestWidth is the number of BabyBear lanes in each root/digest of the
// pinned 25-lane public-input contract (see Publics).
const DigestWidth = 8

// NumPublicInputs is the pinned public-input lane count:
// genesis_root[8] ++ final_root[8] ++ num_turns ++ chain_digest[8] = 25.
const NumPublicInputs = 3*DigestWidth + 1

// Publics are the wrap circuit's Groth16 public inputs, in the EXACT pinned
// 25-lane order shared with the Solidity side:
//
//	genesis_root[0..8] ++ final_root[0..8] ++ num_turns ++ chain_digest[0..8]
//
// Every lane is a canonical BabyBear residue (strictly < 0x78000001 =
// 2013265921); Define enforces this fail-closed. The Solidity ABI shape is
// (uint32[8] genesisRoot, uint32[8] finalRoot, uint32 numTurns,
// uint32[8] chainDigest). gnark exposes public inputs in struct field order,
// which matches the pinned order below.
type Publics struct {
	GenesisRoot [DigestWidth]frontend.Variable `gnark:",public"`
	FinalRoot   [DigestWidth]frontend.Variable `gnark:",public"`
	NumTurns    frontend.Variable              `gnark:",public"`
	ChainDigest [DigestWidth]frontend.Variable `gnark:",public"`
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
	// The expose_claim table's exposed segment, in the pinned 25-lane order
	// (tooth 3 compares this to Publics lane by lane).
	ExposedSegment [NumPublicInputs]frontend.Variable
	// (… trace/quotient openings, logup bus values, NPO Poseidon2 rows, etc.)
}

// Circuit is the native wrap statement: "this root proof verifies AND exposes
// exactly these public inputs."
type Circuit struct {
	Publics
	Root RootProofWitness
}

// Define lays out the three teeth. The VK (tooth 1) is best baked as a circuit
// CONSTANT at setup (the circuit is built for one proof shape), so the
// per-instance check reduces to structural equality and the blake3 fingerprint
// stays out of band — see ETH-NATIVE-WRAP.md §4.
func (c *Circuit) Define(api frontend.API) error {
	bb := NewBBApi(api)

	// Fail-closed lane hygiene: every public input is a canonical BabyBear
	// residue (< 2013265921). A lane holding p, or anything in [p, 2^31), or
	// any larger BN254 value, is rejected here.
	for i := 0; i < DigestWidth; i++ {
		bb.AssertIsCanonical(c.GenesisRoot[i])
		bb.AssertIsCanonical(c.FinalRoot[i])
		bb.AssertIsCanonical(c.ChainDigest[i])
	}
	bb.AssertIsCanonical(c.NumTurns)

	// TOOTH 1 — VK pin. recursion_vk_fingerprint (plonky3_recursion_impl.rs:646).
	//   Bake the trusted RecursionVk shape as a constant; assert the witness's
	//   structural fields match it. (No in-circuit blake3.)
	//   TODO(milestone 2): implement once the witness exporter fixes the layout.
	//
	// TOOTH 2 — the root. verify_recursive_batch_proof_with_config under
	//   ir2_leaf_wrap_config → verify_all_tables (plonky3_recursion_impl.rs:732):
	//     a. rebuild the Fiat-Shamir transcript (DuplexChallenger over
	//        Poseidon2W16 below); squeeze alpha, the FRI betas, and the 19
	//        query indices — MUST be byte-identical to the Rust challenger
	//        (transcript fidelity = soundness; validate against a fixture
	//        FIRST);
	//     b. for each of the 19 queries: Poseidon2 Merkle-path openings for
	//        trace/quotient/FRI layers, the per-table constraint+quotient
	//        evaluation (BBExt arithmetic), the logup interaction-bus check,
	//        and the NPO tables (Poseidon2-w16/w24, recompose, expose_claim);
	//     c. FRI low-degree test: per-layer folding consistency + final-poly
	//        check.
	//   TODO(milestone 2): the gadgets exist (BBApi.Add/Sub/Mul, BBApi.ExtMul,
	//   BBApi.Poseidon2W16); this is the multi-week assembly.
	//
	// TOOTH 3 — the segment tooth (ivc_turn_chain.rs:2887-2905): the proof's
	// exposed segment IS the public-input vector, lane for lane, in the pinned
	// 25-lane order.
	k := 0
	for i := 0; i < DigestWidth; i++ {
		api.AssertIsEqual(c.Root.ExposedSegment[k], c.GenesisRoot[i])
		k++
	}
	for i := 0; i < DigestWidth; i++ {
		api.AssertIsEqual(c.Root.ExposedSegment[k], c.FinalRoot[i])
		k++
	}
	api.AssertIsEqual(c.Root.ExposedSegment[k], c.NumTurns)
	k++
	for i := 0; i < DigestWidth; i++ {
		api.AssertIsEqual(c.Root.ExposedSegment[k], c.ChainDigest[i])
		k++
	}
	return nil
}
