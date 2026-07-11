// FRI query proof-of-work (PoW / grinding) verification as a gnark circuit
// gadget — a load-bearing soundness component of the native ETH-wrap FRI
// verifier. ir2_leaf_wrap_config carries 16 query proof-of-work bits that
// contribute to the 6*19+16 = 130-bit soundness budget
// (docs/deos/ETH-NATIVE-WRAP.md §0). If the in-circuit verifier did NOT check
// the grinding witness, a cheating prover could skip the grinding work and the
// 16 bits would drop out of the budget — so this check is mandatory, and it must
// advance the Fiat-Shamir transcript byte-for-byte like the Rust verifier.
//
// Ground truth is p3_challenger::GrindingChallenger::check_witness as driven by
// the FRI verifier, at the workspace-pinned Plonky3 rev
// 82cfad73cd734d37a0d51953094f970c531817ec:
//
//   challenger/src/grinding_challenger.rs:40-46  check_witness (the DEFAULT
//   trait method, used by DuplexChallenger):
//
//       fn check_witness(&mut self, bits: usize, witness: Self::Witness) -> bool {
//           if bits == 0 { return true; }
//           self.observe(witness);
//           self.sample_bits(bits) == 0
//       }
//
//   fri/src/verifier.rs:254  the FRI query-phase call:
//
//       if !challenger.check_witness(params.query_proof_of_work_bits,
//                                    proof.query_pow_witness) {
//           return Err(FriError::InvalidPowWitness);
//       }
//
//   challenger/src/duplex_challenger.rs:264  sample_bits (the plain CanSampleBits
//   impl — one base sample reduced to its low `bits` bits):
//
//       let rand_f: F = self.sample();
//       rand_f.as_canonical_u64() as usize & ((1 << bits) - 1)
//
// SAMPLE_UNIFORM_BITS IS NOT ON THIS VERIFY PATH. The FRI verifier (verifier.rs
// :222 commit-phase, :254 query-phase) calls check_witness, whose default impl
// uses the plain sample_bits above. The rejection-sampled sample_uniform_bits
// (duplex_challenger.rs:431) is only reached via check_witness_uniform /
// grind_uniform (grinding_challenger.rs:75,90), and the ir2 leaf-wrap FRI config
// (fri/src/config.rs:82-83, query_proof_of_work_bits = 16, commit = 0) does not
// select the uniform variant. So this gadget implements plain check_witness, and
// sample_uniform_bits is intentionally NOT built here.
package friverifier

import "github.com/consensys/gnark/frontend"

// CheckWitness enforces the FRI proof-of-work grinding check in-circuit,
// mirroring GrindingChallenger::check_witness (grinding_challenger.rs:40-46).
//
// It absorbs the candidate `witness` into the Fiat-Shamir transcript
// (grinding_challenger.rs:44 self.observe(witness)) and asserts that the low
// `powBits` bits of the next base-field sample are all zero
// (grinding_challenger.rs:45 self.sample_bits(bits) == 0). A witness that fails
// the target yields an UNSATISFIABLE constraint system: fail-closed, exactly the
// FriError::InvalidPowWitness reject of verifier.rs:254 — a proof carrying a
// witness below the difficulty target cannot be produced.
//
// This mutates the challenger (one Observe, one Sample) precisely as the Rust
// verifier's challenger is advanced by the PoW check, so subsequent query-index
// sampling (verifier.rs:268 challenger.sample_bits(...)) stays in lockstep with
// the transcript.
//
// `witness` is a canonical BabyBear variable; Observe asserts canonicality at
// the ingestion boundary (fail-closed). `powBits` is a compile-time structural
// parameter (it drives the bit decomposition), matching the Rust constant
// params.query_proof_of_work_bits. It must satisfy 2^powBits < p, mirroring the
// Rust assert (1 << bits) < F::ORDER_U64 (grinding_challenger.rs:113,
// duplex_challenger.rs:265).
func CheckWitness(c *Challenger, powBits int, witness frontend.Variable) {
	if powBits == 0 {
		// grinding_challenger.rs:41 — 0 bits require no PoW; the Rust default
		// impl returns true WITHOUT observing the witness or advancing the
		// challenger. Mirror that: no observe, no constraint.
		return
	}
	// grinding_challenger.rs:44 — absorb the candidate witness into the transcript.
	c.Observe(witness)
	// grinding_challenger.rs:45 + duplex_challenger.rs:264 — the low powBits bits
	// of the next base sample must all be zero. SampleBitsDecomposed draws that
	// single base sample and returns its low powBits bits (bits[0] = LSB);
	// asserting each is zero is exactly sample_bits(powBits) == 0.
	bits := c.SampleBitsDecomposed(powBits)
	for _, b := range bits {
		c.bb.api.AssertIsEqual(b, 0)
	}
}
