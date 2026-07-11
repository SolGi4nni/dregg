// Plain-Go (non-circuit) reference twin of the FRI proof-of-work grinding
// check. The circuit gadget in grinding.go is differentially tested against
// this, and this is pinned lane-for-lane to the Rust GrindingChallenger at the
// workspace-pinned Plonky3 rev 82cfad73cd734d37a0d51953094f970c531817ec:
//
//   - challenger/src/grinding_challenger.rs:40-46  check_witness(): if bits==0
//     return true; else observe(witness), then sample_bits(bits) == 0.
//   - challenger/src/duplex_challenger.rs:264       sample_bits(): low `bits`
//     bits of one base sample (challengerRef.sampleBits, challenger_ref.go).
//   - challenger/src/grinding_challenger.rs:106-227 grind(): brute-force search
//     for the smallest witness whose check_witness passes. The SIMD search is
//     documented (l.160) as "semantically equivalent to serially trying
//     witnesses"; grindRef below is that serial oracle, used by tests to compute
//     a real grinding witness.
package friverifier

// clone deep-copies the reference challenger. grind tries each candidate witness
// on a fresh clone of the challenger (grinding_challenger.rs:275 / :309
// `self.clone().check_witness(...)`), because check_witness mutates the
// transcript.
func (c *challengerRef) clone() *challengerRef {
	nc := &challengerRef{state: c.state}
	if c.inBuf != nil {
		nc.inBuf = append([]uint32(nil), c.inBuf...)
	}
	if c.outBuf != nil {
		nc.outBuf = append([]uint32(nil), c.outBuf...)
	}
	return nc
}

// checkWitness is the native twin of GrindingChallenger::check_witness
// (grinding_challenger.rs:40-46). It MUTATES the challenger (one observe, one
// sample), exactly as the Rust FRI verifier's challenger is advanced by the PoW
// check (verifier.rs:254). Returns true iff the low `bits` bits of the base
// sample drawn after observing `witness` are all zero.
func (c *challengerRef) checkWitness(bits int, witness uint32) bool {
	if bits == 0 {
		return true // grinding_challenger.rs:41 — no PoW, no observe.
	}
	c.observe(witness)              // grinding_challenger.rs:44
	return c.sampleBits(bits) == 0 // grinding_challenger.rs:45 (sample_bits==0)
}

// grindRef brute-forces a valid PoW witness for the challenger's current
// transcript, the serial oracle of DuplexChallenger::grind
// (grinding_challenger.rs:106). It returns the smallest canonical BabyBear
// element `w` for which check_witness passes on a fresh clone (so `c` itself is
// left unmutated). Used by tests to compute a real grinding witness by brute
// force over small bit counts.
//
// Mirrors the Rust invariants: bits==0 returns 0 (grind returns F::ZERO,
// grinding_challenger.rs:117); otherwise every candidate is tried on a clone
// (l.275/309) and the found witness satisfies check_witness by construction.
func grindRef(c *challengerRef, bits int) uint32 {
	if bits == 0 {
		return 0
	}
	for w := uint64(0); w < BabyBearP; w++ {
		if c.clone().checkWitness(bits, uint32(w)) {
			return uint32(w)
		}
	}
	panic("grindRef: no proof-of-work witness found (unreachable: a solution always exists for bits < 31)")
}

// firstRejectingWitness returns the smallest canonical BabyBear element that the
// PoW check REJECTS for the challenger's current transcript (a witness whose low
// `bits` sampled bits are not all zero). Used by tests to obtain a
// deterministically-invalid witness (no flakiness from picking a random wrong
// witness that might coincidentally satisfy the target). `c` is left unmutated.
func firstRejectingWitness(c *challengerRef, bits int) uint32 {
	for w := uint64(0); w < BabyBearP; w++ {
		if !c.clone().checkWitness(bits, uint32(w)) {
			return uint32(w)
		}
	}
	panic("firstRejectingWitness: every witness passes (unreachable for bits >= 1)")
}
