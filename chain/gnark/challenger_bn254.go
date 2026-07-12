// Native-BN254 Fiat-Shamir DuplexChallenger — the native twin of the emulated
// BabyBear challenger (challenger.go) for the re-architected wrap's OUTER
// shrink-layer transcript (docs/deos/WRAP-NATIVE-HASH-DECISION.md). The sponge
// permutation is the native width-3 Poseidon2Bn254 (~243 R1CS,
// poseidon2_bn254.go) instead of the emulated width-16 Poseidon2W16
// (~16,837 R1CS), so every duplexing costs ~69x less.
//
// Duplex semantics are the same p3_challenger::DuplexChallenger discipline the
// emulated gadget pins (challenger/src/duplex_challenger.rs at rev
// 82cfad73cd734d37a0d51953094f970c531817ec), instantiated at WIDTH=3, RATE=2,
// CAPACITY=1 — the standard width-3 duplex split, and the split plonky3's
// BN254-facing challengers use for their inner sponge:
//
//   - duplexing (duplex_challenger.rs:86): buffered inputs OVERWRITE
//     state[0..len(inBuf)] (the capacity lane carries over), the permutation is
//     applied, and the output buffer is refilled from state[0..RATE].
//   - observe (:148): any buffered output is stale and dropped, the value is
//     buffered, and a full rate triggers a duplexing.
//   - sample (:235): duplex iff input is pending or the output buffer is
//     drained, then pop from the END of the output buffer.
//   - sample_bits (:264): one sample reduced to its low n bits.
//
// Unlike the emulated gadget there is no per-value canonicity assertion: the
// absorbed values ARE native field elements — every representable witness value
// is canonical, so the fail-closed ingestion concern is vacuous here.
//
// NAMED FOLLOWUP (not this gadget): the BabyBear<->BN254 MultiField pack/split
// on the absorb/squeeze boundary — how a stream of BabyBear proof elements
// packs into BN254 absorptions and how a squeezed BN254 element splits back
// into BabyBear challenges (p3 MultiField32Challenger). This file is the native
// sponge core that boundary will drive.
package friverifier

import "github.com/consensys/gnark/frontend"

const (
	// bn254SpongeWidth is the duplex sponge width (the Poseidon2Bn254 state).
	bn254SpongeWidth = bn254P3Width // 3
	// bn254SpongeRate is the duplex rate; the remaining lane is capacity.
	bn254SpongeRate = 2
)

// ChallengerBn254 is the in-circuit native duplex sponge (rate 2, width 3,
// capacity 1). A fresh challenger holds state = [0; 3].
type ChallengerBn254 struct {
	api    frontend.API
	state  [bn254SpongeWidth]frontend.Variable
	inBuf  []frontend.Variable
	outBuf []frontend.Variable
}

// NewChallengerBn254 builds a fresh native challenger (state = [0; 3], empty
// input/output buffers).
func NewChallengerBn254(api frontend.API) *ChallengerBn254 {
	c := &ChallengerBn254{api: api}
	for i := range c.state {
		c.state[i] = frontend.Variable(0)
	}
	return c
}

// duplexing: the buffered inputs overwrite state[0..len(inBuf)] (capacity lane
// carries over), the width-3 native permutation is applied, and the output
// buffer is refilled from state[0..RATE].
func (c *ChallengerBn254) duplexing() {
	if len(c.inBuf) > bn254SpongeRate {
		panic("ChallengerBn254.duplexing: input buffer overflow")
	}
	for i, v := range c.inBuf {
		c.state[i] = v
	}
	c.inBuf = c.inBuf[:0]
	Poseidon2Bn254(c.api, &c.state)
	c.outBuf = append(c.outBuf[:0], c.state[:bn254SpongeRate]...)
}

// Observe absorbs one native field element: stale output is dropped, the value
// is buffered, and a full rate triggers a duplexing.
func (c *ChallengerBn254) Observe(v frontend.Variable) {
	c.outBuf = c.outBuf[:0] // any buffered output is now stale
	c.inBuf = append(c.inBuf, v)
	if len(c.inBuf) == bn254SpongeRate {
		c.duplexing()
	}
}

// ObserveSlice absorbs a run of elements in order.
func (c *ChallengerBn254) ObserveSlice(vs []frontend.Variable) {
	for _, v := range vs {
		c.Observe(v)
	}
}

// Sample squeezes one native-field challenge: duplex if there is pending input
// or the output buffer is drained, then pop from the END of the output buffer.
func (c *ChallengerBn254) Sample() frontend.Variable {
	if len(c.inBuf) > 0 || len(c.outBuf) == 0 {
		c.duplexing()
	}
	n := len(c.outBuf)
	v := c.outBuf[n-1]
	c.outBuf = c.outBuf[:n-1]
	return v
}

// bn254MaxSampleBits bounds SampleBits: 2^n must stay below the BN254 scalar
// modulus p (p has 254 bits and 2^253 < p, so n ≤ 253).
const bn254MaxSampleBits = 253

// SampleBits draws an n-bit challenge (e.g. a query index): one native sample
// reduced to its low n bits, returned as a single variable in [0, 2^n).
//
// Soundness of the reduction: the sample is decomposed at the FULL field bit
// width, and gnark's full-width ToBinary additionally constrains the bit string
// ≤ p-1 (the reducedness check in std/math/bits), so the decomposition is the
// UNIQUE canonical one — no v vs v+p aliasing — and the low n bits are exactly
// the low bits of the canonical representative, matching the plain-Go
// reference's big-integer masking.
func (c *ChallengerBn254) SampleBits(n int) frontend.Variable {
	bits := c.SampleBitsDecomposed(n)
	if n == 0 {
		return frontend.Variable(0)
	}
	return c.api.FromBinary(bits...)
}

// SampleBitsDecomposed is SampleBits returning the low n bits individually
// (each a constrained boolean), LSB-first — the form the Merkle-path
// index-steering consumes directly (VerifyMerklePathBn254 pathBits).
func (c *ChallengerBn254) SampleBitsDecomposed(n int) []frontend.Variable {
	if n < 0 || n > bn254MaxSampleBits {
		panic("ChallengerBn254.SampleBitsDecomposed: bit count out of range for BN254")
	}
	base := c.Sample()
	if n == 0 {
		return nil
	}
	// Full-width canonical decomposition (see SampleBits doc).
	bits := c.api.ToBinary(base)
	return bits[:n]
}
