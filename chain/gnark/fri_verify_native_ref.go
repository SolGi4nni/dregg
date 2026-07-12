// Plain-Go (non-circuit) reference twin of the NATIVE-HASH single-matrix FRI
// verifier flow (fri_verify_native.go), so the native-hash gadget is
// differentially tested the same way the emulated one is (fri_verify_ref.go).
//
// Same fork semantics, two swaps (the wrap re-architecture,
// docs/deos/WRAP-NATIVE-HASH-DECISION.md):
//   - transcript = multiFieldChallengerRef (the MultiField32Challenger twin:
//     native BN254 duplex, BabyBear pack/split) instead of challengerRef;
//     commit roots observed as native BN254 digests.
//   - Merkle = native BN254 Poseidon2 nodes (poseidon2Bn254RefCompress) with
//     the radix-2^31 leaf packing, instead of the 8-lane Poseidon2-w16 tree.
//
// The fold arithmetic is UNCHANGED — it reuses friFoldCoreRef /
// invSFromParentRef / foldVectorRef verbatim (fri_query_ref.go): the fold is
// BabyBear field arithmetic, not hashing.
package friverifier

import (
	"math/big"

	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
)

// --- MultiField challenger ref extensions (grinding + ext sampling) ---------

// clone deep-copies the MultiField reference challenger; grinding tries each
// candidate witness on a fresh clone (grinding_challenger.rs:275/:309), because
// checkWitness mutates the transcript.
func (c *multiFieldChallengerRef) clone() *multiFieldChallengerRef {
	nc := &multiFieldChallengerRef{state: c.state}
	if c.outBuf != nil {
		nc.outBuf = append([]fr.Element(nil), c.outBuf...)
	}
	if c.fBuf != nil {
		nc.fBuf = append([]uint32(nil), c.fBuf...)
	}
	if c.fSqueezeBuf != nil {
		nc.fSqueezeBuf = append([]uint32(nil), c.fSqueezeBuf...)
	}
	return nc
}

// sampleExt squeezes a degree-4 extension challenge: four base samples, the
// first popped becoming coefficient 0 (sample_algebra_element), matching
// SampleBabyBearExt on the gadget.
func (c *multiFieldChallengerRef) sampleExt() bbExtRef {
	var e bbExtRef
	for i := range e {
		e[i] = c.sampleBabyBear()
	}
	return e
}

// checkWitness is GrindingChallenger::check_witness over the MultiField
// transcript (grinding_challenger.rs:40-46): 0 bits returns true without
// advancing; otherwise observe the witness and require the low `bits` bits of
// the next BabyBear sample to be zero. Mutates the challenger exactly as the
// verifier's transcript advances.
func (c *multiFieldChallengerRef) checkWitness(bits int, witness uint32) bool {
	if bits == 0 {
		return true
	}
	c.observeBabyBear(witness)
	return c.sampleBits(bits) == 0
}

// mfGrindRef brute-forces a valid PoW witness for the MultiField challenger's
// current transcript (the serial oracle of GrindingChallenger::grind), leaving
// `c` unmutated. Tests use it to compute a REAL grinding witness.
func mfGrindRef(c *multiFieldChallengerRef, bits int) uint32 {
	if bits == 0 {
		return 0
	}
	for w := uint64(0); w < BabyBearP; w++ {
		if c.clone().checkWitness(bits, uint32(w)) {
			return uint32(w)
		}
	}
	panic("mfGrindRef: no proof-of-work witness found (unreachable for bits < 31)")
}

// --- Native BN254 Merkle reference -------------------------------------------

// mfRefPackExt packs one extension element's 4 canonical coordinates into a
// native BN254 element, little-endian radix 2^31 — the reference twin of
// packBBExtToBn254 (injective on canonical coordinates: 4·31 = 124 < 254 bits).
func mfRefPackExt(e bbExtRef) fr.Element {
	acc := new(big.Int)
	for i := 3; i >= 0; i-- {
		acc.Lsh(acc, mfAbsorbRadixBits)
		acc.Add(acc, new(big.Int).SetUint64(uint64(e[i])))
	}
	var out fr.Element
	out.SetBigInt(acc)
	return out
}

// merkleLeafHashBn254Ref hashes a commit-phase leaf row of two extension evals
// into ONE native BN254 node: compress(pack(e0), pack(e1)) — the reference twin
// of friMerkleLeafHashNative.
func merkleLeafHashBn254Ref(e0, e1 bbExtRef) fr.Element {
	return poseidon2Bn254RefCompress(mfRefPackExt(e0), mfRefPackExt(e1))
}

// merkleCommitBn254Ref builds the whole native binary Merkle tree over a
// commit-phase evaluation vector f (leaf i = leafHash(f[2i], f[2i+1])) and
// returns the root plus every layer (layer 0 = leaves) for opening — the
// native twin of merkleCommitRef.
func merkleCommitBn254Ref(f []bbExtRef) (root fr.Element, layers [][]fr.Element) {
	h := len(f) / 2
	leaf := make([]fr.Element, h)
	for i := 0; i < h; i++ {
		leaf[i] = merkleLeafHashBn254Ref(f[2*i], f[2*i+1])
	}
	layers = append(layers, leaf)
	cur := leaf
	for len(cur) > 1 {
		next := make([]fr.Element, len(cur)/2)
		for i := range next {
			next[i] = poseidon2Bn254RefCompress(cur[2*i], cur[2*i+1])
		}
		layers = append(layers, next)
		cur = next
	}
	return cur[0], layers
}

// merkleOpenBn254Ref returns the native sibling path for leaf `index`, bottom-up.
func merkleOpenBn254Ref(layers [][]fr.Element, index int) []fr.Element {
	var path []fr.Element
	idx := index
	for l := 0; l < len(layers)-1; l++ {
		path = append(path, layers[l][idx^1])
		idx >>= 1
	}
	return path
}

// merkleRootFromOpeningBn254Ref reconstructs the root from the reconstructed
// sibling group, the path bits (LSB-first) and the native sibling nodes — the
// reference twin of the VerifyMerklePathBn254 walk (bit 0 => node left).
func merkleRootFromOpeningBn254Ref(e0, e1 bbExtRef, pathBits []uint32, siblings []fr.Element) fr.Element {
	node := merkleLeafHashBn254Ref(e0, e1)
	for l := range siblings {
		if pathBits[l] == 0 {
			node = poseidon2Bn254RefCompress(node, siblings[l])
		} else {
			node = poseidon2Bn254RefCompress(siblings[l], node)
		}
	}
	return node
}

// --- Native proof shape + reference verifier ----------------------------------

// friNativeQueryOpeningRef is one query's opening data for the native-hash
// flow: BabyBear evals (folded arithmetic), native BN254 Merkle paths.
type friNativeQueryOpeningRef struct {
	InitialEval  bbExtRef
	Siblings     []bbExtRef     // [R]
	MerkleProofs [][]fr.Element // [R][lfh_r] native sibling nodes, bottom-up
}

// friNativeProofRef is the native-hash single-matrix FRI proof: native BN254
// commit roots, BabyBear final poly, grinding witness, per-query openings.
// Betas and query indices are absent by design — re-derived from the
// MultiField transcript.
type friNativeProofRef struct {
	R           int
	CommitRoots []fr.Element // [R]
	FinalPoly   []bbExtRef   // [2^LogFinalPolyLen]
	PowWitness  uint32
	Queries     []friNativeQueryOpeningRef
}

// verifyFriNativeRef drives the MultiField transcript exactly as
// verifyFriNativeImpl does and runs the per-query native-Merkle fold chain.
// `c` is the challenger positioned at the commit phase.
func verifyFriNativeRef(c *multiFieldChallengerRef, cfg friConfigRef, p *friNativeProofRef) bool {
	return verifyFriNativeRefImpl(c, cfg, p, false)
}

// verifyFriNativeRefImpl carries the same test-only swapOrder flag as
// verifyFriRefImpl: swapOrder=true samples beta BEFORE observing the root (the
// transcript-order canary feeds a VALID proof through it and requires REJECT).
func verifyFriNativeRefImpl(c *multiFieldChallengerRef, cfg friConfigRef, p *friNativeProofRef, swapOrder bool) bool {
	R := p.R

	// Commit phase: observe the NATIVE root digest, commit PoW, sample beta.
	betas := make([]bbExtRef, R)
	for r := 0; r < R; r++ {
		if swapOrder {
			betas[r] = c.sampleExt()
			c.observeBn254Digest([]fr.Element{p.CommitRoots[r]})
		} else {
			c.observeBn254Digest([]fr.Element{p.CommitRoots[r]}) // verifier.rs:221
			if !c.checkWitness(cfg.CommitPowBits, 0) {
				return false // verifier.rs:222-224 (0 bits: always true)
			}
			betas[r] = c.sampleExt() // verifier.rs:225
		}
	}

	// verifier.rs:238 observe_algebra_slice(&final_poly).
	for _, coeff := range p.FinalPoly {
		c.observeBabyBearSlice(coeff[:])
	}

	// verifier.rs:249-251 the arity schedule (log_arity 1 per arity-2 round).
	for r := 0; r < R; r++ {
		c.observeBabyBear(1)
	}

	// verifier.rs:254 query PoW grinding.
	if !c.checkWitness(cfg.QueryPowBits, p.PowWitness) {
		return false
	}

	logGlobalMaxHeight := R + cfg.LogBlowup + cfg.LogFinalPolyLen
	for _, q := range p.Queries {
		// verifier.rs:268 index = sample_bits(log_global_max_height + extra).
		index := uint(c.sampleBits(logGlobalMaxHeight + cfg.ExtraQueryIndexBits))
		// verifier.rs:287 domain_index = index >> extra.
		domainIndex := index >> uint(cfg.ExtraQueryIndexBits)

		indexBits := make([]uint32, R)
		for i := 0; i < R; i++ {
			indexBits[i] = uint32((domainIndex >> uint(i)) & 1)
		}
		finalEval := finalPolyEvalRef(p.FinalPoly, domainIndex, logGlobalMaxHeight)

		// Per-query fold chain with NATIVE Merkle openings; the fold itself is
		// friFoldCoreRef/invSFromParentRef — the unchanged arithmetic residual.
		folded := q.InitialEval
		ok := true
		for r := 0; r < R; r++ {
			lfh := R - r - 1
			bR := indexBits[r]
			var e0, e1 bbExtRef
			if bR == 1 {
				e0, e1 = q.Siblings[r], folded
			} else {
				e0, e1 = folded, q.Siblings[r]
			}
			root := merkleRootFromOpeningBn254Ref(e0, e1, indexBits[r+1:r+1+lfh], q.MerkleProofs[r])
			if !root.Equal(&p.CommitRoots[r]) {
				ok = false
				break
			}
			parent := indexFromBits(indexBits, r+1, lfh)
			folded = friFoldCoreRef(e0, e1, betas[r], invSFromParentRef(parent, lfh, R, r))
		}
		if !ok || folded != finalEval {
			return false
		}
	}
	return true
}
