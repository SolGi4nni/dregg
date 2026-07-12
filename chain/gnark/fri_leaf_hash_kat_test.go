// CROSS-SIDE leaf-hash KATs: the gnark native Merkle LEAF hash must equal the
// Rust shrink layer's MMCS leaf hash (circuit-prove/src/dregg_outer_config.rs,
// OuterHash = MultiField32PaddingFreeSponge<BabyBear, Bn254, Poseidon2Bn254<3>,
// 3, 2, 1>) — a divergence means the gnark verifier REJECTS every valid shrink
// proof.
//
// PROVENANCE OF THE PINNED DIGESTS: computed by the REAL Rust-side hasher — a
// harness instantiating the fork's own MultiField32PaddingFreeSponge and
// MerkleTreeMmcs types at the workspace-pinned Plonky3 rev
// 82cfad73cd734d37a0d51953094f970c531817ec, over the Poseidon2Bn254<3>
// permutation built from the RC3 tables spliced VERBATIM from
// dregg_outer_config.rs (the harness asserts the shared Rust/gnark [0,1,2]
// gold KAT before emitting any digest, so the permutation is pinned to the
// same function both sides already agree on). The `mmcs root` value comes from
// an actual MerkleTreeMmcs::commit of the 2x8 matrix [leafA; leafB] at
// cap_height 0 — the real MMCS commit path, not the sponge in isolation.
//
// These tests are therefore a REAL cross-side agreement (gnark == Rust MMCS
// digest on shared inputs), not a gnark-only round-trip.
package friverifier

import (
	"math/rand"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/test"
)

// bbPm1 = p - 1, the maximum canonical BabyBear digit (shifted digit = p).
const bbPm1 = uint32(BabyBearP - 1)

// Pinned inputs (BabyBear canonical values) and their Rust-side digests.
var (
	katLeafA = []uint32{0, 1, bbPm1, 3, 4, 5, 6, 7}
	katLeafB = []uint32{7, 6, 5, 4, bbPm1, 2, 1, 0}
	kat4     = []uint32{42, 0, bbPm1, 1}
	kat16    = append(append([]uint32{}, katLeafA...), katLeafB...)
	kat20    = append(append([]uint32{}, kat16...), 11, 22, 33, 44)

	// Digest of leafA: one 8-limb slot, one permutation.
	katLeafAHex = "0x2ba8b0c66b63687cd86e4c52baa38aad9d1c2fcba9df2fb4deab1f69a9919101"
	katLeafBHex = "0x1ebed07295259c9085b8735dab239495adeb8278b8994dca56e833b15f758307"
	// 4 limbs: a partial slot (shifted packing keeps lengths distinct).
	kat4Hex = "0x2c1d1415d7a6209522147d85acc07a4e57ead13e8b1880c642b7fdfa15afeb54"
	// 16 limbs: two rate slots, ONE permutation.
	kat16Hex = "0x01e162b091a9f8702ae974ed06ffe42d6c7273bcf54f72236495a67ff3958d80"
	// 20 limbs: a full block + a partial second block (slot-1 retention path).
	kat20Hex = "0x21f3e87124673d957b16d062769c4c6c0ae8cd9927925be5d09976a3b7101e83"
	// MerkleTreeMmcs::commit root of the 2x8 matrix [leafA; leafB], cap 0.
	katMmcsRootHex = "0x0cad604ef568e95b9030970fb98da86f70dd5fc1c3777829bb4f8fae3792db76"
)

// ---------------------------------------------------------------------------
// Reference twin vs the Rust MMCS digests.
// ---------------------------------------------------------------------------

func TestLeafHashRefMatchesRustMmcsKAT(t *testing.T) {
	cases := []struct {
		name  string
		limbs []uint32
		want  string
	}{
		{"leafA-8", katLeafA, katLeafAHex},
		{"leafB-8", katLeafB, katLeafBHex},
		{"partial-4", kat4, kat4Hex},
		{"two-slots-16", kat16, kat16Hex},
		{"two-blocks-20", kat20, kat20Hex},
	}
	for _, tc := range cases {
		got := mfRefSpongeHash(tc.limbs)
		want := frFromHex(tc.want)
		if !got.Equal(&want) {
			t.Fatalf("%s: ref sponge = %s, Rust MMCS digest = %s", tc.name, got.String(), want.String())
		}
	}

	// The leaf-row form (two extension evals, e0 coefficients first) is the
	// same 8 limbs.
	e0 := bbExtRef{katLeafA[0], katLeafA[1], katLeafA[2], katLeafA[3]}
	e1 := bbExtRef{katLeafA[4], katLeafA[5], katLeafA[6], katLeafA[7]}
	gotLeaf := merkleLeafHashBn254Ref(e0, e1)
	wantLeaf := frFromHex(katLeafAHex)
	if !gotLeaf.Equal(&wantLeaf) {
		t.Fatalf("merkleLeafHashBn254Ref diverges from the Rust MMCS leaf digest")
	}

	// The MMCS ROOT: compress(leafA, leafB) must equal the root of an actual
	// Rust MerkleTreeMmcs::commit over [leafA; leafB].
	root := poseidon2Bn254RefCompress(mfRefSpongeHash(katLeafA), mfRefSpongeHash(katLeafB))
	wantRoot := frFromHex(katMmcsRootHex)
	if !root.Equal(&wantRoot) {
		t.Fatalf("ref tree root = %s, Rust MerkleTreeMmcs root = %s", root.String(), wantRoot.String())
	}

	// REJECT canary (the comparisons are not vacuous): one tampered limb must
	// change the digest.
	tampered := append([]uint32{}, katLeafA...)
	tampered[2] = tampered[2] - 1
	gotTampered := mfRefSpongeHash(tampered)
	if gotTampered.Equal(&wantLeaf) {
		t.Fatal("tampered leaf reproduced the pinned digest")
	}

	// SHIFT canary: the +1 shifted encoding is load-bearing — a trailing zero
	// limb must yield a DIFFERENT digest (the unshifted stand-in this test
	// retired could not distinguish them inside one slot).
	withTrailingZero := mfRefSpongeHash([]uint32{42, 0, bbPm1, 1, 0})
	without := mfRefSpongeHash([]uint32{42, 0, bbPm1, 1})
	if withTrailingZero.Equal(&without) {
		t.Fatal("shifted packing failed to distinguish a trailing zero limb")
	}
}

// ---------------------------------------------------------------------------
// Gadget vs the Rust MMCS digests (through the gnark test engine).
// ---------------------------------------------------------------------------

type mfHashKATCircuit struct {
	Limbs  []frontend.Variable
	Digest frontend.Variable
}

func (c *mfHashKATCircuit) Define(api frontend.API) error {
	api.AssertIsEqual(multiField32HashNative(api, c.Limbs), c.Digest)
	return nil
}

type leafHashKATCircuit struct {
	E0, E1 BBExt
	Digest frontend.Variable
}

func (c *leafHashKATCircuit) Define(api frontend.API) error {
	api.AssertIsEqual(friMerkleLeafHashNative(api, c.E0, c.E1), c.Digest)
	return nil
}

// mmcsRootKATCircuit pins the full two-leaf tree: leaf sponge + node compress
// against the root of an actual Rust MerkleTreeMmcs::commit.
type mmcsRootKATCircuit struct {
	A0, A1, B0, B1 BBExt
	Root           frontend.Variable
}

func (c *mmcsRootKATCircuit) Define(api frontend.API) error {
	la := friMerkleLeafHashNative(api, c.A0, c.A1)
	lb := friMerkleLeafHashNative(api, c.B0, c.B1)
	api.AssertIsEqual(Poseidon2Bn254Compress(api, la, lb), c.Root)
	return nil
}

func limbsToExts(limbs []uint32) (BBExt, BBExt) {
	e0 := bbExtRef{limbs[0], limbs[1], limbs[2], limbs[3]}
	e1 := bbExtRef{limbs[4], limbs[5], limbs[6], limbs[7]}
	return extToVars(e0), extToVars(e1)
}

func TestLeafHashGadgetMatchesRustMmcsKAT(t *testing.T) {
	field := ecc.BN254.ScalarField()

	cases := []struct {
		name  string
		limbs []uint32
		want  string
	}{
		{"leafA-8", katLeafA, katLeafAHex},
		{"leafB-8", katLeafB, katLeafBHex},
		{"partial-4", kat4, kat4Hex},
		{"two-slots-16", kat16, kat16Hex},
		{"two-blocks-20", kat20, kat20Hex},
	}
	for _, tc := range cases {
		tmpl := &mfHashKATCircuit{Limbs: make([]frontend.Variable, len(tc.limbs))}
		w := &mfHashKATCircuit{Limbs: make([]frontend.Variable, len(tc.limbs))}
		for i, v := range tc.limbs {
			w.Limbs[i] = v
		}
		w.Digest = mustHex(tc.want)
		if err := test.IsSolved(tmpl, w, field); err != nil {
			t.Fatalf("%s: gadget sponge != Rust MMCS digest: %v", tc.name, err)
		}
	}

	// The leaf-row form.
	e0, e1 := limbsToExts(katLeafA)
	if err := test.IsSolved(&leafHashKATCircuit{},
		&leafHashKATCircuit{E0: e0, E1: e1, Digest: mustHex(katLeafAHex)}, field); err != nil {
		t.Fatalf("friMerkleLeafHashNative != Rust MMCS leaf digest: %v", err)
	}

	// The MMCS root through the gadget tree path.
	a0, a1 := limbsToExts(katLeafA)
	b0, b1 := limbsToExts(katLeafB)
	if err := test.IsSolved(&mmcsRootKATCircuit{},
		&mmcsRootKATCircuit{A0: a0, A1: a1, B0: b0, B1: b1, Root: mustHex(katMmcsRootHex)}, field); err != nil {
		t.Fatalf("gadget tree root != Rust MerkleTreeMmcs root: %v", err)
	}

	// REJECT canary: a tampered coordinate must NOT satisfy the pinned digest.
	tampered := append([]uint32{}, katLeafA...)
	tampered[5]++
	t0, t1 := limbsToExts(tampered)
	if err := test.IsSolved(&leafHashKATCircuit{},
		&leafHashKATCircuit{E0: t0, E1: t1, Digest: mustHex(katLeafAHex)}, field); err == nil {
		t.Fatal("gadget ACCEPTED a tampered leaf against the pinned digest")
	}
}

// ---------------------------------------------------------------------------
// Differential: gadget sponge == reference sponge across limb counts that
// exercise every absorb path (partial slot, slot boundary, block boundary,
// slot-retention in a partial second block).
// ---------------------------------------------------------------------------

func TestLeafHashDifferentialRefVsGadget(t *testing.T) {
	field := ecc.BN254.ScalarField()
	rng := rand.New(rand.NewSource(31337))

	for _, n := range []int{1, 3, 7, 8, 9, 15, 16, 17, 20, 24, 31, 32, 33, 40} {
		limbs := make([]uint32, n)
		for i := range limbs {
			limbs[i] = uint32(rng.Uint64() % BabyBearP)
		}
		want := mfRefSpongeHash(limbs)

		tmpl := &mfHashKATCircuit{Limbs: make([]frontend.Variable, n)}
		w := &mfHashKATCircuit{Limbs: make([]frontend.Variable, n)}
		for i, v := range limbs {
			w.Limbs[i] = v
		}
		w.Digest = frToBig(want)
		if err := test.IsSolved(tmpl, w, field); err != nil {
			t.Fatalf("n=%d: gadget sponge != reference sponge: %v", n, err)
		}
	}
}
