// Tests for the native-BN254 Merkle-path opening gadget (merkle_bn254.go):
// a plain-Go reference twin (built on poseidon2Bn254RefCompress), a pinned
// root KAT, gadget/reference differential, REJECT canaries (tampered leaf /
// wrong sibling / flipped bit / corrupted root / non-boolean bit), and the
// native-vs-emulated constraint measurement (the hashing swing of
// docs/deos/WRAP-NATIVE-HASH-DECISION.md).
package friverifier

import (
	"math/big"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
	"github.com/consensys/gnark/test"
)

// --- plain-Go reference twin ---

// merkleBn254RefRoot recomputes the root from (leaf, siblings, bits) with the
// reference compression — the non-circuit twin of ComputeMerkleRootBn254.
func merkleBn254RefRoot(leaf fr.Element, sibs []fr.Element, bits []uint64) fr.Element {
	node := leaf
	for i := range sibs {
		var l, r fr.Element
		if bits[i] == 0 {
			l, r = node, sibs[i]
		} else {
			l, r = sibs[i], node
		}
		node = poseidon2Bn254RefCompress(l, r)
	}
	return node
}

// --- pinned KAT ---

// Root of the depth-4 path: leaf=7, siblings=(100+i), bits=i%2, computed by
// the reference twin (which is itself pinned to the zkhash gold KAT via
// poseidon2_bn254_test.go). Pins the compression order and bit-steering
// convention against silent drift.
const merkleBn254KATRootHex = "0x2bd9273ae1bb6e81433d70a9b80e26c9d9473c99fea81a860151b4110cf5f27d"

func merkleBn254KATInputs() (fr.Element, []fr.Element, []uint64) {
	leaf := frFromU64(7)
	sibs := make([]fr.Element, 4)
	bits := make([]uint64, 4)
	for i := range sibs {
		sibs[i] = frFromU64(uint64(100 + i))
		bits[i] = uint64(i % 2)
	}
	return leaf, sibs, bits
}

func TestMerkleBn254RefMatchesPinnedRoot(t *testing.T) {
	leaf, sibs, bits := merkleBn254KATInputs()
	root := merkleBn254RefRoot(leaf, sibs, bits)
	t.Logf("depth-4 KAT root = 0x%s", root.Text(16))
	want := frFromHex(merkleBn254KATRootHex)
	if !root.Equal(&want) {
		t.Fatalf("reference root drifted from the pinned KAT:\n got 0x%s\nwant %s",
			root.Text(16), merkleBn254KATRootHex)
	}
	// REJECT polarity for the KAT itself: a flipped bit changes the root.
	bits[2] ^= 1
	if r2 := merkleBn254RefRoot(leaf, sibs, bits); r2.Equal(&want) {
		t.Fatal("flipped path bit still produced the pinned root")
	}
}

// --- gadget circuit + witness plumbing ---

type merkleBn254PathCircuit struct {
	Leaf     frontend.Variable
	Siblings []frontend.Variable
	PathBits []frontend.Variable
	Root     frontend.Variable `gnark:",public"`
}

func (c *merkleBn254PathCircuit) Define(api frontend.API) error {
	VerifyMerklePathBn254(api, c.Leaf, c.Siblings, c.PathBits, c.Root)
	return nil
}

func emptyMerkleBn254Circuit(depth int) *merkleBn254PathCircuit {
	return &merkleBn254PathCircuit{
		Siblings: make([]frontend.Variable, depth),
		PathBits: make([]frontend.Variable, depth),
	}
}

// merkleBn254Witness builds a consistent depth-D witness via the reference
// twin (mixed bit pattern, distinct siblings).
func merkleBn254Witness(depth int) *merkleBn254PathCircuit {
	leaf := frFromU64(0xDA_ECC0)
	sibs := make([]fr.Element, depth)
	bits := make([]uint64, depth)
	for i := 0; i < depth; i++ {
		sibs[i] = frFromU64(uint64(5000 + 13*i))
		bits[i] = uint64((i * 5 % 3) % 2) // 0,1,0,1,1,0,... mixed
	}
	root := merkleBn254RefRoot(leaf, sibs, bits)
	w := emptyMerkleBn254Circuit(depth)
	w.Leaf = leaf.BigInt(new(big.Int))
	w.Root = root.BigInt(new(big.Int))
	for i := 0; i < depth; i++ {
		w.Siblings[i] = sibs[i].BigInt(new(big.Int))
		w.PathBits[i] = new(big.Int).SetUint64(bits[i])
	}
	return w
}

// The gadget accepts reference-built paths (the differential: two independent
// implementations agree), at a shallow depth and the full FRI depth 24.
func TestMerkleBn254GadgetAcceptsReferencePaths(t *testing.T) {
	field := ecc.BN254.ScalarField()
	for _, depth := range []int{4, 24} {
		if err := test.IsSolved(emptyMerkleBn254Circuit(depth), merkleBn254Witness(depth), field); err != nil {
			t.Fatalf("depth %d: valid reference path rejected: %v", depth, err)
		}
	}
}

// REJECT canaries: every tampered component of a depth-8 opening must fail.
func TestMerkleBn254GadgetRejectsTampering(t *testing.T) {
	field := ecc.BN254.ScalarField()
	const depth = 8
	bump := func(v frontend.Variable) frontend.Variable {
		return new(big.Int).Add(v.(*big.Int), big.NewInt(1))
	}
	cases := []struct {
		name   string
		tamper func(w *merkleBn254PathCircuit)
	}{
		{"tampered leaf", func(w *merkleBn254PathCircuit) { w.Leaf = bump(w.Leaf) }},
		{"wrong sibling", func(w *merkleBn254PathCircuit) { w.Siblings[3] = bump(w.Siblings[3]) }},
		{"flipped path bit", func(w *merkleBn254PathCircuit) {
			b := w.PathBits[2].(*big.Int)
			w.PathBits[2] = new(big.Int).Xor(b, big.NewInt(1))
		}},
		{"corrupted root", func(w *merkleBn254PathCircuit) { w.Root = bump(w.Root) }},
		{"non-boolean path bit", func(w *merkleBn254PathCircuit) { w.PathBits[5] = big.NewInt(2) }},
	}
	for _, tc := range cases {
		w := merkleBn254Witness(depth)
		tc.tamper(w)
		if err := test.IsSolved(emptyMerkleBn254Circuit(depth), w, field); err == nil {
			t.Fatalf("%s: circuit accepted the tampered opening", tc.name)
		}
	}
}

// --- constraint measurement: native vs emulated per level (the swing) ---

// emulated equivalent: D levels of the fri_query.go commit-opening walk
// (friMerkleCompressStep over 8-lane BabyBear digests, one Poseidon2W16
// permutation per level).
type merkleEmulatedLevelsCircuit struct {
	Node [DigestWidth]frontend.Variable
	Sibs [][DigestWidth]frontend.Variable
	Bits []frontend.Variable
	Out  [DigestWidth]frontend.Variable
}

func (c *merkleEmulatedLevelsCircuit) Define(api frontend.API) error {
	bb := NewBBApi(api)
	d := c.Node
	for l := range c.Sibs {
		api.AssertIsBoolean(c.Bits[l])
		d = friMerkleCompressStep(bb, d, c.Sibs[l], c.Bits[l])
	}
	for i := 0; i < DigestWidth; i++ {
		api.AssertIsEqual(d[i], c.Out[i])
	}
	return nil
}

func emptyMerkleEmulatedCircuit(depth int) *merkleEmulatedLevelsCircuit {
	return &merkleEmulatedLevelsCircuit{
		Sibs: make([][DigestWidth]frontend.Variable, depth),
		Bits: make([]frontend.Variable, depth),
	}
}

func TestMerkleBn254NativeVsEmulatedConstraints(t *testing.T) {
	field := ecc.BN254.ScalarField()
	compile := func(c frontend.Circuit) int {
		cs, err := frontend.Compile(field, r1cs.NewBuilder, c)
		if err != nil {
			t.Fatalf("compile: %v", err)
		}
		return cs.GetNbConstraints()
	}

	n8 := compile(emptyMerkleBn254Circuit(8))
	n24 := compile(emptyMerkleBn254Circuit(24))
	nativePerLevel := (n24 - n8) / 16
	t.Logf("NATIVE Merkle opening: depth-8 %d R1CS, depth-24 %d R1CS, per-level %d", n8, n24, nativePerLevel)

	e1 := compile(emptyMerkleEmulatedCircuit(1))
	e2 := compile(emptyMerkleEmulatedCircuit(2))
	emulatedPerLevel := e2 - e1
	t.Logf("EMULATED Merkle opening (fri_query friMerkleCompressStep): 1-level %d R1CS, 2-level %d R1CS, per-level %d", e1, e2, emulatedPerLevel)
	t.Logf("SWING: emulated/native per Merkle level = %d/%d = %.1fx; a depth-24 path drops %d -> %d R1CS",
		emulatedPerLevel, nativePerLevel, float64(emulatedPerLevel)/float64(nativePerLevel),
		24*emulatedPerLevel, 24*nativePerLevel)

	if nativePerLevel >= emulatedPerLevel {
		t.Fatalf("native per-level (%d) is not below emulated per-level (%d); the re-architecture premise fails",
			nativePerLevel, emulatedPerLevel)
	}
}
