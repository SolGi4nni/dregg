// Tests for the native-BN254 DuplexChallenger (challenger_bn254.go): a plain-Go
// reference twin over fr.Element, a pinned transcript KAT, gadget/reference
// differential across the full API surface (Observe/Sample/SampleBits/
// SampleBitsDecomposed), REJECT canaries (tampered challenge / tampered
// transcript / tampered index), a challenger->Merkle round-trip (sampled index
// bits steer a native path opening), and the native-vs-emulated duplexing
// constraint measurement.
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

// --- plain-Go reference twin (duplex discipline identical to challengerRef) ---

type challengerBn254Ref struct {
	state  [bn254SpongeWidth]fr.Element
	inBuf  []fr.Element
	outBuf []fr.Element
}

func newChallengerBn254Ref() *challengerBn254Ref { return &challengerBn254Ref{} }

func (c *challengerBn254Ref) duplexing() {
	if len(c.inBuf) > bn254SpongeRate {
		panic("challengerBn254Ref.duplexing: input buffer overflow")
	}
	copy(c.state[:], c.inBuf)
	c.inBuf = c.inBuf[:0]
	poseidon2Bn254Ref(&c.state)
	c.outBuf = append(c.outBuf[:0], c.state[:bn254SpongeRate]...)
}

func (c *challengerBn254Ref) observe(v fr.Element) {
	c.outBuf = c.outBuf[:0]
	c.inBuf = append(c.inBuf, v)
	if len(c.inBuf) == bn254SpongeRate {
		c.duplexing()
	}
}

func (c *challengerBn254Ref) observeSlice(vs []fr.Element) {
	for _, v := range vs {
		c.observe(v)
	}
}

func (c *challengerBn254Ref) sample() fr.Element {
	if len(c.inBuf) > 0 || len(c.outBuf) == 0 {
		c.duplexing()
	}
	v := c.outBuf[len(c.outBuf)-1]
	c.outBuf = c.outBuf[:len(c.outBuf)-1]
	return v
}

// sampleBits: low n bits of the CANONICAL representative of one sample — the
// semantics the gadget's canonical full-width decomposition enforces.
func (c *challengerBn254Ref) sampleBits(n int) *big.Int {
	if n < 0 || n > bn254MaxSampleBits {
		panic("challengerBn254Ref.sampleBits: bit count out of range")
	}
	v := c.sample()
	b := v.BigInt(new(big.Int))
	mask := new(big.Int).Lsh(big.NewInt(1), uint(n))
	mask.Sub(mask, big.NewInt(1))
	return b.And(b, mask)
}

// --- the shared transcript protocol (exercises every duplex edge) ---
//
// observe 11,22,33 (one full-rate duplexing at 2, one buffered) ->
// sample s0 (pending input forces a duplexing) -> sample s1 (buffered pop) ->
// sample s2 (drained buffer forces a duplexing) -> observe 44 (stales output)
// -> sample s3 -> sampleBits(16) (buffered pop + mask).

const challengerBn254KATBits = 16

func challengerBn254KATAbsorb() []uint64 { return []uint64{11, 22, 33} }

const challengerBn254KATExtra = uint64(44)

func challengerBn254RefTranscript() (s [4]fr.Element, idx *big.Int) {
	c := newChallengerBn254Ref()
	abs := challengerBn254KATAbsorb()
	for _, v := range abs {
		c.observe(frFromU64(v))
	}
	s[0] = c.sample()
	s[1] = c.sample()
	s[2] = c.sample()
	c.observe(frFromU64(challengerBn254KATExtra))
	s[3] = c.sample()
	idx = c.sampleBits(challengerBn254KATBits)
	return
}

// --- pinned KAT (regression pin; the permutation itself is pinned to the
// zkhash gold vector in poseidon2_bn254_test.go) ---

var challengerBn254KATHex = [4]string{
	"0x195f00382f107430de76a50bed6a40d20a8cc13d879aebaa3a841c66375df992",
	"0x17d47c3f41d6ebfc6b6342b05abfd3f38a80b9539d6d044e49430a38a6140ec4",
	"0x200547e0b2171b7a9d43b0bbf7399f22952d7d593575d3f4f8ef8c49f7918845",
	"0x2ffb78e229a28f3056d37670d48907d6a818c57d0437cf7b50457248b9db0bfc",
}

// low 16 bits of s4 (0x...d4db): pinned alongside the challenges.
const challengerBn254KATIdx = uint64(54491)

func TestChallengerBn254RefMatchesPinnedKAT(t *testing.T) {
	s, idx := challengerBn254RefTranscript()
	for i := range s {
		t.Logf("KAT s%d = 0x%s", i, s[i].Text(16))
	}
	t.Logf("KAT idx = %s", idx.String())
	for i := range s {
		want := frFromHex(challengerBn254KATHex[i])
		if !s[i].Equal(&want) {
			t.Fatalf("s%d drifted from the pinned KAT:\n got 0x%s\nwant %s", i, s[i].Text(16), challengerBn254KATHex[i])
		}
	}
	if idx.Uint64() != challengerBn254KATIdx {
		t.Fatalf("idx drifted from the pinned KAT: got %s want %d", idx.String(), challengerBn254KATIdx)
	}
}

// REJECT polarity for the KAT itself: a tampered absorbed value changes every
// downstream challenge (the transcript binds its inputs; non-degenerate).
func TestChallengerBn254RefTamperedAbsorbBites(t *testing.T) {
	tampered := newChallengerBn254Ref()
	abs := challengerBn254KATAbsorb()
	for i, v := range abs {
		if i == 0 {
			v++ // tamper the first absorbed element
		}
		tampered.observe(frFromU64(v))
	}
	got := tampered.sample()
	want := frFromHex(challengerBn254KATHex[0])
	if got.Equal(&want) {
		t.Fatal("tampered absorb still produced the pinned first challenge")
	}
}

// sampleBits determinism + range + low-bits-of-sample semantics.
func TestChallengerBn254RefSampleBits(t *testing.T) {
	for _, n := range []int{1, 5, 16, 31, 64, 253} {
		a := newChallengerBn254Ref()
		a.observe(frFromU64(9))
		b := newChallengerBn254Ref()
		b.observe(frFromU64(9))
		ia, ib := a.sampleBits(n), b.sampleBits(n)
		if ia.Cmp(ib) != 0 {
			t.Fatalf("sampleBits(%d) not deterministic: %s vs %s", n, ia, ib)
		}
		if ia.BitLen() > n {
			t.Fatalf("sampleBits(%d) = %s out of range", n, ia)
		}
		// low-bits-of-sample: mask the raw sample directly.
		c := newChallengerBn254Ref()
		c.observe(frFromU64(9))
		raw := c.sample()
		want := raw.BigInt(new(big.Int))
		mask := new(big.Int).Lsh(big.NewInt(1), uint(n))
		want.And(want, mask.Sub(mask, big.NewInt(1)))
		if ia.Cmp(want) != 0 {
			t.Fatalf("sampleBits(%d)=%s is not the low bits of the sample (%s)", n, ia, want)
		}
	}
}

// --- gadget vs reference differential (the full transcript in-circuit) ---

type challengerBn254Circuit struct {
	Absorbed [3]frontend.Variable
	Extra    frontend.Variable
	S        [4]frontend.Variable
	Idx      frontend.Variable
}

func (c *challengerBn254Circuit) Define(api frontend.API) error {
	ch := NewChallengerBn254(api)
	ch.ObserveSlice(c.Absorbed[:])
	for i := 0; i < 3; i++ {
		api.AssertIsEqual(ch.Sample(), c.S[i])
	}
	ch.Observe(c.Extra)
	api.AssertIsEqual(ch.Sample(), c.S[3])
	api.AssertIsEqual(ch.SampleBits(challengerBn254KATBits), c.Idx)
	return nil
}

func challengerBn254Witness() *challengerBn254Circuit {
	s, idx := challengerBn254RefTranscript()
	w := &challengerBn254Circuit{Extra: new(big.Int).SetUint64(challengerBn254KATExtra), Idx: idx}
	for i, v := range challengerBn254KATAbsorb() {
		w.Absorbed[i] = new(big.Int).SetUint64(v)
	}
	for i := range s {
		w.S[i] = s[i].BigInt(new(big.Int))
	}
	return w
}

// The gadget reproduces the reference transcript exactly (two independent
// implementations of the duplex discipline agree, in-circuit).
func TestChallengerBn254GadgetMatchesReference(t *testing.T) {
	if err := test.IsSolved(&challengerBn254Circuit{}, challengerBn254Witness(), ecc.BN254.ScalarField()); err != nil {
		t.Fatalf("gadget diverges from the native reference: %v", err)
	}
}

// REJECT canaries: tampered challenge, tampered query index, and a tampered
// TRANSCRIPT (absorbed value changed while the expected challenges are kept)
// must each be unsatisfiable.
func TestChallengerBn254GadgetRejectsTampering(t *testing.T) {
	field := ecc.BN254.ScalarField()
	bump := func(v frontend.Variable) frontend.Variable {
		return new(big.Int).Add(v.(*big.Int), big.NewInt(1))
	}
	cases := []struct {
		name   string
		tamper func(w *challengerBn254Circuit)
	}{
		{"tampered challenge", func(w *challengerBn254Circuit) { w.S[1] = bump(w.S[1]) }},
		{"tampered query index", func(w *challengerBn254Circuit) { w.Idx = bump(w.Idx) }},
		{"tampered transcript", func(w *challengerBn254Circuit) { w.Absorbed[0] = bump(w.Absorbed[0]) }},
		{"tampered late observe", func(w *challengerBn254Circuit) { w.Extra = bump(w.Extra) }},
	}
	for _, tc := range cases {
		w := challengerBn254Witness()
		tc.tamper(w)
		if err := test.IsSolved(&challengerBn254Circuit{}, w, field); err == nil {
			t.Fatalf("%s: gadget accepted the tampered transcript", tc.name)
		}
	}
}

// --- round-trip: challenger-sampled index bits steer a native Merkle opening
// (the exact composition the native FRI query walk performs) ---

type challengerBn254MerkleCircuit struct {
	Absorbed [2]frontend.Variable
	Leaf     frontend.Variable
	Siblings [4]frontend.Variable
	Root     frontend.Variable `gnark:",public"`
}

func (c *challengerBn254MerkleCircuit) Define(api frontend.API) error {
	ch := NewChallengerBn254(api)
	ch.ObserveSlice(c.Absorbed[:])
	bits := ch.SampleBitsDecomposed(4)
	VerifyMerklePathBn254(api, c.Leaf, c.Siblings[:], bits, c.Root)
	return nil
}

func challengerBn254MerkleWitness() *challengerBn254MerkleCircuit {
	// Draw the index from the reference challenger.
	ref := newChallengerBn254Ref()
	ref.observe(frFromU64(55))
	ref.observe(frFromU64(66))
	idx := ref.sampleBits(4)

	leaf := frFromU64(0xFEED)
	sibs := make([]fr.Element, 4)
	bits := make([]uint64, 4)
	for i := range sibs {
		sibs[i] = frFromU64(uint64(9000 + i))
		bits[i] = uint64(idx.Bit(i))
	}
	root := merkleBn254RefRoot(leaf, sibs, bits)

	w := &challengerBn254MerkleCircuit{
		Absorbed: [2]frontend.Variable{55, 66},
		Leaf:     leaf.BigInt(new(big.Int)),
		Root:     root.BigInt(new(big.Int)),
	}
	for i := range sibs {
		w.Siblings[i] = sibs[i].BigInt(new(big.Int))
	}
	return w
}

func TestChallengerBn254DrivesMerklePath(t *testing.T) {
	field := ecc.BN254.ScalarField()
	w := challengerBn254MerkleWitness()
	if err := test.IsSolved(&challengerBn254MerkleCircuit{}, w, field); err != nil {
		t.Fatalf("challenger-steered Merkle opening rejected a valid witness: %v", err)
	}
	// REJECT: an opening built for a DIFFERENT index (transcript decides the
	// index; the prover cannot pick it).
	bad := challengerBn254MerkleWitness()
	bad.Absorbed[1] = big.NewInt(67) // different transcript -> different index
	if err := test.IsSolved(&challengerBn254MerkleCircuit{}, bad, field); err == nil {
		t.Fatal("opening for the wrong transcript-sampled index was accepted")
	}
}

// --- constraint measurement: native vs emulated duplexing (the swing) ---

// challengerBn254CostCircuit: absorb NObserve elements, then one Sample (or
// SampleBits(NBits) when NBits > 0).
type challengerBn254CostCircuit struct {
	In    []frontend.Variable
	Out   frontend.Variable
	NBits int
}

func (c *challengerBn254CostCircuit) Define(api frontend.API) error {
	ch := NewChallengerBn254(api)
	ch.ObserveSlice(c.In)
	if c.NBits > 0 {
		api.AssertIsEqual(ch.SampleBits(c.NBits), c.Out)
	} else {
		api.AssertIsEqual(ch.Sample(), c.Out)
	}
	return nil
}

// challengerEmulatedCostCircuit: the same protocol through the emulated
// BabyBear challenger (challenger.go).
type challengerEmulatedCostCircuit struct {
	In    []frontend.Variable
	Out   frontend.Variable
	NBits int
}

func (c *challengerEmulatedCostCircuit) Define(api frontend.API) error {
	ch := NewChallenger(NewBBApi(api))
	ch.ObserveSlice(c.In)
	if c.NBits > 0 {
		api.AssertIsEqual(ch.SampleBits(c.NBits), c.Out)
	} else {
		api.AssertIsEqual(ch.Sample(), c.Out)
	}
	return nil
}

func TestChallengerBn254NativeVsEmulatedConstraints(t *testing.T) {
	field := ecc.BN254.ScalarField()
	compile := func(c frontend.Circuit) int {
		cs, err := frontend.Compile(field, r1cs.NewBuilder, c)
		if err != nil {
			t.Fatalf("compile: %v", err)
		}
		return cs.GetNbConstraints()
	}
	vars := func(n int) []frontend.Variable { return make([]frontend.Variable, n) }

	// Native: rate 2 — 2 observes = 1 duplexing, 4 observes = 2 duplexings.
	n1 := compile(&challengerBn254CostCircuit{In: vars(2)})
	n2 := compile(&challengerBn254CostCircuit{In: vars(4)})
	nBits := compile(&challengerBn254CostCircuit{In: vars(2), NBits: 31})
	nativePerDuplex := n2 - n1
	t.Logf("NATIVE challenger: observe2+sample %d R1CS, observe4+sample %d R1CS, per-duplexing %d; SampleBits(31) overhead %d",
		n1, n2, nativePerDuplex, nBits-n1)

	// Emulated: rate 8 — 8 observes = 1 duplexing, 16 observes = 2 duplexings.
	// (The per-duplexing delta includes the 8 per-observe canonicity checks —
	// the honest full per-absorb-block cost of the emulated lane.)
	e1 := compile(&challengerEmulatedCostCircuit{In: vars(8)})
	e2 := compile(&challengerEmulatedCostCircuit{In: vars(16)})
	eBits := compile(&challengerEmulatedCostCircuit{In: vars(8), NBits: 30})
	emulatedPerDuplex := e2 - e1
	t.Logf("EMULATED challenger: observe8+sample %d R1CS, observe16+sample %d R1CS, per-duplexing %d; SampleBits(30) overhead %d",
		e1, e2, emulatedPerDuplex, eBits-e1)

	t.Logf("SWING: emulated/native per duplexing = %d/%d = %.1fx",
		emulatedPerDuplex, nativePerDuplex, float64(emulatedPerDuplex)/float64(nativePerDuplex))

	if nativePerDuplex >= emulatedPerDuplex {
		t.Fatalf("native per-duplexing (%d) is not below emulated (%d); the re-architecture premise fails",
			nativePerDuplex, emulatedPerDuplex)
	}
}
