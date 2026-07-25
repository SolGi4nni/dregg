// Light unit test of the peer-wrap public-input MAPPING (BindPeerFinalityLanes)
// in ISOLATION — the one new gadget the peer wrap adds over SettlementCircuit.
// This compiles + solves a tiny circuit (a handful of felts + two 128-bit
// splits), so it is cheap: it does NOT touch the multi-million-constraint FRI
// verification body, which is exercised end-to-end only against a REAL exported
// LC shrink fixture.
//
// THE GNARK-BUILD RESIDUAL (named): PeerFinalityCircuit.Define (the full wrap)
// compiles via `go build`, but proving it end-to-end needs an exported
// light-client shrink fixture — produced by the LC prove path
// (descriptor_by_name → prove_vm_descriptor2 → apex → BN254-native re-prove,
// Rust, off-box). Emitting that fixture + running the single-party dev Groth16
// setup to generate the peer verifier is the remaining gnark step, the twin of
// settlement_snark_test.go's TestSettlementGroth16EndToEnd. The REAL VK
// trusted-setup ceremony on top of that is the ember-gated DEPLOY residual.
package friverifier

import (
	"math/big"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/test"
)

// peerLaneBindCircuit exercises ONLY BindPeerFinalityLanes over a synthetic
// claim channel.
type peerLaneBindCircuit struct {
	Pub   PeerPublics
	Claim []frontend.Variable
	m     PeerLaneMap
}

func (c *peerLaneBindCircuit) Define(api frontend.API) error {
	bb := NewBBApi(api)
	BindPeerFinalityLanes(bb, c.Claim, c.m, &c.Pub)
	return nil
}

// packRootFeltsRef mirrors BindPeerFinalityLanes' radix-2^31 Horner packing
// host-side, then splits at 128 bits — the reference (rootHi, rootLo) an honest
// prover fills.
func packRootFeltsRef(claim []uint64, rootLanes []int) (hi, lo *big.Int) {
	base := new(big.Int).Lsh(big.NewInt(1), RootLimbRadixBits)
	packed := big.NewInt(0)
	for _, li := range rootLanes {
		packed.Mul(packed, base)
		packed.Add(packed, new(big.Int).SetUint64(claim[li]))
	}
	mask := new(big.Int).Sub(new(big.Int).Lsh(big.NewInt(1), 128), big.NewInt(1))
	lo = new(big.Int).And(packed, mask)
	hi = new(big.Int).Rsh(packed, 128)
	return hi, lo
}

func solve(t *testing.T, m PeerLaneMap, claim []uint64, chainID, height, rootHi, rootLo *big.Int) error {
	t.Helper()
	circ := &peerLaneBindCircuit{Claim: make([]frontend.Variable, len(claim)), m: m}
	w := &peerLaneBindCircuit{Claim: make([]frontend.Variable, len(claim)), m: m}
	for i, v := range claim {
		w.Claim[i] = new(big.Int).SetUint64(v)
	}
	w.Pub = PeerPublics{ChainID: chainID, Height: height, RootHi: rootHi, RootLo: rootLo}
	return test.IsSolved(circ, w, ecc.BN254.ScalarField())
}

// TestPeerLaneBindAccepts: each per-chain map accepts an honest witness whose
// (chainId, height, rootHi, rootLo) match the mapping over the LC statement.
func TestPeerLaneBindAccepts(t *testing.T) {
	cases := []struct {
		name   string
		m      PeerLaneMap
		claim  []uint64 // the LC ExposeClaim channel felts
		height uint64   // honest finalized height
	}{
		// eth: [committee_root, fin_state_root×9 limbs (full 256-bit, MSB-first),
		// domain_gvr]; no height felt. Root value 123456789 sits in the LSB limb.
		{"eth", EthLcPeerMap(PeerChainIdEth), []uint64{0xC0FFEE, 0, 0, 0, 0, 0, 0, 0, 0, 123456789, 0x7ABCDEF}, 0},
		// base: same map, chainId 8453; root value 222 in the LSB limb.
		{"base", EthLcPeerMap(PeerChainIdBase), []uint64{111, 0, 0, 0, 0, 0, 0, 0, 0, 222, 333}, 0},
		// tm: [next_vals_root, app_hash×9 limbs (full 256-bit, MSB-first),
		// chain_id=118]; app_hash value 987654321 in the LSB limb, chain_id at PI 10.
		{"tm", TmLcPeerMap, []uint64{777, 0, 0, 0, 0, 0, 0, 0, 0, 987654321, 118}, 0},
		// sol: [anchor_root, bank_root×9 limbs, slot]; height := slot (PI 10). Root
		// value 555666777 in the LSB limb.
		{"sol", SolLcPeerMap, []uint64{444, 0, 0, 0, 0, 0, 0, 0, 0, 555666777, 250000000}, 250000000},
		// mid: [anchor_root, target_root×9 limbs, round, era]; height := round (PI
		// 10), era at PI 11. Root value 2013265900 in the LSB limb.
		{"mid", MidLcPeerMap, []uint64{1, 0, 0, 0, 0, 0, 0, 0, 0, 2013265900, 42, 7}, 42},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			hi, lo := packRootFeltsRef(tc.claim, tc.m.RootLanes)
			if err := solve(t, tc.m, tc.claim, tc.m.ChainID,
				new(big.Int).SetUint64(tc.height), hi, lo); err != nil {
				t.Fatalf("%s: honest witness REJECTED: %v", tc.name, err)
			}
		})
	}
}

// TestPeerLaneBindRejects: the mapping is a real binding — a wrong lane fails.
func TestPeerLaneBindRejects(t *testing.T) {
	base := SolLcPeerMap
	// [anchor_root, bank_root×9 limbs (root value in LSB limb), slot@PI10].
	claim := []uint64{444, 0, 0, 0, 0, 0, 0, 0, 0, 555666777, 250000000}
	hi, lo := packRootFeltsRef(claim, base.RootLanes)
	height := big.NewInt(250000000)

	t.Run("wrong-chainId", func(t *testing.T) {
		if err := solve(t, base, claim, big.NewInt(999), height, hi, lo); err == nil {
			t.Fatal("accepted a chainId != the baked per-chain constant")
		}
	})
	t.Run("wrong-height", func(t *testing.T) {
		// sol binds height := slot; a mismatched height must fail.
		if err := solve(t, base, claim, base.ChainID, big.NewInt(1), hi, lo); err == nil {
			t.Fatal("accepted a height != the LC slot felt")
		}
	})
	t.Run("wrong-rootLo", func(t *testing.T) {
		if err := solve(t, base, claim, base.ChainID, height, hi, new(big.Int).Add(lo, big.NewInt(1))); err == nil {
			t.Fatal("accepted a rootLo the LC root felt does not pack to")
		}
	})
	t.Run("nonzero-rootHi-for-low-root", func(t *testing.T) {
		// The 9-limb root here has only the LSB limb set, so it packs to < 2^128
		// and rootHi MUST be 0.
		if err := solve(t, base, claim, base.ChainID, height, big.NewInt(1), lo); err == nil {
			t.Fatal("accepted a nonzero rootHi for a root that packs below 2^128")
		}
	})
	t.Run("tm-wrong-descriptor-chainId-felt", func(t *testing.T) {
		// tm cross-checks claim[chain_id] == the baked const; a forged felt (PI 10,
		// past the 9 app_hash limbs) fails.
		bad := []uint64{777, 0, 0, 0, 0, 0, 0, 0, 0, 987654321, 999}
		bhi, blo := packRootFeltsRef(bad, TmLcPeerMap.RootLanes)
		if err := solve(t, TmLcPeerMap, bad, TmLcPeerMap.ChainID, big.NewInt(0), bhi, blo); err == nil {
			t.Fatal("accepted a tm proof whose descriptor chain_id felt != the baked const")
		}
	})
}

// TestPeerLaneBindMultiFeltRootSplit demonstrates the FULL 128-bit split (the
// forward-compatible path): a multi-felt root packs past 2^128, so rootHi is
// nonzero and the split is exercised for real — the same gadget the next LC-AIR
// iteration uses when it exposes the root as N felts.
func TestPeerLaneBindMultiFeltRootSplit(t *testing.T) {
	// A synthetic 6-felt-root map (root lanes 1..6, MS first). 6·31 = 186 bits,
	// so rootHi != 0.
	m := PeerLaneMap{
		Name: "synthetic-6felt", PiCount: 7, ChainID: big.NewInt(1),
		ChainIDLane: -1, HeightLane: 0, RootLanes: []int{1, 2, 3, 4, 5, 6},
	}
	claim := []uint64{99 /*height*/, 2013265900, 1234567, 2013265900, 7, 2013265900, 42}
	hi, lo := packRootFeltsRef(claim, m.RootLanes)
	if hi.Sign() == 0 {
		t.Fatal("test setup: expected a nonzero rootHi for a 6-felt root")
	}
	if err := solve(t, m, claim, m.ChainID, big.NewInt(99), hi, lo); err != nil {
		t.Fatalf("multi-felt honest split REJECTED: %v", err)
	}
	// Swap hi and lo → reject.
	if err := solve(t, m, claim, m.ChainID, big.NewInt(99), lo, hi); err == nil {
		t.Fatal("accepted a swapped (rootHi, rootLo) split")
	}
}
