// ReplayClosed on the REAL multi-height MMCS batch input-open, per input round.
//
// This is the reject-polarity teeth for block 2b's rewire: the Lean-emitted
// batchData templates (InputOpenBatchEmit.lean, one per deployed round shape) are
// driven through ReplayClosed against the REAL apex-shrink fixture openings — the
// class-concatenated opened row limbs, the committed input root, and the query's
// path nodes/bits — for every input round (trace / quotient / preprocessed /
// permutation). The correct opening BINDS (the batch walk over the per-class leaf
// hashes reproduces the committed input root, in-circuit, with Lean-authored
// constraints); a tampered opened row limb, path node, or root each REJECT.
//
// These are NOT vacuous: the honest opening is accepted first (so the reject is a
// real polarity flip, not a circuit that rejects everything), and the native
// openInputBatchRootRef self-check inside the witness builder guarantees the fed
// values reproduce the committed root before the circuit ever runs.
package friverifier

import (
	"math/big"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/test"
)

// realBatchWitness is one query's real opening of one input round, in the exact
// (rows, root, sibs, bits) shape the Lean batchData template binds by index.
type realBatchWitness struct {
	rows  []*big.Int // R opened row limbs, class-concatenated (tallest-first)
	root  *big.Int   // the committed input-round Merkle root
	sibs  []*big.Int // maxLh path nodes (bottom-up)
	bits  []int      // maxLh path bits (LSB-first from the reduced index)
	R     int
	maxLh int
}

// buildRealBatchWitness materializes one (query, input-round) opening from the
// real fixture. It self-checks natively (openInputBatchRootRef must reproduce the
// committed input root) so a replication bug fails LOUDLY here, never as a fake
// circuit divergence.
func buildRealBatchWitness(t *testing.T, fx *shrinkRealFixture, ex *shrinkStarkExtract, qi, ri int) realBatchWitness {
	t.Helper()
	round := OpenInputRoundShape{}
	for _, m := range fx.InputRounds[ri].Matrices {
		round.Matrices = append(round.Matrices,
			OpenInputMatrixShape{m.LogHeight, m.Width, m.NumPoints, m.NextPointBits})
	}
	groups := openInputHeightGroupsOf(round)
	maxLh := groups[0].logHeight
	logMax := fx.Fri.LogGlobalMaxHeight
	roots := shrinkInputRootsRef(t, fx, ex.loc)

	opRef := shrinkInputOpeningsRef(t, fx, qi)[ri]
	gotRoot, err := openInputBatchRootRef(round, opRef, fx.Queries[qi].ExpectedIndex, logMax)
	if err != nil {
		t.Fatalf("query %d round %d: native batch root: %v", qi, ri, err)
	}
	if !gotRoot.Equal(&roots[ri]) {
		t.Fatalf("query %d round %d: native batch root != committed input root "+
			"(row-order/fold replication bug, NOT an emit-circuit divergence)", qi, ri)
	}

	var rows []*big.Int
	for _, grp := range groups {
		for _, mi := range grp.mats {
			for _, v := range fx.Queries[qi].InputOpenings[ri].Rows[mi] {
				rows = append(rows, big.NewInt(int64(v)))
			}
		}
	}
	reduced := fx.Queries[qi].ExpectedIndex >> uint(logMax-maxLh)
	var sibs []*big.Int
	var bits []int
	for s := 0; s < maxLh; s++ {
		sibs = append(sibs, frToBig(parseBn254Hex(t, fx.Queries[qi].InputOpenings[ri].Path[s])))
		bits = append(bits, int((reduced>>uint(s))&1))
	}
	return realBatchWitness{rows: rows, root: frToBig(roots[ri]), sibs: sibs, bits: bits,
		R: len(rows), maxLh: maxLh}
}

// realBatchOpenCircuit binds the batch template's rows/root/siblings/bits by the
// index layout (rows at 0..R-1, root at R, sibling s at R+1+2s, bit s at
// R+1+2s+1 — InputOpenBatchEmit.lean §9) and drives the closed circuit through
// ReplayClosed (which solves the Poseidon internals + keeps the real checks).
type realBatchOpenCircuit struct {
	Rows []frontend.Variable
	Root frontend.Variable
	Sibs []frontend.Variable
	Bits []frontend.Variable

	tpl   *Template
	R     int
	maxLh int
}

func (c *realBatchOpenCircuit) Define(api frontend.API) error {
	b := make(map[int]frontend.Variable, c.R+1+2*c.maxLh)
	for i, v := range c.Rows {
		b[i] = v
	}
	b[c.R] = c.Root
	for s := 0; s < c.maxLh; s++ {
		b[c.R+1+2*s] = c.Sibs[s]
		b[c.R+1+2*s+1] = c.Bits[s]
	}
	return ReplayClosed(api, *c.tpl, b)
}

func allocRealBatch(tpl *Template, R, maxLh int) *realBatchOpenCircuit {
	return &realBatchOpenCircuit{
		Rows: make([]frontend.Variable, R),
		Sibs: make([]frontend.Variable, maxLh),
		Bits: make([]frontend.Variable, maxLh),
		tpl:  tpl, R: R, maxLh: maxLh,
	}
}

func assignRealBatch(tpl *Template, wt realBatchWitness) *realBatchOpenCircuit {
	c := allocRealBatch(tpl, wt.R, wt.maxLh)
	for i, v := range wt.rows {
		c.Rows[i] = v
	}
	c.Root = wt.root
	for s := 0; s < wt.maxLh; s++ {
		c.Sibs[s] = wt.sibs[s]
		c.Bits[s] = wt.bits[s]
	}
	return c
}

// TestReplayClosedInputBatchRealFixture: for every input round of the real
// apex-shrink proof, the Lean-emitted batchData template binds the real opening
// to the committed input root (ACCEPT), and each single tamper REJECTS.
func TestReplayClosedInputBatchRealFixture(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	ex := extractShrinkStark(t, fx)
	field := ecc.BN254.ScalarField()

	cases := []struct {
		name string
		path string
		ri   int
	}{
		{"round0-trace [76,304,8,164]", "emitted/inputopen_batch_r0.json", 0},
		{"round1-quotient [8,16,16,8]", "emitted/inputopen_batch_template.json", 1},
		{"round2-preprocessed [59,26,8,82]", "emitted/inputopen_batch_r2.json", 2},
		{"round3-permutation [72,32,8,164]", "emitted/inputopen_batch_r3.json", 3},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			tpl, err := LoadTemplate(tc.path)
			if err != nil {
				t.Fatalf("load %s: %v", tc.path, err)
			}
			wt := buildRealBatchWitness(t, fx, ex, 0, tc.ri)
			if len(tpl.PublicInputs) != 1 || tpl.PublicInputs[0].Var != wt.R {
				t.Fatalf("template root boundary %v != single root at var R=%d", tpl.PublicInputs, wt.R)
			}

			// ACCEPT: the real opening binds to the committed input root.
			if err := test.IsSolved(allocRealBatch(tpl, wt.R, wt.maxLh),
				assignRealBatch(tpl, wt), field); err != nil {
				t.Fatalf("Lean batch template REJECTED the real opening (round %d): %v", tc.ri, err)
			}

			// REJECT: tampered opened row limb (moves the class leaf hash → root).
			{
				bad := assignRealBatch(tpl, wt)
				bad.Rows[0] = new(big.Int).Add(wt.rows[0], big.NewInt(1))
				if err := test.IsSolved(allocRealBatch(tpl, wt.R, wt.maxLh), bad, field); err == nil {
					t.Fatal("accepted a tampered opened row limb")
				}
			}
			// REJECT: tampered path node.
			{
				bad := assignRealBatch(tpl, wt)
				bad.Sibs[0] = new(big.Int).Add(wt.sibs[0], big.NewInt(1))
				if err := test.IsSolved(allocRealBatch(tpl, wt.R, wt.maxLh), bad, field); err == nil {
					t.Fatal("accepted a tampered path node")
				}
			}
			// REJECT: tampered claimed input root.
			{
				bad := assignRealBatch(tpl, wt)
				bad.Root = new(big.Int).Add(wt.root, big.NewInt(1))
				if err := test.IsSolved(allocRealBatch(tpl, wt.R, wt.maxLh), bad, field); err == nil {
					t.Fatal("accepted a tampered input root")
				}
			}
		})
	}
}
