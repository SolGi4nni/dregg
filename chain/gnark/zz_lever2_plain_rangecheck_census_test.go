// LEVER-2 MEASUREMENT: what does the gnark Pedersen commitment actually cost,
// and what does removing it cost in R1CS?
//
// The SettlementCircuit never calls api.Commit. The ONE Pedersen commitment in
// the exported Solidity verifier is inserted IMPLICITLY by
// std/rangecheck.New(api) (babybear.go:57): the r1cs builder implements
// frontend.Committer, so rangecheck returns the commitment-based
// log-derivative checker, whose logderivarg.Build calls multicommit ->
// api.Commit exactly once.
//
// rangecheck.New's FIRST branch is `if rc, ok := api.(frontend.Rangechecker)`.
// So wrapping the api in a type that itself implements Check() short-circuits
// the commitment path entirely — no api.Commit, no commitment, and every range
// check becomes a bit decomposition. That is exactly the lever.
//
// This test compiles both variants and reports:
//   - the range-check census (count + bit-width histogram),
//   - the R1CS of the real (commitment) circuit,
//   - the R1CS of the bit-decomposition circuit,
//   - the blowup.
//
// Heavy (multi-million-R1CS compiles). Run with:
//
//	cd chain/gnark && DREGG_LEVER2=1 go test -run TestLever2 -v -timeout 180m
package friverifier

import (
	"fmt"
	"math/big"
	"os"
	"sort"
	"testing"
	"time"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
	"github.com/consensys/gnark/std/math/bits"
)

// plainRCApi wraps a frontend.API and ALSO satisfies frontend.Rangechecker, so
// rangecheck.New(plainRCApi) returns it directly and the commitment-based
// checker is never constructed. Check() is gnark's own plainChecker body
// (std/rangecheck/rangecheck_plain.go).
type plainRCApi struct {
	frontend.API
	n     int
	hist  map[int]int
	count bool
}

func (p *plainRCApi) Check(v frontend.Variable, nbBits int) {
	p.n++
	if p.hist == nil {
		p.hist = map[int]int{}
	}
	p.hist[nbBits]++
	if p.count {
		return // census-only: do not emit the decomposition constraints
	}
	bits.ToBinary(p.API, v, bits.WithNbDigits(nbBits))
}

// lever2Circuit runs the REAL SettlementCircuit.Define against the wrapped api.
type lever2Circuit struct {
	SettlementCircuit
	seen  **plainRCApi // out-param: the wrapper, for the census
	count bool
}

func (c *lever2Circuit) Define(api frontend.API) error {
	w := &plainRCApi{API: api, hist: map[int]int{}, count: c.count}
	if c.seen != nil {
		*c.seen = w
	}
	return c.SettlementCircuit.Define(w)
}

func lever2Compile(t *testing.T, label string, c frontend.Circuit) int {
	t.Helper()
	t0 := time.Now()
	cs, err := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, c)
	if err != nil {
		t.Fatalf("%s compile: %v", label, err)
	}
	n := cs.GetNbConstraints()
	t.Logf("%-34s %10d R1CS   (%s)", label, n, time.Since(t0).Round(time.Millisecond))
	return n
}

func TestLever2RangecheckCensusAndPlainCost(t *testing.T) {
	if os.Getenv("DREGG_LEVER2") == "" {
		t.Skip("heavy multi-million-R1CS compiles; run with DREGG_LEVER2=1")
	}
	fx := loadShrinkRealFixture(t)
	ex := extractShrinkStark(t, fx)
	sym := loadShrinkSymbolicConstraints(t)

	// (0) CENSUS ONLY — Check() records and emits nothing. This isolates the
	// non-rangecheck body of the circuit AND gives the exact census.
	var w *plainRCApi
	censusOnly := lever2Compile(t, "census-only (no rc constraints)", &lever2Circuit{
		SettlementCircuit: *allocSettlementCircuit(t, fx, ex, sym),
		seen:              &w,
		count:             true,
	})
	widths := make([]int, 0, len(w.hist))
	for b := range w.hist {
		widths = append(widths, b)
	}
	sort.Ints(widths)
	totalBits := 0
	for _, b := range widths {
		totalBits += b * w.hist[b]
		t.Logf("  rangecheck width %3d bits : %8d checks", b, w.hist[b])
	}
	t.Logf("RANGE CHECKS: %d calls, %d total checked bits", w.n, totalBits)

	// (1) THE REAL CIRCUIT — commitment-based log-derivative range checks.
	real := lever2Compile(t, "REAL (commitment rangecheck)", allocSettlementCircuit(t, fx, ex, sym))

	// (2) THE LEVER — bit-decomposition range checks, NO commitment.
	plain := lever2Compile(t, "PLAIN (bit-decomp, no commit)", &lever2Circuit{
		SettlementCircuit: *allocSettlementCircuit(t, fx, ex, sym),
		seen:              new(*plainRCApi),
	})

	fmt.Printf("\n=== LEVER 2 ===\nreal   %d\nplain  %d\ndelta  %+d  (%.2fx)\n"+
		"rangecheck term: commitment %d vs bit-decomp %d\n",
		real, plain, plain-real, float64(plain)/float64(real),
		real-censusOnly, plain-censusOnly)
}

// ---------------------------------------------------------------------------
// AssertIsCanonical is 2 of every 3 range checks (284,592 of 376,058, all
// 31-bit, and rc.Check(·,31) appears ONLY in babybear.go:70-71). Under bit
// decomposition the SECOND check is pure waste: once you hold the 31 bits of
// v, "v < p" is a comparison against a CONSTANT. This measures the marginal
// R1CS of the three canonicity variants.
// ---------------------------------------------------------------------------

// lever2CanonicalFromBits: v < BabyBearP, from a single 31-bit decomposition.
// p-1 = 0x78000000 (bits 30..27 set, 26..0 clear), so with v < 2^31 pinned by
// the decomposition, v >= p iff (b30&b29&b28&b27) AND (low27 != 0).
func lever2CanonicalFromBits(api frontend.API, v frontend.Variable) {
	b := bits.ToBinary(api, v, bits.WithNbDigits(31))
	top := api.Mul(api.Mul(b[30], b[29]), api.Mul(b[28], b[27]))
	var low frontend.Variable = 0
	c := big.NewInt(1)
	for i := 0; i < 27; i++ {
		low = api.Add(low, api.Mul(b[i], c))
		c = new(big.Int).Lsh(c, 1)
	}
	api.AssertIsEqual(api.Mul(top, api.Sub(1, api.IsZero(low))), 0)
}

type lever2CanonChain struct {
	n    int
	mode string // commit | plain | special
	A    frontend.Variable
}

func (c *lever2CanonChain) Define(api frontend.API) error {
	work := func(a frontend.API, canon func(frontend.Variable)) {
		for i := 1; i <= c.n; i++ {
			canon(a.Mul(c.A, i)) // constant scalar: a free linear expression
		}
	}
	switch c.mode {
	case "commit":
		bb := NewBBApi(api)
		work(api, bb.AssertIsCanonical)
	case "plain":
		w := &plainRCApi{API: api, hist: map[int]int{}}
		bb := NewBBApi(w)
		work(w, bb.AssertIsCanonical)
	case "special":
		w := &plainRCApi{API: api, hist: map[int]int{}}
		work(w, func(v frontend.Variable) { lever2CanonicalFromBits(w, v) })
	}
	return nil
}

func TestLever2CanonicalityMarginalCost(t *testing.T) {
	if os.Getenv("DREGG_LEVER2") == "" {
		t.Skip("run with DREGG_LEVER2=1")
	}
	for _, mode := range []string{"commit", "plain", "special"} {
		lo, hi := 256, 1024
		a := lever2Compile(t, mode+" n=256", &lever2CanonChain{n: lo, mode: mode})
		b := lever2Compile(t, mode+" n=1024", &lever2CanonChain{n: hi, mode: mode})
		t.Logf(">>> AssertIsCanonical [%s]: %.2f R1CS/call", mode, float64(b-a)/float64(hi-lo))
	}
}
