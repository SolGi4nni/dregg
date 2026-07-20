// THE ZETA-BIND COST DIFFERENTIAL. bindBlockZeta (emitted_verifier_full.go) is
// what makes block 3's zeta-derived inputs provably the ones at the
// transcript-squeezed zeta: it re-derives the Lagrange selectors in-circuit at
// that zeta (tooth 1), equates the openings-at-zeta against the transcript-observed
// opened stream (tooth 2), and asserts the DEEP quotient identity
// folded == quotient(zeta)·Z_H(zeta) over the transcript-observed opened chunks
// (tooth 3). This file MEASURES what that costs by compiling the stage-ON
// circuit twice — bind off (meta.zetaSampleOff < 0) and bind on — and reporting
// the R1CS delta. Nothing here is a deployed path; the off variant exists only to
// price the on variant.
package friverifier

import (
	"testing"
	"time"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
)

func TestEmittedVerifierFullZetaBindCost(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	sym := loadShrinkSymbolicConstraints(t)

	compile := func(label string, c *VerifierFullCircuit) int {
		t0 := time.Now()
		cs, err := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, c)
		if err != nil {
			t.Fatalf("%s: compile: %v", label, err)
		}
		n := cs.GetNbConstraints()
		t.Logf("%s: %d R1CS constraints (%s)", label, n, time.Since(t0).Round(time.Millisecond))
		return n
	}

	// Bind OFF: the same stage-ON circuit with the zeta bind disabled.
	off := allocVerifierFullWithTranscript(t, fx, sym)
	off.txMeta.zetaSampleOff = -1
	nOff := compile("stage ON, zeta bind OFF", off)

	// Bind ON: selectors re-derived at the squeezed zeta + the openings bind.
	nOn := compile("stage ON, zeta bind ON", allocVerifierFullWithTranscript(t, fx, sym))

	if nOn <= nOff {
		t.Fatalf("the zeta bind added %d constraints — it cannot be doing anything", nOn-nOff)
	}
	t.Logf("=== ZETA BIND DELTA: +%d R1CS constraints (%.4f%% of %d) ===",
		nOn-nOff, 100*float64(nOn-nOff)/float64(nOff), nOff)
}
