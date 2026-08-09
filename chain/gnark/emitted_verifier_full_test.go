// Tests for the compact full-verifier descriptor interpreter
// (emitted_verifier_full.go).
//
// The descriptor is loaded from the ACTUAL committed Lean artifact
// chain/gnark/emitted/verifier_full.json (the byte-for-byte #guard-pinned
// output of emitVerifierFullJson, EmitJson.lean §4), never re-authored here.
// Block 3's constraint DAG comes from the companion committed emitted artifact
// fixtures/shrink_symbolic_constraints.json (see emitted_verifier_full.go §1,
// named seam #1).
package friverifier

import (
	"testing"
	"time"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
)

const emittedVerifierFullPath = "emitted/verifier_full.json"

func loadVerifierFullT(t *testing.T) *VerifierFull {
	t.Helper()
	vf, err := LoadVerifierFull(emittedVerifierFullPath)
	if err != nil {
		t.Fatalf("load %s: %v", emittedVerifierFullPath, err)
	}
	if vf.Schema != verifierFullSchema {
		t.Fatalf("unexpected schema %q", vf.Schema)
	}
	if vf.Name != "gnark_fri_verifier_composed_v1" {
		t.Fatalf("unexpected name %q", vf.Name)
	}
	return vf
}

// The descriptor loads, validates, and its derived parity oracle holds against
// the gadget records + shape.
func TestVerifierFullLoadsAndValidates(t *testing.T) {
	vf := loadVerifierFullT(t)
	if len(vf.Gadgets) != 10 {
		t.Fatalf("expected 10 gadget records, got %d", len(vf.Gadgets))
	}
	if vf.Derived.CommitMerkleCompressions != 6384 {
		t.Fatalf("commit_merkle_compressions = %d, want 6384", vf.Derived.CommitMerkleCompressions)
	}
	if vf.Derived.InputMerkleCompressions != 2888 {
		t.Fatalf("input_merkle_compressions = %d, want 2888", vf.Derived.InputMerkleCompressions)
	}
	// checkDerivedParity ran inside Validate; a second explicit call documents it.
	if err := vf.checkDerivedParity(); err != nil {
		t.Fatalf("derived parity: %v", err)
	}
}

// Block 3 fail-closes without the companion DAG (named seam #1) rather than
// fabricating a constraint DAG.
func TestVerifierFullBlock3FailsClosedWithoutSym(t *testing.T) {
	vf := loadVerifierFullT(t)
	if _, err := AllocVerifierFullCircuit(vf, nil); err == nil {
		t.Fatal("block 3 was allocated WITHOUT the companion symbolic DAG (should fail-closed)")
	}
}

// THE DELIVERABLE: the interpreter builds the FULL composed verifier from the
// emitted descriptor + companion DAG and COMPILES to an R1CS. Reports the
// materialized constraint count and the per-block primitive multiplicities.
func TestVerifierFullCompilesToR1CS(t *testing.T) {
	vf := loadVerifierFullT(t)
	sym := loadShrinkSymbolicConstraints(t)

	circuit, err := AllocVerifierFullCircuit(vf, sym)
	if err != nil {
		t.Fatalf("alloc: %v", err)
	}
	t.Logf("witness bank: %d fresh variables", len(circuit.W))
	t.Logf("commit-phase Merkle compressions: %d", vf.Derived.CommitMerkleCompressions)
	t.Logf("input-batch Merkle compressions:  %d", vf.Derived.InputMerkleCompressions)
	t.Logf("FRI fold-row ext-muls:            %d", vf.Derived.FoldRows)

	t0 := time.Now()
	cs, err := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, circuit)
	if err != nil {
		t.Fatalf("compile: %v", err)
	}
	n := cs.GetNbConstraints()
	t.Logf("=== VerifierFull materialized to %d R1CS constraints in %s ===",
		n, time.Since(t0).Round(time.Millisecond))

	if n == 0 {
		t.Fatal("compiled to 0 constraints")
	}
	// Sanity floor: the 8436 Merkle Poseidon2-BN254 compressions alone are
	// ~240 R1CS each, so the total must clear ~1.5M.
	if n < 1_500_000 {
		t.Fatalf("only %d constraints — expected >~1.5M from the 8436 Poseidon2 compressions", n)
	}
}
