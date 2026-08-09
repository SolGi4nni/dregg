// Tests for the WITNESS-AWARE replay entry point (emitted_gadget_replay.go:
// ReplayTemplateWithWitness) — driving a Lean-emitted template that carries FREE
// INTERNAL WITNESS VARIABLES, which the plain ReplayTemplate/ReplayClosed solver
// cannot: a booleanity `mul(b,b) == var(b)` puts the fresh witness `b` on one side
// while the other side reads `b`, so there is nothing to define it from — it is a
// value the prover chooses, pinned by the constraint.
//
// The motivating instance is the STARK Lagrange-selector derivation
// (SelectorEmit.lean, emitted/selectors_db{0,9,15,16}.json): inputs `[zeta]`, outputs
// `[isFirstRow, isLastRow, isTransition]`, with thousands of free internal witnesses
// (the 31-bit canonicity decompositions of every ingested/minted extension
// coordinate, the two hinted field inverses of the `ExtInv` gadget, and the
// range-checked minted products of the ζ-squaring chain). The honest witness is the
// Lean-generated assignment `selectorsAsg` (SelectorEmit.lean), the same object the
// `selectorTemplate_refines` ∀-theorem quantifies over, dumped var-index-ordered to
// emitted/selectors_witness_db{N}.json.
//
// The KAT: fed zeta + the honest free witnesses, ReplayTemplateWithWitness SOLVES the
// derived outputs, and they equal computeStarkSelectorsRef (the plain-Go twin of the
// deployed computeStarkSelectorsNative, stark_verify_native.go:379) bit-exact; a
// wrong internal witness makes the emitted R1CS unsatisfiable (the booleanity /
// range / inverse pins bite).
package friverifier

import (
	"bytes"
	"encoding/json"
	"fmt"
	"math/big"
	"os"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/test"
)

// The real fixture transcript ζ (SelectorEmit.lean katZeta — the emitted templates'
// placeholder point; the emitted constraint structure is value-independent).
var selectorsKatZeta = bbExtRef{99790091, 1104783006, 255303953, 1593865295}

// loadWitnessValues reads a Lean-dumped honest assignment: a JSON array of decimal
// field residues, index = template variable.
func loadWitnessValues(path string) ([]*big.Int, error) {
	raw, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	var nums []json.Number
	dec := json.NewDecoder(bytes.NewReader(raw))
	dec.UseNumber()
	if err := dec.Decode(&nums); err != nil {
		return nil, err
	}
	out := make([]*big.Int, len(nums))
	for i, n := range nums {
		v, ok := new(big.Int).SetString(n.String(), 10)
		if !ok {
			return nil, fmt.Errorf("witness[%d]=%q not a decimal integer", i, n.String())
		}
		out[i] = v
	}
	return out, nil
}

// selectorsWitnessCircuit drives a selectors template through
// ReplayTemplateWithWitness and pins the solved outputs to the native selectors.
type selectorsWitnessCircuit struct {
	Zeta    [4]frontend.Variable // the input boundary (bound to the fixture ζ)
	Witness []frontend.Variable  // the free internal witnesses, by ClassifyVars order

	// config (non-frontend.Variable → ignored by gnark's witness parser)
	tpl        *Template
	witnessIdx []int          // Witness[k] binds template variable witnessIdx[k]
	expect     [3][4]*big.Int // native isFirstRow / isLastRow / isTransition
}

func (c *selectorsWitnessCircuit) Define(api frontend.API) error {
	wmap := make(map[int]frontend.Variable, len(c.Witness))
	for k, idx := range c.witnessIdx {
		wmap[idx] = c.Witness[k]
	}
	outs, err := ReplayTemplateWithWitness(api, *c.tpl, c.Zeta[:], wmap)
	if err != nil {
		return err
	}
	if len(outs) != 12 {
		return fmt.Errorf("expected 12 solved outputs (3 ext selectors), got %d", len(outs))
	}
	// outs = [isFirstRow_0..3, isLastRow_0..3, isTransition_0..3] — the public-input
	// suffix order (SelectorEmit.lean selectorsData). Pin each to the native value.
	for g := 0; g < 3; g++ {
		for i := 0; i < 4; i++ {
			api.AssertIsEqual(outs[g*4+i], c.expect[g][i])
		}
	}
	return nil
}

// mkSelectorsWitnessCircuit builds the circuit-template + a fully-valued assignment
// from the committed template and the Lean honest assignment.
func mkSelectorsWitnessCircuit(t *testing.T, db int) (*selectorsWitnessCircuit, *selectorsWitnessCircuit) {
	t.Helper()
	tpl, err := LoadTemplate(fmt.Sprintf("emitted/selectors_db%d.json", db))
	if err != nil {
		t.Fatalf("load selectors_db%d.json: %v", db, err)
	}
	wit, err := loadWitnessValues(fmt.Sprintf("emitted/selectors_witness_db%d.json", db))
	if err != nil {
		t.Fatalf("load selectors_witness_db%d.json: %v", db, err)
	}
	if len(wit) != tpl.NumVars() {
		t.Fatalf("db%d: witness has %d values, template has %d variables", db, len(wit), tpl.NumVars())
	}

	// zeta is the 4-coordinate input boundary (the first 4 public inputs).
	cls, err := tpl.ClassifyVars(4)
	if err != nil {
		t.Fatalf("db%d: ClassifyVars: %v", db, err)
	}
	if len(cls.Inputs) != 4 {
		t.Fatalf("db%d: expected 4 input vars, got %d", db, len(cls.Inputs))
	}

	// Native reference selectors at the fixture ζ / this db.
	sel, err := computeStarkSelectorsRef(selectorsKatZeta, db)
	if err != nil {
		t.Fatalf("db%d: computeStarkSelectorsRef: %v", db, err)
	}
	var expect [3][4]*big.Int
	for i := 0; i < 4; i++ {
		expect[0][i] = new(big.Int).SetUint64(uint64(sel.isFirstRow[i]))
		expect[1][i] = new(big.Int).SetUint64(uint64(sel.isLastRow[i]))
		expect[2][i] = new(big.Int).SetUint64(uint64(sel.isTransition[i]))
	}

	// The circuit-template carries the config + a witness slice of the right length.
	circuit := &selectorsWitnessCircuit{
		Witness:    make([]frontend.Variable, len(cls.Witness)),
		tpl:        tpl,
		witnessIdx: cls.Witness,
		expect:     expect,
	}
	// The assignment carries the honest values.
	asg := &selectorsWitnessCircuit{
		Witness:    make([]frontend.Variable, len(cls.Witness)),
		tpl:        tpl,
		witnessIdx: cls.Witness,
		expect:     expect,
	}
	for i := 0; i < 4; i++ {
		asg.Zeta[i] = wit[cls.Inputs[i]]
	}
	for k, idx := range cls.Witness {
		asg.Witness[k] = wit[idx]
	}
	return circuit, asg
}

// TestReplayTemplateWithWitnessSelectorsKAT: for every degree bits the shrink uses,
// ReplayTemplateWithWitness on the committed selectors template COMPILES (the
// free-witness classification is complete — no "reads var before determined"), and —
// fed the Lean honest witness — SOLVES {isFirstRow, isLastRow, isTransition} to the
// native computeStarkSelectorsRef bit-exact (test.IsSolved accepts).
func TestReplayTemplateWithWitnessSelectorsKAT(t *testing.T) {
	field := ecc.BN254.ScalarField()
	for _, db := range []int{0, 9, 15, 16} {
		db := db
		t.Run(fmt.Sprintf("db%d", db), func(t *testing.T) {
			circuit, asg := mkSelectorsWitnessCircuit(t, db)
			if err := test.IsSolved(circuit, asg, field); err != nil {
				t.Fatalf("db%d: ReplayTemplateWithWitness did not reproduce the native selectors "+
					"under the honest witness (the emitted template diverges, or the witness/derived "+
					"classification is wrong): %v", db, err)
			}
		})
	}
}

// TestReplayTemplateWithWitnessClassification pins the input/free-witness/derived
// partition ClassifyVars produces for the selectors template: 4 zeta inputs, 12
// derived public outputs plus a small internal-derived tail, and everything else a
// free witness — a total, disjoint cover of the variable space.
func TestReplayTemplateWithWitnessClassification(t *testing.T) {
	for _, tc := range []struct {
		db      int
		nvars   int
		witness int
		derived int
	}{
		{0, 3936, 3912, 20},
		{9, 7608, 7584, 20},
		{15, 10056, 10032, 20},
		{16, 10464, 10440, 20},
	} {
		tpl, err := LoadTemplate(fmt.Sprintf("emitted/selectors_db%d.json", tc.db))
		if err != nil {
			t.Fatalf("load db%d: %v", tc.db, err)
		}
		if tpl.NumVars() != tc.nvars {
			t.Fatalf("db%d: NumVars=%d want %d", tc.db, tpl.NumVars(), tc.nvars)
		}
		cls, err := tpl.ClassifyVars(4)
		if err != nil {
			t.Fatalf("db%d: ClassifyVars: %v", tc.db, err)
		}
		if len(cls.Inputs) != 4 || len(cls.Witness) != tc.witness || len(cls.Derived) != tc.derived {
			t.Fatalf("db%d: classify inputs=%d witness=%d derived=%d; want 4/%d/%d",
				tc.db, len(cls.Inputs), len(cls.Witness), len(cls.Derived), tc.witness, tc.derived)
		}
		// Total disjoint cover.
		if len(cls.Inputs)+len(cls.Witness)+len(cls.Derived) != tpl.NumVars() {
			t.Fatalf("db%d: partition does not cover the variable space", tc.db)
		}
		seen := make([]bool, tpl.NumVars())
		for _, s := range [][]int{cls.Inputs, cls.Witness, cls.Derived} {
			for _, v := range s {
				if seen[v] {
					t.Fatalf("db%d: variable %d classified twice", tc.db, v)
				}
				seen[v] = true
			}
		}
		// The 12 trailing public outputs must all be DERIVED (solved), never witness.
		outStart := 4
		derivedSet := make(map[int]bool, len(cls.Derived))
		for _, v := range cls.Derived {
			derivedSet[v] = true
		}
		for _, p := range tpl.PublicInputs[outStart:] {
			if !derivedSet[p.Var] {
				t.Fatalf("db%d: output %q (var %d) is not derived", tc.db, p.Name, p.Var)
			}
		}
	}
}

// TestReplayTemplateWithWitnessRejectsBadWitness: a wrong internal witness makes the
// emitted R1CS unsatisfiable. Corrupting a single booleanity bit to a non-bit value
// trips the `mul(b,b) == b` constraint the witness-aware path applies as a real
// check — exactly the pin the plain solver could not carry.
func TestReplayTemplateWithWitnessRejectsBadWitness(t *testing.T) {
	field := ecc.BN254.ScalarField()
	db := 9
	circuit, asg := mkSelectorsWitnessCircuit(t, db)

	// Find a witness slot holding a booleanity bit (honest value 0 or 1) and corrupt
	// it to 2 — mul(2,2)=4 ≠ 2, the booleanity constraint is now unsatisfiable.
	corrupted := -1
	for k := range asg.Witness {
		if v, ok := asg.Witness[k].(*big.Int); ok && (v.Sign() == 0 || v.Cmp(big.NewInt(1)) == 0) {
			asg.Witness[k] = big.NewInt(2)
			corrupted = k
			break
		}
	}
	if corrupted < 0 {
		t.Fatal("no booleanity-bit witness slot found to corrupt")
	}
	if err := test.IsSolved(circuit, asg, field); err == nil {
		t.Fatalf("db%d: a corrupted booleanity bit (witness slot %d set to 2) was accepted — "+
			"the range/booleanity pins are not biting", db, corrupted)
	}
}
