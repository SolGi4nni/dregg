// Tests for the GKR-batched Poseidon2Bn254 prototype (gkr_poseidon2_bn254.go).
//
// PARITY GATE (always on): the GKR-batched digests must equal BOTH the native
// reference (poseidon2_bn254_ref.go) and the direct in-circuit gadget
// (Poseidon2Bn254Compress) bit-exactly — a smaller-but-wrong hash batch is
// worthless. The negative test flips one expected digest and demands the
// solver reject.
//
// CENSUS (always on): pins the Poseidon2 permutation count of the real
// settlement fixture (the mass GKR would batch) so the extrapolation in the
// measurement test stays grounded.
//
// MEASUREMENT (DREGG_PROFILE=1): compiles the GKR batch vs the direct gadget
// at growing N and reports the R1CS totals — the honest verdict input.
package friverifier

import (
	"encoding/json"
	"math/big"
	"os"
	"testing"
	"time"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
)

// ============================================================================
// Parity
// ============================================================================

// gkrP2ParityCircuit checks, per instance i:
//
//	gkrOut_i == Expected_i  (vs the native reference, witness-pinned)
//	gkrOut_i == Poseidon2Bn254Compress(L_i, R_i)  (vs the direct gadget)
type gkrP2ParityCircuit struct {
	L, R     []frontend.Variable
	Expected []frontend.Variable
	hashName string
}

func (c *gkrP2ParityCircuit) Define(api frontend.API) error {
	outs, err := gkrBatchPoseidon2Bn254CompressWithHash(api, c.L, c.R, c.hashName)
	if err != nil {
		return err
	}
	for i := range outs {
		api.AssertIsEqual(outs[i], c.Expected[i])
		api.AssertIsEqual(outs[i], Poseidon2Bn254Compress(api, c.L[i], c.R[i]))
	}
	return nil
}

func gkrP2RandomBatch(t *testing.T, n int) (l, r, expected []frontend.Variable) {
	t.Helper()
	l = make([]frontend.Variable, n)
	r = make([]frontend.Variable, n)
	expected = make([]frontend.Variable, n)
	for i := 0; i < n; i++ {
		var a, b fr.Element
		if _, err := a.SetRandom(); err != nil {
			t.Fatal(err)
		}
		if _, err := b.SetRandom(); err != nil {
			t.Fatal(err)
		}
		l[i] = a.BigInt(new(big.Int))
		r[i] = b.BigInt(new(big.Int))
		d := poseidon2Bn254RefCompress(a, b)
		expected[i] = d.BigInt(new(big.Int))
	}
	return
}

func gkrP2Solve(t *testing.T, n int, l, r, expected []frontend.Variable, hashName string) error {
	t.Helper()
	circuit := &gkrP2ParityCircuit{
		L:        make([]frontend.Variable, n),
		R:        make([]frontend.Variable, n),
		Expected: make([]frontend.Variable, n),
		hashName: hashName,
	}
	cs, err := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, circuit)
	if err != nil {
		t.Fatalf("compile: %v", err)
	}
	w, err := frontend.NewWitness(
		&gkrP2ParityCircuit{L: l, R: r, Expected: expected}, ecc.BN254.ScalarField())
	if err != nil {
		t.Fatalf("witness: %v", err)
	}
	return cs.IsSolved(w)
}

// TestGkrPoseidon2Parity: GKR-batched == reference == direct gadget,
// bit-exact, on a random batch — under BOTH transcript hashes (this also
// cross-checks the in-circuit/native Poseidon2 transcript twins: a mismatch
// desynchronises the sum-check challenges and the solve fails).
func TestGkrPoseidon2Parity(t *testing.T) {
	const n = 16
	for _, hashName := range []string{"mimc", gkrP2TranscriptHashName} {
		l, r, expected := gkrP2RandomBatch(t, n)
		if err := gkrP2Solve(t, n, l, r, expected, hashName); err != nil {
			t.Fatalf("parity batch (transcript %q) did not solve: %v", hashName, err)
		}
	}
}

// TestGkrPoseidon2ParityRejectsWrongDigest: one corrupted expected digest must
// make the system unsatisfiable (the GKR verifier is not vacuous).
func TestGkrPoseidon2ParityRejectsWrongDigest(t *testing.T) {
	const n = 16
	for _, hashName := range []string{"mimc", gkrP2TranscriptHashName} {
		l, r, expected := gkrP2RandomBatch(t, n)
		bad := new(big.Int).Add(expected[n/2].(*big.Int), big.NewInt(1))
		expected[n/2] = bad
		if err := gkrP2Solve(t, n, l, r, expected, hashName); err == nil {
			t.Fatalf("corrupted digest solved (transcript %q) — the GKR batch is not binding", hashName)
		}
	}
}

// ============================================================================
// Census: the batchable Poseidon2 mass in the REAL settlement fixture
// ============================================================================

// TestGkrPoseidon2PermCensus counts the Poseidon2Bn254 permutations the
// SettlementCircuit performs (walk compresses + leaf-sponge permutations,
// open_input + FRI core) from the real fixture, mirroring
// verifyOpenInputBatchNative / VerifyFriQueryNative structure.
func TestGkrPoseidon2PermCensus(t *testing.T) {
	raw, err := os.ReadFile("fixtures/apex_shrink_fri_real.json")
	if err != nil {
		t.Fatal(err)
	}
	var fx struct {
		Fri struct {
			NumQueries int `json:"num_queries"`
		} `json:"fri"`
		InputRounds []struct {
			Matrices []struct {
				LogHeight int `json:"log_height"`
				Width     int `json:"width"`
			} `json:"matrices"`
		} `json:"input_rounds"`
		Queries []struct {
			MerklePaths [][]string `json:"merkle_paths"`
		} `json:"queries"`
	}
	if err := json.Unmarshal(raw, &fx); err != nil {
		t.Fatal(err)
	}
	const blockLimbs = bn254SpongeRate * mfAbsorbNumFElms

	walk, leaf := 0, 0
	for _, r := range fx.InputRounds {
		heights := map[int]int{} // logHeight -> summed width (limbs per group)
		maxLh := 0
		for _, m := range r.Matrices {
			heights[m.LogHeight] += m.Width
			if m.LogHeight > maxLh {
				maxLh = m.LogHeight
			}
		}
		walk += maxLh + (len(heights) - 1) // path + height-class injections
		for _, limbs := range heights {
			leaf += (limbs + blockLimbs - 1) / blockLimbs
		}
	}
	friWalk, friLeaf := 0, 0
	for _, p := range fx.Queries[0].MerklePaths {
		friWalk += len(p)
		friLeaf++ // 8 limbs = one sponge permutation per commit-phase leaf
	}
	perQuery := walk + leaf + friWalk + friLeaf
	total := perQuery * fx.Fri.NumQueries

	t.Logf("open_input walk=%d leaf=%d, fri walk=%d leaf=%d => %d perms/query × %d queries = %d perms (~%.2fM R1CS at 243/perm)",
		walk, leaf, friWalk, friLeaf, perQuery, fx.Fri.NumQueries, total, float64(total)*243/1e6)
	// ⚑ 12008 → 13072 on 2026-08-08. Every input is READ FROM THE FIXTURE, so this pin is a
	// pure drift tripwire, and it fired correctly: the apex-VK flag day moved the shrink proof's
	// shape (FRI rounds 15 → 16, log_global_max_height 18 → 19, and the expose_claim table 132 →
	// 164 limbs wide once the root's VK-spine block joined the re-exposed claim), which is more
	// Merkle path levels and one more leaf-sponge block per query. Re-derived, not silenced.
	if total != 13072 {
		t.Fatalf("perm census drifted: %d (want 13072) — re-derive the GKR extrapolation", total)
	}
}

// ============================================================================
// Measurement (DREGG_PROFILE=1): R1CS of GKR batch vs direct gadget
// ============================================================================

// gkrP2BatchOnlyCircuit is the GKR side of the measurement: outputs bound to
// witness (no direct gadget in the same circuit, so the count is pure).
type gkrP2BatchOnlyCircuit struct {
	L, R     []frontend.Variable
	Expected []frontend.Variable
	hashName string
}

func (c *gkrP2BatchOnlyCircuit) Define(api frontend.API) error {
	outs, err := gkrBatchPoseidon2Bn254CompressWithHash(api, c.L, c.R, c.hashName)
	if err != nil {
		return err
	}
	for i := range outs {
		api.AssertIsEqual(outs[i], c.Expected[i])
	}
	return nil
}

// gkrP2DirectOnlyCircuit is the same statement via the direct gadget.
type gkrP2DirectOnlyCircuit struct {
	L, R     []frontend.Variable
	Expected []frontend.Variable
}

func (c *gkrP2DirectOnlyCircuit) Define(api frontend.API) error {
	for i := range c.L {
		api.AssertIsEqual(Poseidon2Bn254Compress(api, c.L[i], c.R[i]), c.Expected[i])
	}
	return nil
}

func gkrP2CompileCount(t *testing.T, c frontend.Circuit) int {
	t.Helper()
	t0 := time.Now()
	cs, err := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, c)
	if err != nil {
		t.Fatalf("compile: %v", err)
	}
	n := cs.GetNbConstraints()
	t.Logf("    compiled %d constraints in %s", n, time.Since(t0).Round(time.Millisecond))
	return n
}

// TestGkrPoseidon2R1CSProfile measures the R1CS of the GKR-batched vs direct
// Poseidon2Bn254Compress at growing batch sizes and extrapolates to the
// settlement circuit's 12,008-permutation mass (padded to 16,384).
//
//	cd chain/gnark && DREGG_PROFILE=1 go test -run TestGkrPoseidon2R1CSProfile -v -timeout 120m
func TestGkrPoseidon2R1CSProfile(t *testing.T) {
	requireProfileEnv(t)
	sizes := []int{256, 1024, 4096}
	type row struct{ n, direct, gkrMimc, gkrP2 int }
	rows := make([]row, 0, len(sizes))
	for _, n := range sizes {
		mk := func() (l, r, e []frontend.Variable) {
			return make([]frontend.Variable, n), make([]frontend.Variable, n), make([]frontend.Variable, n)
		}
		t.Logf("N=%d direct ...", n)
		l, r, e := mk()
		direct := gkrP2CompileCount(t, &gkrP2DirectOnlyCircuit{L: l, R: r, Expected: e})
		t.Logf("N=%d gkr (mimc transcript) ...", n)
		l, r, e = mk()
		gkrMimc := gkrP2CompileCount(t, &gkrP2BatchOnlyCircuit{L: l, R: r, Expected: e, hashName: "mimc"})
		t.Logf("N=%d gkr (poseidon2 transcript) ...", n)
		l, r, e = mk()
		gkrP2 := gkrP2CompileCount(t, &gkrP2BatchOnlyCircuit{L: l, R: r, Expected: e, hashName: gkrP2TranscriptHashName})
		rows = append(rows, row{n, direct, gkrMimc, gkrP2})
	}
	t.Logf("%8s %12s %12s %12s %12s %12s", "N", "direct", "gkr/mimc", "gkr/p2", "mimc/perm", "p2/perm")
	for _, r := range rows {
		t.Logf("%8d %12d %12d %12d %12.1f %12.1f", r.n, r.direct, r.gkrMimc, r.gkrP2,
			float64(r.gkrMimc)/float64(r.n), float64(r.gkrP2)/float64(r.n))
	}
	// Fit cost(N) = a·log2(N) + m·N + c from the three sizes (per-wire
	// sum-check rounds grow with log N; input/output MLE evals with N), then
	// project the settlement batch (12,008 perms padded to N=16,384).
	project := func(name string, y0, y1, y2 int) float64 {
		// sizes 256(log 8), 1024(log 10), 4096(log 12)
		d01, d12 := float64(y1-y0), float64(y2-y1)
		m := (d12 - d01) / float64((4096-1024)-(1024-256))
		a := (d01 - m*float64(1024-256)) / 2
		c := float64(y0) - a*8 - m*256
		proj := a*14 + m*16384 + c
		t.Logf("%s: fit a=%.0f/log-round, m=%.1f/instance, c=%.0f => N=16384 ≈ %.2fM R1CS",
			name, a, m, c, proj/1e6)
		return proj
	}
	r0, r1, r2 := rows[0], rows[1], rows[2]
	pm := project("gkr/mimc", r0.gkrMimc, r1.gkrMimc, r2.gkrMimc)
	pp := project("gkr/p2", r0.gkrP2, r1.gkrP2, r2.gkrP2)
	direct12k := 12008.0 * float64(r2.direct) / float64(r2.n)
	t.Logf("settlement mass: direct 12008 perms ≈ %.2fM R1CS; GKR(mimc) ≈ %.2fM; GKR(poseidon2) ≈ %.2fM",
		direct12k/1e6, pm/1e6, pp/1e6)
}
