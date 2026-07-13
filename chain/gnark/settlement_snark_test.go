// THE GROTH16 WRAP END-TO-END: compile the SettlementCircuit to R1CS over
// BN254, run a (dev/unsafe) Groth16 trusted setup, prove the REAL shrink
// proof's witness, verify — and emit the Solidity verifier + a calldata
// fixture for the Foundry settlement test
// (chain/test/DreggSettlement.t.sol).
//
// ⚠ TRUSTED SETUP: groth16.Setup here is the SINGLE-PARTY DEV CEREMONY —
// whoever runs it knows the toxic waste and can forge proofs for this VK. A
// production deployment needs a real MPC ceremony (or a Powers-of-Tau-based
// scheme). The emitted verifier is honest about what it is: a REAL verifier
// for a REAL circuit under a DEV setup.
//
// Heavy (multi-million R1CS: compile + setup + prove are minutes and tens of
// GB): skipped unless DREGG_SNARK=1.
//
//	cd chain/gnark && DREGG_SNARK=1 go test -run TestSettlementGroth16EndToEnd -v -timeout 240m
package friverifier

import (
	"encoding/binary"
	"encoding/json"
	"fmt"
	"os"
	"runtime"
	"testing"
	"time"

	"github.com/consensys/gnark-crypto/ecc"
	groth16bn254 "github.com/consensys/gnark/backend/groth16/bn254"

	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/backend/groth16"
	"github.com/consensys/gnark/backend/solidity"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
)

const (
	generatedVerifierPath = "../contracts/DreggGroth16Verifier25.sol"
	foundryFixturePath    = "../test/fixtures/settlement_groth16.json"
)

func memMB() (heap, sys uint64) {
	var m runtime.MemStats
	runtime.ReadMemStats(&m)
	return m.HeapAlloc / (1 << 20), m.Sys / (1 << 20)
}

func logPhase(t *testing.T, name string, start time.Time) {
	h, s := memMB()
	t.Logf("%-22s %12s   heap %6d MB  sys %6d MB", name, time.Since(start).Round(time.Millisecond), h, s)
}

// settlementGroth16Fixture is the calldata fixture the Foundry test
// (DreggSettlement.t.sol) replays against the GENERATED verifier.
type settlementGroth16Fixture struct {
	// The 8 proof words (Ar, Bs, Krs in EIP-197 order — gnark
	// MarshalSolidity), then the Pedersen commitments (2 words each), then
	// the commitment PoK (2 words). All 0x-prefixed 32-byte hex.
	Proof         []string `json:"proof"`
	Commitments   []string `json:"commitments"`
	CommitmentPok []string `json:"commitment_pok"`
	// The 25 public inputs (decimal strings), pinned order.
	Inputs []string `json:"inputs"`
	// The same 25 lanes split for DreggSettlement.settle.
	GenesisRoot [8]uint32 `json:"genesis_root"`
	FinalRoot   [8]uint32 `json:"final_root"`
	NumTurns    uint32    `json:"num_turns"`
	ChainDigest [8]uint32 `json:"chain_digest"`
}

func TestSettlementGroth16EndToEnd(t *testing.T) {
	if os.Getenv("DREGG_SNARK") == "" {
		t.Skip("heavy Groth16 end-to-end (multi-million R1CS; minutes + tens of GB); " +
			"run with DREGG_SNARK=1")
	}
	fx := loadShrinkRealFixture(t)
	ex := extractShrinkStark(t, fx)
	sym := loadShrinkSymbolicConstraints(t)
	claim := fx.TablePublics[fx.ClaimInstance]

	// ---- 1. Compile to R1CS: THE CONSTRAINT COUNT.
	t0 := time.Now()
	ccs, err := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder,
		allocSettlementCircuit(t, fx, ex, sym))
	if err != nil {
		t.Fatalf("compile: %v", err)
	}
	logPhase(t, "compile", t0)
	t.Logf("R1CS: %d constraints, %d public (incl. ONE wire), %d secret, %d internal",
		ccs.GetNbConstraints(), ccs.GetNbPublicVariables(), ccs.GetNbSecretVariables(),
		ccs.GetNbInternalVariables())
	if got, want := ccs.GetNbPublicVariables(), NumPublicInputs+1; got != want {
		t.Fatalf("public variables = %d, want %d (the pinned 25 lanes + ONE wire)", got, want)
	}

	// ---- 2. Groth16 setup (DEV/UNSAFE single-party ceremony — see file doc).
	t1 := time.Now()
	pk, vk, err := groth16.Setup(ccs)
	if err != nil {
		t.Fatalf("groth16.Setup: %v", err)
	}
	logPhase(t, "setup (UNSAFE dev)", t1)

	// ---- 3. Prove the REAL witness.
	t2 := time.Now()
	w, err := frontend.NewWitness(assignSettlementCircuit(t, fx, ex, sym), ecc.BN254.ScalarField())
	if err != nil {
		t.Fatalf("witness: %v", err)
	}
	// Solidity-target proving: the exported verifier folds the Pedersen
	// commitment with keccak256, so the proof must be minted (and verified)
	// with the matching hash-to-field — otherwise the on-chain pairing check
	// rejects a Go-valid proof.
	proof, err := groth16.Prove(ccs, pk, w,
		solidity.WithProverTargetSolidityVerifier(backend.GROTH16))
	if err != nil {
		t.Fatalf("groth16.Prove: %v", err)
	}
	logPhase(t, "prove", t2)

	// ---- 4. Verify (and REJECT a forged public statement).
	t3 := time.Now()
	pubw, err := w.Public()
	if err != nil {
		t.Fatalf("public witness: %v", err)
	}
	if err := groth16.Verify(proof, vk, pubw,
		solidity.WithVerifierTargetSolidityVerifier(backend.GROTH16)); err != nil {
		t.Fatalf("groth16.Verify REJECTED the real proof: %v", err)
	}
	logPhase(t, "verify", t3)

	// Forged-statement tooth at the SNARK level: the same proof against a
	// wrong genesis lane must NOT verify.
	forged := allocSettlementCircuit(t, fx, ex, sym)
	forgedClaim := append([]uint32(nil), claim...)
	forgedClaim[0] = bbAddRef(forgedClaim[0], 1)
	assignSettlementPublics(forged, forgedClaim)
	fw, err := frontend.NewWitness(forged, ecc.BN254.ScalarField(), frontend.PublicOnly())
	if err != nil {
		t.Fatalf("forged public witness: %v", err)
	}
	if err := groth16.Verify(proof, vk, fw,
		solidity.WithVerifierTargetSolidityVerifier(backend.GROTH16)); err == nil {
		t.Fatal("groth16.Verify ACCEPTED the proof against a genesis root it does not attest")
	}

	// ---- 5. Emit the Solidity verifier + the Foundry calldata fixture.
	vf, err := os.Create(generatedVerifierPath)
	if err != nil {
		t.Fatalf("create verifier file: %v", err)
	}
	if err := vk.ExportSolidity(vf); err != nil {
		t.Fatalf("ExportSolidity: %v", err)
	}
	if err := vf.Close(); err != nil {
		t.Fatal(err)
	}
	t.Logf("wrote %s", generatedVerifierPath)

	// MarshalSolidity layout (gnark raw serialization): Ar(2 words) ++
	// Bs(4 words) ++ Krs(2 words) ++ a 4-BYTE commitment COUNT ++
	// commitments(2 words each) ++ commitmentPok(2 words). The generated
	// verifier's calldata takes the words WITHOUT the count prefix.
	sol := proof.(*groth16bn254.Proof).MarshalSolidity()
	if len(sol) < 8*32+4 || (len(sol)-8*32-4)%32 != 0 {
		t.Fatalf("MarshalSolidity returned %d bytes (unexpected layout)", len(sol))
	}
	word := func(b []byte, i int) string { return fmt.Sprintf("0x%x", b[32*i:32*i+32]) }
	nComm := int(binary.BigEndian.Uint32(sol[8*32 : 8*32+4]))
	rest := sol[8*32+4:]
	if len(rest) != 32*(2*nComm+2) {
		t.Fatalf("commitment section is %d bytes for %d commitment(s)", len(rest), nComm)
	}
	t.Logf("proof: 8 words + %d commitment(s) + PoK", nComm)

	fixture := settlementGroth16Fixture{}
	for i := 0; i < 8; i++ {
		fixture.Proof = append(fixture.Proof, word(sol, i))
	}
	for i := 0; i < 2*nComm; i++ {
		fixture.Commitments = append(fixture.Commitments, word(rest, i))
	}
	for i := 2 * nComm; i < 2*nComm+2; i++ {
		fixture.CommitmentPok = append(fixture.CommitmentPok, word(rest, i))
	}
	// Only the FIRST NumPublicInputs lanes are the Groth16 public inputs (the
	// Publics struct — the arity of the generated verifier's `uint256[25]`).
	// The claim channel's tail ApexVkLanes lanes are the re-exposed apex VK
	// core: baked VK constants, NOT public inputs — they must NOT ride in the
	// fixture's `inputs` vector (the Foundry test + bridge both pin it to 25).
	for _, v := range claim[:NumPublicInputs] {
		fixture.Inputs = append(fixture.Inputs, fmt.Sprintf("%d", v))
	}
	copy(fixture.GenesisRoot[:], claim[0:8])
	copy(fixture.FinalRoot[:], claim[8:16])
	fixture.NumTurns = claim[16]
	copy(fixture.ChainDigest[:], claim[17:25])

	if err := os.MkdirAll("../test/fixtures", 0o755); err != nil {
		t.Fatal(err)
	}
	blob, err := json.MarshalIndent(&fixture, "", "  ")
	if err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(foundryFixturePath, blob, 0o644); err != nil {
		t.Fatal(err)
	}
	t.Logf("wrote %s", foundryFixturePath)
	t.Log("NEXT: cd chain && forge test --match-contract DreggSettlementRealProofTest")
}
