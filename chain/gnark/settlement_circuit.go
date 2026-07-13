// THE SETTLEMENT CIRCUIT — the assembled native shrink-proof verifier WITH
// the pinned 25-lane public settlement statement attached.
//
// This is the circuit Groth16-wrapped for IDreggSettlement.settle: ONE Define
// that
//
//  1. replays the shrink proof's pre-FRI Fiat–Shamir transcript (pinning
//     every sampled challenge to the in-circuit MultiField challenger),
//  2. runs the full batch-STARK algebra layer (constraint evaluation at zeta
//     for all 6 instances via the emitted symbolic DAGs + quotient identity +
//     global LogUp balance — stark_verify_native.go),
//  3. verifies the FRI core (fri_verify_native.go), and
//  4. closes the open_input seam (stark_open_input.go): Merkle-opens the
//     input batches against the transcript-observed commitments and binds
//     the derived reduced openings to the FRI fold seeds,
//
// and — THE SETTLEMENT BINDING — asserts its 25 gnark PUBLIC inputs
// (genesis_root[8] ++ final_root[8] ++ num_turns ++ chain_digest[8], the
// pinned `Publics` order shared with DreggSettlement.sol) equal the shrink
// proof's expose_claim table public values, lane for lane.
//
// WHY THAT EQUALITY IS A BINDING AND NOT A LABEL: the claim lanes the circuit
// equates against are the SAME variables the transcript replay absorbed
// (verify_batch observes per-instance public values right after the main
// commitment — so they seed every downstream challenge), AND they feed the
// ExposeClaimAir constraint evaluation (`public_value[lane] == v_0` of the
// bus-bound read, enforced through the quotient identity at zeta over the
// COMMITTED expose_claim trace). The bus binds that trace cell to the very
// circuit witnesses the in-circuit apex verification consumed as the apex's
// public values — i.e. the apex's genuine 25-lane exposed claim
// (circuit-prove/src/apex_shrink_gnark_export.rs shrink_apex_to_outer_exposed
// documents the full chain). A prover cannot satisfy this circuit with public
// inputs the verified proof does not attest: swapping the claim changes the
// absorbed transcript (all challenges move — the fixed Merkle/fold data no
// longer verifies) and breaks the ExposeClaimAir identity for the committed
// trace.
//
// VK PIN (tooth 1, the shrink half): `vkPreprocessedRoot`, when set, bakes
// the shrink proof's preprocessed (op-list) commitment digest as a circuit
// CONSTANT — the shrink circuit's VK core.
//
// APEX-VK PIN (tooth 2, the apex half — closes the same-shape-apex forgery):
// the APEX's own VK identity (its preprocessed commitment, the RecursionVk-
// fingerprinted value) is a PROVER-SUPPLIED public input of the shrink
// circuit, verified only against itself — without this tooth a same-shape
// malicious apex with doctored preprocessed columns could steer its
// expose_claim to ANY (genesisRoot, finalRoot) and settle a FALSE root. The
// Rust side (apex_shrink_gnark_export.rs shrink_apex_to_outer_exposed) now
// (a) pins that commitment IN the shrink circuit (`pin_preprocessed_commit`:
// baked constants connected to the apex-verification's inputs) and (b)
// re-exposes the same 8 constant lanes through the shrink's expose_claim
// table, after the 25 claim lanes. `apexPreprocessedCommit`, when set, bakes
// the DEPLOYED dregg apex's commitment as circuit constants and asserts the
// exposed lanes 25..33 equal it — a shrink proof minted over any OTHER apex
// circuit cannot satisfy this circuit (its exposed VK-core lanes differ, and
// they are transcript-absorbed + ExposeClaimAir-bound, so they cannot be
// swapped without re-proving).
//
// WHERE THE PINNED VALUE COMES FROM (the pin's VALUE authority): the baked
// constant is NOT read from the proof fixture. It is loaded from the DERIVED
// identity artifact fixtures/apex_vk_identity.json, which the Rust derivation
// lane (circuit-prove/tests/apex_shrink_gnark_fixture.rs
// derive_deployed_apex_vk_identity_and_check_fixture) mints from a FRESH fold
// of the apex circuit at HEAD — VK material is content-independent and
// depth-invariant, so the derivation depends only on the deployed circuit
// definition — together with the apex's RecursionVk fingerprint, which is
// ASSERTED equal to the governance-pinned DreggApexRecursionVk constant
// (below) at every load, fail-closed. The fingerprint hashes the preprocessed
// commitment as a labeled component, making the (fingerprint, lanes) pair
// self-binding, and the Rust derivation lane asserts the same pin
// (DREGG_APEX_RECURSION_VK) on the freshly derived fingerprint before
// emitting the artifact — so the lanes the circuit bakes are the ones the
// pinned anchor hashes, not whatever sits at HEAD. The same Rust lane plus
// TestApexPinFixtureMatchesDerivedDeployedIdentity assert the proof fixture's
// apex VK-core equals this derived value (a same-shape non-deployed apex
// would mint a SELF-consistent fixture; the cross-artifact differential is
// what catches it). HONEST RESIDUAL: there is no proof-free
// preprocessed-commitment computation (the commitment is produced by the
// prover's preprocessed-trace commit; a keygen-only path does not exist in
// p3-circuit-prover), so "derived from the deployed circuit" means "derived
// by running the HEAD circuit once and recording the fingerprint-bound,
// anchor-checked result" — re-checkable by anyone via the Rust derivation
// test.
package friverifier

import (
	"math/big"

	"github.com/consensys/gnark/frontend"
)

// DreggApexRecursionVk is the GOVERNANCE-PINNED deployed-apex RecursionVk
// fingerprint (blake3-32, hex) — dregg's apex weak-subjectivity anchor, the
// exact analogue of the Solana bridge's pinned WeakSubjectivityAnchor
// (bridge/src/solana_trustless.rs check_pinned_anchor). Every consumer of the
// derived identity artifact fixtures/apex_vk_identity.json asserts its
// recursion_vk_hex equals THIS constant, fail-closed (loadApexVkIdentity via
// checkApexVkIdentityAnchor, stark_algebra_real_fixture_test.go), so the
// apex-VK pin's VALUE authority is "checked against a governance-pinned
// anchor", not "trust the apex source at HEAD".
//
// The 8 ApexVkLanes the settlement circuit bakes are bound to this
// fingerprint by the recursion_vk_fingerprint self-binding pair — the
// fingerprint hashes the apex's preprocessed commitment (gp.commitment) as a
// labeled component, and the lanes ARE that commitment's roots — enforced
// where the VK material exists: the Rust derivation lane
// (circuit-prove/src/apex_shrink_gnark_export.rs DREGG_APEX_RECURSION_VK +
// check_apex_vk_identity_pin) computes fingerprint and lanes from the SAME
// object and asserts the fingerprint equals the same pin before emitting the
// artifact. The Go side additionally cross-checks the identity's lanes
// against the loader-verified proof fixture's apex VK-core
// (TestApexPinFixtureMatchesDerivedDeployedIdentity), so doctored lanes
// under an honest fingerprint also reject.
//
// GOVERNANCE RESIDUAL (weak subjectivity, same shape as the Solana anchor
// pin): this constant is committed in-repo; governance chooses it at deploy,
// and an apex circuit change requires a governance/operator step — re-derive
// via derive_deployed_apex_vk_identity_and_check_fixture, then update this
// constant AND the Rust mirror — until then every identity load fails
// closed. The trust model is "trust a governance-pinned recent fingerprint",
// NOT "trust whoever compiled".
const DreggApexRecursionVk = "3ad1c9c601686a0983ed8df43a4a145e729d985194386ec22156029b92fc5503"

// shrinkPrefixOp is the structural script for replaying the pre-FRI
// transcript prefix in-circuit.
type shrinkPrefixOp struct {
	kind string // observe_bb | observe_digest | sample_bb
	n    int
}

// shrinkStarkPrefixLoc holds flat offsets into the prefix observe/sample/
// digest streams for the STARK-algebra inputs, the table-publics block (the
// settlement claim channel), and the anchored commitment digests.
type shrinkStarkPrefixLoc struct {
	permChSampleOff int // 8 values: perm alpha then perm beta coords
	alphaSampleOff  int // 4 values
	zetaSampleOff   int // 4 values
	friAlphaOff     int // 4 values: the FRI batch-combination alpha
	openedObsOff    int // 4*totalEF values
	openedObsLen    int
	cumObsOff       int // 4*numGlobalLookups values
	cumObsLen       int
	// Digest-word offsets of the input-round commitments, in PCS ROUND order
	// (trace=main, quotient, preprocessed, permutation) — the roots the
	// open_input Merkle checks bind against.
	inputRootDigOff [4]int
	// The per-instance table PUBLIC VALUES block (flattened, instance order),
	// observed right after the main commitment (verify_batch's transcript):
	// flat offset into the observe stream + per-instance lane counts.
	pubObsOff int
	pubLens   []int
	// Digest-word offset of the preprocessed (VK-core) commitment.
	preDigOff int
}

// pubObsOffOf returns the flat observe-stream offset of instance i's public
// values within the publics block.
func (l *shrinkStarkPrefixLoc) pubObsOffOf(i int) int {
	off := l.pubObsOff
	for j := 0; j < i; j++ {
		off += l.pubLens[j]
	}
	return off
}

// SettlementCircuit is the assembled native verify with the pinned 25-lane
// public statement. gnark exposes public inputs in struct field order, so
// `Publics` (fri_verifier.go — genesis_root[8] ++ final_root[8] ++ num_turns
// ++ chain_digest[8]) comes FIRST, matching the Solidity side's input vector.
type SettlementCircuit struct {
	Publics

	// Structural (unexported: ignored by the gnark schema walker).
	script           []shrinkPrefixOp
	cfg              FriConfig
	r                int
	rollInAfterRound []int
	shapes           []StarkInstanceShape
	loc              shrinkStarkPrefixLoc
	sym              *SymbolicConstraints  // the emitted constraint DAGs (required)
	inputRounds      []OpenInputRoundShape // open_input structural shapes
	claimInstance    int                   // the expose_claim instance index
	// vkPreprocessedRoot, when non-nil, pins the shrink proof's preprocessed
	// (op-list) commitment digest as a circuit constant — the shrink-VK core.
	vkPreprocessedRoot *big.Int
	// apexPreprocessedCommit, when non-nil, pins the APEX's preprocessed
	// commitment (the deployed dregg apex's VK-identity core, ApexVkLanes
	// BabyBear lanes) as circuit constants against the claim channel's
	// re-exposed VK-core lanes — the apex-VK pin (tooth 2). The value is the
	// DERIVED deployed identity (fixtures/apex_vk_identity.json, minted from
	// the apex circuit at HEAD and RecursionVk-fingerprint-bound), not a
	// fixture-read constant — see the package doc's VALUE-authority note.
	apexPreprocessedCommit []*big.Int

	PrefixObs     []frontend.Variable
	PrefixDigests []frontend.Variable
	PrefixSamples []frontend.Variable
	CommitRoots   []frontend.Variable
	FinalPoly     []BBExt
	PowWitness    frontend.Variable
	Queries       []FriNativeQueryOpening
	InputOpenings [][]OpenInputBatchOpening // [query][input round]
}

func (c *SettlementCircuit) Define(api frontend.API) error {
	bb := NewBBApi(api)
	ch := NewMultiFieldChallenger(bb)

	if c.sym == nil {
		panic("SettlementCircuit: emitted symbolic constraints are required")
	}

	// ---- Public-statement hygiene: every lane a canonical BabyBear residue
	// (fail-closed; mirrors DreggSettlement.sol's _requireCanonical).
	for i := 0; i < DigestWidth; i++ {
		bb.AssertIsCanonical(c.GenesisRoot[i])
		bb.AssertIsCanonical(c.FinalRoot[i])
		bb.AssertIsCanonical(c.ChainDigest[i])
	}
	bb.AssertIsCanonical(c.NumTurns)

	// ---- Transcript replay — every observed value canonicity-bound by the
	// challenger, every sampled challenge pinned.
	io, id, is := 0, 0, 0
	for _, op := range c.script {
		switch op.kind {
		case "observe_bb":
			ch.ObserveBabyBearSlice(c.PrefixObs[io : io+op.n])
			io += op.n
		case "observe_digest":
			ch.ObserveBn254Digest(c.PrefixDigests[id : id+op.n])
			id += op.n
		case "sample_bb":
			for k := 0; k < op.n; k++ {
				api.AssertIsEqual(ch.SampleBabyBear(), c.PrefixSamples[is])
				is++
			}
		}
	}

	// ---- THE SETTLEMENT BINDING: the first 25 lanes of the shrink proof's
	// expose_claim public values (the transcript-absorbed, AIR-constrained
	// claim channel) ARE the 25 public inputs, in the pinned order. The
	// channel's tail ApexVkLanes lanes are the re-exposed apex VK core.
	claim := c.PrefixObs[c.loc.pubObsOffOf(c.claimInstance) : c.loc.pubObsOffOf(c.claimInstance)+
		c.loc.pubLens[c.claimInstance]]
	if len(claim) != NumPublicInputs+ApexVkLanes {
		panic("SettlementCircuit: claim channel is not the pinned 25-lane statement + 8-lane apex VK core")
	}
	k := 0
	for i := 0; i < DigestWidth; i++ {
		api.AssertIsEqual(claim[k], c.GenesisRoot[i])
		k++
	}
	for i := 0; i < DigestWidth; i++ {
		api.AssertIsEqual(claim[k], c.FinalRoot[i])
		k++
	}
	api.AssertIsEqual(claim[k], c.NumTurns)
	k++
	for i := 0; i < DigestWidth; i++ {
		api.AssertIsEqual(claim[k], c.ChainDigest[i])
		k++
	}

	// ---- VK pin (tooth 1, shrink half): the preprocessed (op-list)
	// commitment digest is a constant of the circuit.
	if c.vkPreprocessedRoot != nil {
		api.AssertIsEqual(c.PrefixDigests[c.loc.preDigOff], c.vkPreprocessedRoot)
	}

	// ---- APEX-VK pin (tooth 2, apex half): the re-exposed apex preprocessed
	// commitment lanes equal the DEPLOYED dregg apex's, as baked constants.
	// These lanes are the same variables the transcript absorbed and the
	// ExposeClaimAir bus-binds to the constants the in-circuit apex
	// verification was pinned to — a same-shape malicious apex (different
	// preprocessed commitment) fails HERE even if everything else self-verifies.
	if c.apexPreprocessedCommit != nil {
		if len(c.apexPreprocessedCommit) != ApexVkLanes {
			panic("SettlementCircuit: apexPreprocessedCommit must carry exactly ApexVkLanes lanes")
		}
		for i, want := range c.apexPreprocessedCommit {
			api.AssertIsEqual(claim[NumPublicInputs+i], want)
		}
	}

	// ---- STARK-algebra layer over the transcript-bound opened values.
	groupEF := func(vars []frontend.Variable) []BBExt {
		out := make([]BBExt, len(vars)/4)
		for i := range out {
			copy(out[i][:], vars[4*i:4*i+4])
		}
		return out
	}
	sampleExt := func(off int) BBExt {
		var e BBExt
		copy(e[:], c.PrefixSamples[off:off+4])
		return e
	}
	openedEF := groupEF(c.PrefixObs[c.loc.openedObsOff : c.loc.openedObsOff+c.loc.openedObsLen])
	zeta := sampleExt(c.loc.zetaSampleOff)
	pubVals := make([][]frontend.Variable, len(c.shapes))
	for i := range c.shapes {
		off := c.loc.pubObsOffOf(i)
		pubVals[i] = c.PrefixObs[off : off+c.loc.pubLens[i]]
	}
	VerifyShrinkStarkAlgebra(bb, c.shapes,
		openedEF,
		groupEF(c.PrefixObs[c.loc.cumObsOff:c.loc.cumObsOff+c.loc.cumObsLen]),
		pubVals,
		ShrinkStarkChallenges{
			PermAlpha: sampleExt(c.loc.permChSampleOff),
			PermBeta:  sampleExt(c.loc.permChSampleOff + 4),
			Alpha:     sampleExt(c.loc.alphaSampleOff),
			Zeta:      zeta,
		},
		c.sym)

	// ---- FRI core, drawing betas and query indices live from the same
	// transcript.
	queryBits := VerifyFriNative(bb, c.cfg, c.r, c.CommitRoots, c.FinalPoly, c.PowWitness,
		c.Queries, c.rollInAfterRound, ch)

	// ---- open_input: bind the fold seeds to the COMMITTED columns.
	roots := make([]frontend.Variable, len(c.loc.inputRootDigOff))
	for i, off := range c.loc.inputRootDigOff {
		roots[i] = c.PrefixDigests[off]
	}
	pre := NewOpenInputPrecomp(bb, c.inputRounds, zeta, sampleExt(c.loc.friAlphaOff),
		openedEF, c.r+c.cfg.LogBlowup+c.cfg.LogFinalPolyLen)
	for qi := range c.Queries {
		BindOpenInputToFriSeedsNative(bb, c.inputRounds, pre, queryBits[qi], roots,
			c.InputOpenings[qi], c.Queries[qi], c.rollInAfterRound)
	}
	return nil
}
