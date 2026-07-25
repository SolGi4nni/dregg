// THE PEER-WRAP CIRCUIT — the light-client-STARK → Groth16 verifier whose
// public inputs are EXACTLY the on-chain DreggPeerRegistry contract
// [chainId, height, rootHi, rootLo] (contracts/IPeerLightClientVerifier.sol).
//
// This is the MIRROR of SettlementCircuit (settlement_circuit.go): where the
// settlement wrap verifies DREGG's own shrink proof and exposes the 25-lane
// turn-chain statement for IDreggSettlement.settle, the peer wrap verifies a
// PEER chain's light-client STARK ("chain X finalized root R at height H") and
// exposes the 4-lane peer-finality statement for
// DreggPeerRegistry.submitPeerFinality. Together they are the two halves of
// mutual cross-chain verification — TRUE PEERS.
//
// ## What it REUSES (the FRI-wrap, verbatim)
//
// A produced light-client STARK is proved + shrunk through the SAME
// descriptor_by_name(name) → prove_vm_descriptor2 → apex → BN254-native
// re-prove pipeline as dregg's own proof (commit 9ba2e575b2 wired the 4 LC
// AIRs into that path). So a peer proof has the SAME shrink-proof shape the
// settlement wrap already verifies — the LC AIR is "just another descriptor"
// whose public values ride the ExposeClaim instance. PeerFinalityCircuit.Define
// therefore runs the IDENTICAL verification body as SettlementCircuit.Define:
//   1. transcript replay (MultiFieldChallenger, every sample pinned),
//   2. the full batch-STARK algebra layer (VerifyShrinkStarkAlgebra),
//   3. the FRI core (VerifyFriNative), and
//   4. the open_input commitment binding (NewOpenInputPrecomp +
//      BindOpenInputToFriSeedsNative).
// NONE of that is re-authored here; the peer wrap calls the same gadget
// functions. The AIR being verified is LEAN-AUTHORED
// (metatheory/Dregg2/Circuit/Emit/LightClient{Eth,Tendermint,Solana,Midnight}Air.lean,
// each carrying its own `*_no_forgery` refinement over the emitted descriptor);
// this Go file is the outer BN254 verifier, exactly as SettlementCircuit is —
// it authors NO constraint / gadget / AIR, only the SNARK-verify + the
// public-input mapping below.
//
// ## What it SWAPS (the ONLY new logic): the public-input binding layer
//
// SettlementCircuit binds the ExposeClaim channel to 25 BabyBear lanes. The
// peer wrap binds it to the 4 BN254 peer-finality lanes via BindPeerFinalityLanes
// (below): a per-chain map from the LC descriptor's public statement into
// [chainId, height, rootHi, rootLo]. That is the entire delta between the two
// wraps.
//
// ## Tooth 1 (the LC-VK pin) is kept; tooth 2 (apex-VK) is dropped
//
// `vkPreprocessedRoot` pins the shrink proof's preprocessed (op-list)
// commitment digest as a circuit constant — the LC circuit's VK core — exactly
// as the settlement wrap does. The apex-VK re-exposure pin (SettlementCircuit's
// tooth 2) is dregg-apex-specific and has no peer analogue, so it is absent:
// a peer proof's ExposeClaim channel carries ONLY the LC public statement, not
// a re-exposed apex VK core.
//
// ## HONEST SCOPE / NAMED RESIDUALS (current-resolution)
//
//   - ALL FOUR chains now expose the FULL 256-bit finality root as 9 radix-2^31
//     limbs (LightClient{Eth,Tendermint,Solana,Midnight}Air.lean, *_LIMBS=9,
//     MSB-first), bound one-limb-per-PI; BindPeerFinalityLanes packs them
//     radix-2^31 and 128-bit-splits into (rootHi, rootLo), which the on-chain
//     splitRoot recomposes exactly — so the wrap binds all 256 bits on every
//     chain (the 31-bit collision gap is closed uniformly). The per-chain root:
//     eth = fin_state_root, tm = app_hash, sol = bank_root, mid = target_root;
//     RootLanes = [1..9] on every map. The non-root anchors shift past the 9 root
//     limbs: tm chain_id 2->10, sol slot 2->10, mid round 2->10 / era 3->11.
//   - eth/tm expose no HEIGHT felt yet; for those chains Height rides as a
//     published peer lane not yet bound to a claim felt (HeightLane = -1). sol
//     (slot) and mid (round) DO expose a height felt and bind it.
//   - The full end-to-end circuit is exercised only against a REAL exported LC
//     shrink fixture; producing one needs the LC prove (Rust, off-box). That is
//     the gnark-build residual (see peer_wrap_circuit_test.go). BindPeerFinalityLanes
//     itself IS exercised here in isolation (TestPeerLaneBind*).
package friverifier

import (
	"math/big"

	"github.com/consensys/gnark/frontend"
)

// PeerNumPublicInputs is the pinned peer-finality lane count: the 4 lanes
// [chainId, height, rootHi, rootLo] IPeerLightClientVerifier.verifyProof
// expects (contracts/IPeerLightClientVerifier.sol).
const PeerNumPublicInputs = 4

// RootLimbRadixBits is the BabyBear limb radix used to pack the LC descriptor's
// canonical root felt(s) into the 256-bit root before the 128-bit split. Each
// canonical BabyBear felt is < 2^31 = 2^RootLimbRadixBits, so up to 8 felts
// pack injectively into < 2^248 < 2^256.
const RootLimbRadixBits = 31

// PeerPublics are the peer wrap's Groth16 public inputs, in the EXACT pinned
// order the on-chain registry assembles
// (DreggPeerRegistry.submitPeerFinality step 2):
//
//	[0] chainId  — the peer chain's identifier (EIP-155 for an EVM peer).
//	[1] height   — the finalized height.
//	[2] rootHi   — top 128 bits of the 32-byte finalized root R.
//	[3] rootLo   — bottom 128 bits of R.
//
// gnark exposes public inputs in struct-field order, and PeerPublics is the
// FIRST field of PeerFinalityCircuit, so the emitted Groth16 public-input
// vector is exactly uint256[4]{chainId, height, rootHi, rootLo} — no reordering
// on the Solidity side.
type PeerPublics struct {
	ChainID frontend.Variable `gnark:",public"`
	Height  frontend.Variable `gnark:",public"`
	RootHi  frontend.Variable `gnark:",public"`
	RootLo  frontend.Variable `gnark:",public"`
}

// PeerLaneMap describes how ONE peer chain's light-client public statement (the
// ExposeClaim channel felts, in the descriptor's piCount order) maps into the
// 4-lane peer-finality statement. One map per LC descriptor; the map IS the
// chain-specific part of the wrap (the wrap circuit is pinned to one peer).
type PeerLaneMap struct {
	// Name is the descriptor short name (diagnostics only).
	Name string
	// PiCount is the LC descriptor's public_input_count — the ExposeClaim
	// channel length this map is asserted against (fail-closed on drift).
	PiCount int
	// ChainID is the peer chainId baked as a circuit constant into lane [0].
	// Being a constant forces every proof under this wrap's VK to speak of this
	// one chain (a proof of chain A can never be recorded as chain B).
	ChainID *big.Int
	// ChainIDLane, when ≥ 0, is a claim index the descriptor exposes carrying
	// the chain id (tm's chain_id PI); the baked constant is cross-checked equal
	// to it. -1 when the descriptor exposes no chain-id felt.
	ChainIDLane int
	// HeightLane, when ≥ 0, is the claim index of the finalized-height felt
	// (sol slot, mid round). -1 = the descriptor exposes no height felt yet, so
	// Height rides as a published peer lane not bound to a claim felt (NAMED
	// RESIDUAL — eth/tm current slice).
	HeightLane int
	// RootLanes are the claim indices of the finalized-root felt(s),
	// most-significant limb first. Length 1 in the current single-anchor LC-AIR
	// slice; grows to the full N-felt root in the next iteration with no
	// interface change.
	RootLanes []int
}

// The four peer-chain maps. The chainId choice is the DEPLOY-PINNED wire
// convention (governance ratifies it; here it is the documented default):
// EIP-155 for the EVM peer, the chain's SLIP-44 coin type as a dregg-assigned
// peer id for the non-EVM peers (a stable, non-arbitrary, collision-free source
// of small ids), and a reserved placeholder where no registry id exists.
var (
	// PeerChainIdEth / PeerChainIdBase — the EVM peer under the ETH/Base LC AIR
	// (LightClientEthAir.lean). Same map shape; the chainId lane distinguishes
	// mainnet (1) from Base (8453).
	PeerChainIdEth  = big.NewInt(1)
	PeerChainIdBase = big.NewInt(8453)
	// PeerChainIdCosmos — SLIP-44 coin type 118 (ATOM) as the dregg-assigned id.
	PeerChainIdCosmos = big.NewInt(118)
	// PeerChainIdSolana — SLIP-44 coin type 501 (SOL).
	PeerChainIdSolana = big.NewInt(501)
	// PeerChainIdMidnight — no SLIP-44 registry entry; reserved placeholder,
	// governance-pinned at deploy (the honest residual on the id itself).
	PeerChainIdMidnight = big.NewInt(2718)
)

// EthLcPeerMap — ETH/Base LC (PIs committee_root[0], fin_state_root as 9
// radix-2^31 limbs[1..9] (full 256-bit, MSB-first), domain_gvr[10]). Records the
// full fin_state_root as the finality root; no height felt yet (HeightLane = -1).
// Use PeerChainIdBase for the Base instance.
func EthLcPeerMap(chainID *big.Int) PeerLaneMap {
	return PeerLaneMap{
		Name:        "eth-lightclient",
		PiCount:     11,
		ChainID:     chainID,
		ChainIDLane: -1,
		HeightLane:  -1,
		RootLanes:   []int{1, 2, 3, 4, 5, 6, 7, 8, 9}, // fin_state_root, 9 limbs (full 256-bit)
	}
}

// TmLcPeerMap — Tendermint/Cosmos LC (PIs next_vals_root[0], app_hash as 9
// radix-2^31 limbs[1..9] (full 256-bit, MSB-first), chain_id[10]). Records
// app_hash as the finality (application-state) root, and cross-checks the baked
// chainId against the descriptor's own chain_id felt (now at PI 10, shifted past
// the 9 root limbs). No height felt yet.
var TmLcPeerMap = PeerLaneMap{
	Name:        "tm-lightclient",
	PiCount:     11,
	ChainID:     PeerChainIdCosmos,
	ChainIDLane: 10, // chain_id (shifted past the 9 app_hash limbs)
	HeightLane:  -1,
	RootLanes:   []int{1, 2, 3, 4, 5, 6, 7, 8, 9}, // app_hash, 9 limbs (full 256-bit)
}

// SolLcPeerMap — Solana LC (PIs anchor_root[0], bank_root as 9 radix-2^31
// limbs[1..9] (full 256-bit, MSB-first), slot[10]). Records bank_root as the
// finality (bank/account-state) root; binds height to slot (now at PI 10,
// shifted past the 9 root limbs).
var SolLcPeerMap = PeerLaneMap{
	Name:        "solana-lightclient",
	PiCount:     11,
	ChainID:     PeerChainIdSolana,
	ChainIDLane: -1,
	HeightLane:  10, // slot (shifted past the 9 bank_root limbs)
	RootLanes:   []int{1, 2, 3, 4, 5, 6, 7, 8, 9}, // bank_root, 9 limbs (full 256-bit)
}

// MidLcPeerMap — Midnight LC (PIs anchor_root[0], target_root as 9 radix-2^31
// limbs[1..9] (full 256-bit, MSB-first), round[10], era[11]). Records
// target_root as the finality root; binds height to round (now at PI 10, shifted
// past the 9 root limbs). The era felt (PI 11) rides as an unbound published PI,
// as before.
var MidLcPeerMap = PeerLaneMap{
	Name:        "midnight-lightclient",
	PiCount:     12,
	ChainID:     PeerChainIdMidnight,
	ChainIDLane: -1,
	HeightLane:  10, // round (shifted past the 9 target_root limbs)
	RootLanes:   []int{1, 2, 3, 4, 5, 6, 7, 8, 9}, // target_root, 9 limbs (full 256-bit)
}

// BindPeerFinalityLanes is THE peer-wrap public-input mapping (the only new
// logic in this file). Given the LC ExposeClaim channel `claim` (each felt
// already canonicity-bound by the transcript replay) and a per-chain map, it
// constrains the 4 PeerPublics lanes to the peer-finality statement:
//
//   - chainId := the baked constant (and, where the descriptor exposes one, the
//     descriptor's own chain-id felt is asserted equal to it);
//   - height := the descriptor's height felt (or an unbound published lane —
//     the NAMED RESIDUAL — where the descriptor exposes none);
//   - (rootHi, rootLo) := the 128-bit split of the radix-2^31 packing of the
//     descriptor's root felt(s), matching DreggPeerRegistry.splitRoot exactly:
//     packed == rootHi·2^128 + rootLo with rootHi, rootLo each < 2^128.
//
// A proof whose ExposeClaim channel does not carry these exact values yields an
// unsatisfiable system (fail-closed): the claim felts are transcript-absorbed
// and ExposeClaimAir-bound, so they cannot be swapped without re-proving.
func BindPeerFinalityLanes(bb *BBApi, claim []frontend.Variable, m PeerLaneMap, pub *PeerPublics) {
	api := bb.API()
	if len(claim) != m.PiCount {
		panic("BindPeerFinalityLanes: claim channel length != descriptor piCount")
	}
	if len(m.RootLanes) == 0 || len(m.RootLanes) > 9 {
		panic("BindPeerFinalityLanes: RootLanes must carry 1..9 felts (radix-2^31; 9 limbs = full 256-bit root)")
	}

	// ---- chainId lane: the baked per-chain constant.
	api.AssertIsEqual(pub.ChainID, m.ChainID)
	if m.ChainIDLane >= 0 {
		// The descriptor's own chain-id anchor must equal the baked constant
		// (tm): a proof minted under a different chain-id felt is refused.
		api.AssertIsEqual(claim[m.ChainIDLane], m.ChainID)
	}

	// ---- height lane.
	if m.HeightLane >= 0 {
		api.AssertIsEqual(pub.Height, claim[m.HeightLane])
	}
	// else: NAMED RESIDUAL — Height is a published peer lane not bound to any
	// claim felt (the current eth/tm LC-AIR slice exposes no height felt). It is
	// still a Groth16 public input the on-chain verifier checks; what is not yet
	// closed is its in-circuit tie to the LC statement.

	// ---- (rootHi, rootLo): radix-2^31 pack of the root felt(s), then the
	// 128-bit split, byte-for-byte the on-chain splitRoot semantics.
	base := new(big.Int).Lsh(big.NewInt(1), RootLimbRadixBits)
	packed := frontend.Variable(0)
	for _, li := range m.RootLanes {
		if li < 0 || li >= m.PiCount {
			panic("BindPeerFinalityLanes: root lane index out of range")
		}
		// Canonicity is what makes the packing injective (each limb < 2^31). The
		// transcript already asserts it; re-assert for the standalone gadget.
		bb.AssertIsCanonical(claim[li])
		packed = api.Add(api.Mul(packed, base), claim[li])
	}
	// rootHi, rootLo each < 2^128 (ToBinary bounds them), and
	// packed == rootHi·2^128 + rootLo pins the unique split (packed < 2^248).
	api.ToBinary(pub.RootHi, 128)
	api.ToBinary(pub.RootLo, 128)
	twoTo128 := new(big.Int).Lsh(big.NewInt(1), 128)
	api.AssertIsEqual(packed, api.Add(api.Mul(pub.RootHi, twoTo128), pub.RootLo))
}

// PeerFinalityCircuit is the peer-wrap: the SettlementCircuit verification body
// (transcript replay + STARK algebra + FRI core + open_input) with the 4-lane
// peer-finality public statement bound to the LC ExposeClaim channel. Its
// structural fields mirror SettlementCircuit's (populated identically from an
// exported LC shrink fixture); only the public-binding block differs.
type PeerFinalityCircuit struct {
	PeerPublics

	// Structural (unexported: ignored by the gnark schema walker) — identical
	// to SettlementCircuit's, driven from the exported LC shrink fixture.
	script           []shrinkPrefixOp
	cfg              FriConfig
	r                int
	rollInAfterRound []int
	shapes           []StarkInstanceShape
	loc              shrinkStarkPrefixLoc
	sym              *SymbolicConstraints
	inputRounds      []OpenInputRoundShape
	claimInstance    int
	laneMap          PeerLaneMap
	// vkPreprocessedRoot pins the LC circuit's preprocessed (op-list) commitment
	// digest as a constant — tooth 1 (the LC-VK pin). No apex pin (peer proofs
	// carry no re-exposed apex VK core).
	vkPreprocessedRoot *big.Int

	PrefixObs     []frontend.Variable
	PrefixDigests []frontend.Variable
	PrefixSamples []frontend.Variable
	CommitRoots   []frontend.Variable
	FinalPoly     []BBExt
	PowWitness    frontend.Variable
	Queries       []FriNativeQueryOpening
	InputOpenings [][]OpenInputBatchOpening // [query][input round]
}

// Define is the PEER TWIN of SettlementCircuit.Define: the same verification
// body, with BindPeerFinalityLanes in place of the 25-lane binding.
func (c *PeerFinalityCircuit) Define(api frontend.API) error {
	bb := NewBBApi(api)
	ch := NewMultiFieldChallenger(bb)

	if c.sym == nil {
		panic("PeerFinalityCircuit: emitted symbolic constraints are required")
	}

	// ---- Transcript replay — every observed value canonicity-bound, every
	// sampled challenge pinned (identical to SettlementCircuit).
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

	// ---- THE PEER BINDING: the LC ExposeClaim channel (the transcript-absorbed,
	// ExposeClaimAir-constrained public statement) maps into the 4 peer lanes.
	claim := c.PrefixObs[c.loc.pubObsOffOf(c.claimInstance) : c.loc.pubObsOffOf(c.claimInstance)+
		c.loc.pubLens[c.claimInstance]]
	BindPeerFinalityLanes(bb, claim, c.laneMap, &c.PeerPublics)

	// ---- VK pin (tooth 1, the LC-VK core).
	if c.vkPreprocessedRoot != nil {
		api.AssertIsEqual(c.PrefixDigests[c.loc.preDigOff], c.vkPreprocessedRoot)
	}

	// ---- STARK-algebra layer over the transcript-bound opened values
	// (identical gadget call to SettlementCircuit).
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

	// ---- FRI core.
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
