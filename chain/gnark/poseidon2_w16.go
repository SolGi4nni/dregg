// Poseidon2 width-16 permutation over BabyBear, as a circuit gadget.
//
// Ground truth is the plonky3 rev pinned by /Users/ember/dev/plonky3-recursion
// (Cargo.toml: p3-baby-bear / p3-poseidon2 at Plonky3 rev
// 82cfad73cd734d37a0d51953094f970c531817ec); the recursion fork instantiates
// exactly default_babybear_poseidon2_16()
// (plonky3-recursion/circuit-prover/src/config.rs:158).
//
// Structure (poseidon2/src/lib.rs:139 permute_mut and
// poseidon2/src/external.rs:321 external_initial_permute_state):
//
//	mds_light(state)                      // initial external linear layer
//	4 × { +RC_init[r]; x^7; mds_light }   // initial full rounds
//	13 × internal round                   // partial rounds
//	4 × { +RC_final[r]; x^7; mds_light }  // terminal full rounds
//
// S-box degree 7 (baby-bear/src/poseidon1.rs:38 BABYBEAR_S_BOX_DEGREE).
//
// mds_light (external.rs:113 mds_light_permutation): apply the 4x4 matrix
// M4 = [[2,3,1,1],[1,2,3,1],[1,1,2,3],[3,1,1,2]] (external.rs:54 apply_mat4)
// to each 4-chunk, then state[i] += sum_k(chunk_k[i mod 4]).
//
// Internal round (monty-31/src/poseidon2.rs:76 permute_state +
// baby-bear/src/poseidon2.rs:376 internal_layer_mat_mul for width 16):
//
//	state[0] += RC; state[0] = state[0]^7
//	sum = Σ state[i]
//	state[i] = V[i]·state[i] + sum        // matrix = AllOnes + Diag(V)
//	V = [-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4,
//	     1/2^8, 1/4, 1/8, 1/2^27, -1/2^8, -1/16, -1/2^27]
//
// Round constants below are the exact BABYBEAR_POSEIDON2_RC_16_* tables
// (baby-bear/src/poseidon2.rs:92,124,155), machine-extracted from the Rust
// source (canonical residues). The engine is width-generic so the width-24
// permutation (RC_24 tables + its 24-entry diagonal) can follow as pure data.
package friverifier

import "github.com/consensys/gnark/frontend"

// poseidon2Params carries everything width-specific; width 24 is a second
// instance of this struct.
type poseidon2Params struct {
	width             int
	rcExternalInitial [][]uint32 // halfFullRounds × width
	rcExternalFinal   [][]uint32 // halfFullRounds × width
	rcInternal        []uint32   // partialRounds
	diag              []uint32   // canonical residues of V (AllOnes+Diag(V))
}

// BABYBEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL (baby-bear/src/poseidon2.rs:92).
var poseidon2W16RCExternalInitial = [4][16]uint32{
	{1774958255, 1185780729, 1621102414, 1796380621, 588815102, 1932426223, 1925334750, 747903232, 89648862, 360728943, 977184635, 1425273457, 256487465, 1200041953, 572403254, 448208942},
	{1215789478, 944884184, 953948096, 547326025, 646827752, 889997530, 1536873262, 86189867, 1065944411, 32019634, 333311454, 456061748, 1963448500, 1827584334, 1391160226, 1348741381},
	{88424255, 104111868, 1763866748, 79691676, 1988915530, 1050669594, 359890076, 573163527, 222820492, 159256268, 669703072, 763177444, 889367200, 256335831, 704371273, 25886717},
	{51754520, 1833211857, 454499742, 1384520381, 777848065, 1053320300, 1851729162, 344647910, 401996362, 1046925956, 5351995, 1212119315, 754867989, 36972490, 751272725, 506915399},
}

// BABYBEAR_POSEIDON2_RC_16_EXTERNAL_FINAL (baby-bear/src/poseidon2.rs:124).
var poseidon2W16RCExternalFinal = [4][16]uint32{
	{1922082829, 1870549801, 1502529704, 1990744480, 1700391016, 1702593455, 321330495, 528965731, 183414327, 1886297254, 1178602734, 1923111974, 744004766, 549271463, 1781349648, 542259047},
	{1536158148, 715456982, 503426110, 340311124, 1558555932, 1226350925, 742828095, 1338992758, 1641600456, 1843351545, 301835475, 43203215, 386838401, 1520185679, 1235297680, 904680097},
	{1491801617, 1581784677, 913384905, 247083962, 532844013, 107190701, 213827818, 1979521776, 1358282574, 1681743681, 1867507480, 1530706910, 507181886, 695185447, 1172395131, 1250800299},
	{1503161625, 817684387, 498481458, 494676004, 1404253825, 108246855, 59414691, 744214112, 890862029, 1342765939, 1417398904, 1897591937, 1066647396, 1682806907, 1015795079, 1619482808},
}

// BABYBEAR_POSEIDON2_RC_16_INTERNAL (baby-bear/src/poseidon2.rs:155).
var poseidon2W16RCInternal = [13]uint32{1518359488, 1765533241, 945325693, 422793067, 311365592, 1311448267, 1629555936, 1009879353, 190525218, 786108885, 557776863, 212616710, 605745517}

// Canonical residues of the width-16 internal diagonal V
// (baby-bear/src/poseidon2.rs:11,376). E.g. 1/2 = (p+1)/2 = 1006632961 and
// 1/2^27 = -15 mod p (since 15·2^27 = p - 1).
var poseidon2W16Diag = [16]uint32{2013265919, 1, 2, 1006632961, 3, 4, 1006632960, 2013265918, 2013265917, 2005401601, 1509949441, 1761607681, 2013265906, 7864320, 125829120, 15}

var poseidon2W16Params = func() *poseidon2Params {
	p := &poseidon2Params{width: 16}
	for i := range poseidon2W16RCExternalInitial {
		p.rcExternalInitial = append(p.rcExternalInitial, poseidon2W16RCExternalInitial[i][:])
	}
	for i := range poseidon2W16RCExternalFinal {
		p.rcExternalFinal = append(p.rcExternalFinal, poseidon2W16RCExternalFinal[i][:])
	}
	p.rcInternal = poseidon2W16RCInternal[:]
	p.diag = poseidon2W16Diag[:]
	return p
}()

// Poseidon2W16 applies the width-16 BabyBear Poseidon2 permutation in-place.
// Inputs are asserted canonical (fail-closed at the gadget boundary); outputs
// are canonical.
func (bb *BBApi) Poseidon2W16(state *[16]frontend.Variable) {
	for i := range state {
		bb.AssertIsCanonical(state[i])
	}
	bb.poseidon2Permute(state[:], poseidon2W16Params)
}

// poseidon2Permute is the width-generic engine. state elements must be
// canonical; the permutation is applied in place.
func (bb *BBApi) poseidon2Permute(state []frontend.Variable, p *poseidon2Params) {
	if len(state) != p.width || p.width%4 != 0 {
		panic("poseidon2Permute: bad state width")
	}
	bb.mdsLight(state)
	for _, rcs := range p.rcExternalInitial {
		bb.poseidon2ExternalRound(state, rcs)
	}
	for _, rc := range p.rcInternal {
		bb.poseidon2InternalRound(state, rc, p.diag)
	}
	for _, rcs := range p.rcExternalFinal {
		bb.poseidon2ExternalRound(state, rcs)
	}
}

// poseidon2ExternalRound: state[i] = (state[i] + rc[i])^7, then mds_light.
func (bb *BBApi) poseidon2ExternalRound(state []frontend.Variable, rcs []uint32) {
	for i := range state {
		// canonical + canonical constant < 2p ≤ 2^32
		state[i] = bb.sboxPow7(bb.api.Add(state[i], rcs[i]), 32)
	}
	bb.mdsLight(state)
}

// poseidon2InternalRound mirrors monty-31/src/poseidon2.rs:76:
// rc+sbox on lane 0, then state = (AllOnes + Diag(V))·state.
func (bb *BBApi) poseidon2InternalRound(state []frontend.Variable, rc uint32, diag []uint32) {
	api := bb.api
	s0 := bb.sboxPow7(api.Add(state[0], rc), 32)
	// partSum = Σ state[1..] raw: (width-1) canonicals < (w-1)·p < 2^36.
	partSum := frontend.Variable(0)
	for i := 1; i < len(state); i++ {
		partSum = api.Add(partSum, state[i])
	}
	// fullSum raw < w·p < 2^36.
	fullSum := api.Add(partSum, s0)
	// V[0] = -2: state[0] = sum - 2·s0 = partSum - s0; raw partSum + (p - s0)
	// < (w+1)·p < 2^37 → bound 40.
	state[0] = bb.ReduceBounded(api.Add(partSum, api.Sub(BabyBearP, s0)), 40)
	for i := 1; i < len(state); i++ {
		// diag[i]·state[i] < 2^62; + fullSum < 2^62 + 2^36 < 2^63.
		state[i] = bb.ReduceBounded(api.Add(api.Mul(diag[i], state[i]), fullSum), 63)
	}
}

// sboxPow7 computes x^7 mod p for x < 2^boundBits (boundBits ≤ 32).
func (bb *BBApi) sboxPow7(x frontend.Variable, boundBits uint) frontend.Variable {
	if boundBits > 32 {
		panic("sboxPow7: input bound too large")
	}
	x2 := bb.ReduceBounded(bb.api.Mul(x, x), 2*boundBits)    // ≤ 64
	x3 := bb.ReduceBounded(bb.api.Mul(x2, x), 31+boundBits)  // ≤ 63
	x6 := bb.ReduceBounded(bb.api.Mul(x3, x3), 62)           //   62
	return bb.ReduceBounded(bb.api.Mul(x6, x), 31+boundBits) // ≤ 63
}

// mdsLight is the external linear layer (external.rs:113): M4 per 4-chunk,
// then the outer circulant sum. Inputs canonical; outputs canonical.
func (bb *BBApi) mdsLight(state []frontend.Variable) {
	api := bb.api
	w := len(state)
	// Raw M4 per chunk: outputs < 7p (< 2^34).
	for c := 0; c+4 <= w; c += 4 {
		bb.rawMat4(state[c : c+4])
	}
	// sums[k] = Σ_j state[4j+k], raw < (w/4)·7p.
	var sums [4]frontend.Variable
	for k := 0; k < 4; k++ {
		s := state[k]
		for j := k + 4; j < w; j += 4 {
			s = api.Add(s, state[j])
		}
		sums[k] = s
	}
	// state[i] + sums[i%4] < 7p·(w/4 + 1) < 2^38 for w ≤ 32 → bound 40.
	for i := range state {
		state[i] = bb.ReduceBounded(api.Add(state[i], sums[i%4]), 40)
	}
}

// rawMat4 multiplies a 4-slice by M4 = [[2,3,1,1],[1,2,3,1],[1,1,2,3],[3,1,1,2]]
// (external.rs:60 apply_mat4) WITHOUT reduction: canonical inputs → outputs
// < 7p.
func (bb *BBApi) rawMat4(x []frontend.Variable) {
	api := bb.api
	t01 := api.Add(x[0], x[1])
	t23 := api.Add(x[2], x[3])
	t0123 := api.Add(t01, t23)
	t01123 := api.Add(t0123, x[1])
	t01233 := api.Add(t0123, x[3])
	x3 := api.Add(t01233, api.Mul(2, x[0])) // 3·x0 + x1 + x2 + 2·x3
	x1 := api.Add(t01123, api.Mul(2, x[2])) // x0 + 2·x1 + 3·x2 + x3
	x0 := api.Add(t01123, t01)              // 2·x0 + 3·x1 + x2 + x3
	x2 := api.Add(t01233, t23)              // x0 + x1 + 2·x2 + 3·x3
	x[0], x[1], x[2], x[3] = x0, x1, x2, x3
}
