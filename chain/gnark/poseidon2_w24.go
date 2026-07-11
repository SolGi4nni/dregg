// Poseidon2 width-24 permutation over BabyBear, as a circuit gadget.
//
// This is a pure-data second instance of the width-generic engine in
// poseidon2_w16.go: identical S-box (x^7), identical external M4/MDS layer and
// round order (4 initial full → 21 partial → 4 final full), only the round
// constants and the 24-entry internal diagonal differ. The segment-digest
// sponge / NPO table for the gnark wrap needs this width.
//
// Ground truth is the same plonky3 rev pinned by
// /Users/ember/dev/plonky3-recursion (Plonky3 rev
// 82cfad73cd734d37a0d51953094f970c531817ec); the width-24 permutation is
// default_babybear_poseidon2_24() (baby-bear/src/poseidon2.rs:257).
//
// Structure (poseidon2/src/lib.rs:139 permute_mut):
//
//	mds_light(state)                      // initial external linear layer
//	4 × { +RC_init[r]; x^7; mds_light }   // initial full rounds
//	21 × internal round                   // partial rounds (RP_24 = 21, .rs:56)
//	4 × { +RC_final[r]; x^7; mds_light }  // terminal full rounds
//
// Internal round (monty-31/src/poseidon2.rs:76 permute_state +
// baby-bear/src/poseidon2.rs:403 internal_layer_mat_mul for width 24):
//
//	state[0] += RC; state[0] = state[0]^7
//	sum = Σ state[i]
//	state[i] = V[i]·state[i] + sum        // matrix = AllOnes + Diag(V)
//	V = [-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4,
//	     1/2^8, 1/4, 1/8, 1/16, 1/2^7, 1/2^9, 1/2^27,
//	     -1/2^8, -1/4, -1/8, -1/16, -1/32, -1/64, -1/2^7, -1/2^27]
//
// The RC tables below are the exact BABYBEAR_POSEIDON2_RC_24_* hex tables from
// the Rust source (canonical residues; BabyBear::new_array takes canonical
// integer form — verified: the width-16 file's decimal tables equal those
// hexes). Retained verbatim as hex for byte-for-byte auditability against the
// fork. The diagonal below is the canonical residue of each V entry.
package friverifier

import "github.com/consensys/gnark/frontend"

// BABYBEAR_POSEIDON2_RC_24_EXTERNAL_INITIAL (baby-bear/src/poseidon2.rs:179).
var poseidon2W24RCExternalInitial = [4][24]uint32{
	{0x0fa20c37, 0x0795bb97, 0x12c60b9c, 0x0eabd88e, 0x096485ca, 0x07093527, 0x1b1d4e50, 0x30a01ace, 0x3bd86f5a, 0x69af7c28, 0x3f94775f, 0x731560e8, 0x465a0ecd, 0x574ef807, 0x62fd4870, 0x52ccfe44, 0x14772b14, 0x4dedf371, 0x260acd7c, 0x1f51dc58, 0x75125532, 0x686a4d7b, 0x54bac179, 0x31947706},
	{0x29799d3b, 0x6e01ae90, 0x203a7a64, 0x4f7e25be, 0x72503f77, 0x45bd3b69, 0x769bd6b4, 0x5a867f08, 0x4fdba082, 0x251c4318, 0x28f06201, 0x6788c43a, 0x4c6d6a99, 0x357784a8, 0x2abaf051, 0x770f7de6, 0x1794b784, 0x4796c57a, 0x724b7a10, 0x449989a7, 0x64935cf1, 0x59e14aac, 0x0e620bb8, 0x3af5a33b},
	{0x4465cc0e, 0x019df68f, 0x4af8d068, 0x08784f82, 0x0cefdeae, 0x6337a467, 0x32fa7a16, 0x486f62d6, 0x386a7480, 0x20f17c4a, 0x54e50da8, 0x2012cf03, 0x5fe52950, 0x09afb6cd, 0x2523044e, 0x5c54d0ef, 0x71c01f3c, 0x60b2c4fb, 0x4050b379, 0x5e6a70a5, 0x418543f5, 0x71debe56, 0x1aad2994, 0x3368a483},
	{0x07a86f3a, 0x5ea43ff1, 0x2443780e, 0x4ce444f7, 0x146f9882, 0x3132b089, 0x197ea856, 0x667030c3, 0x2317d5dc, 0x0c2c48a7, 0x56b2df66, 0x67bd81e9, 0x4fcdfb19, 0x4baaef32, 0x0328d30a, 0x6235760d, 0x12432912, 0x0a49e258, 0x030e1b70, 0x48caeb03, 0x49e4d9e9, 0x1051b5c6, 0x6a36dbbe, 0x4cff27a5},
}

// BABYBEAR_POSEIDON2_RC_24_EXTERNAL_FINAL (baby-bear/src/poseidon2.rs:215).
var poseidon2W24RCExternalFinal = [4][24]uint32{
	{0x032959ad, 0x2b18af6a, 0x55d3dc8c, 0x43bd26c8, 0x0c41595f, 0x7048d2e2, 0x00db8983, 0x2af563d7, 0x6e84758f, 0x611d64e1, 0x1f9977e2, 0x64163a0a, 0x5c5fc27b, 0x02e22561, 0x3a2d75db, 0x1ba7b71a, 0x34343f64, 0x7406b35d, 0x19df8299, 0x6ff4480a, 0x514a81c8, 0x57ab52ce, 0x6ad69f52, 0x3e0c0e0d},
	{0x48126114, 0x2a9d62cc, 0x17441f23, 0x485762bb, 0x2f218674, 0x06fdc64a, 0x0861b7f2, 0x3b36eee6, 0x70a11040, 0x04b31737, 0x3722a872, 0x2a351c63, 0x623560dc, 0x62584ab2, 0x382c7c04, 0x3bf9edc7, 0x0e38fe51, 0x376f3b10, 0x5381e178, 0x3afc61c7, 0x5c1bcb4d, 0x6643ce1f, 0x2d0af1c1, 0x08f583cc},
	{0x5d6ff60f, 0x6324c1e5, 0x74412fb7, 0x70c0192e, 0x0b72f141, 0x4067a111, 0x57388c4f, 0x351009ec, 0x0974c159, 0x539a58b3, 0x038c0cff, 0x476c0392, 0x3f7bc15f, 0x4491dd2c, 0x4d1fef55, 0x04936ae3, 0x58214dd4, 0x683c6aad, 0x1b42f16b, 0x6dc79135, 0x2d4e71ec, 0x3e2946ea, 0x59dce8db, 0x6cee892a},
	{0x47f07350, 0x7106ce93, 0x3bd4a7a9, 0x2bfe636a, 0x430011e9, 0x001cd66a, 0x307faf5b, 0x0d9ef3fe, 0x6d40043a, 0x2e8f470c, 0x1b6865e8, 0x0c0e6c01, 0x4d41981f, 0x423b9d3d, 0x410408cc, 0x263f0884, 0x5311bbd0, 0x4dae58d8, 0x30401cea, 0x09afa575, 0x4b3d5b42, 0x63ac0b37, 0x5fe5bb14, 0x5244e9d4},
}

// BABYBEAR_POSEIDON2_RC_24_INTERNAL (baby-bear/src/poseidon2.rs:250) — 21 scalars.
var poseidon2W24RCInternal = [21]uint32{
	0x1da78ec2, 0x730b0924, 0x3eb56cf3, 0x5bd93073, 0x37204c97, 0x51642d89, 0x66e943e8, 0x1a3e72de,
	0x70beb1e9, 0x30ff3b3f, 0x4240d1c4, 0x12647b8d, 0x65d86965, 0x49ef4d7c, 0x47785697, 0x46b3969f,
	0x5c7b7a0e, 0x7078fc60, 0x4f22d482, 0x482a9aee, 0x6beb839d,
}

// Canonical residues of the width-24 internal diagonal V
// (baby-bear/src/poseidon2.rs:405,406-428). Derived from the V spec by modular
// inverse of the powers of two; the values are pinned end-to-end by the fork
// KAT (test_default_babybear_poseidon2_width_24). E.g. 1/2 = (p+1)/2 =
// 1006632961, 1/4 = 1509949441, 1/2^27 = -15 mod p (15·2^27 = p-1) = 15 after
// the -1/2^27 sign flip on lane 23. diag[0] mirrors the w16 layout (stored but
// unused: lane 0 is handled specially with V[0] = -2).
var poseidon2W24Diag = [24]uint32{
	2013265919, 1, 2, 1006632961, 3, 4, 1006632960, 2013265918, 2013265917,
	2005401601, 1509949441, 1761607681, 1887436801, 1997537281, 2009333761, 2013265906,
	7864320, 503316480, 251658240, 125829120, 62914560, 31457280, 15728640, 15,
}

var poseidon2W24Params = func() *poseidon2Params {
	p := &poseidon2Params{width: 24}
	for i := range poseidon2W24RCExternalInitial {
		p.rcExternalInitial = append(p.rcExternalInitial, poseidon2W24RCExternalInitial[i][:])
	}
	for i := range poseidon2W24RCExternalFinal {
		p.rcExternalFinal = append(p.rcExternalFinal, poseidon2W24RCExternalFinal[i][:])
	}
	p.rcInternal = poseidon2W24RCInternal[:]
	p.diag = poseidon2W24Diag[:]
	return p
}()

// Poseidon2W24 applies the width-24 BabyBear Poseidon2 permutation in-place.
// Inputs are asserted canonical (fail-closed at the gadget boundary); outputs
// are canonical. Reuses the width-generic engine (poseidon2Permute) verbatim.
func (bb *BBApi) Poseidon2W24(state *[24]frontend.Variable) {
	for i := range state {
		bb.AssertIsCanonical(state[i])
	}
	bb.poseidon2Permute(state[:], poseidon2W24Params)
}
