//! Poseidon2 over BabyBear — the VERBATIM permutation + compression of
//! `circuit/src/poseidon2.rs` (Plonky3-conformant: width 16, S-box x^7, R_F=8,
//! R_P=13, the BABYBEAR_POSEIDON2 round constants + internal diagonal). The ONLY
//! change for `no_std` is the round-constant table: the host crate caches it in a
//! `std::sync::LazyLock`; here it is built eagerly from the same `const` u32
//! tables (a handful of `BabyBear::new`s — no lock, no `std`). The permutation,
//! the S-box, both linear layers, and the `hash_2_to_1` / `hash_bytes` domain
//! separation are byte-for-byte identical, so the known-answer vectors
//! (`hash_4_to_1([1,2,3,4]) == 1163579196`, the width-16 permutation KAT, and the
//! Plonky3 cross-check) all still hold for digests produced here.

#![allow(dead_code)]

use crate::field::BabyBear;

pub const WIDTH: usize = 16;
pub const EXTERNAL_ROUNDS: usize = 8;
pub const INTERNAL_ROUNDS: usize = 13;
pub const TOTAL_ROUNDS: usize = EXTERNAL_ROUNDS + INTERNAL_ROUNDS;
const SBOX_ALPHA: u32 = 7;

const RC_EXT_INIT: [[u32; 16]; 4] = [
    [
        0x69cbb6af, 0x46ad93f9, 0x60a00f4e, 0x6b1297cd, 0x23189afe, 0x732e7bef, 0x72c246de,
        0x2c941900, 0x0557eede, 0x1580496f, 0x3a3ea77b, 0x54f3f271, 0x0f49b029, 0x47872fe1,
        0x221e2e36, 0x1ab7202e,
    ],
    [
        0x487779a6, 0x3851c9d8, 0x38dc17c0, 0x209f8849, 0x268dcee8, 0x350c48da, 0x5b9ad32e,
        0x0523272b, 0x3f89055b, 0x01e894b2, 0x13ddedde, 0x1b2ef334, 0x7507d8b4, 0x6ceeb94e,
        0x52eb6ba2, 0x50642905,
    ],
    [
        0x05453f3f, 0x06349efc, 0x6922787c, 0x04bfff9c, 0x768c714a, 0x3e9ff21a, 0x15737c9c,
        0x2229c807, 0x0d47f88c, 0x097e0ecc, 0x27eadba0, 0x2d7d29e4, 0x3502aaa0, 0x0f475fd7,
        0x29fbda49, 0x018afffd,
    ],
    [
        0x0315b618, 0x6d4497d1, 0x1b171d9e, 0x52861abd, 0x2e5d0501, 0x3ec8646c, 0x6e5f250a,
        0x148ae8e6, 0x17f5fa4a, 0x3e66d284, 0x0051aa3b, 0x483f7913, 0x2cfe5f15, 0x023427ca,
        0x2cc78315, 0x1e36ea47,
    ],
];

const RC_EXT_FINAL: [[u32; 16]; 4] = [
    [
        0x7290a80d, 0x6f7e5329, 0x598ec8a8, 0x76a859a0, 0x6559e868, 0x657b83af, 0x13271d3f,
        0x1f876063, 0x0aeeae37, 0x706e9ca6, 0x46400cee, 0x72a05c26, 0x2c589c9e, 0x20bd37a7,
        0x6a2d3d10, 0x20523767,
    ],
    [
        0x5b8fe9c4, 0x2aa501d6, 0x1e01ac3e, 0x1448bc54, 0x5ce5ad1c, 0x4918a14d, 0x2c46a83f,
        0x4fcf6876, 0x61d8d5c8, 0x6ddf4ff9, 0x11fda4d3, 0x02933a8f, 0x170eaf81, 0x5a9c314f,
        0x49a12590, 0x35ec52a1,
    ],
    [
        0x58eb1611, 0x5e481e65, 0x367125c9, 0x0eba33ba, 0x1fc28ded, 0x066399ad, 0x0cbec0ea,
        0x75fd1af0, 0x50f5bf4e, 0x643d5f41, 0x6f4fe718, 0x5b3cbbde, 0x1e3afb3e, 0x296fb027,
        0x45e1547b, 0x4a8db2ab,
    ],
    [
        0x59986d19, 0x30bcdfa3, 0x1db63932, 0x1d7c2824, 0x53b33681, 0x0673b747, 0x038a98a3,
        0x2c5bce60, 0x351979cd, 0x5008fb73, 0x547bca78, 0x711af481, 0x3f93bf64, 0x644d987b,
        0x3c8bcd87, 0x608758b8,
    ],
];

const RC_INTERNAL: [u32; 13] = [
    0x5a8053c0, 0x693be639, 0x3858867d, 0x19334f6b, 0x128f0fd8, 0x4e2b1ccb, 0x61210ce0, 0x3c318939,
    0x0b5b2f22, 0x2edb11d5, 0x213effdf, 0x0cac4606, 0x241af16d,
];

/// Internal diagonal d_i = 1 + V[i] (the BabyBear-optimized vector).
static INTERNAL_DIAG: [BabyBear; WIDTH] = [
    BabyBear(2013265920),
    BabyBear(2),
    BabyBear(3),
    BabyBear(1006632962),
    BabyBear(4),
    BabyBear(5),
    BabyBear(1006632961),
    BabyBear(2013265919),
    BabyBear(2013265918),
    BabyBear(2005401602),
    BabyBear(1509949442),
    BabyBear(1761607682),
    BabyBear(2013265907),
    BabyBear(7864321),
    BabyBear(125829121),
    BabyBear(16),
];

/// Build the per-round constant table eagerly (no `LazyLock`): full-width vectors
/// for the external rounds, first-element-only for the internal rounds — exactly
/// `compute_round_constants()` in the host crate.
fn round_constants() -> [[BabyBear; WIDTH]; TOTAL_ROUNDS] {
    let mut constants = [[BabyBear::ZERO; WIDTH]; TOTAL_ROUNDS];
    let mut idx = 0;
    for round in 0..EXTERNAL_ROUNDS / 2 {
        for j in 0..WIDTH {
            constants[idx][j] = BabyBear::new(RC_EXT_INIT[round][j]);
        }
        idx += 1;
    }
    for round in 0..INTERNAL_ROUNDS {
        constants[idx][0] = BabyBear::new(RC_INTERNAL[round]);
        idx += 1;
    }
    for round in 0..EXTERNAL_ROUNDS / 2 {
        for j in 0..WIDTH {
            constants[idx][j] = BabyBear::new(RC_EXT_FINAL[round][j]);
        }
        idx += 1;
    }
    constants
}

#[derive(Clone)]
pub struct Poseidon2State {
    pub state: [BabyBear; WIDTH],
}

impl Poseidon2State {
    pub fn new() -> Self {
        Self {
            state: [BabyBear::ZERO; WIDTH],
        }
    }

    #[inline]
    pub fn sbox(x: BabyBear) -> BabyBear {
        x.pow(SBOX_ALPHA)
    }

    /// External linear layer: MDSMat4 [2,3,1,1] blockwise + column sums.
    pub fn external_linear_layer(&mut self) {
        for cs in (0..WIDTH).step_by(4) {
            let (x0, x1, x2, x3) = (
                self.state[cs],
                self.state[cs + 1],
                self.state[cs + 2],
                self.state[cs + 3],
            );
            let t01 = x0 + x1;
            let t23 = x2 + x3;
            let t0123 = t01 + t23;
            let t01123 = t0123 + x1;
            let t01233 = t0123 + x3;
            self.state[cs] = t01123 + t01;
            self.state[cs + 1] = t01123 + x2 + x2;
            self.state[cs + 2] = t01233 + t23;
            self.state[cs + 3] = t01233 + x0 + x0;
        }
        let mut sums = [BabyBear::ZERO; 4];
        for k in 0..4 {
            for j in (0..WIDTH).step_by(4) {
                sums[k] = sums[k] + self.state[j + k];
            }
        }
        for i in 0..WIDTH {
            self.state[i] = self.state[i] + sums[i % 4];
        }
    }

    /// Internal linear layer: (1 + Diag(V)) * x.
    pub fn internal_linear_layer(&mut self) {
        let diag = &INTERNAL_DIAG;
        let sum: BabyBear = self
            .state
            .iter()
            .copied()
            .fold(BabyBear::ZERO, |a, b| a + b);
        for i in 0..WIDTH {
            self.state[i] = sum + (diag[i] - BabyBear::ONE) * self.state[i];
        }
    }

    /// The full Poseidon2 permutation (initial linear layer, 4 external, 13
    /// internal, 4 external) — identical control flow to the host crate.
    pub fn permute(&mut self) {
        let rc = round_constants();

        self.external_linear_layer();

        for round in 0..EXTERNAL_ROUNDS / 2 {
            for i in 0..WIDTH {
                self.state[i] += rc[round][i];
            }
            for i in 0..WIDTH {
                self.state[i] = Self::sbox(self.state[i]);
            }
            self.external_linear_layer();
        }

        for round in 0..INTERNAL_ROUNDS {
            let rc_idx = EXTERNAL_ROUNDS / 2 + round;
            self.state[0] += rc[rc_idx][0];
            self.state[0] = Self::sbox(self.state[0]);
            self.internal_linear_layer();
        }

        for round in 0..EXTERNAL_ROUNDS / 2 {
            let rc_idx = EXTERNAL_ROUNDS / 2 + INTERNAL_ROUNDS + round;
            for i in 0..WIDTH {
                self.state[i] += rc[rc_idx][i];
            }
            for i in 0..WIDTH {
                self.state[i] = Self::sbox(self.state[i]);
            }
            self.external_linear_layer();
        }
    }
}

/// Poseidon2 2-to-1 compression — the in-circuit Merkle NODE hash. This is the
/// `dregg_poseidon2_hash` portal's documented binding ("Poseidon2 4-to-1
/// compression `hash_2_to_1`, the in-circuit Merkle node hash"). Byte-for-byte
/// `circuit/src/poseidon2.rs::hash_2_to_1`.
pub fn hash_2_to_1(left: BabyBear, right: BabyBear) -> BabyBear {
    let mut state = Poseidon2State::new();
    state.state[0] = left;
    state.state[1] = right;
    state.state[4] = BabyBear::new(2); // arity tag (capacity domain separation)
    state.permute();
    state.state[0]
}

/// Poseidon2 4-to-1 compression (the 4-ary Merkle internal node). Verbatim.
pub fn hash_4_to_1(inputs: &[BabyBear; 4]) -> BabyBear {
    let mut state = Poseidon2State::new();
    state.state[0] = inputs[0];
    state.state[1] = inputs[1];
    state.state[2] = inputs[2];
    state.state[3] = inputs[3];
    state.state[4] = BabyBear::new(4); // arity tag
    state.permute();
    state.state[0]
}

/// Sponge over an arbitrary number of field elements (rate 4, capacity 12).
/// Verbatim `hash_many`.
pub fn hash_many(inputs: &[BabyBear]) -> BabyBear {
    let rate = 4;
    let mut state = Poseidon2State::new();
    state.state[4] = BabyBear::new(inputs.len() as u32);
    for chunk in inputs.chunks(rate) {
        for (i, &elem) in chunk.iter().enumerate() {
            state.state[i] += elem;
        }
        state.permute();
    }
    state.state[0]
}

/// Hash arbitrary bytes into a single BabyBear via Poseidon2 (the injective
/// `bytes_to_lanes` preimage, then the sponge). Verbatim `hash_bytes` — the bridge
/// from byte data (e.g. a BLAKE3 commitment) into the field domain.
///
/// ⚠ The SQUEEZE is still one felt (`2^15.45` birthday); only the preimage's two `O(1)`
/// collisions were closed on 2026-08-01. See the workspace twin's doc for the split.
pub fn hash_bytes(data: &[u8]) -> BabyBear {
    let elements = BabyBear::bytes_to_lanes(data);
    hash_many(&elements)
}
