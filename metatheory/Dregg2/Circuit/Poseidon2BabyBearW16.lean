/-
# Dregg2.Circuit.Poseidon2BabyBearW16 — the REAL BabyBear Poseidon2-w16 permutation,
in Lean, with the actual round constants, KAT-validated bit-exact against the deployed
hash.

**Why this module exists.** `FriVerifier.lean` models the verifier transcript /
Merkle recompute abstractly over a permutation `perm : List F → List F`; its
cross-implementation fidelity `#guard`s replay p3-challenger's OWN reference vectors
over a `reverse` stand-in permutation (a genuine check of the Challenger LOGIC, but
NOT of the real hash). This module closes that gap for the HASH: it implements the
deployed `Poseidon2BabyBear<16>` permutation — the ONE BabyBear permutation the
recursion uses for ALL MMCS/FRI/sponge hashing
(`default_babybear_poseidon2_16`, `circuit-prove/src/plonky3_recursion_impl.rs:187`)
— concretely in Lean, with the REAL round constants and linear layers, and VALIDATES
it bit-exactly against a known-answer test emitted from the deployed Rust permutation.

**Faithfulness, grounded.** The algorithm mirrors p3 exactly
(`p3-poseidon2-0.6.1/src/{external,generic}.rs`, `p3-baby-bear-0.6.1/src/poseidon2.rs`,
`p3-monty-31-0.6.1/src/poseidon2.rs`):
  * field = BabyBear `p = 2^31 − 2^27 + 1`, worked in CANONICAL `ℕ`-mod-`p` form (the
    stored `0x…` constants ARE the canonical field elements — every value `< p`), so
    no Montgomery bookkeeping is needed: canonical field arithmetic is faithful;
  * S-box `x ↦ x^7`; external linear layer = `mds_light_permutation` over the `MDSMat4`
    circulant (`apply_mat4` then the outer block-sum); internal layer
    `s ↦ (1 + Diag(V))s` with `V = [-2,1,2,½,3,4,-½,-3,-4,2⁻⁸,¼,⅛,2⁻²⁷,-2⁻⁸,-1/16,-2⁻²⁷]`;
  * round structure: initial MDS, then 4 external rounds (`RC_16_EXTERNAL_INITIAL`),
    13 internal rounds (`RC_16_INTERNAL`), 4 external rounds (`RC_16_EXTERNAL_FINAL`).

**The validation (no faking).** The `#guard`s at the bottom replay TWO known-answer
tests emitted from the deployed Rust `default_babybear_poseidon2_16().permute(·)`: the
permutation of `[0,1,…,15]` and of the all-zero state. If this Lean implementation
diverged from the deployed hash by even one limb, the `#guard`s would FAIL the build.
This is a genuine cross-implementation fidelity check on the REAL Poseidon2-w16 — the
Merkle/`compress` calibration the FRI verifier's `merkleRecompute_binds` rests on now
has a concrete, validated referent. Import-free (pure `ℕ` arithmetic), like
`FriVerifier`.
-/

namespace Dregg2.Circuit.Poseidon2BabyBearW16

/-! ## 1. BabyBear canonical field arithmetic (`ℕ`-mod-`p`). -/

/-- The BabyBear prime `p = 2^31 − 2^27 + 1 = 2013265921`. -/
def P : Nat := 2013265921

/-- `2⁻¹ mod p = (p+1)/2`. -/
def inv2 : Nat := 1006632961

def fadd (a b : Nat) : Nat := (a + b) % P
def fsub (a b : Nat) : Nat := (a + P - b % P) % P
def fmul (a b : Nat) : Nat := (a * b) % P
def fhalve (a : Nat) : Nat := fmul a inv2

/-- `a · 2⁻ᵏ mod p` — `div_2exp_u64 k`, as `k` repeated halvings. -/
def fdiv2exp (a : Nat) : Nat → Nat
  | 0 => a % P
  | (k+1) => fhalve (fdiv2exp a k)

/-- The S-box `x ↦ x^7 = (x²)²·x²·x`. -/
def sbox (a : Nat) : Nat :=
  let x2 := fmul a a
  let x4 := fmul x2 x2
  fmul (fmul x4 x2) a

/-! ## 2. The external linear layer — `mds_light_permutation` over `MDSMat4`. -/

/-- Read state element `i` (canonical), `0` past the end. -/
@[inline] def g (s : List Nat) (i : Nat) : Nat := s.getD i 0

/-- `apply_mat4` on a 4-element block (the `MDSMat4` circulant `[[2,3,1,1],…]`),
operation-for-operation as `p3-poseidon2/src/external.rs::apply_mat4`. -/
def mat4 (x0 x1 x2 x3 : Nat) : Nat × Nat × Nat × Nat :=
  let t01 := fadd x0 x1
  let t23 := fadd x2 x3
  let t0123 := fadd t01 t23
  let t01123 := fadd t0123 x1
  let t01233 := fadd t0123 x3
  let y3 := fadd t01233 (fadd x0 x0)   -- 3·x0 + x1 + x2 + 2·x3
  let y1 := fadd t01123 (fadd x2 x2)   -- x0 + 2·x1 + 3·x2 + x3
  let y0 := fadd t01123 t01            -- 2·x0 + 3·x1 + x2 + x3
  let y2 := fadd t01233 t23            -- x0 + x1 + 2·x2 + 3·x3
  (y0, y1, y2, y3)

/-- The width-16 external linear layer: `MDSMat4` on each block of 4, then the outer
circulant `state[i] += Σ_{j≡i mod 4} state[j]`. -/
def mdsLight (s : List Nat) : List Nat :=
  -- post-`mat4` state, as a function of index (4 blocks of 4)
  let blk : Nat → Nat × Nat × Nat × Nat := fun k =>
    mat4 (g s (4*k)) (g s (4*k+1)) (g s (4*k+2)) (g s (4*k+3))
  let m : Nat → Nat := fun i =>
    let (a, b, c, d) := blk (i / 4)
    match i % 4 with | 0 => a | 1 => b | 2 => c | _ => d
  let sums : Nat → Nat := fun k =>
    fadd (fadd (m k) (m (4+k))) (fadd (m (8+k)) (m (12+k)))
  (List.range 16).map (fun i => fadd (m i) (sums (i % 4)))

/-! ## 3. The internal layer — `(1 + Diag(V))` with the BabyBear-w16 shift diagonal. -/

/-- One internal round: add the constant + S-box to `state[0]`, then the diagonal
diffusion `(1 + Diag(V)) s` with `V` the BabyBear-w16 vector. `state[1..15]` use the
ORIGINAL inputs and the full sum; `state[0] = part_sum − state[0]` (the `V₀ = −2`
case). Mirrors `p3-monty-31::generic_internal_linear_layer` +
`p3-baby-bear::internal_layer_mat_mul`. -/
def internalRound (rc : Nat) (s : List Nat) : List Nat :=
  let s0 := sbox (fadd (g s 0) rc)
  let partSum := (List.range 15).foldl (fun acc j => fadd acc (g s (j+1))) 0
  let fullSum := fadd partSum s0
  let n0  := fsub partSum s0                              -- V₀ = −2
  let n1  := fadd (g s 1) fullSum                         -- +1
  let n2  := fadd (fadd (g s 2) (g s 2)) fullSum          -- +2
  let n3  := fadd (fhalve (g s 3)) fullSum                -- +½
  let n4  := fadd fullSum (fmul 3 (g s 4))                -- +3
  let n5  := fadd fullSum (fmul 4 (g s 5))                -- +4
  let n6  := fsub fullSum (fhalve (g s 6))                -- −½
  let n7  := fsub fullSum (fmul 3 (g s 7))                -- −3
  let n8  := fsub fullSum (fmul 4 (g s 8))                -- −4
  let n9  := fadd (fdiv2exp (g s 9) 8) fullSum            -- +2⁻⁸
  let n10 := fadd (fdiv2exp (g s 10) 2) fullSum           -- +¼
  let n11 := fadd (fdiv2exp (g s 11) 3) fullSum           -- +⅛
  let n12 := fadd (fdiv2exp (g s 12) 27) fullSum          -- +2⁻²⁷
  let n13 := fsub fullSum (fdiv2exp (g s 13) 8)           -- −2⁻⁸
  let n14 := fsub fullSum (fdiv2exp (g s 14) 4)           -- −1/16
  let n15 := fsub fullSum (fdiv2exp (g s 15) 27)          -- −2⁻²⁷
  [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15]

/-- One external round: `(state[i] + rc[i])^7` elementwise, then the external layer. -/
def externalRound (rc : List Nat) (s : List Nat) : List Nat :=
  mdsLight ((List.range 16).map (fun i => sbox (fadd (g s i) (g rc i))))

/-! ## 4. The round constants (the REAL BabyBear-w16 values, `p3-baby-bear/poseidon2.rs`). -/

/-- `BABYBEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL` (4 rounds × 16). -/
def rcExtInitial : List (List Nat) :=
  [[0x69cbb6af, 0x46ad93f9, 0x60a00f4e, 0x6b1297cd, 0x23189afe, 0x732e7bef, 0x72c246de,
    0x2c941900, 0x0557eede, 0x1580496f, 0x3a3ea77b, 0x54f3f271, 0x0f49b029, 0x47872fe1,
    0x221e2e36, 0x1ab7202e],
   [0x487779a6, 0x3851c9d8, 0x38dc17c0, 0x209f8849, 0x268dcee8, 0x350c48da, 0x5b9ad32e,
    0x0523272b, 0x3f89055b, 0x01e894b2, 0x13ddedde, 0x1b2ef334, 0x7507d8b4, 0x6ceeb94e,
    0x52eb6ba2, 0x50642905],
   [0x05453f3f, 0x06349efc, 0x6922787c, 0x04bfff9c, 0x768c714a, 0x3e9ff21a, 0x15737c9c,
    0x2229c807, 0x0d47f88c, 0x097e0ecc, 0x27eadba0, 0x2d7d29e4, 0x3502aaa0, 0x0f475fd7,
    0x29fbda49, 0x018afffd],
   [0x0315b618, 0x6d4497d1, 0x1b171d9e, 0x52861abd, 0x2e5d0501, 0x3ec8646c, 0x6e5f250a,
    0x148ae8e6, 0x17f5fa4a, 0x3e66d284, 0x0051aa3b, 0x483f7913, 0x2cfe5f15, 0x023427ca,
    0x2cc78315, 0x1e36ea47]]

/-- `BABYBEAR_POSEIDON2_RC_16_EXTERNAL_FINAL` (4 rounds × 16). -/
def rcExtFinal : List (List Nat) :=
  [[0x7290a80d, 0x6f7e5329, 0x598ec8a8, 0x76a859a0, 0x6559e868, 0x657b83af, 0x13271d3f,
    0x1f876063, 0x0aeeae37, 0x706e9ca6, 0x46400cee, 0x72a05c26, 0x2c589c9e, 0x20bd37a7,
    0x6a2d3d10, 0x20523767],
   [0x5b8fe9c4, 0x2aa501d6, 0x1e01ac3e, 0x1448bc54, 0x5ce5ad1c, 0x4918a14d, 0x2c46a83f,
    0x4fcf6876, 0x61d8d5c8, 0x6ddf4ff9, 0x11fda4d3, 0x02933a8f, 0x170eaf81, 0x5a9c314f,
    0x49a12590, 0x35ec52a1],
   [0x58eb1611, 0x5e481e65, 0x367125c9, 0x0eba33ba, 0x1fc28ded, 0x066399ad, 0x0cbec0ea,
    0x75fd1af0, 0x50f5bf4e, 0x643d5f41, 0x6f4fe718, 0x5b3cbbde, 0x1e3afb3e, 0x296fb027,
    0x45e1547b, 0x4a8db2ab],
   [0x59986d19, 0x30bcdfa3, 0x1db63932, 0x1d7c2824, 0x53b33681, 0x0673b747, 0x038a98a3,
    0x2c5bce60, 0x351979cd, 0x5008fb73, 0x547bca78, 0x711af481, 0x3f93bf64, 0x644d987b,
    0x3c8bcd87, 0x608758b8]]

/-- `BABYBEAR_POSEIDON2_RC_16_INTERNAL` (13 scalar constants). -/
def rcInternal : List Nat :=
  [0x5a8053c0, 0x693be639, 0x3858867d, 0x19334f6b, 0x128f0fd8, 0x4e2b1ccb, 0x61210ce0,
   0x3c318939, 0x0b5b2f22, 0x2edb11d5, 0x213effdf, 0x0cac4606, 0x241af16d]

/-! ## 5. The full permutation. -/

/-- **`perm` — the deployed BabyBear Poseidon2-w16 permutation.** Initial external
linear layer, 4 external-initial rounds, 13 internal rounds, 4 external-final rounds.
Input/output are 16-element canonical-`ℕ` state lists. -/
def perm (input : List Nat) : List Nat :=
  let s := mdsLight input
  let s := rcExtInitial.foldl (fun st rc => externalRound rc st) s
  let s := rcInternal.foldl (fun st rc => internalRound rc st) s
  let s := rcExtFinal.foldl (fun st rc => externalRound rc st) s
  s

/-- **`compress` — the deployed `TruncatedPermutation<·, 2, 8, 16>`**: hash two
8-element leaves by permuting their concatenation and truncating to the first 8 lanes.
The Merkle-tree compression `merkleRecompute_binds` rests on. -/
def compress (a b : List Nat) : List Nat := (perm (a ++ b)).take 8

/-! ## 6. KAT validation (bit-exact against the deployed Rust permutation).

Emitted from `default_babybear_poseidon2_16().permute(·)` (the deployed hash). A single
diverging limb fails the build. -/

/- `permute([0,1,…,15])`, canonical, from the deployed Rust permutation. -/
#guard perm (List.range 16) =
  [1906786279, 1737026427, 1959749225, 700325316, 1638050605, 1021608788, 1726691001,
   1761127344, 1552405120, 417318995, 36799261, 1215172152, 614923223, 1300746575,
   957311597, 304856115]

/- `permute([0,0,…,0])`, canonical, from the deployed Rust permutation. -/
#guard perm (List.replicate 16 0) =
  [1168947398, 128782440, 747404447, 883925857, 360581875, 1704698758, 1878363991,
   1054281681, 682225194, 705839125, 1218819873, 41544645, 1095344608, 174996601,
   1678438226, 11259290]

/- `compress([0..7],[8..15])` is the first 8 lanes of `permute([0..15])` — the Merkle
leaf-compression of two adjacent leaves, bit-exact. -/
#guard compress (List.range 8) ((List.range 8).map (· + 8)) =
  [1906786279, 1737026427, 1959749225, 700325316, 1638050605, 1021608788, 1726691001,
   1761127344]

/- Field-arithmetic sanity: `2⁻¹` is a genuine inverse, and the S-box is `x^7`. -/
#guard fmul 2 inv2 = 1
#guard sbox 2 = 128
#guard fdiv2exp 256 8 = 1

end Dregg2.Circuit.Poseidon2BabyBearW16
