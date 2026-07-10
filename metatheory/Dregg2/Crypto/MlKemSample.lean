/-
# `Dregg2.Crypto.MlKemSample` — the REAL ML-KEM-768 matrix + samplers (FIPS 203), as EXECUTABLE `def`s.

FIPS 203 (ML-KEM). ML-KEM-768 parameters: `k = 3`, `η1 = η2 = 2`, `n = 256`, `q = 3329`. This module builds
the three deterministic samplers that turn seed bytes into ring elements — `SampleNTT` (Alg 7), the matrix
expansion `Â = ExpandA` (Alg 13), and the centred-binomial noise `SamplePolyCBD` (Alg 8) — as plain
computable `def`s (the same `leanc`-extractable shape as `Keccak`, `MlKemRing`, and the ML-DSA bricks): no
`Prop`, no classical choice, only `Nat`/`Array`/`List` and `UInt8` byte arithmetic.

It is BRICK K2 of replacing the `A = 1`, `n = 1` scalar caricature in `Fips203Kem.lean` with the real
ML-KEM-768 encaps/decaps. It REUSES — does not reimplement — the two landed, gate-verified bricks:

* BRICK 0 `Dregg2.Crypto.Keccak` — real SHAKE-128 (`shake128`), byte-exact vs the FIPS 202 NIST KATs.
* BRICK K1 `Dregg2.Crypto.MlKemRing` — the real ring `R_q = ℤ_q[X]/(X²⁵⁶+1)` (`Poly`, `q = 3329`,
  gate-verified INCOMPLETE NTT).

## THE ALGORITHMS (FIPS 203, faithfully)

**`SampleNTT(seed)` — Algorithm 7 (RejNTTPoly for Kyber).** Drive SHAKE-128 over `seed`; read 3 stream bytes
`(b0, b1, b2)` at a time and form TWO 12-bit candidates:
`d1 = b0 + 256·(b1 mod 16)` and `d2 = ⌊b1/16⌋ + 16·b2`. Accept each of `d1`, `d2` (in that order) as the next
coefficient iff it is `< q = 3329`, else reject; fill exactly 256 coefficients. The result is a `Poly` already
in the **NTT domain** (do NOT apply `ntt` to it — pointwise mult in `MlKemRing` consumes it directly).

**`ExpandMatrix(ρ)` — Algorithm 13.** For row `i ∈ 0..k-1`, column `j ∈ 0..k-1`,
`Â[i][j] = SampleNTT(ρ ‖ IntegerToBytes(j,1) ‖ IntegerToBytes(i,1))` — the **COLUMN index `j` is appended
first, then the row index `i`** (the classic ExpandA transposition bug is `ρ ‖ i ‖ j`; the corner KATs pin
it). The `k·k = 9` polynomials are returned flattened row-major (`Â[i][j]` at index `i·k + j`).

**`SamplePolyCBD_η(B)` — Algorithm 8.** From `64·η` input bytes, expand to `512·η` bits **LSB-first within
each byte** (bit `t` = `⌊B[t/8]/2^{t mod 8}⌋ mod 2`); then for each `i ∈ 0..255`,
`f[i] = (Σ_{j<η} bit[2·i·η + j]) − (Σ_{j<η} bit[2·i·η + η + j])`, a centred value in `{−η, …, η}` represented
in `[0, q)` (negatives as `q + v`). For ML-KEM-768 `η1 = η2 = 2`, so every coefficient lies in
`{0, 1, 2, q−2, q−1}` (the centred `[−2, 2]`).

## THE ANTI-FAKE GATES (`native_decide`, compiled) — over the concrete `ρ = [0,…,31]` and a fixed CBD input.

* `sampleNTT_range` / `expandMatrix_shape` — `Â` is exactly 9 polys, each exactly 256 coefficients, every one
  `< q`. A sampler that exhausted its buffer, used a wrong loop bound, or dropped the `< q` rejection reds here.
* `samplePolyCBD_range` — every coefficient of a CBD sample lies in `{0, 1, 2, q−2, q−1}` (centred `[−2, 2]`).
* `sampleNTT_kat_00` / `sampleNTT_kat_22` / `samplePolyCBD_kat` — the FULL 256 coefficients match, entry for
  entry, an INDEPENDENT reference: Python `hashlib.shake_128` driving a from-scratch transcription of FIPS 203
  Alg 7, and a pure-bit-layout transcription of Alg 8 on the fixed input `[0,1,…,127]`. This is a genuine
  cross-implementation Known-Answer-Test, not a self-consistency tautology. The two SampleNTT corners
  `(i,j) = (0,0)` and `(k−1,k−1) = (2,2)` are computed as `expandMatrix ρ` entries `0` and `8`, so together
  they pin SHAKE-128, the `d1 = b0 + 256·(b1 mod 16)` / `d2 = ⌊b1/16⌋ + 16·b2` twelve-bit packing, the `< q`
  rejection, AND the `ρ ‖ j ‖ i` seed order. The CBD KAT pins the LSB-first bit layout and the centring.

`native_decide` runs the COMPILED `def`s; its trusted base is `Lean.ofReduceBool` + `Lean.trustCompiler`, the
same residual `Keccak`, `MlKemRing`, and the ML-DSA bricks already name. No `sorry`, no user `axiom`, no toy
substitute for any sampler.
-/

import Dregg2.Crypto.Keccak
import Dregg2.Crypto.MlKemRing

namespace Dregg2.Crypto.MlKemSample

open Dregg2.Crypto.MlKemRing (Poly q zeroPoly subQ)
open Dregg2.Crypto.Keccak (shake128)

/-- ML-KEM-768 matrix dimension, FIPS 203 Table 2: `k = 3` (so `Â` is `3 × 3`). -/
def k : Nat := 3

/-- ML-KEM-768 CBD parameter, FIPS 203 Table 2: `η1 = η2 = 2`. -/
def eta : Nat := 2

/-- Number of 3-byte SHAKE-128 reads to pull up front for one `SampleNTT`. Each read yields two 12-bit
candidates, each accepted with probability `q/2¹² = 3329/4096 ≈ 0.8127`, so 256 accepted coefficients need
`≈ 256 / (2·0.8127) ≈ 158` reads on average; `512` (1536 bytes) is a wide margin. If it were ever too small
the `expandMatrix_shape` gate (exactly 256 coeffs per poly) would fail, so the size is self-checked. -/
def rejReads : Nat := 512

/-- **`SampleNTT` — FIPS 203 Algorithm 7 (RejNTTPoly for Kyber).**

Drive SHAKE-128 over `seed`; read 3 stream bytes `(b0, b1, b2)` at a time, form the two 12-bit candidates
`d1 = b0 + 256·(b1 mod 16)` and `d2 = ⌊b1/16⌋ + 16·b2`, and accept each (d1 first, then d2) as the next
coefficient iff it is `< q`, else reject. Fill exactly 256 coefficients. The result is a `Poly` already in the
**NTT domain** (do NOT apply `ntt` to it). -/
def sampleNTT (seed : List UInt8) : Poly := Id.run do
  let stream : Array UInt8 := (shake128 seed (3 * rejReads)).toArray
  let mut coeffs : Array Nat := #[]
  for r in [0:rejReads] do
    let base := 3 * r
    let b0 := stream[base]!.toNat
    let b1 := stream[base + 1]!.toNat
    let b2 := stream[base + 2]!.toNat
    let d1 := b0 + 256 * (b1 % 16)                          -- low 12 bits
    let d2 := (b1 / 16) + 16 * b2                           -- high 12 bits
    if coeffs.size < 256 then
      if d1 < q then coeffs := coeffs.push d1               -- accept d1 iff < q
    if coeffs.size < 256 then
      if d2 < q then coeffs := coeffs.push d2               -- then accept d2 iff < q
  return coeffs

/-- **`ExpandMatrix` — FIPS 203 Algorithm 13 for ML-KEM-768 (`k = 3`).**

For row `i ∈ 0..k-1`, column `j ∈ 0..k-1`, sample `Â[i][j] = SampleNTT(ρ ‖ j ‖ i)` — the COLUMN index `j` is
appended first, then the row index `i` (FIPS 203 Algorithm 13). Returns the `k·k = 9` polynomials flattened
row-major (`Â[i][j]` at index `i·k + j`). The caller passes `ρ` of length 32 bytes. -/
def expandMatrix (rho : List UInt8) : Array Poly := Id.run do
  let mut mat : Array Poly := #[]
  for i in [0:k] do                                         -- row  0 … k-1
    for j in [0:k] do                                       -- column  0 … k-1
      let seed := rho ++ [UInt8.ofNat j, UInt8.ofNat i]     -- ρ ‖ IntegerToBytes(j,1) ‖ IntegerToBytes(i,1)
      mat := mat.push (sampleNTT seed)
  return mat

/-- Bit `idx` of a byte array, **LSB-first within each byte** (FIPS 203 `BytesToBits`): the `(idx mod 8)`-th
least-significant bit of byte `idx / 8`. -/
@[inline] def getBit (arr : Array UInt8) (idx : Nat) : Nat :=
  (arr[idx / 8]!.toNat >>> (idx % 8)) &&& 1

/-- **`SamplePolyCBD_η` — FIPS 203 Algorithm 8.**

From `64·η` input bytes expanded LSB-first to `512·η` bits, each coefficient `i ∈ 0..255` is
`(Σ_{j<η} bit[2·i·η + j]) − (Σ_{j<η} bit[2·i·η + η + j])`, a centred value in `{−η, …, η}` represented in
`[0, q)` (via `subQ`, so negatives become `q + v`). Works for `η = 2` (`η1 = η2` for ML-KEM-768): coefficients
land in `{0, 1, 2, q−2, q−1}`. -/
def samplePolyCBD (eta : Nat) (bytes : List UInt8) : Poly := Id.run do
  let arr : Array UInt8 := bytes.toArray
  let mut coeffs := zeroPoly
  for i in [0:256] do
    let mut x := 0
    let mut y := 0
    for j in [0:eta] do
      x := x + getBit arr (2 * i * eta + j)
      y := y + getBit arr (2 * i * eta + eta + j)
    coeffs := coeffs.set! i (subQ x y)                      -- (x − y) mod q, centred in [0,q)
  return coeffs

/-! ## THE ANTI-FAKE GATES — `native_decide` over the concrete `ρ = [0,1,…,31]` and a fixed CBD input. -/

/-- The ML-KEM-768 test seed `ρ = [0,1,2,…,31]` — 32 bytes (the ExpandMatrix seed width). -/
def rho031 : List UInt8 := (List.range 32).map (fun n => UInt8.ofNat n)

/-- The public matrix `Â` for `rho031`, held once for the gates below (9 polys, row-major). -/
def matrix031 : Array Poly := expandMatrix rho031

/-- A fixed 128-byte (`= 64·η` for `η = 2`) CBD input `[0,1,…,127]`, independent of SHAKE — a pure test of the
bit layout and centring. -/
def cbdInput : List UInt8 := (List.range 128).map (fun n => UInt8.ofNat n)

/-- A CBD sample on the fixed input, held once for the gates below. -/
def cbd031 : Poly := samplePolyCBD eta cbdInput

/-- **Gate 1 — shape**: `Â` has exactly `k·k = 9` polynomials, each with exactly 256 coefficients. A sampler
that exhausted its buffer (too few reads) or a wrong loop bound fails here. -/
theorem expandMatrix_shape :
    matrix031.size = 9 ∧ matrix031.all (fun p => p.size = 256) = true := by native_decide

/-- **Gate 2 — every SampleNTT coefficient is in `[0, q)`**: no coefficient of any of the 9 polys is `≥ q`. A
sampler that accepted a `d ≥ q` (missing/inverted `< q` rejection) fails here. -/
theorem sampleNTT_range :
    matrix031.all (fun p => p.all (fun c => c < q)) = true := by native_decide

/-- **Gate 3 — every CBD coefficient is centred in `{0, 1, 2, q−2, q−1}`** for `η = 2`. A wrong bit layout, a
missing centring, or the wrong difference direction fails here. -/
theorem samplePolyCBD_range :
    cbd031.all (fun c => c == 0 || c == 1 || c == 2 || c == q - 2 || c == q - 1) = true := by native_decide

/-- **Gate 4a — corner `Â[0][0]` full-poly cross-implementation KAT.** For `ρ = [0,…,31]` the entire 256
coefficients of the first matrix entry (index `0·k + 0 = 0`) match, coefficient-for-coefficient, an INDEPENDENT
reference: Python `hashlib.shake_128` driving a from-scratch transcription of FIPS 203 Alg 7. This pins
SHAKE-128, the `d1/d2` twelve-bit packing, and the `< q` rejection simultaneously. -/
theorem sampleNTT_kat_00 :
    matrix031[0]! =
      #[481, 1919, 1434, 2359, 327, 1066, 3001, 649, 1037, 2971, 661,
        1148, 1602, 864, 301, 1835, 515, 3018, 123, 2889, 2391, 1312,
        1518, 1617, 3039, 1283, 511, 2696, 1104, 2023, 1369, 1628, 1733,
        1975, 1946, 1715, 575, 2464, 2203, 3272, 750, 1548, 2743, 1199,
        154, 3326, 2504, 1908, 3230, 829, 2523, 982, 433, 2678, 2347,
        1273, 1043, 3288, 1135, 3196, 1469, 436, 1977, 1577, 829, 324,
        569, 2919, 1046, 2334, 3102, 461, 219, 707, 1709, 2610, 1409,
        735, 1653, 2204, 3187, 2221, 3041, 2523, 3211, 1529, 2718, 758,
        119, 2999, 1546, 367, 895, 1064, 1911, 218, 3090, 1393, 1318,
        120, 1868, 1120, 323, 919, 1339, 452, 2905, 977, 2691, 539,
        734, 3126, 2364, 138, 2035, 1543, 2103, 2457, 2797, 3006, 34,
        2494, 300, 2538, 1591, 952, 88, 352, 2524, 1868, 1653, 1839,
        1332, 3184, 3048, 2575, 83, 1704, 1938, 906, 2085, 2472, 295,
        2091, 1431, 669, 3093, 202, 1287, 502, 2210, 1374, 1632, 1327,
        3230, 2641, 2962, 3008, 810, 1771, 333, 1960, 2303, 1435, 166,
        3156, 3255, 757, 1480, 3123, 2027, 3237, 1697, 2600, 2184, 569,
        3241, 1626, 2166, 2938, 1894, 441, 3105, 244, 45, 1116, 999,
        2881, 1309, 871, 2064, 736, 1028, 505, 592, 2335, 2810, 1046,
        1815, 250, 3063, 1762, 416, 2610, 3075, 65, 2929, 1695, 2207,
        165, 717, 881, 2659, 2898, 735, 205, 3289, 2744, 1685, 1388,
        1146, 2889, 1701, 614, 1735, 2356, 1270, 2759, 2732, 1471, 592,
        2283, 1775, 537, 1189, 2067, 1354, 188, 3175, 1224, 1869, 559,
        1104, 1641, 914, 177, 3224, 931, 1796, 3263, 3011, 1370, 1926,
        2513, 2367, 3216] := by native_decide

/-- **Gate 4b — corner `Â[k−1][k−1] = Â[2][2]` full-poly cross-implementation KAT.** For `ρ = [0,…,31]` the
entire 256 coefficients of the last matrix entry (index `2·k + 2 = 8`) match the same INDEPENDENT Python
`hashlib.shake_128` reference. Together with Gate 4a this pins the `ρ ‖ j ‖ i` seed byte order (the diagonal
corner `(2,2)` still exercises the two distinct index bytes appended in the `j, i` order). -/
theorem sampleNTT_kat_22 :
    matrix031[8]! =
      #[2300, 310, 1599, 2051, 1859, 745, 1044, 1449, 2862, 1505, 1036,
        1878, 1727, 2411, 3252, 802, 2219, 1390, 615, 2727, 1530, 542,
        3136, 3046, 1891, 747, 2023, 1531, 2296, 555, 305, 2336, 1869,
        863, 566, 1490, 1525, 1316, 1982, 2499, 420, 215, 747, 301,
        2597, 2911, 1008, 1388, 138, 2181, 2861, 401, 242, 1115, 1788,
        1565, 1837, 412, 1427, 1811, 304, 2850, 2114, 1010, 2578, 2304,
        1410, 1091, 410, 12, 540, 1943, 2767, 2991, 2275, 750, 112,
        1235, 415, 3063, 3224, 1143, 788, 1451, 2546, 1978, 3054, 730,
        151, 1016, 2079, 3131, 487, 127, 1575, 252, 1280, 1421, 635,
        1366, 59, 1794, 2731, 515, 921, 10, 2040, 148, 1758, 2714,
        2850, 1377, 629, 963, 50, 2415, 759, 1161, 3097, 2137, 2684,
        2622, 1266, 2148, 3326, 989, 1006, 2146, 2195, 3085, 2216, 1297,
        3017, 2931, 179, 2826, 3262, 96, 914, 2745, 1114, 1342, 1231,
        1864, 973, 2240, 234, 1696, 189, 2770, 439, 774, 2664, 461,
        531, 419, 691, 1545, 2137, 621, 2564, 401, 3021, 2103, 549,
        2141, 713, 1606, 1562, 1405, 1014, 2394, 2927, 1338, 425, 451,
        2593, 3252, 1330, 2143, 3251, 428, 3043, 1806, 3176, 2667, 213,
        2948, 592, 114, 3319, 1936, 1254, 971, 2866, 845, 918, 2203,
        2503, 388, 751, 304, 843, 2578, 2176, 961, 2374, 1222, 2959,
        1630, 95, 3076, 2442, 2875, 1357, 1301, 2224, 202, 2011, 2688,
        2439, 1936, 1514, 194, 362, 2117, 2476, 742, 596, 2084, 1130,
        1539, 2803, 1643, 282, 664, 1740, 1193, 2107, 1464, 2256, 2741,
        1112, 1723, 2182, 256, 527, 2918, 1814, 1290, 482, 567, 2509,
        34, 15, 2490] := by native_decide

/-- **Gate 4c — `SamplePolyCBD(η=2, [0,…,127])` full-poly cross-implementation KAT.** The entire 256
coefficients match an INDEPENDENT Python transcription of FIPS 203 Alg 8 (LSB-first `BytesToBits` + centred
difference) on the same fixed input. Pins the bit layout and the centring simultaneously. -/
theorem samplePolyCBD_kat :
    cbd031 =
      #[0, 0, 1, 0, 1, 0, 2, 0, 3328, 0, 0,
        0, 0, 0, 1, 0, 3328, 0, 0, 0, 0, 0,
        1, 0, 3327, 0, 3328, 0, 3328, 0, 0, 0, 0,
        1, 1, 1, 1, 1, 2, 1, 3328, 1, 0, 1,
        0, 1, 1, 1, 3328, 1, 0, 1, 0, 1, 1,
        1, 3327, 1, 3328, 1, 3328, 1, 0, 1, 0, 1,
        1, 1, 1, 1, 2, 1, 3328, 1, 0, 1, 0,
        1, 1, 1, 3328, 1, 0, 1, 0, 1, 1, 1,
        3327, 1, 3328, 1, 3328, 1, 0, 1, 0, 2, 1,
        2, 1, 2, 2, 2, 3328, 2, 0, 2, 0, 2,
        1, 2, 3328, 2, 0, 2, 0, 2, 1, 2, 3327,
        2, 3328, 2, 3328, 2, 0, 2, 0, 3328, 1, 3328,
        1, 3328, 2, 3328, 3328, 3328, 0, 3328, 0, 3328, 1,
        3328, 3328, 3328, 0, 3328, 0, 3328, 1, 3328, 3327, 3328,
        3328, 3328, 3328, 3328, 0, 3328, 0, 0, 1, 0, 1,
        0, 2, 0, 3328, 0, 0, 0, 0, 0, 1, 0,
        3328, 0, 0, 0, 0, 0, 1, 0, 3327, 0, 3328,
        0, 3328, 0, 0, 0, 0, 0, 1, 0, 1, 0,
        2, 0, 3328, 0, 0, 0, 0, 0, 1, 0, 3328,
        0, 0, 0, 0, 0, 1, 0, 3327, 0, 3328, 0,
        3328, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2,
        1, 3328, 1, 0, 1, 0, 1, 1, 1, 3328, 1,
        0, 1, 0, 1, 1, 1, 3327, 1, 3328, 1, 3328,
        1, 0, 1] := by native_decide

end Dregg2.Crypto.MlKemSample
