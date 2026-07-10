/-
# `Dregg2.Crypto.MlDsaExpandA` — the REAL ML-DSA-65 `ExpandA` (FIPS 204 Algorithm 32), as EXECUTABLE `def`s.

FIPS 204 §7.3, Algorithm 32. `ExpandA(ρ)` deterministically derives the public matrix `Â ∈ R_q^{k×ℓ}` from the
32-byte seed `ρ` by driving, for each entry, a SHAKE-128 rejection sampler (`RejNTTPoly`, Algorithm 30). For
ML-DSA-65 the dimensions are `k = 6`, `ℓ = 5`, so `Â` is a `6 × 5` matrix of ring elements — 30 polynomials.

This is BRICK 4 of replacing the `A = id` scalar caricature in `Fips204Verify.lean` with the real ML-DSA-65
verify. It REUSES — does not reimplement — the two landed, verified bricks:

* BRICK 1 `Dregg2.Crypto.Keccak` — real SHAKE-128 (`shake128`), byte-exact vs the FIPS 202 NIST KATs.
* BRICK 2 `Dregg2.Crypto.MlDsaRing` — the real ring `R_q = ℤ_q[X]/(X²⁵⁶+1)` (`Poly`, `q = 8380417`, gate-verified NTT).

Each `Â[i][j]` is produced already in the **NTT domain** (`RejNTTPoly` samples the transform-domain coefficients
directly), so `ntt` is NOT applied to it — brick 6 `verifyCore` multiplies `Â · ẑ` pointwise in the NTT domain.

## THE ALGORITHM (FIPS 204, faithfully)

`RejNTTPoly(ρ')` (Algorithm 30): drive SHAKE-128 over `ρ'`; read 3 stream bytes `(b0, b1, b2)` at a time, form
`d = b0 + 256·b1 + 65536·(b2 &&& 0x7F)` (a 23-bit value — the top bit of `b2` is masked), ACCEPT `d` as the next
coefficient iff `d < q = 8380417`, else reject; fill exactly 256 coefficients. The result is a `Poly` already in
the NTT domain.

`ExpandA(ρ)` (Algorithm 32): for row `i ∈ 0..k-1`, column `j ∈ 0..ℓ-1`,
`Â[i][j] = RejNTTPoly(ρ ‖ IntegerToBytes(j,1) ‖ IntegerToBytes(i,1))` — the **COLUMN index `j` is appended
first, then the row index `i`** (FIPS 204 Algorithm 32 lines: `s` = column runs the inner loop, `ρ' = ρ ‖ s ‖ r`).
Getting this order backwards is the classic ExpandA transposition bug; the corner-poly KATs below pin it.

The matrix is returned flattened row-major: `expandA ρ` is an `Array Poly` of length `k·ℓ = 30`, entry `Â[i][j]`
at index `i·ℓ + j`.

The one implementation liberty: rather than an incremental squeeze, we pull a generously-sized SHAKE-128 block up
front and cursor 3 bytes at a time. Acceptance probability is `q/2²³ ≈ 0.99902`, so 256 coefficients need
`≈ 256.25` reads on average; pulling `384` reads (1152 bytes) is a wide margin. If it were ever too small the
`expandA_shape` gate (each poly exactly 256 coeffs) would red the build, so the size is self-checked.

## THE ANTI-FAKE GATES (`native_decide`, compiled)

* `expandA_shape` — `Â` has exactly `30` polynomials, each with exactly `256` coefficients.
* `rejNTTPoly_coeffs_in_range` — every coefficient of every one of the 30 polys is in `[0, q)`.
* `expandA_kat_corner_00` / `expandA_kat_corner_54` — for the concrete `ρ = [0,1,…,31]`, the FULL 256 coefficients
  of the corner polys `Â[0][0]` and `Â[k−1][ℓ−1] = Â[5][4]` are byte-for-byte the values produced by an
  INDEPENDENT reference: Python `hashlib.shake_128` driving a from-scratch transcription of FIPS 204 RejNTTPoly on
  the same `ρ`. This is a genuine cross-implementation Known-Answer-Test, not a self-consistency tautology; it
  pins SHAKE-128, the 3-byte little-endian coefficient packing, the `0x7F` top-bit mask, the `< q` rejection, AND
  the `ρ ‖ j ‖ i` seed byte order (the two corners exercise `(i,j) = (0,0)` and `(5,4)` — a transposition to
  `ρ ‖ i ‖ j` would swap `Â[5][4]` with `Â[4][5]` and red the corner KAT).

`native_decide` runs the COMPILED `def`s; its trusted base is `Lean.ofReduceBool` + `Lean.trustCompiler`, the same
residual `Keccak` and `MlDsaRing` already name. No `sorry`, no user `axiom`, no toy substitute.
-/

import Dregg2.Crypto.Keccak
import Dregg2.Crypto.MlDsaRing

namespace Dregg2.Crypto.MlDsaExpandA

open Dregg2.Crypto.MlDsaRing (Poly q)
open Dregg2.Crypto.Keccak (shake128)

/-- ML-DSA-65 matrix row count, FIPS 204 Table 2: `k = 6`. -/
def k : Nat := 6

/-- ML-DSA-65 matrix column count, FIPS 204 Table 2: `ℓ = 5`. -/
def ell : Nat := 5

/-- Number of 3-byte SHAKE-128 reads to pull up front for one `RejNTTPoly`. Acceptance probability is
`q/2²³ ≈ 0.99902`, so 256 accepted coefficients need `≈ 256.25` reads; `384` is a wide margin. If it were ever
too small the `expandA_shape` gate (exactly 256 coeffs per poly) would fail, so the size is self-checked. -/
def rejReads : Nat := 384

/-- **`RejNTTPoly` — FIPS 204 Algorithm 30.**

Drive SHAKE-128 over `seed`; read 3 stream bytes `(b0, b1, b2)` at a time, form
`d = b0 + 256·b1 + 65536·(b2 &&& 0x7F)`, and ACCEPT `d` as the next coefficient iff `d < q`, else reject. Fill
exactly 256 coefficients. The result is a `Poly` already in the **NTT domain** (do NOT apply `ntt` to it). -/
def rejNTTPoly (seed : List UInt8) : Poly := Id.run do
  let stream : Array UInt8 := (shake128 seed (3 * rejReads)).toArray
  let mut coeffs : Array Nat := #[]
  for r in [0:rejReads] do
    if coeffs.size < 256 then
      let base := 3 * r
      let b0 := stream[base]!.toNat
      let b1 := stream[base + 1]!.toNat
      let b2 := (stream[base + 2]! &&& 0x7F).toNat        -- mask the top bit of the third byte
      let d := b0 + 256 * b1 + 65536 * b2                 -- little-endian 23-bit value
      if d < q then
        coeffs := coeffs.push d                           -- accept iff d < q
  return coeffs

/-- **`ExpandA` — FIPS 204 Algorithm 32 for ML-DSA-65 (`k = 6`, `ℓ = 5`).**

For row `i ∈ 0..k-1`, column `j ∈ 0..ℓ-1`, sample `Â[i][j] = RejNTTPoly(ρ ‖ j ‖ i)` — the COLUMN index `j` is
appended first, then the row index `i` (FIPS 204 Algorithm 32). Returns the `k·ℓ = 30` polynomials flattened
row-major (`Â[i][j]` at index `i·ℓ + j`). The caller passes `ρ` of length 32 bytes. -/
def expandA (rho : List UInt8) : Array Poly := Id.run do
  let mut mat : Array Poly := #[]
  for i in [0:k] do                                       -- row  0 … k-1
    for j in [0:ell] do                                   -- column  0 … ℓ-1
      let seed := rho ++ [UInt8.ofNat j, UInt8.ofNat i]   -- ρ ‖ IntegerToBytes(j,1) ‖ IntegerToBytes(i,1)
      mat := mat.push (rejNTTPoly seed)
  return mat

/-! ## THE ANTI-FAKE GATES — `native_decide` over the concrete `ρ = [0,1,…,31]`. -/

/-- The ML-DSA-65 test seed `ρ = [0,1,2,…,31]` — 32 bytes (the ExpandA seed width). -/
def rho031 : List UInt8 := (List.range 32).map (fun n => UInt8.ofNat n)

/-- The public matrix for `rho031`, held once for the gates below. -/
def matrix031 : Array Poly := expandA rho031

/-- **Gate 1 — shape**: `Â` has exactly `k·ℓ = 30` polynomials, each with exactly 256 coefficients. A sampler
that exhausted its buffer (too few reads) or a wrong loop bound fails here. -/
theorem expandA_shape :
    matrix031.size = 30 ∧ matrix031.all (fun p => p.size = 256) = true := by native_decide

/-- **Gate 2 — every coefficient is in `[0, q)`**: no coefficient of any of the 30 polys is `≥ q`. A sampler that
accepted a `d ≥ q` (missing/inverted rejection) or failed to mask the top bit fails here. -/
theorem rejNTTPoly_coeffs_in_range :
    matrix031.all (fun p => p.all (fun c => c < q)) = true := by native_decide

/-- **Gate 3a — corner `Â[0][0]` full-poly cross-implementation KAT.** For `ρ = [0,…,31]` the entire 256
coefficients of the first matrix entry (index `0·ℓ + 0 = 0`) match, coefficient-for-coefficient, an INDEPENDENT
reference: Python `hashlib.shake_128` driving a from-scratch transcription of FIPS 204 RejNTTPoly. This pins
SHAKE-128, the 3-byte packing, the `0x7F` mask, and the `< q` rejection simultaneously. -/
theorem expandA_kat_corner_00 :
    matrix031[0]! =
      #[7905761, 7863978, 1275290, 4366663, 7850937, 4248201, 2710427, 4706185, 6565264, 5317472, 6267181,
        2111275, 3977058, 3444859, 5376343, 6624750, 5258207, 2654719, 4526041, 5609447, 7099996, 7972791,
        7751347, 1704511, 7317659, 3075272, 2848268, 631983, 1871102, 4843380, 1946429, 1774550, 2583960,
        6420779, 5932281, 5080083, 4703343, 7484861, 8098228, 3397161, 1330999, 3568185, 1172502, 1891358,
        900895, 2899822, 2303661, 3011969, 640629, 711795, 1948641, 6265995, 3107486, 3895415, 1504778,
        3669620, 6243368, 7296887, 896287, 5708818, 5402318, 7651448, 5651922, 1324128, 6898583, 1852731,
        4004697, 5630595, 3007003, 1297462, 8335498, 6323621, 1677367, 7887597, 142270, 1231294, 6404586,
        3900983, 1441880, 1953688, 6805324, 7534197, 7750964, 4099184, 342543, 7939752, 152458, 1210792,
        5863467, 4280989, 831351, 2057479, 5748898, 6686046, 5612847, 2432158, 7483373, 3935122, 7242538,
        1365739, 1046440, 6976923, 8269990, 4541959, 5332151, 6062837, 8305715, 6954149, 559656, 4887097,
        7566938, 3647606, 1808230, 1002529, 4571181, 3412967, 3568925, 3016720, 2069508, 2428855, 3123487,
        7435286, 4157690, 1705698, 4209202, 3608641, 652959, 2936997, 2503537, 3013458, 5083341, 5889426,
        2854243, 5686933, 4697715, 5299711, 3448449, 2516645, 1263303, 5205307, 8195350, 2804423, 6028846,
        963152, 2201327, 79013, 771402, 8363111, 7656648, 4522543, 5793385, 3747834, 4817073, 7357347,
        4980350, 5614531, 1906566, 4786495, 3135436, 7329485, 3556531, 4757142, 7997228, 5384380, 4990682,
        7309888, 7190665, 3571542, 2770749, 4816625, 6855032, 6357482, 7369551, 2644264, 4167100, 1839385,
        4205995, 5440074, 3794874, 3441900, 2752750, 6642015, 4248563, 4984715, 3541354, 5055170, 3885715,
        863845, 1495616, 4279852, 6968065, 7035290, 4449543, 1433687, 5671820, 6715062, 687926, 3586769,
        4109667, 3802980, 4777993, 395064, 401334, 7508875, 4230044, 850868, 6047906, 3774087, 1687736,
        1912479, 7321489, 715723, 1997211, 799639, 7042412, 3557898, 1816079, 2119738, 8246927, 2020283,
        8364226, 2709802, 5224716, 4672215, 3949038, 7793820, 5358617, 4403671, 825367, 7620937, 3364516,
        4262262, 908122, 6396034, 471918, 6433180, 2346940, 6088643, 1332404, 6608879, 995641, 1880268,
        3631122, 1415824, 1889218, 6368911, 2849437, 6642265, 7689118, 8200413, 3662638, 4538159, 2469409,
        6266376, 6362081, 6955102] := by native_decide

/-- **Gate 3b — corner `Â[k−1][ℓ−1] = Â[5][4]` full-poly cross-implementation KAT.** For `ρ = [0,…,31]` the
entire 256 coefficients of the last matrix entry (index `5·ℓ + 4 = 29`) match the same INDEPENDENT Python
`hashlib.shake_128` reference. Together with Gate 3a this pins the `ρ ‖ j ‖ i` seed byte order: the classic
transposition `ρ ‖ i ‖ j` would swap `Â[5][4]` with `Â[4][5]` and red this gate. -/
theorem expandA_kat_corner_54 :
    matrix031[29]! =
      #[4009351, 2760419, 8179188, 6762876, 2074200, 212750, 3681925, 4125595, 4057275, 4270945, 6965584,
        1937209, 775769, 7519349, 3025735, 6951942, 4683924, 1637528, 8263061, 3714166, 34971, 4446970,
        8122976, 7614611, 1812397, 7946750, 474234, 94436, 7338090, 7987252, 8078402, 7041987, 2601816,
        3855079, 6716741, 1776399, 4609227, 6550053, 7043611, 1530129, 8302999, 8238247, 5650803, 6435360,
        5404585, 2343159, 4677765, 607822, 8285753, 7874894, 1677312, 282203, 76661, 5810657, 2907901,
        5464961, 1620449, 1811407, 6114840, 412734, 1008850, 7128321, 4670958, 6803717, 3410373, 2409498,
        6782996, 6303421, 3047749, 780444, 2961360, 6452174, 4087653, 23334, 4774645, 3367897, 3403312,
        1098681, 2197079, 3872758, 1140240, 4028920, 4817187, 1581296, 7661189, 7671420, 5236155, 4096024,
        8197180, 5864051, 6162515, 1912408, 1607029, 2233688, 7821353, 7474750, 2351222, 5536768, 3497548,
        6102226, 6309717, 2823074, 6507994, 2613262, 6455672, 5920425, 2872241, 513467, 5547301, 3011140,
        7321162, 6513967, 42736, 22982, 730761, 886975, 7228598, 5011112, 2965200, 5862422, 1897377, 1598061,
        5837141, 2637901, 7914865, 2409040, 6363461, 8290917, 8357370, 5844821, 5705390, 3018674, 6857423,
        3498484, 5114781, 3015910, 6170409, 2694788, 4748850, 5924874, 3307206, 721436, 5576396, 4786476,
        5865079, 5377028, 7426189, 3292701, 5608127, 3569608, 4771980, 3481400, 482762, 3786883, 1406995,
        3942599, 2784776, 4908988, 183010, 4088193, 2826653, 4247773, 5974834, 6263649, 6519446, 5698012,
        8102436, 7558715, 3534018, 2076166, 3167085, 2486113, 1610467, 8275464, 1472746, 4312764, 4900627,
        4079857, 1201499, 6129643, 2737313, 5184392, 5679688, 946994, 1668377, 3958010, 5051223, 941491,
        3563557, 6938990, 7422998, 1761787, 5849650, 6875332, 6941940, 3167291, 6280509, 4736620, 6959457,
        8060060, 2697558, 2174048, 1981434, 2704103, 2479882, 267980, 2422447, 4431783, 6246411, 7885328,
        3163246, 359803, 7487926, 1758109, 7056087, 2150694, 4190381, 6262167, 1935525, 6217448, 5935213,
        645563, 4109685, 2138623, 4229213, 3979044, 7187639, 1594594, 6706601, 1772033, 7508494, 192,
        6992126, 4336987, 375391, 5965615, 2348710, 5032020, 1750773, 8092861, 7371983, 1773502, 7054870,
        7728677, 8302716, 2322261, 4257475, 266127, 4923125, 145804, 1005027, 3598361, 4686290, 5387829,
        28793, 3820859] := by native_decide

end Dregg2.Crypto.MlDsaExpandA
