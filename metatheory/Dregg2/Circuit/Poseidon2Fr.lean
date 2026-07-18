/-
# Dregg2.Circuit.Poseidon2Fr — the Poseidon2-BN254 hash gadget over the R1csFr foundation.

The deployed compression primitive of the STARK→EVM wrap is the NATIVE BN254 Poseidon2
permutation (`chain/gnark/poseidon2_bn254.go`, reference twin `poseidon2_bn254_ref.go`):
Poseidon2 with `(n,t,d) = (256,3,5)`, `R_F = 8` (4 initial + 4 terminal full rounds),
`R_P = 56` partial rounds, round constants machine-extracted from HorizenLabs
`poseidon2_instance_bn256.rs` RC3 (the exact table plonky3 pins as its zkhash reference).

This module is that gadget in Lean, twice, over `Dregg2.Circuit.R1csFr`:

  * **`permute`** — the permutation as a plain `Fr`-function (the semantic ground truth),
    the same schedule as the Go: initial `extLinear`; 4 × {+RC; x⁵ all lanes; `extLinear`};
    56 × {lane0 += RC; lane0 := lane0⁵; `intLinear`}; 4 × {+RC; x⁵ all lanes; `extLinear`}.
  * **`permCircuit`** — the gadget as a frontend op-DAG (`Wire`/`Circuit`): a builder in
    the gnark-frontend style where every S-box multiplication is snapped to a fresh
    frontend variable (gnark's `api.Mul` returning an internal wire) and each linear layer
    is likewise named — so the `Wire` TREES stay constant-size and the whole 64-round DAG
    is shared, exactly as gnark's DAG is. Vars 0-2 = input lanes, 3-5 = claimed output
    lanes, 6+ = internals in mint order. Through `R1csFr.gHolds`/`lower_sound` this
    frontend circuit IS an R1CS over Fr with a soundness bridge already proven.

**KAT (bit-exactness vs the deployed Go).** The gold vector in
`chain/gnark/poseidon2_bn254_test.go` (`bn254KATOutHex`) — Poseidon2Bn254⟨3⟩ of `[0,1,2]`,
produced by the HorizenLabs zkhash plain implementation and reproduced by the deployed Go
reference (`TestPoseidon2Bn254RefMatchesGoldKAT`, green at authoring time) — is `#guard`ed
below against BOTH the Lean `permute` and the Lean circuit, with the Go tests' reject
polarities mirrored (tampered input diverges; tampered output lane refutes the circuit),
and the circuit is additionally checked ≡ `permute` on the Go test's differential inputs
`{0,0,0}, {1,2,3}, {7,42,999}, {2⁴⁰,2⁵⁰,2⁶⁰}` — at the frontend AND the lowered-R1CS level.

One representation note: the Go writes `2·s₂` in the internal layer as a constant
multiplication (linear, zero constraints); here it is `s₂ + s₂` — the same field value,
still linear, so the op-DAG stays mul-free outside the S-boxes just like the Go gadget.
-/
import Dregg2.Circuit.R1csFr

namespace Dregg2.Circuit.Poseidon2Fr

open Dregg2.Circuit.R1csFr

/-! ## §1 Round constants — chain/gnark/poseidon2_bn254_constants.go, verbatim.

`rcExtInitial`/`rcExtTerminal`: the 4+4 external full rounds, all 3 lanes.
`rcInternal`: the 56 partial rounds, added to lane 0 only. Any transcription error here is
caught by the gold-KAT `#guard`s in §5 — the vector pins constants, S-box, layer order and
both linear layers simultaneously. -/

/-- The 4 initial external-round constant triples (`rc3ExtInitial`). -/
def rcExtInitial : List (Fr × Fr × Fr) := [
  (0x1d066a255517b7fd8bddd3a93f7804ef7f8fcde48bb4c37a59a09a1a97052816,
   0x29daefb55f6f2dc6ac3f089cebcc6120b7c6fef31367b68eb7238547d32c1610,
   0x1f2cb1624a78ee001ecbd88ad959d7012572d76f08ec5c4f9e8b7ad7b0b4e1d1),
  (0x0aad2e79f15735f2bd77c0ed3d14aa27b11f092a53bbc6e1db0672ded84f31e5,
   0x2252624f8617738cd6f661dd4094375f37028a98f1dece66091ccf1595b43f28,
   0x1a24913a928b38485a65a84a291da1ff91c20626524b2b87d49f4f2c9018d735),
  (0x22fc468f1759b74d7bfc427b5f11ebb10a41515ddff497b14fd6dae1508fc47a,
   0x1059ca787f1f89ed9cd026e9c9ca107ae61956ff0b4121d5efd65515617f6e4d,
   0x02be9473358461d8f61f3536d877de982123011f0bf6f155a45cbbfae8b981ce),
  (0x0ec96c8e32962d462778a749c82ed623aba9b669ac5b8736a1ff3a441a5084a4,
   0x292f906e073677405442d9553c45fa3f5a47a7cdb8c99f9648fb2e4d814df57e,
   0x274982444157b86726c11b9a0f5e39a5cc611160a394ea460c63f0b2ffe5657e)]

/-- The 56 partial-round constants (`rc3Internal`), lane 0 only. -/
def rcInternal : List Fr := [
  0x1a1d063e54b1e764b63e1855bff015b8cedd192f47308731499573f23597d4b5,
  0x26abc66f3fdf8e68839d10956259063708235dccc1aa3793b91b002c5b257c37,
  0x0c7c64a9d887385381a578cfed5aed370754427aabca92a70b3c2b12ff4d7be8,
  0x1cf5998769e9fab79e17f0b6d08b2d1eba2ebac30dc386b0edd383831354b495,
  0x0f5e3a8566be31b7564ca60461e9e08b19828764a9669bc17aba0b97e66b0109,
  0x18df6a9d19ea90d895e60e4db0794a01f359a53a180b7d4b42bf3d7a531c976e,
  0x04f7bf2c5c0538ac6e4b782c3c6e601ad0ea1d3a3b9d25ef4e324055fa3123dc,
  0x29c76ce22255206e3c40058523748531e770c0584aa2328ce55d54628b89ebe6,
  0x198d425a45b78e85c053659ab4347f5d65b1b8e9c6108dbe00e0e945dbc5ff15,
  0x25ee27ab6296cd5e6af3cc79c598a1daa7ff7f6878b3c49d49d3a9a90c3fdf74,
  0x138ea8e0af41a1e024561001c0b6eb1505845d7d0c55b1b2c0f88687a96d1381,
  0x306197fb3fab671ef6e7c2cba2eefd0e42851b5b9811f2ca4013370a01d95687,
  0x1a0c7d52dc32a4432b66f0b4894d4f1a21db7565e5b4250486419eaf00e8f620,
  0x2b46b418de80915f3ff86a8e5c8bdfccebfbe5f55163cd6caa52997da2c54a9f,
  0x12d3e0dc0085873701f8b777b9673af9613a1af5db48e05bfb46e312b5829f64,
  0x263390cf74dc3a8870f5002ed21d089ffb2bf768230f648dba338a5cb19b3a1f,
  0x0a14f33a5fe668a60ac884b4ca607ad0f8abb5af40f96f1d7d543db52b003dcd,
  0x28ead9c586513eab1a5e86509d68b2da27be3a4f01171a1dd847df829bc683b9,
  0x1c6ab1c328c3c6430972031f1bdb2ac9888f0ea1abe71cffea16cda6e1a7416c,
  0x1fc7e71bc0b819792b2500239f7f8de04f6decd608cb98a932346015c5b42c94,
  0x03e107eb3a42b2ece380e0d860298f17c0c1e197c952650ee6dd85b93a0ddaa8,
  0x2d354a251f381a4669c0d52bf88b772c46452ca57c08697f454505f6941d78cd,
  0x094af88ab05d94baf687ef14bc566d1c522551d61606eda3d14b4606826f794b,
  0x19705b783bf3d2dc19bcaeabf02f8ca5e1ab5b6f2e3195a9d52b2d249d1396f7,
  0x09bf4acc3a8bce3f1fcc33fee54fc5b28723b16b7d740a3e60cef6852271200e,
  0x1803f8200db6013c50f83c0c8fab62843413732f301f7058543a073f3f3b5e4e,
  0x0f80afb5046244de30595b160b8d1f38bf6fb02d4454c0add41f7fef2faf3e5c,
  0x126ee1f8504f15c3d77f0088c1cfc964abcfcf643f4a6fea7dc3f98219529d78,
  0x23c203d10cfcc60f69bfb3d919552ca10ffb4ee63175ddf8ef86f991d7d0a591,
  0x2a2ae15d8b143709ec0d09705fa3a6303dec1ee4eec2cf747c5a339f7744fb94,
  0x07b60dee586ed6ef47e5c381ab6343ecc3d3b3006cb461bbb6b5d89081970b2b,
  0x27316b559be3edfd885d95c494c1ae3d8a98a320baa7d152132cfe583c9311bd,
  0x1d5c49ba157c32b8d8937cb2d3f84311ef834cc2a743ed662f5f9af0c0342e76,
  0x2f8b124e78163b2f332774e0b850b5ec09c01bf6979938f67c24bd5940968488,
  0x1e6843a5457416b6dc5b7aa09a9ce21b1d4cba6554e51d84665f75260113b3d5,
  0x11cdf00a35f650c55fca25c9929c8ad9a68daf9ac6a189ab1f5bc79f21641d4b,
  0x21632de3d3bbc5e42ef36e588158d6d4608b2815c77355b7e82b5b9b7eb560bc,
  0x0de625758452efbd97b27025fbd245e0255ae48ef2a329e449d7b5c51c18498a,
  0x2ad253c053e75213e2febfd4d976cc01dd9e1e1c6f0fb6b09b09546ba0838098,
  0x1d6b169ed63872dc6ec7681ec39b3be93dd49cdd13c813b7d35702e38d60b077,
  0x1660b740a143664bb9127c4941b67fed0be3ea70a24d5568c3a54e706cfef7fe,
  0x0065a92d1de81f34114f4ca2deef76e0ceacdddb12cf879096a29f10376ccbfe,
  0x1f11f065202535987367f823da7d672c353ebe2ccbc4869bcf30d50a5871040d,
  0x26596f5c5dd5a5d1b437ce7b14a2c3dd3bd1d1a39b6759ba110852d17df0693e,
  0x16f49bc727e45a2f7bf3056efcf8b6d38539c4163a5f1e706743db15af91860f,
  0x1abe1deb45b3e3119954175efb331bf4568feaf7ea8b3dc5e1a4e7438dd39e5f,
  0x0e426ccab66984d1d8993a74ca548b779f5db92aaec5f102020d34aea15fba59,
  0x0e7c30c2e2e8957f4933bd1942053f1f0071684b902d534fa841924303f6a6c6,
  0x0812a017ca92cf0a1622708fc7edff1d6166ded6e3528ead4c76e1f31d3fc69d,
  0x21a5ade3df2bc1b5bba949d1db96040068afe5026edd7a9c2e276b47cf010d54,
  0x01f3035463816c84ad711bf1a058c6c6bd101945f50e5afe72b1a5233f8749ce,
  0x0b115572f038c0e2028c2aafc2d06a5e8bf2f9398dbd0fdf4dcaa82b0f0c1c8b,
  0x1c38ec0b99b62fd4f0ef255543f50d2e27fc24db42bc910a3460613b6ef59e2f,
  0x1c89c6d9666272e8425c3ff1f4ac737b2f5d314606a297d4b1d0b254d880c53e,
  0x03326e643580356bf6d44008ae4c042a21ad4880097a5eb38b71e2311bb88f8f,
  0x268076b0054fb73f67cee9ea0e51e3ad50f27a6434b5dceb5bdde2299910a4c9]

/-- The 4 terminal external-round constant triples (`rc3ExtTerminal`). -/
def rcExtTerminal : List (Fr × Fr × Fr) := [
  (0x1acd63c67fbc9ab1626ed93491bda32e5da18ea9d8e4f10178d04aa6f8747ad0,
   0x19f8a5d670e8ab66c4e3144be58ef6901bf93375e2323ec3ca8c86cd2a28b5a5,
   0x1c0dc443519ad7a86efa40d2df10a011068193ea51f6c92ae1cfbb5f7b9b6893),
  (0x14b39e7aa4068dbe50fe7190e421dc19fbeab33cb4f6a2c4180e4c3224987d3d,
   0x1d449b71bd826ec58f28c63ea6c561b7b820fc519f01f021afb1e35e28b0795e,
   0x1ea2c9a89baaddbb60fa97fe60fe9d8e89de141689d1252276524dc0a9e987fc),
  (0x0478d66d43535a8cb57e9c1c3d6a2bd7591f9a46a0e9c058134d5cefdb3c7ff1,
   0x19272db71eece6a6f608f3b2717f9cd2662e26ad86c400b21cde5e4a7b00bebe,
   0x14226537335cab33c749c746f09208abb2dd1bd66a87ef75039be846af134166),
  (0x01fd6af15956294f9dfe38c0d976a088b21c21e4a1c2e823f912f44961f9a9ce,
   0x18e5abedd626ec307bca190b8b2cab1aaee2e62ed229ba5a5ad8518d4e5f2a57,
   0x0fc1bbceba0590f5abbdffa6d3b35e3297c021a3a409926d0e2d54dc1c84fda6)]

/-! ## §2 The permutation over Fr — semantic ground truth (`poseidon2Bn254Ref` shape). -/

/-- A width-3 state. -/
abbrev St := Fr × Fr × Fr

/-- The S-box `x ↦ x⁵`, in the Go decomposition (`x² := x·x; x⁴ := x²·x²; x⁴·x`). -/
def sbox (x : Fr) : Fr :=
  let x2 := x * x
  let x4 := x2 * x2
  x4 * x

/-- The S-box is genuinely the 5th power. -/
theorem sbox_eq_pow (x : Fr) : sbox x = x ^ 5 := by
  simp only [sbox]; ring

/-- External MDS-light layer (`bn254ExtLinear`): `sum := s₀+s₁+s₂; sᵢ += sum`. -/
def extLinear : St → St
  | (s0, s1, s2) =>
      let sum := s0 + s1 + s2
      (s0 + sum, s1 + sum, s2 + sum)

/-- `extLinear` is the matrix `M_E = [[2,1,1],[1,2,1],[1,1,2]]`. -/
theorem extLinear_matrix (a b c : Fr) :
    extLinear (a, b, c) = (2*a + b + c, a + 2*b + c, a + b + 2*c) := by
  simp only [extLinear, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

/-- Internal diffusion layer (`bn254IntLinear`): `1 + diag([1,1,2])` —
`sum := s₀+s₁+s₂; s₀ += sum; s₁ += sum; s₂ := 2·s₂ + sum`. -/
def intLinear : St → St
  | (s0, s1, s2) =>
      let sum := s0 + s1 + s2
      (s0 + sum, s1 + sum, s2 + s2 + sum)

/-- `intLinear` is the matrix `[[2,1,1],[1,2,1],[1,1,3]]`. -/
theorem intLinear_matrix (a b c : Fr) :
    intLinear (a, b, c) = (2*a + b + c, a + 2*b + c, a + b + 3*c) := by
  simp only [intLinear, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

/-- One external full round: add the constant triple, S-box all lanes, `extLinear`. -/
def fullRound (s : St) (rc : Fr × Fr × Fr) : St :=
  extLinear (sbox (s.1 + rc.1), sbox (s.2.1 + rc.2.1), sbox (s.2.2 + rc.2.2))

/-- One internal partial round: lane 0 gets the constant and the S-box, then `intLinear`. -/
def partialRound (s : St) (rc : Fr) : St :=
  intLinear (sbox (s.1 + rc), s.2.1, s.2.2)

/-- **The Poseidon2-BN254⟨3⟩ permutation** — the exact `poseidon2Bn254Ref` schedule:
initial `extLinear`, 4 initial full rounds, 56 partial rounds, 4 terminal full rounds. -/
def permute (s : St) : St :=
  let s := extLinear s
  let s := rcExtInitial.foldl fullRound s
  let s := rcInternal.foldl partialRound s
  rcExtTerminal.foldl fullRound s

/-- **The deployed 2-to-1 Merkle compression** (`Poseidon2Bn254Compress`): absorb
`(left, right)` into the rate-2/capacity-0 state and squeeze lane 0. -/
def compress (left right : Fr) : Fr :=
  (permute (left, right, 0)).1

/-! ## §3 The gadget as a frontend op-DAG over R1csFr.

The `Wire` type is a tree; a literal 64-round expression would blow up exponentially. The
gnark frontend has no such problem because `api.Mul`/`api.Add` return references into a
shared DAG. We recover exactly that sharing inside the R1csFr model with a builder that
snaps every S-box product AND every linear-layer output to a fresh frontend variable via
`assertIsEqual (definingWire, var fresh)` — each tree stays O(1), the DAG is the variable
graph. Extra named linear wires cost only linear R1CS rows; the multiplication count (the
real R1CS cost, 3 per S-box × 80 S-boxes = 240) is unchanged from the Go gadget. -/

/-- Builder state: next fresh frontend variable, assert list so far (in emit order). -/
abbrev BuilderM := StateM (ℕ × List (Wire × Wire))

/-- Name `w`: mint a fresh frontend variable `v`, assert `w = var v`, return `var v`. -/
def emit (w : Wire) : BuilderM Wire := do
  let (n, cs) ← get
  set (n + 1, cs ++ [(w, Wire.var n)])
  pure (Wire.var n)

/-- S-box on a wire: three named multiplications (the gnark `bn254Sbox`). -/
def sboxW (x : Wire) : BuilderM Wire := do
  let x2 ← emit (.mul x x)
  let x4 ← emit (.mul x2 x2)
  emit (.mul x4 x)

/-- External linear layer on wires (additions only — zero multiplications). -/
def extLinearW (s : Wire × Wire × Wire) : BuilderM (Wire × Wire × Wire) := do
  let sum := Wire.add s.1 (Wire.add s.2.1 s.2.2)
  let a ← emit (.add s.1 sum)
  let b ← emit (.add s.2.1 sum)
  let c ← emit (.add s.2.2 sum)
  pure (a, b, c)

/-- Internal linear layer on wires (`2·s₂` as `s₂ + s₂` — still additions only). -/
def intLinearW (s : Wire × Wire × Wire) : BuilderM (Wire × Wire × Wire) := do
  let sum := Wire.add s.1 (Wire.add s.2.1 s.2.2)
  let a ← emit (.add s.1 sum)
  let b ← emit (.add s.2.1 sum)
  let c ← emit (.add (.add s.2.2 s.2.2) sum)
  pure (a, b, c)

/-- One external full round on wires. -/
def fullRoundW (s : Wire × Wire × Wire) (rc : Fr × Fr × Fr) : BuilderM (Wire × Wire × Wire) := do
  let a ← sboxW (.add s.1 (.const rc.1))
  let b ← sboxW (.add s.2.1 (.const rc.2.1))
  let c ← sboxW (.add s.2.2 (.const rc.2.2))
  extLinearW (a, b, c)

/-- One internal partial round on wires. -/
def partialRoundW (s : Wire × Wire × Wire) (rc : Fr) : BuilderM (Wire × Wire × Wire) := do
  let a ← sboxW (.add s.1 (.const rc))
  intLinearW (a, s.2.1, s.2.2)

/-- The full permutation on wires — the same schedule as `permute`, round for round. -/
def permuteW (s : Wire × Wire × Wire) : BuilderM (Wire × Wire × Wire) := do
  let s ← extLinearW s
  let s ← rcExtInitial.foldlM fullRoundW s
  let s ← rcInternal.foldlM partialRoundW s
  rcExtTerminal.foldlM fullRoundW s

/-- Build the permutation circuit: inputs = vars 0-2, claimed outputs = vars 3-5,
internals minted from 6 up; the final three asserts pin the permuted lanes to 3-5. -/
def buildAsserts : List (Wire × Wire) :=
  (StateT.run (m := Id) (do
      let out ← permuteW (.var 0, .var 1, .var 2)
      let (n, cs) ← get
      set (n, cs ++ [(out.1, Wire.var 3), (out.2.1, Wire.var 4), (out.2.2, Wire.var 5)]))
    (6, [])).2.2

/-- **The Poseidon2-BN254 permutation as an R1csFr `Circuit`.** `Circuit.lower` compiles
it to genuine R1CS over Fr; `gHolds`/`lower_sound` (proven in R1csFr) give the
completeness/soundness bridge for it with no further work. -/
def permCircuit : Circuit := ⟨buildAsserts⟩

/-! ## §4 Witness solving.

Every emitted assert is `(definingWire, var n)` with `n` fresh and `definingWire` over
already-defined variables, so the honest witness is computed by one forward pass. -/

/-- One solver step: a defining assert for the next fresh variable appends its computed
value; the three output-pinning asserts (rhs var < length) change nothing. -/
def solveStep (acc : List Fr) (p : Wire × Wire) : List Fr :=
  match p.2 with
  | .var n => if n = acc.length then acc ++ [p.1.eval fun v => acc.getD v 0] else acc
  | _ => acc

/-- Solve the whole witness from `[in₀, in₁, in₂, out₀, out₁, out₂]` (claimed outputs —
the solver fills internals honestly from the inputs regardless, so a wrong claimed output
yields a witness the circuit refutes, which is the reject-polarity teeth below). -/
def solve (base : List Fr) : List Fr :=
  buildAsserts.foldl solveStep base

/-- Frontend acceptance of the circuit on inputs/claimed outputs (witness solved once,
then checked — `Bool` so the `#guard`s below execute). -/
def checkPerm (i : St) (o : St) : Bool :=
  let w := solve [i.1, i.2.1, i.2.2, o.1, o.2.1, o.2.2]
  decide (permCircuit.satisfied fun v => w.getD v 0)

/-- Lowered-R1CS acceptance: the same witness pushed through `Circuit.lower` with the
canonical aux extension (`assertsAux`) — the executable face of `gHolds`. -/
def checkPermR1cs (i : St) (o : St) : Bool :=
  let w := solve [i.1, i.2.1, i.2.2, o.1, o.2.1, o.2.2]
  let a : Assignment := fun v => w.getD v 0
  let aux := assertsAux a permCircuit.asserts
  let z : RAssignment := fun v =>
    match v with
    | .inl v => a v
    | .inr j => aux.getD j 0
  decide (r1csSatisfied permCircuit.lower z)

/-- Circuit-vs-reference differential on one input: does the circuit accept exactly the
outputs `permute` computes? -/
def checkPermSelf (i : St) : Bool := checkPerm i (permute i)

/-! ## §5 KAT — bit-exact against the deployed Go reference.

`bn254KATOutHex` from `chain/gnark/poseidon2_bn254_test.go`: the HorizenLabs zkhash gold
vector for input `[0,1,2]`, reproduced by the deployed `poseidon2Bn254Ref`
(`TestPoseidon2Bn254RefMatchesGoldKAT`) and accepted by the deployed gnark circuit
(`TestPoseidon2Bn254CircuitMatchesGoldAndRef`). -/

/-- The gold KAT output for input `(0, 1, 2)` — `bn254KATOutHex`, verbatim. -/
def katOut : St :=
  (0x0bb61d24daca55eebcb1929a82650f328134334da98ea4f847f760054f4a3033,
   0x303b6f7c86d043bfcbcc80214f26a30277a15d3f74ca654992defe7ff8d03570,
   0x1ed25194542b12eef8617361c3ba7c52e660b145994427cc86296242cf766ec8)

-- Sanity on the constant tables' shape (4 / 56 / 4).
#guard rcExtInitial.length = 4
#guard rcInternal.length = 56
#guard rcExtTerminal.length = 4

-- **THE KAT.** The Lean permutation reproduces the zkhash/Go gold vector bit-exactly.
#guard permute (0, 1, 2) = katOut

-- Reject polarity for the KAT itself (mirrors `TestPoseidon2Bn254RefKATBites`):
-- tampering the input (last lane 2 → 3) must change lane 0 of the output.
#guard (permute (0, 1, 3)).1 ≠ katOut.1

-- The op-DAG circuit accepts the gold KAT (mirrors the gold leg of
-- `TestPoseidon2Bn254CircuitMatchesGoldAndRef`) — frontend AND lowered R1CS.
#guard checkPerm (0, 1, 2) katOut
#guard checkPermR1cs (0, 1, 2) katOut

-- Differential vs the reference on the Go test's input set (circuit ≡ `permute`).
#guard checkPermSelf (0, 0, 0)
#guard checkPermSelf (1, 2, 3)
#guard checkPermSelf (7, 42, 999)
#guard checkPermSelf (2 ^ 40, 2 ^ 50, 2 ^ 60)

-- Reject polarity for the circuit (mirrors `TestPoseidon2Bn254CircuitRejectsTamperedOutput`):
-- bump output lane 1 — refused at the frontend and at the lowered-R1CS level.
#guard let o := permute (7, 42, 999)
       !checkPerm (7, 42, 999) (o.1, o.2.1 + 1, o.2.2)
#guard let o := permute (7, 42, 999)
       !checkPermR1cs (7, 42, 999) (o.1, o.2.1 + 1, o.2.2)

-- The compression squeezes lane 0 of the permuted (l, r, 0) state; on (0, 1) that IS
-- lane 0 of the gold KAT with capacity lane 2 → 0 permuted — pin its concrete value
-- through `permute` (compress is definitionally the squeeze, this guards non-vacuously
-- that the wiring stays put).
#guard compress 0 1 = (permute (0, 1, 0)).1
#guard compress 0 1 ≠ compress 1 0

/-! ## §6 The soundness face — inherited from R1csFr, stated for THIS gadget. -/

/-- **Soundness for the Poseidon2 gadget's R1CS**: ANY witness of the lowered system that
agrees with `a` on the frontend variables — however the aux region was filled — forces
every gadget constraint at the frontend, in particular the three output-pinning equalities:
the prover cannot claim a wrong permutation output. Pure `lower_sound` applied here. -/
theorem permCircuit_sound (a : Assignment) (z : RAssignment)
    (hinl : ∀ v, z (.inl v) = a v) (hsat : r1csSatisfied permCircuit.lower z) :
    permCircuit.satisfied a :=
  lower_sound permCircuit a z hinl hsat

/-- Completeness face: frontend acceptance transports to the lowered R1CS with the
canonical extension (this is what `checkPermR1cs` exercises executably above). -/
theorem permCircuit_complete (a : Assignment) (h : permCircuit.satisfied a) :
    r1csSatisfied permCircuit.lower (permCircuit.extend a) :=
  (gHolds permCircuit a).mp h

#assert_axioms sbox_eq_pow
#assert_axioms extLinear_matrix
#assert_axioms intLinear_matrix
#assert_axioms permCircuit_sound
#assert_axioms permCircuit_complete

end Dregg2.Circuit.Poseidon2Fr
