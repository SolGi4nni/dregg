/-
# Dregg2.Circuit.ChallengerFr — the multifield Fiat-Shamir challenger as a frontend op-DAG
over Fr, BIT-EXACT to the deployed Go gadgets.

The deployed references (the re-architected wrap's transcript boundary,
`docs/deos/WRAP-NATIVE-HASH-DECISION.md`):

  * `chain/gnark/poseidon2_bn254.go`   — Poseidon2Bn254<3> (WIDTH=3, d=5, R_F=8, R_P=56),
    HorizenLabs RC3 constants, pinned to the zkhash gold vector.
  * `chain/gnark/challenger_bn254.go`  — the native width-3 duplex challenger
    (RATE=2, CAPACITY=1; p3 DuplexChallenger discipline at rev 82cfad7).
  * `chain/gnark/multifield_challenger.go` — the BabyBear↔BN254 MultiField adapter on top
    of that sponge (p3 MultiField32Challenger: radix-2^31 8-limb injective PACK on absorb,
    7-limb base-p SPLIT on squeeze, length-tagged rate-padded absorption).

This module models those gadgets over `R1csFr` — the same `Wire` op-DAG gnark's frontend
compiles — at TWO layers, exactly the Go test architecture (ref twin ⇒ gadget differential):

  1. **Pure reference twin** (§2–§4): `perm`, `Chal`, `MRef` — plain `Fr`/`ℕ` state
     machines, the Lean twins of `poseidon2Bn254Ref` / `challengerBn254Ref` /
     `multiFieldChallengerRef`. KAT `#guard`s pin them BIT-EXACT to the Go-pinned vectors:
     the zkhash permutation gold vector, the 4-challenge + 16-bit-index native transcript
     KAT (`challenger_bn254_test.go`), and the 6-challenge + 20-bit-index fork-executed
     MultiField gold KAT (`multifield_challenger_test.go` — executed by the Rust fork
     itself). Both polarities (tampered absorb ≠ pinned challenge).

  2. **The op-DAG gadget** (§5–§7): the same transcripts built as a `Circuit` of `Wire`
     asserts via a builder that mints one frontend variable per DAG sharing point (each
     minted var = one gnark frontend node; `Wire` is a tree, so per-round binding IS the
     DAG sharing gnark's hash-consed builder does implicitly). Witness-supplied
     decompositions (the split limbs, the ToBinary bits) are minted as fresh variables
     with their booleanity/recomposition constraints asserted — the hint-plus-constraint
     shape of the Go gadget. `#guard`s: the KAT circuits are SATISFIED by the canonical
     assignment (every bound node's tree re-evaluates to its minted value AND the final
     challenges equal the pinned constants — this is the gadget-produces-the-KAT check,
     in-circuit), and REJECT tampered absorbs / challenges / indices. One permutation
     probe is additionally pushed through `Circuit.lower` to GENUINE R1CS and checked
     satisfied/refuted there, and `lower_sound` is instantiated at the built KAT circuits
     (no adversarial aux filling can fake the transcript).

Classified seam (named, enforcement-only — NOT the computed transcript): gnark's
range-check families on witness-supplied decompositions — BabyBear canonicity
(`AssertIsCanonical`), the 38-bit split-remainder bound, the lexicographic
(r, c6..c0) ≤ digits(p_BN254−1) canonicity bound, and full-width ToBinary reducedness —
are SOUNDNESS constraints against a malicious prover choosing a shifted decomposition.
Here every minted decomposition is the canonical one by construction, so the computed
transcript (what the KAT pins) is identical with or without them; modeling them as
bit-level circuits is the follow-up enforcement lane. Booleanity and the exact
recomposition equalities ARE modeled and asserted.
-/
import Dregg2.Circuit.R1csFr

namespace Dregg2.Circuit.ChallengerFr

open Dregg2.Circuit.R1csFr

/-! ## §1 Poseidon2Bn254 round constants — HorizenLabs RC3, machine-extracted from
`chain/gnark/poseidon2_bn254_constants.go` (itself machine-extracted from
`poseidon2_instance_bn256.rs`, the exact table plonky3 pins). 4 initial full rounds × 3
lanes, 56 partial-round lane-0 constants, 4 terminal full rounds × 3 lanes. -/

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
   0x274982444157b86726c11b9a0f5e39a5cc611160a394ea460c63f0b2ffe5657e)
]

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
  0x268076b0054fb73f67cee9ea0e51e3ad50f27a6434b5dceb5bdde2299910a4c9
]

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
   0x0fc1bbceba0590f5abbdffa6d3b35e3297c021a3a409926d0e2d54dc1c84fda6)
]

/-! ## §2 The pure permutation — the Lean twin of `poseidon2Bn254Ref`. -/

/-- The width-3 sponge state. -/
structure St3 where
  a : Fr
  b : Fr
  c : Fr

/-- `x^5` in the S-box association the Go gadget uses (`x2 = x·x; x4 = x2·x2; x4·x`). -/
def sbox (x : Fr) : Fr :=
  let x2 := x * x
  let x4 := x2 * x2
  x4 * x

/-- External MDS-light layer for t=3 (`mds_light_permutation`): `sᵢ += Σ s`. -/
def extLinear (s : St3) : St3 :=
  let sum := s.a + s.b + s.c
  ⟨s.a + sum, s.b + sum, s.c + sum⟩

/-- Internal diffusion `1 + diag([1,1,2])`: `s₀ += Σ; s₁ += Σ; s₂ = 2·s₂ + Σ`. -/
def intLinear (s : St3) : St3 :=
  let sum := s.a + s.b + s.c
  ⟨s.a + sum, s.b + sum, 2 * s.c + sum⟩

/-- One external full round: add RCs, S-box all lanes, external layer. -/
def fullRound (rc : Fr × Fr × Fr) (s : St3) : St3 :=
  extLinear ⟨sbox (s.a + rc.1), sbox (s.b + rc.2.1), sbox (s.c + rc.2.2)⟩

/-- One internal partial round: RC + S-box on lane 0 only, internal layer. -/
def partialRound (rc : Fr) (s : St3) : St3 :=
  intLinear ⟨sbox (s.a + rc), s.b, s.c⟩

/-- **The Poseidon2Bn254<3> permutation** — initial external layer, 4 full rounds,
56 partial rounds, 4 full rounds (`Poseidon2Bn254` in `poseidon2_bn254.go`). -/
def perm (s : St3) : St3 :=
  let s := extLinear s
  let s := rcExtInitial.foldl (fun s rc => fullRound rc s) s
  let s := rcInternal.foldl (fun s rc => partialRound rc s) s
  rcExtTerminal.foldl (fun s rc => fullRound rc s) s

-- The zkhash gold vector (`bn254KATOutHex`, `poseidon2_bn254_test.go`): perm [0,1,2].
-- Pins constants, S-box, round order, and both linear layers simultaneously.
def goldPerm : St3 := perm ⟨0, 1, 2⟩
#guard goldPerm.a = 0x0bb61d24daca55eebcb1929a82650f328134334da98ea4f847f760054f4a3033
#guard goldPerm.b = 0x303b6f7c86d043bfcbcc80214f26a30277a15d3f74ca654992defe7ff8d03570
#guard goldPerm.c = 0x1ed25194542b12eef8617361c3ba7c52e660b145994427cc86296242cf766ec8
-- REJECT polarity: a tampered input does not produce the gold lane.
#guard (perm ⟨1, 1, 2⟩).a ≠ 0x0bb61d24daca55eebcb1929a82650f328134334da98ea4f847f760054f4a3033

/-! ## §3 The pure native duplex challenger — twin of `challengerBn254Ref`
(WIDTH=3, RATE=2, CAPACITY=1; p3 `DuplexChallenger` discipline). -/

structure Chal where
  st     : St3     := ⟨0, 0, 0⟩
  inBuf  : List Fr := []
  outBuf : List Fr := []

/-- Duplexing: buffered inputs OVERWRITE `state[0..len]` (capacity lane carries over),
permute, refill the output buffer from the rate lanes. -/
def Chal.duplex (c : Chal) : Chal :=
  let st := match c.inBuf with
    | []          => c.st
    | [x]         => ⟨x, c.st.b, c.st.c⟩
    | x :: y :: _ => ⟨x, y, c.st.c⟩
  let st := perm st
  ⟨st, [], [st.a, st.b]⟩

/-- Observe: stale output dropped, value buffered, full rate triggers a duplexing. -/
def Chal.observe (c : Chal) (v : Fr) : Chal :=
  let c : Chal := { c with outBuf := [], inBuf := c.inBuf ++ [v] }
  if c.inBuf.length == 2 then c.duplex else c

/-- Sample: duplex iff input pending or output drained, then pop from the END. -/
def Chal.sample (c : Chal) : Fr × Chal :=
  let c := if !c.inBuf.isEmpty || c.outBuf.isEmpty then c.duplex else c
  (c.outBuf.getLast?.getD 0, { c with outBuf := c.outBuf.dropLast })

/-- SampleBits: low `n` bits of the CANONICAL representative of one sample. -/
def Chal.sampleBits (c : Chal) (n : ℕ) : ℕ × Chal :=
  let (v, c) := c.sample
  (v.val % 2 ^ n, c)

/-- The pinned transcript protocol of `challenger_bn254_test.go`: observe 11,22,33 →
s0,s1,s2 → observe 44 → s3 → sampleBits 16. Exercises every duplex edge. -/
def bnRefTranscript : List Fr × ℕ :=
  let c : Chal := {}
  let c := ((c.observe 11).observe 22).observe 33
  let (s0, c) := c.sample
  let (s1, c) := c.sample
  let (s2, c) := c.sample
  let c := c.observe 44
  let (s3, c) := c.sample
  let (idx, _) := c.sampleBits 16
  ([s0, s1, s2, s3], idx)

-- The four pinned challenges (`challengerBn254KATHex`) — bit-exact canonical values.
def bnKS0 : Fr := 0x195f00382f107430de76a50bed6a40d20a8cc13d879aebaa3a841c66375df992
def bnKS1 : Fr := 0x17d47c3f41d6ebfc6b6342b05abfd3f38a80b9539d6d044e49430a38a6140ec4
def bnKS2 : Fr := 0x200547e0b2171b7a9d43b0bbf7399f22952d7d593575d3f4f8ef8c49f7918845
def bnKS3 : Fr := 0x2ffb78e229a28f3056d37670d48907d6a818c57d0437cf7b50457248b9db0bfc
/-- The pinned 16-bit query index (`challengerBn254KATIdx`). -/
def bnKIdx : ℕ := 54491

#guard bnRefTranscript.1 = [bnKS0, bnKS1, bnKS2, bnKS3]
#guard bnRefTranscript.2 = bnKIdx
-- REJECT polarity: tampering the first absorbed value kills the first challenge.
#guard ((((({} : Chal).observe 12).observe 22).observe 33).sample).1 ≠ bnKS0

/-! ## §4 The pure MultiField challenger — twin of `multiFieldChallengerRef`
(p3 `MultiField32Challenger<BabyBear, Bn254, Poseidon2Bn254<3>, WIDTH=3, RATE=2>`).
BabyBear values are canonical `ℕ < bbP`. -/

/-- The BabyBear prime `p = 15·2^27 + 1`. -/
def bbP : ℕ := 2013265921

/-- PACK (`reduce_packed`): little-endian radix-2^31 Horner of ≤ 8 canonical BabyBear
limbs — injective into Fr since `(p−1)·Σ_{i<8} 2^{31i} < 2^248 < r`. Exact over ℕ. -/
def packLE (vals : List ℕ) : Fr :=
  ((vals.foldr (fun v acc => acc * 2 ^ 31 + v) 0 : ℕ) : Fr)

/-- SPLIT (`split_pf_to_field_order_limbs`): the 7 little-endian base-p digits of the
canonical representative (the div-p^7 remainder is discarded, exactly as in the fork). -/
def splitLimbs (v : Fr) : List ℕ :=
  (List.range 7).map fun i => v.val / bbP ^ i % bbP

structure MRef where
  st     : St3     := ⟨0, 0, 0⟩
  outBuf : List Fr := []
  fBuf   : List ℕ  := []
  fSq    : List ℕ  := []

/-- `absorb_rate_padded_with_tag`: rate slots overwritten (zero-padded), length tag ADDED
to the capacity slot, permute, refill the output buffer. -/
def MRef.absorbTag (m : MRef) (values : List Fr) (tag : ℕ) : MRef :=
  let st := perm ⟨values.getD 0 0, values.getD 1 0, m.st.c + (tag : Fr)⟩
  { m with st := st, outBuf := [st.a, st.b] }

/-- Flush pending BabyBear values: pack in chunks of 8, absorb with the count as tag. -/
def MRef.flush (m : MRef) : MRef :=
  if m.fBuf.isEmpty then m
  else
    let packed := if m.fBuf.length ≤ 8 then [packLE m.fBuf]
                  else [packLE (m.fBuf.take 8), packLE (m.fBuf.drop 8)]
    let m := m.absorbTag packed m.fBuf.length
    { m with fBuf := [], fSq := [] }

/-- Observe one canonical BabyBear value: stale squeeze output dropped, value buffered,
a full 16-element batch auto-flushes. -/
def MRef.observeBB (m : MRef) (v : ℕ) : MRef :=
  let m : MRef := { m with outBuf := [], fSq := [], fBuf := m.fBuf ++ [v] }
  if m.fBuf.length == 16 then m.flush else m

def MRef.observeBBs (m : MRef) (vs : List ℕ) : MRef := vs.foldl (·.observeBB ·) m

/-- Observe native BN254 digest words: flush pending F, absorb natively in RATE-chunks
with the chunk length as tag (no PF→F→repack detour). -/
def MRef.observeDigest (m : MRef) (words : List Fr) : MRef :=
  let m : MRef := { m with outBuf := [], fSq := [] }
  go m.flush words
where
  go (m : MRef) : List Fr → MRef
    | []             => m
    | [x]            => { m.absorbTag [x] 1 with fSq := [] }
    | x :: y :: rest => go { m.absorbTag [x, y] 2 with fSq := [] } rest

/-- Duplexing with no pending inner input: permute, refill from the rate lanes. -/
def MRef.duplex (m : MRef) : MRef :=
  let st := perm m.st
  { m with st := st, outBuf := [st.a, st.b] }

/-- Sample one canonical BabyBear challenge: flush, refill the limb queue from a
duplexing if drained (splitting every rate cell IN ORDER), pop from the END. -/
def MRef.sampleBB (m : MRef) : ℕ × MRef :=
  let m := m.flush
  let m := if m.fSq.isEmpty then
      let m := if m.outBuf.isEmpty then m.duplex else m
      { m with fSq := (m.outBuf.map splitLimbs).flatten, outBuf := [] }
    else m
  (m.fSq.getLast?.getD 0, { m with fSq := m.fSq.dropLast })

/-- SampleBits: low `n` bits of one canonical BabyBear sample (requires `2^n < p`). -/
def MRef.sampleBits (m : MRef) (n : ℕ) : ℕ × MRef :=
  let (v, m) := m.sampleBB
  (v % 2 ^ n, m)

/-- The fork-executed gold protocol of `multifield_challenger_test.go`: observe [11,22,33]
(partial chunk) → s0,s1,s2 → one native digest word → s3 → a 17-value batch (auto-flush
at 16 incl. `p−1` and `2^30`, one straggler) → s4 → 13 buffered pops → s5 (the pop that
crosses a squeeze-batch boundary) → sampleBits 20. -/
def mfBatch : List ℕ :=
  [2013265920, 1073741824] ++ ((List.range 14).map (100 + ·)) ++ [424242]

def mfDigestWord : Fr := ((12345678901234567890 : ℕ) : Fr)

def mfRefTranscript : List ℕ × ℕ :=
  let m : MRef := {}
  let m := m.observeBBs [11, 22, 33]
  let (s0, m) := m.sampleBB
  let (s1, m) := m.sampleBB
  let (s2, m) := m.sampleBB
  let m := m.observeDigest [mfDigestWord]
  let (s3, m) := m.sampleBB
  let m := m.observeBBs mfBatch
  let (s4, m) := m.sampleBB
  let m := (List.range 13).foldl (fun m _ => (m.sampleBB).2) m
  let (s5, m) := m.sampleBB
  let (idx, _) := m.sampleBits 20
  ([s0, s1, s2, s3, s4, s5], idx)

/-- The six pinned fork-executed challenges (`mfForkKATS`) and 20-bit index. -/
def mfKS : List ℕ := [1330327576, 1916157604, 1399880191, 412774374, 436327734, 1700675939]
def mfKIdx : ℕ := 31374

#guard mfRefTranscript.1 = mfKS
#guard mfRefTranscript.2 = mfKIdx
-- REJECT polarity: tampered absorb kills the first challenge.
#guard ((({} : MRef).observeBBs [12, 22, 33]).sampleBB).1 ≠ mfKS.getD 0 0

/-! ## §5 The op-DAG gadget builder — `Wire` trees with explicit DAG sharing.

A `GW` is a wire together with its value under the canonical assignment being built.
`share` mints a fresh frontend variable carrying that value and asserts the tree equal to
it — one minted var per gnark frontend DAG node; downstream wires reference the var, so
sharing is explicit instead of hash-consed. `mintVar` alone is the hint shape: a
witness-supplied value with only the constraints the caller asserts. -/

/-- A gadget wire: the op-DAG tree plus its value under the canonical assignment. -/
structure GW where
  w : Wire
  v : Fr

structure GB where
  vals    : Array Fr           := #[]
  asserts : Array (Wire × Wire) := #[]

abbrev M := StateM GB

def gconst (c : Fr) : GW := ⟨.const c, c⟩
def gadd (x y : GW) : GW := ⟨.add x.w y.w, x.v + y.v⟩
def gmul (x y : GW) : GW := ⟨.mul x.w y.w, x.v * y.v⟩

/-- Mint a fresh frontend variable carrying `v` (the hint/witness-input shape). -/
def mintVar (v : Fr) : M GW := do
  let b ← get
  set { b with vals := b.vals.push v }
  return ⟨.var b.vals.size, v⟩

/-- `assertIsEqual`. -/
def assertEq (x y : GW) : M Unit :=
  modify fun b => { b with asserts := b.asserts.push (x.w, y.w) }

/-- DAG sharing point: mint a variable for this wire's value and pin the tree to it. -/
def share (g : GW) : M GW := do
  let x ← mintVar g.v
  assertEq g x
  return x

def runBuild (script : M Unit) : Circuit × Assignment :=
  let b := (script.run {}).2
  (⟨b.asserts.toList⟩, fun v => b.vals.getD v 0)

/-- LSB-first binary recomposition `Σ bitsᵢ·2^i` (gnark `FromBinary`), pure linear tree. -/
def gRecompose (bits : List GW) : GW :=
  (bits.foldl (fun (acc : GW × ℕ) b =>
      (gadd acc.1 (gmul b (gconst ((2 ^ acc.2 : ℕ) : Fr))), acc.2 + 1))
    (gconst 0, 0)).1

/-- gnark `ToBinary`: mint `width` witness bit variables (the canonical bits of the
value), assert each boolean (`b·b = b`) and the exact recomposition `Σ bᵢ·2^i = x`.
Exact for canonical values since `x.v.val < 2^width` at every call site. (The ≤ p−1
reducedness side constraint is the named enforcement seam.) -/
def gToBits (x : GW) (width : ℕ) : M (List GW) := do
  let n := x.v.val
  let mut bits : Array GW := #[]
  for i in List.range width do
    let bit ← mintVar ((n / 2 ^ i % 2 : ℕ) : Fr)
    assertEq (gmul bit bit) bit
    bits := bits.push bit
  assertEq (gRecompose bits.toList) x
  return bits.toList

/-! ## §6 The permutation and challenger gadgets — op-DAG mirrors of the Go circuits. -/

abbrev GW3 := GW × GW × GW

def gSbox (x : GW) : GW :=
  let x2 := gmul x x
  let x4 := gmul x2 x2
  gmul x4 x

def gExtLinear (s : GW3) : GW3 :=
  let sum := gadd (gadd s.1 s.2.1) s.2.2
  (gadd s.1 sum, gadd s.2.1 sum, gadd s.2.2 sum)

def gIntLinear (s : GW3) : GW3 :=
  let sum := gadd (gadd s.1 s.2.1) s.2.2
  (gadd s.1 sum, gadd s.2.1 sum, gadd (gmul (gconst 2) s.2.2) sum)

def shareSt (s : GW3) : M GW3 :=
  return (← share s.1, ← share s.2.1, ← share s.2.2)

def gFullRound (rc : Fr × Fr × Fr) (s : GW3) : M GW3 :=
  shareSt (gExtLinear
    (gSbox (gadd s.1 (gconst rc.1)),
     gSbox (gadd s.2.1 (gconst rc.2.1)),
     gSbox (gadd s.2.2 (gconst rc.2.2))))

def gPartialRound (rc : Fr) (s : GW3) : M GW3 :=
  shareSt (gIntLinear (gSbox (gadd s.1 (gconst rc)), s.2.1, s.2.2))

/-- **The in-circuit permutation** (`Poseidon2Bn254`), bound per round. -/
def gPerm (s : GW3) : M GW3 := do
  let s ← shareSt (gExtLinear s)
  let s ← rcExtInitial.foldlM (fun s rc => gFullRound rc s) s
  let s ← rcInternal.foldlM (fun s rc => gPartialRound rc s) s
  rcExtTerminal.foldlM (fun s rc => gFullRound rc s) s

/-- The in-circuit native duplex challenger (`ChallengerBn254`). Buffer discipline is
build-time (Go slices ≙ Lean lists); only field ops hit the circuit. -/
structure GChal where
  st     : GW3
  inBuf  : List GW := []
  outBuf : List GW := []

def GChal.new : GChal := ⟨(gconst 0, gconst 0, gconst 0), [], []⟩

def GChal.duplex (c : GChal) : M GChal := do
  let st : GW3 := match c.inBuf with
    | []          => c.st
    | [x]         => (x, c.st.2.1, c.st.2.2)
    | x :: y :: _ => (x, y, c.st.2.2)
  let st ← gPerm st
  return ⟨st, [], [st.1, st.2.1]⟩

def GChal.observe (c : GChal) (v : GW) : M GChal := do
  let c : GChal := { c with outBuf := [], inBuf := c.inBuf ++ [v] }
  if c.inBuf.length == 2 then c.duplex else pure c

def GChal.sample (c : GChal) : M (GW × GChal) := do
  let c ← if !c.inBuf.isEmpty || c.outBuf.isEmpty then c.duplex else pure c
  return (c.outBuf.getLast?.getD (gconst 0), { c with outBuf := c.outBuf.dropLast })

/-- `SampleBits`: one sample, full-width canonical decomposition (254 bits: `r < 2^254`),
low `n` bits recomposed (`FromBinary` on the low bits). -/
def GChal.sampleBits (c : GChal) (n : ℕ) : M (GW × GChal) := do
  let (base, c) ← c.sample
  let bits ← gToBits base 254
  return (gRecompose (bits.take n), c)

/-- The in-circuit MultiField challenger (`MultiFieldChallenger`), ref-twin shape (the
adapter never routes through the inner observe path, so no inner input buffer). -/
structure GMChal where
  st     : GW3
  outBuf : List GW := []
  fBuf   : List GW := []
  fSq    : List GW := []

def GMChal.new : GMChal := ⟨(gconst 0, gconst 0, gconst 0), [], [], []⟩

/-- PACK in-circuit: little-endian radix-2^31 Horner — a pure linear tree. -/
def gPackLE (vals : List GW) : GW :=
  vals.foldr (fun v acc => gadd (gmul acc (gconst ((2 ^ 31 : ℕ) : Fr))) v) (gconst 0)

/-- SPLIT in-circuit (`splitToFieldOrderLimbs`): 7 limb variables + the remainder minted
as witness (the hint), pinned by the exact recomposition `x = Σ limbᵢ·p^i + r·p^7`.
Canonicity range checks and the lexicographic bound are the named enforcement seam. -/
def gSplit (x : GW) : M (List GW) := do
  let n := x.v.val
  let mut limbs : Array GW := #[]
  for i in List.range 7 do
    limbs := limbs.push (← mintVar ((n / bbP ^ i % bbP : ℕ) : Fr))
  let r ← mintVar ((n / bbP ^ 7 : ℕ) : Fr)
  let recomb := (limbs.toList.foldl (fun (acc : GW × ℕ) l =>
      (gadd acc.1 (gmul l (gconst ((bbP ^ acc.2 : ℕ) : Fr))), acc.2 + 1))
    (gconst 0, 0)).1
  assertEq x (gadd recomb (gmul r (gconst ((bbP ^ 7 : ℕ) : Fr))))
  return limbs.toList

def GMChal.absorbTag (m : GMChal) (values : List GW) (tag : ℕ) : M GMChal := do
  let st ← gPerm
    (values.getD 0 (gconst 0), values.getD 1 (gconst 0),
     gadd m.st.2.2 (gconst ((tag : ℕ) : Fr)))
  return { m with st := st, outBuf := [st.1, st.2.1] }

def GMChal.flush (m : GMChal) : M GMChal := do
  if m.fBuf.isEmpty then return m
  let packed := if m.fBuf.length ≤ 8 then [gPackLE m.fBuf]
                else [gPackLE (m.fBuf.take 8), gPackLE (m.fBuf.drop 8)]
  let m' ← m.absorbTag packed m.fBuf.length
  return { m' with fBuf := [], fSq := [] }

def GMChal.observeBB (m : GMChal) (v : GW) : M GMChal := do
  let m : GMChal := { m with outBuf := [], fSq := [], fBuf := m.fBuf ++ [v] }
  if m.fBuf.length == 16 then m.flush else pure m

def GMChal.observeBBs (m : GMChal) (vs : List GW) : M GMChal :=
  vs.foldlM (·.observeBB ·) m

def GMChal.observeDigest (m : GMChal) (words : List GW) : M GMChal := do
  let m : GMChal := { m with outBuf := [], fSq := [] }
  go (← m.flush) words
where
  go (m : GMChal) : List GW → M GMChal
    | []             => pure m
    | [x]            => do return { (← m.absorbTag [x] 1) with fSq := [] }
    | x :: y :: rest => do go { (← m.absorbTag [x, y] 2) with fSq := [] } rest

def GMChal.duplex (m : GMChal) : M GMChal := do
  let st ← gPerm m.st
  return { m with st := st, outBuf := [st.1, st.2.1] }

def GMChal.sampleBB (m : GMChal) : M (GW × GMChal) := do
  let m ← m.flush
  let m ← if m.fSq.isEmpty then do
      let m ← if m.outBuf.isEmpty then m.duplex else pure m
      let mut sq : List GW := []
      for pf in m.outBuf do
        sq := sq ++ (← gSplit pf)
      pure { m with fSq := sq, outBuf := [] }
    else pure m
  return (m.fSq.getLast?.getD (gconst 0), { m with fSq := m.fSq.dropLast })

/-- `SampleBits`: one BabyBear sample (canonical, `< p < 2^31`), 31-bit exact
decomposition, low `n` bits recomposed. -/
def GMChal.sampleBits (m : GMChal) (n : ℕ) : M (GW × GMChal) := do
  let (base, m) ← m.sampleBB
  let bits ← gToBits base 31
  return (gRecompose (bits.take n), m)

/-! ## §7 The KAT circuits — the gadgets run the pinned transcripts in-circuit.

Satisfaction of the built circuit under its canonical assignment checks BOTH that every
bound op-DAG node re-evaluates to its minted value (the whole arithmetic chain, permutation
included) AND that the final challenge wires equal the PINNED constants — the in-circuit
bit-exactness KAT. Tampered variants must be UNSATISFIABLE. -/

/-- The native-challenger KAT script, parameterized so tampered variants share the
builder: absorb `a0`,22,33 → 3 challenges → absorb 44 → challenge → 16-bit index,
each pinned by `assertIsEqual` against the expected constants. -/
def bnScript (a0 : Fr) (e0 e1 e2 e3 : Fr) (eIdx : Fr) : M Unit := do
  let c := GChal.new
  let c ← c.observe (gconst a0)
  let c ← c.observe (gconst 22)
  let c ← c.observe (gconst 33)
  let (s0, c) ← c.sample
  assertEq s0 (gconst e0)
  let (s1, c) ← c.sample
  assertEq s1 (gconst e1)
  let (s2, c) ← c.sample
  assertEq s2 (gconst e2)
  let c ← c.observe (gconst 44)
  let (s3, c) ← c.sample
  assertEq s3 (gconst e3)
  let (idx, _) ← c.sampleBits 16
  assertEq idx (gconst eIdx)

/-- The built native-challenger KAT circuit + canonical assignment (gold constants). -/
def bnKATBuilt : Circuit × Assignment :=
  runBuild (bnScript 11 bnKS0 bnKS1 bnKS2 bnKS3 ((bnKIdx : ℕ) : Fr))

-- ACCEPT: the gadget reproduces the deployed KAT bit-exactly, in-circuit.
#guard bnKATBuilt.1.satisfied bnKATBuilt.2
-- REJECT: tampered challenge / tampered transcript / tampered index.
#guard ¬ (let t := runBuild (bnScript 11 bnKS0 (bnKS1 + 1) bnKS2 bnKS3 ((bnKIdx : ℕ) : Fr));
          t.1.satisfied t.2)
#guard ¬ (let t := runBuild (bnScript 12 bnKS0 bnKS1 bnKS2 bnKS3 ((bnKIdx : ℕ) : Fr));
          t.1.satisfied t.2)
#guard ¬ (let t := runBuild (bnScript 11 bnKS0 bnKS1 bnKS2 bnKS3 ((bnKIdx + 1 : ℕ) : Fr));
          t.1.satisfied t.2)

/-- The MultiField gold-KAT script (the full fork-executed protocol in-circuit). -/
def mfScript (a0 : ℕ) (e : List ℕ) (eIdx : ℕ) : M Unit := do
  let m := GMChal.new
  let m ← m.observeBBs [gconst ((a0 : ℕ) : Fr), gconst 22, gconst 33]
  let (s0, m) ← m.sampleBB
  assertEq s0 (gconst ((e.getD 0 0 : ℕ) : Fr))
  let (s1, m) ← m.sampleBB
  assertEq s1 (gconst ((e.getD 1 0 : ℕ) : Fr))
  let (s2, m) ← m.sampleBB
  assertEq s2 (gconst ((e.getD 2 0 : ℕ) : Fr))
  let m ← m.observeDigest [gconst mfDigestWord]
  let (s3, m) ← m.sampleBB
  assertEq s3 (gconst ((e.getD 3 0 : ℕ) : Fr))
  let m ← m.observeBBs (mfBatch.map fun v => gconst ((v : ℕ) : Fr))
  let (s4, m) ← m.sampleBB
  assertEq s4 (gconst ((e.getD 4 0 : ℕ) : Fr))
  let m ← (List.range 13).foldlM (fun m _ => do let (_, m) ← m.sampleBB; pure m) m
  let (s5, m) ← m.sampleBB
  assertEq s5 (gconst ((e.getD 5 0 : ℕ) : Fr))
  let (idx, _) ← m.sampleBits 20
  assertEq idx (gconst ((eIdx : ℕ) : Fr))

/-- The built MultiField KAT circuit + canonical assignment (fork gold constants). -/
def mfKATBuilt : Circuit × Assignment := runBuild (mfScript 11 mfKS mfKIdx)

-- ACCEPT: the MultiField gadget reproduces the fork-executed gold KAT, in-circuit.
#guard mfKATBuilt.1.satisfied mfKATBuilt.2
-- REJECT: tampered absorb / tampered post-boundary challenge / tampered index.
#guard ¬ (let t := runBuild (mfScript 12 mfKS mfKIdx); t.1.satisfied t.2)
#guard ¬ (let t := runBuild (mfScript 11 (mfKS.set 5 1700675940) mfKIdx); t.1.satisfied t.2)
#guard ¬ (let t := runBuild (mfScript 11 mfKS (mfKIdx + 1)); t.1.satisfied t.2)

/-! ## §8 Down to genuine R1CS — the permutation gadget through `Circuit.lower`.

One full permutation probe (the zkhash gold vector, in-circuit) is lowered to the real
bilinear-constraint system and checked satisfied by the canonical extension — and REFUTED
when the expected output is tampered. The aux region is materialized once (`probeAux`)
so the guard does not recompute `assertsAux` per lookup; `probeZ` IS `Circuit.extend`
extensionally. -/

def permProbeScript (g0 : Fr) : M Unit := do
  let s ← gPerm (gconst 0, gconst 1, gconst 2)
  assertEq s.1 (gconst g0)
  assertEq s.2.1 (gconst goldPerm.b)
  assertEq s.2.2 (gconst goldPerm.c)

def permProbe : Circuit × Assignment := runBuild (permProbeScript goldPerm.a)
def permProbeBad : Circuit × Assignment := runBuild (permProbeScript (goldPerm.a + 1))

#guard permProbe.1.satisfied permProbe.2
#guard ¬ permProbeBad.1.satisfied permProbeBad.2

def probeAux : List Fr := assertsAux permProbe.2 permProbe.1.asserts
/-- The canonical extended witness for the lowered probe (== `permProbe.1.extend`). -/
def probeZ : RAssignment := fun v => match v with
  | .inl x => permProbe.2 x
  | .inr i => probeAux.getD i 0

def probeBadAux : List Fr := assertsAux permProbeBad.2 permProbeBad.1.asserts
def probeBadZ : RAssignment := fun v => match v with
  | .inl x => permProbeBad.2 x
  | .inr i => probeBadAux.getD i 0

-- The REAL R1CS of the permutation gadget: satisfied at the gold vector, refuted off it.
#guard r1csSatisfied permProbe.1.lower probeZ
#guard ¬ r1csSatisfied permProbeBad.1.lower probeBadZ

/-! ## §9 Soundness instantiations — no adversarial aux filling fakes the transcript.

`lower_sound` at the BUILT gadget circuits: ANY R1CS witness for the lowered KAT circuit
agreeing with the canonical assignment on the frontend variables forces frontend
satisfaction — the minted constraints pin the whole aux region. -/

theorem bnKAT_no_aux_forgery (z : RAssignment)
    (hz : ∀ v, z (.inl v) = bnKATBuilt.2 v)
    (h : r1csSatisfied bnKATBuilt.1.lower z) :
    bnKATBuilt.1.satisfied bnKATBuilt.2 :=
  lower_sound _ _ _ hz h

theorem mfKAT_no_aux_forgery (z : RAssignment)
    (hz : ∀ v, z (.inl v) = mfKATBuilt.2 v)
    (h : r1csSatisfied mfKATBuilt.1.lower z) :
    mfKATBuilt.1.satisfied mfKATBuilt.2 :=
  lower_sound _ _ _ hz h

theorem permProbe_no_aux_forgery (z : RAssignment)
    (hz : ∀ v, z (.inl v) = permProbe.2 v)
    (h : r1csSatisfied permProbe.1.lower z) :
    permProbe.1.satisfied permProbe.2 :=
  lower_sound _ _ _ hz h

#assert_all_clean [bnKAT_no_aux_forgery, mfKAT_no_aux_forgery, permProbe_no_aux_forgery]

end Dregg2.Circuit.ChallengerFr
