/-
# Dregg2.Circuit.BytesLanes — THE INJECTIVE VARIABLE-LENGTH BYTE→LANE ENCODER

## SUBSTRATE, SAID OUT LOUD

⚠ **This is NOT AIR material and nothing here is a constraint.** `hash_bytes` is a HOST-SIDE
sponge; measured 2026-08-01 across `metatheory/`, no emitted descriptor recomputes a byte packing —
every Lean hash carrier is felt- or `Nat`-domain (`hash : List ℤ → ℤ`), the "in-AIR `hash_bytes`
recompute" named at `circuit/src/effect_vm/authority_digest_weld.rs:54` is a felt-domain chip
lookup over two floor felts, and `InAirAuthorityDigestSelector.lean:42` calls the byte-sponge
version *"the named, genuinely-VK-affecting remaining work"* — i.e. NOT BUILT.

So the file this belongs beside is `FieldLanes9`, not an `Emit/*`: it authors an ENCODER with a
total decoder and a machine-checked left inverse, and the Rust twin is pinned to it by
Lean-COMPUTED `#guard` vectors plus a round-trip sweep. That is the `Faithful9` rung — *"evidence
that the value came from a Rust encoder pinned to a verified spec by Lean-computed KAT vectors and
a round-trip sweep, not from a verified encoder"* — and it must be described at exactly that
resolution.

⚑ **AND THE DEFERRAL THIS REFUTES.** The wound below was left open on the ground that *"`hash_bytes`
is an in-AIR recompute, so the primitive is emit-owned."* It is not emit-owned. Nothing emits it.

## THE WOUND: `hash_bytes` is not injective on its input, in TWO independent ways

`circuit/src/poseidon2.rs:566` is `hash_many(BabyBear::from_bytes_packed(data))`, and

  * `from_bytes_packed` (`circuit/src/field.rs:188`) walks the input in 4-byte strides and
    ZERO-FILLS the final partial chunk (`for j in 0..4 { if i + j < bytes.len() { … } }`), while
    `hash_many` (`circuit/src/poseidon2.rs:381`) tags `state[4] = inputs.len()` — the FELT count,
    not the byte count. So appending NUL bytes up to the next multiple of four changes nothing:
    `hash_bytes(b"foo") = hash_bytes(b"foo\0")` and `hash_bytes(b"f") = hash_bytes(b"f\0\0\0")`.
    **Cost 0. Not a search — an append.**
  * each 4-byte chunk becomes `BabyBear::new(val)`, a `u32` reduced mod `p = 2013265921 < 2^32`.
    `2^32 - p = 2281701375`, so every chunk value `x < 2281701375` — **53.1% of all `u32`s** — has
    a sibling `x + p` with the identical felt. **Also cost 0**, and this one bites FIXED-length
    inputs too, where the padding wound does not.

Named consumers, all COMMITTED: `sandstorm-bridge/src/cell.rs:66,78` (`var_addr` / `var_value_felt`
— a grain's `/var` heap address and leaf value, so *serve `value ‖ "\0"` and the inclusion proof
still verifies*), `storage/src/bucket_commitment.rs:122`, `starbridge-apps/site-host/src/site.rs:187`,
`zkoracle-prove/src/attestation.rs:48` (the whole HTTP response body), `wasm/src/lib.rs:647`
(reaches `PI_FACT_COMMITMENT`).

## THE REPLACEMENT, and why it is `2^16` rather than nine base-`2^29` digits

⚠ **GET THE PRIMITIVE RIGHT PER JOB.** `KeyLanes9` needed the MINIMUM-WIDTH injective encoding
because its lanes are PERSISTENT COLUMNS in the rotated block and every column costs 174 members'
worth of trace. These lanes are an ABSORBED PREIMAGE — they exist for one sponge call and are never
stored — so width is nearly free and the right axis is byte-alignment and a total decoder.
`docs/DESIGN-canonical-byte-felt-codec.md` §2.6 already designated that codec: **`Limbs16`, sixteen
little-endian `u16` limbs**, promoted into `dregg-codec`. This file is that codec at VARIABLE
length, which `dregg_codec::Limbs16` (32 bytes, fixed) does not cover.

```text
  bytesToLanes bs = lenLanes bs.length ++ u16LanesLE bs
```

  * `lenLanes n` — the byte count as FOUR base-`2^16` digits. The BYTE count, which is the thing the
    old tag was not; four digits so the header is total to `2^64` bytes rather than correct-in-practice.
  * `u16LanesLE bs` — the bytes in little-endian pairs, `⌈len/2⌉` lanes, the final lane's high byte
    zero when the length is odd. `2^16 ≪ p`, so **NO lane ever reduces** and the mod-`p` alias above
    is not merely narrowed, it is structurally absent.

The zero-padding of that final lane is exactly what the old packer also did — the difference is that
here the LENGTH HEADER disambiguates it, which is the whole content of `lanesToBytes_bytesToLanes`.

`lanesToBytes` is TOTAL (defined on every lane list, including ones no encoder produced) and is a
LEFT INVERSE on every byte string shorter than `2^64`; `bytesToLanes_injective` is the corollary.
**Not a hash bound, not a birthday bound** — an injection with a machine-checked inverse.

## ⚠ WHAT THIS DOES NOT CLOSE — say the residual out loud, with its bound

Fixing the preimage closes the **`O(1)` preimage-collision** class ENTIRELY and closes nothing else.
`hash_bytes` still SQUEEZES ONE FELT, and one BabyBear felt is `log₂ p = 30.907` bits, so a
collision by unstructured search costs the birthday bound

```text
  2^(30.906891 / 2)  =  2^15.4534   ≈  44,900 evaluations
```

— milliseconds. `docs/DESIGN-canonical-byte-felt-codec.md` §2.3 BANS that shape by name (*"`Digest1`
— any 32-byte value compressed to a single felt … There is no security boundary where that is
acceptable"*). It is a DIFFERENT defect from this one and neither fix reaches the other: no
widening of the squeeze removes an append-collision in the preimage, and no repair of the preimage
removes a birthday collision in a 31-bit codomain. Its fix is the heap/IMT VALUE widening (the
`HeapLeaf.value : BabyBear` field, and with it the `MapOp` value width in the emitted AIR) — a
constraint change, owned by that campaign, and NOT a later phase of this one.

`hashBytes8Lanes` below is the 8-felt companion for the sites that can already take it
(`2^123.63` birthday over `p^8`); the sites that cannot are the ones the widening campaign owns.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. No `sorry`, no `native_decide`.
-/
import Mathlib.Tactic
import Mathlib.Data.List.GetD
import Dregg2.Circuit.FieldLanes9
import Dregg2.Tactics

namespace Dregg2.Circuit.BytesLanes

set_option autoImplicit false
set_option linter.unusedVariables false

open Dregg2.Circuit.FieldLanes9 (P ofDigits digitsN ofDigits_digitsN digitsN_length digitsN_lt)

/-! ## §1 — the lane radix.

`2^16 = 65536`, and `65536 < 2013265921 = P`. That single inequality is the whole reason no lane
ever reduces, which is the whole reason the mod-`p` alias of the deployed packer cannot recur. -/

/-- The lane radix, `2^16`. -/
def U16 : Nat := 65536

theorem U16_lt_P : U16 < P := by decide

/-- A byte, as the deployed `u8`. -/
abbrev Byte := Fin 256

/-! ## §2 — THE ENCODER. -/

/-- The bytes in little-endian PAIRS: `[b₀ + 256·b₁, b₂ + 256·b₃, …]`, with the final lane's high
byte zero when the length is odd. Every lane is `< 2^16`. -/
def u16LanesLE : List Nat → List Nat
  | [] => []
  | [a] => [a]
  | a :: b :: rest => (a + 256 * b) :: u16LanesLE rest

/-- The BYTE count as four base-`2^16` digits — total to `2^64` bytes. ⚑ This is the header the
deployed primitive does not have: `hash_many`'s `state[4]` carries the FELT count, which is exactly
the quantity a NUL-append leaves fixed. -/
def lenLanes (n : Nat) : List Nat := digitsN U16 4 n

theorem lenLanes_length (n : Nat) : (lenLanes n).length = 4 := digitsN_length _ _ _

/-- **THE ENCODER.** Length header, then the little-endian `u16` lanes. -/
def bytesToLanes (bs : List Nat) : List Nat := lenLanes bs.length ++ u16LanesLE bs

/-! ### Every lane is below the radix, hence below `P` — nothing reduces. -/

theorem u16LanesLE_lt : ∀ (bs : List Nat), (∀ x ∈ bs, x < 256) →
    ∀ y ∈ u16LanesLE bs, y < U16 := by
  intro bs
  induction bs using u16LanesLE.induct with
  | case1 => intro _ y hy; simp [u16LanesLE] at hy
  | case2 a =>
    intro h y hy
    have ha := h a (by simp)
    simp only [u16LanesLE, List.mem_cons, List.not_mem_nil, or_false] at hy
    subst hy
    simp only [U16]; omega
  | case3 a b rest ih =>
    intro h y hy
    simp only [u16LanesLE, List.mem_cons] at hy
    rcases hy with rfl | hy
    · have ha := h a (by simp)
      have hb := h b (by simp)
      simp only [U16]; omega
    · exact ih (fun z hz => h z (by simp [hz])) y hy

theorem lenLanes_lt (n : Nat) : ∀ x ∈ lenLanes n, x < U16 :=
  digitsN_lt U16 (by decide) 4 n

/-- **NO LANE EVER REDUCES.** Every emitted lane is a genuine `u16`, so the deployed
`BabyBear::new(lane)` is the identity on it — the `x` vs `x + p` alias of `from_bytes_packed`
cannot occur at any lane of this encoder. -/
theorem bytesToLanes_lt_U16 {bs : List Nat} (h : ∀ x ∈ bs, x < 256) :
    ∀ x ∈ bytesToLanes bs, x < U16 := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact lenLanes_lt _ x hx
  · exact u16LanesLE_lt bs h x hx

theorem bytesToLanes_lt_P {bs : List Nat} (h : ∀ x ∈ bs, x < 256) :
    ∀ x ∈ bytesToLanes bs, x < P :=
  fun x hx => lt_trans (bytesToLanes_lt_U16 h x hx) U16_lt_P

/-! ## §3 — THE DECODER: total, explicit, and the inverse. -/

/-- Each lane back to its two little-endian bytes. Total on EVERY lane list — a lane an encoder
never produced (one `≥ 2^16`) is read modulo `2^16`, which is what makes this a function rather
than a partial one. -/
def lanesToBytesAux : List Nat → List Nat
  | [] => []
  | l :: rest => (l % 256) :: (l / 256 % 256) :: lanesToBytesAux rest

/-- **THE DECODER.** Read the length header, decode the pairs, keep exactly that many bytes. -/
def lanesToBytes (L : List Nat) : List Nat :=
  (lanesToBytesAux (L.drop 4)).take (ofDigits U16 (L.take 4))

theorem lanesToBytesAux_length (L : List Nat) :
    (lanesToBytesAux L).length = 2 * L.length := by
  induction L with
  | nil => rfl
  | cons l rest ih => simp [lanesToBytesAux, ih]; omega

/-- The pair decode undoes the pair encode, up to the ONE zero byte an odd length pads with. Stated
as a `take`, which is what the length header then discharges. -/
theorem lanesToBytesAux_u16LanesLE : ∀ (bs : List Nat), (∀ x ∈ bs, x < 256) →
    (lanesToBytesAux (u16LanesLE bs)).take bs.length = bs := by
  intro bs
  induction bs using u16LanesLE.induct with
  | case1 => intro _; rfl
  | case2 a =>
    intro h
    have ha := h a (by simp)
    simp only [u16LanesLE, lanesToBytesAux, List.length_cons, List.length_nil]
    rw [Nat.mod_eq_of_lt ha, Nat.div_eq_of_lt ha]
    rfl
  | case3 a b rest ih =>
    intro h
    have ha := h a (by simp)
    have hb := h b (by simp)
    have hrest : ∀ x ∈ rest, x < 256 := fun y hy => h y (by simp [hy])
    have hlo : (a + 256 * b) % 256 = a := by omega
    have hhi : (a + 256 * b) / 256 % 256 = b := by omega
    simp only [u16LanesLE, lanesToBytesAux, hlo, hhi, List.length_cons]
    rw [show rest.length + 1 + 1 = rest.length + 2 from rfl, List.take_succ_cons,
      List.take_succ_cons]
    rw [ih hrest]

/-- **THE LEFT INVERSE.** Every byte string shorter than `2^64` round-trips through the lanes.

⚑ **THIS IS THE ANTI-VACUITY STATEMENT.** It says the VALUE comes back, not that two encodings
differ — a scrambling "repair" satisfies a difference-only test and fails this one. -/
theorem lanesToBytes_bytesToLanes {bs : List Nat} (h : ∀ x ∈ bs, x < 256)
    (hlen : bs.length < U16 ^ 4) :
    lanesToBytes (bytesToLanes bs) = bs := by
  have htake : (bytesToLanes bs).take 4 = lenLanes bs.length :=
    List.take_left' (lenLanes_length _)
  have hdrop : (bytesToLanes bs).drop 4 = u16LanesLE bs :=
    List.drop_left' (lenLanes_length _)
  have hhdr : ofDigits U16 (lenLanes bs.length) = bs.length :=
    ofDigits_digitsN U16 (by decide) 4 bs.length hlen
  simp only [lanesToBytes, htake, hdrop, hhdr]
  exact lanesToBytesAux_u16LanesLE bs h

/-- **THE THEOREM.** The variable-length byte encoder is INJECTIVE on byte strings shorter than
`2^64`: no two distinct inputs share a lane vector. In particular a NUL-append changes the lanes,
which is precisely what the deployed `hash_bytes` preimage does not do. -/
theorem bytesToLanes_injective {a b : List Nat}
    (ha : ∀ x ∈ a, x < 256) (hb : ∀ x ∈ b, x < 256)
    (hla : a.length < U16 ^ 4) (hlb : b.length < U16 ^ 4)
    (h : bytesToLanes a = bytesToLanes b) : a = b := by
  have := congrArg lanesToBytes h
  rwa [lanesToBytes_bytesToLanes ha hla, lanesToBytes_bytesToLanes hb hlb] at this

#assert_axioms lanesToBytesAux_u16LanesLE
#assert_axioms lanesToBytes_bytesToLanes
#assert_axioms bytesToLanes_injective
#assert_axioms bytesToLanes_lt_U16

/-! ## §4 — ⚑ THE OLD PRIMITIVE, AS A LEAN TWIN, AND ITS TWO COLLISIONS EXHIBITED.

`from_bytes_packed` byte-for-byte: 4-byte little-endian strides, the final partial chunk zero-filled,
each chunk reduced mod `P`. Written here so the OLD-ADMITS half of the old-admits/new-rejects pair
is a machine-checked exhibit over the deployed shape rather than a sentence about it. -/

/-- The deployed packer's per-chunk value, before the `mod P`: `b₀ | b₁<<8 | b₂<<16 | b₃<<24` over
whatever prefix of four bytes remains, MISSING BYTES READ AS ZERO. -/
def packedChunk : List Nat → Nat
  | [] => 0
  | [a] => a
  | [a, b] => a + 256 * b
  | [a, b, c] => a + 256 * b + 65536 * c
  | a :: b :: c :: d :: _ => a + 256 * b + 65536 * c + 16777216 * d

/-- **THE DEPLOYED PACKER**, `circuit/src/field.rs:188`, as a Lean twin. Written out four-at-a-time
so the recursion is STRUCTURAL and the exhibits below reduce under `decide` — a `drop 3` phrasing is
the same function but needs well-founded recursion, which does not compute in the kernel. -/
def fromBytesPacked : List Nat → List Nat
  | [] => []
  | [a] => [a % P]
  | [a, b] => [(a + 256 * b) % P]
  | [a, b, c] => [(a + 256 * b + 65536 * c) % P]
  | a :: b :: c :: d :: rest =>
      ((a + 256 * b + 65536 * c + 16777216 * d) % P) :: fromBytesPacked rest

/-- The deployed preimage of `hash_bytes`: the packed felts, and `hash_many`'s domain tag is their
COUNT. So two inputs collide under `hash_bytes` as soon as these two agree. -/
def legacyPreimage (bs : List Nat) : List Nat × Nat :=
  (fromBytesPacked bs, (fromBytesPacked bs).length)

/-! ### Exhibit 1 — the NUL-append. Cost 0: one byte. -/

/-- `b"foo"`. -/
def foo : List Nat := [102, 111, 111]
/-- `b"foo\0"`. -/
def fooNul : List Nat := [102, 111, 111, 0]
/-- `b"f"`. -/
def f1 : List Nat := [102]
/-- `b"f\0\0\0"`. -/
def f1Nul3 : List Nat := [102, 0, 0, 0]

/-- **OLD ADMITS.** Two DISTINCT byte strings with an IDENTICAL deployed preimage — identical felt
list AND identical felt count, so `hash_bytes` agrees on the nose. Both pairs are the exact
equalities a prior lane ran in Rust; here they are decided over the twin. -/
theorem legacy_admits_the_nul_append :
    foo ≠ fooNul ∧ legacyPreimage foo = legacyPreimage fooNul
    ∧ f1 ≠ f1Nul3 ∧ legacyPreimage f1 = legacyPreimage f1Nul3 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- **NEW REJECTS.** The same two pairs SEPARATE under `bytesToLanes` — and not by accident of the
tail: the LENGTH HEADER differs in lane 0. -/
theorem nonet_rejects_the_nul_append :
    bytesToLanes foo ≠ bytesToLanes fooNul
    ∧ bytesToLanes f1 ≠ bytesToLanes f1Nul3
    ∧ (bytesToLanes foo).getD 0 0 = 3 ∧ (bytesToLanes fooNul).getD 0 0 = 4 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-! ### Exhibit 2 — the mod-`P` chunk alias. Cost 0, and it bites FIXED lengths too.

`P = 2013265921 = 0x78000001`, so the four bytes `01 00 00 78` pack to exactly `P` and reduce to
`0`, colliding with `00 00 00 00`. Same length, same felt count — the length header of §2 does NOT
save the old packer here, which is why the repair had to change the RADIX and not merely add a tag. -/

/-- Four zero bytes. -/
def zero4 : List Nat := [0, 0, 0, 0]
/-- The four bytes that pack to exactly `P` and reduce to `0`. -/
def pAlias4 : List Nat := [1, 0, 0, 120]

/-- **OLD ADMITS, AT EQUAL LENGTH.** Two distinct FOUR-byte strings whose deployed preimages are
identical, so no length tag of any kind could separate them. -/
theorem legacy_admits_the_modP_alias :
    zero4 ≠ pAlias4
    ∧ packedChunk pAlias4 = P
    ∧ legacyPreimage zero4 = legacyPreimage pAlias4 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **NEW REJECTS.** They separate under `bytesToLanes`, because `2^16 < P` means no lane reduces. -/
theorem nonet_rejects_the_modP_alias :
    bytesToLanes zero4 ≠ bytesToLanes pAlias4 := by decide

/-- **THE VERDICT**, in one proposition so a reader cannot take the pleasant half: the deployed
preimage conflates strings by APPENDING and by ADDING `P`; the replacement does neither, and it is
injective rather than merely different. -/
theorem bytes_preimage_verdict :
    (∃ a b : List Nat, a ≠ b ∧ legacyPreimage a = legacyPreimage b)
    ∧ (∃ a b : List Nat, a ≠ b ∧ a.length = b.length ∧ legacyPreimage a = legacyPreimage b)
    ∧ (∀ a b : List Nat, (∀ x ∈ a, x < 256) → (∀ x ∈ b, x < 256) →
        a.length < U16 ^ 4 → b.length < U16 ^ 4 →
        bytesToLanes a = bytesToLanes b → a = b) := by
  refine ⟨⟨foo, fooNul, by decide, by decide⟩,
    ⟨zero4, pAlias4, by decide, by decide, by decide⟩,
    fun a b ha hb hla hlb h => bytesToLanes_injective ha hb hla hlb h⟩

#assert_axioms legacy_admits_the_nul_append
#assert_axioms nonet_rejects_the_nul_append
#assert_axioms legacy_admits_the_modP_alias
#assert_axioms nonet_rejects_the_modP_alias
#assert_axioms bytes_preimage_verdict

/-! ## §5 — Lean-COMPUTED protocol vectors.

⚑ COMPUTED BY LEAN, not transcribed from a Rust run. `circuit/tests/bytes_lanes_injective.rs`
asserts the deployed `bytes_to_lanes` reproduces them AND that `lanes_to_bytes` returns the VALUE —
round-trip, not "the digests differ". -/

/-- `b"grain/var/value:v1\0"` — the deployed `VAR_VALUE_DOMAIN` of `sandstorm-bridge/src/cell.rs:56`,
19 bytes, so its length is ODD and its final lane is the zero-padded one. -/
def varValueDomain : List Nat :=
  [103, 114, 97, 105, 110, 47, 118, 97, 114, 47, 118, 97, 108, 117, 101, 58, 118, 49, 0]

#guard bytesToLanes [] = [0, 0, 0, 0]
#guard bytesToLanes [255] = [1, 0, 0, 0, 255]
#guard bytesToLanes [255, 255] = [2, 0, 0, 0, 65535]
#guard bytesToLanes foo = [3, 0, 0, 0, 28518, 111]
#guard bytesToLanes fooNul = [4, 0, 0, 0, 28518, 111]
#guard bytesToLanes zero4 = [4, 0, 0, 0, 0, 0]
#guard bytesToLanes pAlias4 = [4, 0, 0, 0, 1, 30720]

/-! The 19-byte domain tag: 4 header lanes + 10 pair lanes, the last high byte the odd pad. -/
#guard (bytesToLanes varValueDomain).length = 14
#guard bytesToLanes varValueDomain
  = [19, 0, 0, 0, 29287, 26977, 12142, 24950, 12146, 24950, 30060, 14949, 12662, 0]

/-! The length header really is four `u16` digits of the BYTE count — a 70000-byte body needs the
second digit, which a one-felt header would still hold but a `u16` one would not. -/
#guard lenLanes 70000 = [4464, 1, 0, 0]
#guard ofDigits U16 (lenLanes 70000) = 70000

/-! ROUND-TRIP, computed: the decoder returns the VALUE. -/
#guard lanesToBytes (bytesToLanes foo) = foo
#guard lanesToBytes (bytesToLanes fooNul) = fooNul
#guard lanesToBytes (bytesToLanes varValueDomain) = varValueDomain
#guard lanesToBytes (bytesToLanes []) = []
#guard lanesToBytes (bytesToLanes [255]) = [255]

/-! The deployed packer, for the pair — identical lists, identical counts. -/
#guard fromBytesPacked foo = fromBytesPacked fooNul
#guard fromBytesPacked zero4 = fromBytesPacked pAlias4
#guard (fromBytesPacked foo).length = (fromBytesPacked fooNul).length

end Dregg2.Circuit.BytesLanes
