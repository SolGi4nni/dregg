/-
# `Dregg2.Crypto.MlKemKeygenRefine` — the BYTE↔RING ML-KEM-768 KeyGen refinement, ∀ (proven).

`MlKemKeygen` states the OPEN obligation `kpkeKeyGen_refines_ring`: decoding the byte-level `ek`/`dkPKE` that
`kpkeKeyGen` emits recovers EXACTLY the ring-level `(t̂, ŝ, ρ)` that the abstract `kpkeKeyGenRing` computes.
This module DISCHARGES it — a genuine `∀`-refinement whose spec side is the RING generator (sample / NTT /
matvec), NOT the byte implementation restated. It rides:

* the codec round-trip `MlKemCodecSpec.byteDecodeAt_byteEncode` (`byteDecode ∘ byteEncode = id` for size-256
  polys with coeffs below the effective modulus — here `q`, the `ByteDecode₁₂` codomain), through
* the per-coefficient BOUND `t̂[i]!, ŝ[i]! < q` — `t̂[i] = addPoly _ _` is `< q` unconditionally
  (`MlKemRing.addPoly_lt`); `ŝ[i] = NTT(sᵢ)` is `< q` because `sᵢ = SamplePolyCBD` is a canonical `R_q`
  element (`samplePolyCBD_lt`/`_size`) and `NTT` preserves the `< q` codomain (`MlKemRing.ntt_lt`/`_size`),
* the block-append offset engine (`appendFold_spec` + `byteDecodeAt_eq_of_window`: `byteDecodeAt` reads only
  its `polyBytes d`-byte window, so a decode at interior offset `i·384` reads exactly the block `byteEncode`
  wrote there), and the `sha3_512` fixed 64-byte output length (so `ρ = G(d‖k).take 32` has length 32).

The `ρ`-length leg is no longer assumed. §0 proves the FIPS 202 `∀`-fact `squeeze_length` — `Keccak.squeeze`
returns EXACTLY `outLen` bytes, for every positive rate, sponge state and length — by a manual
`forIn`/`ForInStep` induction through the sponge's two-mutable-variable `Id.run do` block (the between-block
`keccakF` sits under an `if` that touches only the state, never the output, so the `out.size` step is
unconditional). `sha3_512_length` and `rhoOf_length` follow, and `kpkeKeyGen_refines_ring` is UNCONDITIONAL.

The byte↔ring bridge is DEFINITIONAL: `kpkeKeyGen` IS `kpkeKeyGenRing` composed with the codec
(`kpkeKeyGen_ek_eq` / `kpkeKeyGen_dk_eq`, both `rfl`), so `kpkeKeyGen_refines_ring` is a real byte-vs-ring
statement, not an identity. No `sorry`, no user `axiom`; the ∀-theorems are `#assert_axioms`-clean.
Public references: NIST FIPS 202 (SHA-3/Keccak), FIPS 203 (ML-KEM) §4.2.1 / §6 / §8.
-/
import Dregg2.Crypto.MlKemKeygen
import Dregg2.Crypto.MlKemCodecSpec
import Dregg2.Crypto.MlKemFips203FullDim
import Dregg2.Crypto.Keccak
import Dregg2.Tactics
import Mathlib

namespace Dregg2.Crypto.MlKemKeygenRefine

open Dregg2.Crypto.MlKemRing (Poly q zeroPoly ntt pointwiseNtt addPoly)
open Dregg2.Crypto.MlKemSample (expandMatrix samplePolyCBD)
open Dregg2.Crypto.MlKemCodec (paramK dCoeff polyBytes ekLen byteEncode byteDecodeAt byteDecode
  ekEncode ekDecode bytesToNatLE)
open Dregg2.Crypto.MlKemCodecSpec (arrayExtAll bytesToNatLE_eq byteDecodeAt_getElem byteDecodeAt_size
  byteDecodeAt_byteEncode decMod byteEncode_size)
open Dregg2.Crypto.MlKemDecaps (sha3_512 prf)
open Dregg2.Crypto.MlKemKeygen (kpkeKeyGen kpkeKeyGenRing)
open Dregg2.Crypto.Keccak (squeeze keccakF)

set_option maxRecDepth 8000

/-! ## §0 — THE FIPS 202 SQUEEZE-LENGTH FACT: `|SHAKE/SHA-3 output| = outLen`, ∀.

`ρ = G(d‖k).take 32` is only 32 bytes long because `G = SHA3-512` really emits 64. That is a `∀`-fact about
`Keccak.squeeze`, and it is the last side condition standing between `kpkeKeyGen_refines_ring_of_rholen` and
the UNCONDITIONAL `kpkeKeyGen_refines_ring`. It is proved here, from the definition of `squeeze` — no `native_decide`, no KAT, no hypothesis.

**Why it is not a one-liner.** `Keccak.squeeze` is an `Id.run do` block with TWO mutable variables (`out` and
the sponge state `s`), so the do-elaborator threads an `MProd (Array UInt8) (Array UInt64)` accumulator through
`forIn`; and the between-block permutation sits under a `if blk + 1 < nblocks then … else …` INSIDE the loop
body. That `if` blocks the usual `List.forIn_pure_yield_eq_foldl` normalisation, because the body is not
syntactically `pure (.yield …)`. The route below is therefore a manual `forIn`/`ForInStep` induction
(`forIn_id_measure`): it only needs that every iteration is a `yield` of some pure step function, and that the
step grows the measure `out.size` by exactly `rate` — which holds UNCONDITIONALLY, since the `if` touches only
`s`, never `out`.

Public reference: NIST FIPS 202 §4 (sponge), §6.2 (SHAKE) — the squeeze phase emits `⌈outLen/rate⌉` rate-byte
blocks and truncates to `outLen`. -/

/-- **The generic `Id`-monad `forIn` measure induction.** If every iteration of a `List.forIn` in `Id` is a
`yield` of a pure step function `g`, and `g` grows the `ℕ`-valued measure `sz` by exactly `k`, then the whole
loop grows `sz` by `l.length * k`. The point: `g` may branch internally (as `squeeze`'s does) — all that is
required is the uniform measure step, so no `foldl` normalisation of the body is needed. -/
theorem forIn_id_measure {σ : Type} (sz : σ → Nat) (k : Nat)
    (f : Nat → σ → Id (ForInStep σ)) (g : Nat → σ → σ)
    (hf : ∀ i s, f i s = pure (ForInStep.yield (g i s)))
    (hsz : ∀ i s, sz (g i s) = sz s + k) :
    ∀ (l : List Nat) (init : σ), sz (forIn l init f : Id σ) = sz init + l.length * k := by
  intro l
  induction l with
  | nil => intro init; show sz init = sz init + 0 * k; simp
  | cons a t ih =>
    intro init
    rw [List.forIn_cons]
    simp only [hf]
    show sz (forIn t (g a init) f : Id σ) = _
    rw [ih (g a init), hsz]
    simp [Nat.succ_mul]
    ring

/-- A `push`-fold grows an array by exactly the length of the driving list. -/
theorem foldlPush_size {β} (F : Nat → β) (l : List Nat) (init : Array β) :
    (List.foldl (fun b a => b.push (F a)) init l).size = init.size + l.length := by
  induction l generalizing init with
  | nil => simp
  | cons a t ih => simp

/-- Ceiling division delivers at least the numerator: `outLen ≤ ⌈outLen/rate⌉ · rate` for `rate > 0`. This is
what makes the final `List.take outLen` of `squeeze` a NO-OP truncation rather than a shortening one. -/
theorem ceilDiv_mul_ge (rate outLen : Nat) (hr : 0 < rate) :
    outLen ≤ ((outLen + rate - 1) / rate) * rate := by
  have h1 := Nat.div_add_mod (outLen + rate - 1) rate
  have h2 : (outLen + rate - 1) % rate < rate := Nat.mod_lt _ hr
  have h3 : outLen ≤ rate * ((outLen + rate - 1) / rate) := by omega
  calc outLen ≤ rate * ((outLen + rate - 1) / rate) := h3
    _ = ((outLen + rate - 1) / rate) * rate := Nat.mul_comm _ _

/-- `f <$> x = f x` in `Id` (the squeeze do-block's `return` is elaborated as a `Functor.map`). -/
theorem id_map_apply {α β : Type} (f : α → β) (x : Id α) : (f <$> x : Id β) = f x := rfl

/-- **THE FIPS 202 SQUEEZE-LENGTH THEOREM, ∀.** For every positive rate, every sponge state and every
requested length, `Keccak.squeeze` returns EXACTLY `outLen` bytes.

Proof shape: the outer block loop's accumulator is an `MProd (Array UInt8) (Array UInt64)`; `forIn_id_measure`
(measure `out.size`, step `rate`) gives `out.size = ⌈outLen/rate⌉ · rate` — the between-block `if` only ever
rewrites the sponge state component, so the measure step is unconditional — and `ceilDiv_mul_ge` makes the
closing `List.take outLen` exact. -/
theorem squeeze_length (rate : Nat) (hr : 0 < rate) (s0 : Array UInt64) (outLen : Nat) :
    (squeeze rate s0 outLen).length = outLen := by
  unfold squeeze
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_one_sub_one, Nat.div_one, bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl]
  have hkey := forIn_id_measure (σ := MProd (Array UInt8) (Array UInt64)) (fun r => r.fst.size) rate
      (fun blk r => (do
        let r1 ← pure (List.foldl
          (fun b a => b.push (r.snd[a / 8]! >>> (8 * (a % 8)).toUInt64).toUInt8) r.fst (List.range' 0 rate))
        if blk + 1 < (outLen + rate - 1) / rate then pure (ForInStep.yield ⟨r1, keccakF r.snd⟩)
          else pure (ForInStep.yield ⟨r1, r.snd⟩)))
      (fun blk r => ⟨List.foldl
          (fun b a => b.push (r.snd[a / 8]! >>> (8 * (a % 8)).toUInt64).toUInt8) r.fst (List.range' 0 rate),
        if blk + 1 < (outLen + rate - 1) / rate then keccakF r.snd else r.snd⟩)
      (by intro i s; by_cases h : i + 1 < (outLen + rate - 1) / rate <;> simp [h])
      (by intro i s; simp)
      (List.range' 0 ((outLen + rate - 1) / rate)) ⟨#[], s0⟩
  simp only [List.length_range', Array.size_empty, Nat.zero_add] at hkey
  rw [id_map_apply]
  simp only [List.length_take, Array.length_toList]
  exact Nat.min_eq_left (le_of_le_of_eq (ceilDiv_mul_ge rate outLen hr) hkey.symm)

/-- **`SHA3-512` emits exactly 64 bytes, ∀ input.** `sha3_512 = squeeze 72 (absorb 72 (sha3Pad 72 ·)) 64`
(FIPS 202: SHA3-512 has rate `1600 − 2·512 = 576` bits `= 72` bytes and a 512-bit digest). -/
theorem sha3_512_length (input : List UInt8) : (sha3_512 input).length = 64 := by
  unfold sha3_512
  exact squeeze_length 72 (by norm_num) _ 64

/-! ## §1 — generic array bookkeeping (block-append fold + interior-window read). -/

theorem getElem!_append_left {β} [Inhabited β] (a b : Array β) (i : Nat) (h : i < a.size) :
    (a ++ b)[i]! = a[i]! := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_append_left h]

theorem getElem!_append_right {β} [Inhabited β] (a b : Array β) (i : Nat)
    (h : a.size ≤ i) (h2 : i < a.size + b.size) : (a ++ b)[i]! = b[i - a.size]! := by
  have hb : i - a.size < b.size := by omega
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_append_right h]

theorem getElem!_extract {β} [Inhabited β] (a : Array β) (start stop i : Nat)
    (h : start + i < min stop a.size) : (a.extract start stop)[i]! = a[start + i]! := by
  have hi : i < (a.extract start stop).size := by rw [Array.size_extract]; omega
  have hb : start + i < a.size := by omega
  rw [getElem!_pos _ i hi, getElem!_pos a (start+i) hb, Array.getElem_extract]

/-- **The block-append fold** `init ++ g 0 ++ … ++ g (n−1)` (uniform block size `s`): its size, its
low-window (the `init` prefix), and its per-block byte layout. The mechanical offset engine. -/
theorem appendFold_spec {β} [Inhabited β] (g : Nat → Array β) (s : Nat) (init : Array β) :
    ∀ (n : Nat), (∀ i, i < n → (g i).size = s) →
      let r := List.foldl (fun out i => out ++ g i) init (List.range' 0 n 1)
      r.size = init.size + n * s
      ∧ (∀ j, j < init.size → r[j]! = init[j]!)
      ∧ (∀ i, i < n → ∀ j, j < s → r[init.size + i * s + j]! = (g i)[j]!) := by
  intro n
  induction n with
  | zero => intro _; refine ⟨by simp, by simp, by intro i hi; omega⟩
  | succ k ih =>
    intro hsz
    obtain ⟨hsize, hlo, hhi⟩ := ih (fun i hi => hsz i (by omega))
    rw [List.range'_1_concat, List.foldl_concat, Nat.zero_add]
    set P := List.foldl (fun out i => out ++ g i) init (List.range' 0 k 1) with hP
    have hgk : (g k).size = s := hsz k (by omega)
    refine ⟨?_, ?_, ?_⟩
    · show (P ++ g k).size = _
      rw [Array.size_append, hsize, hgk]; ring
    · intro j hj
      rw [getElem!_append_left _ _ _ (by rw [hsize]; omega), hlo j hj]
    · intro i hi j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · have hik : i * s + j < k * s := by
          have h2 : (i+1) * s ≤ k * s := by apply Nat.mul_le_mul_right; omega
          rw [Nat.succ_mul] at h2; omega
        rw [getElem!_append_left _ _ _ (by rw [hsize]; omega), hhi i h j hj]
      · subst h
        rw [getElem!_append_right _ _ _ (by rw [hsize]; omega) (by rw [hsize, hgk]; omega),
            show init.size + i*s + j - P.size = j from by rw [hsize]; omega]

/-- The generic push-index fold (used to read off `ekDecode`'s `t̂` array and `dkDecode`'s `ŝ` array). -/
theorem pushIdxFold_spec {β} [Inhabited β] (f : Nat → β) :
    ∀ (n : Nat) (init : Array β),
      let r := List.foldl (fun out i => out.push (f i)) init (List.range' 0 n 1)
      r.size = init.size + n ∧ (∀ j, j < init.size → r[j]! = init[j]!) ∧
        (∀ j, j < n → r[init.size + j]! = f j) := by
  intro n
  induction n with
  | zero => intro init; refine ⟨by simp, by simp, by intro j hj; omega⟩
  | succ k ih =>
    intro init
    obtain ⟨hsize, hlo, hhi⟩ := ih init
    rw [List.range'_1_concat, List.foldl_concat, Nat.zero_add]
    set P := List.foldl (fun out i => out.push (f i)) init (List.range' 0 k 1) with hP
    refine ⟨?_, ?_, ?_⟩
    · show (P.push (f k)).size = _; rw [Array.size_push, hsize]; omega
    · intro j hj
      rw [MlKemCodecSpec.getElem!_push_lt _ _ _ (by rw [hsize]; omega), hlo j hj]
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
      · rw [MlKemCodecSpec.getElem!_push_lt _ _ _ (by rw [hsize]; omega), hhi j h]
      · subst h
        rw [show init.size + j = P.size from by rw [hsize], MlKemCodecSpec.getElem!_push_eq]

/-- **`byteDecodeAt` reads only its window.** If `b`/`b'` agree on the `polyBytes d`-byte window
`[off, off+polyBytes d)` / `[off', off'+polyBytes d)`, they decode to the same poly (the interior-offset
decode reads exactly the block written there). -/
theorem byteDecodeAt_eq_of_window (d : Nat) (b b' : Array UInt8) (off off' : Nat)
    (h : ∀ i, i < polyBytes d → b[off + i]! = b'[off' + i]!) :
    byteDecodeAt d b off = byteDecodeAt d b' off' := by
  apply arrayExtAll
  · rw [byteDecodeAt_size, byteDecodeAt_size]
  · intro j hj
    rw [byteDecodeAt_size] at hj
    rw [byteDecodeAt_getElem d b off j hj, byteDecodeAt_getElem d b' off' j hj]
    have hbn : bytesToNatLE b off (polyBytes d) = bytesToNatLE b' off' (polyBytes d) := by
      rw [bytesToNatLE_eq, bytesToNatLE_eq]
      exact Finset.sum_congr rfl (fun i hi => by rw [h i (Finset.mem_range.mp hi)])
    rw [hbn]

/-! ## §2 — the ring KeyGen output made explicit + its per-coefficient bounds. -/

/-- The `G(d‖k)` bytes `ρ` is sourced from. -/
def rhoOf (d : List UInt8) : List UInt8 := (sha3_512 (d ++ [UInt8.ofNat paramK])).take 32
/-- The `G(d‖k)` PRF seed `σ`. -/
def sigOf (d : List UInt8) : List UInt8 := (sha3_512 (d ++ [UInt8.ofNat paramK])).drop 32

/-- The `i`-th sampled `sᵢ = SamplePolyCBD_η1(PRF(σ, i))`. -/
def sPoly (d : List UInt8) (i : Nat) : Poly := samplePolyCBD 2 (prf 2 (sigOf d) i)

/-- The `ŝ` array is the explicit `#[NTT s₀, NTT s₁, NTT s₂]`. -/
theorem kr_sHat (d : List UInt8) :
    (kpkeKeyGenRing d).2.1 = #[ntt (sPoly d 0), ntt (sPoly d 1), ntt (sPoly d 2)] := by
  unfold sPoly sigOf kpkeKeyGenRing
  simp only [paramK, Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_one_sub_one,
    Nat.div_one]
  rfl

/-- `ρ` recovered from the ring generator is `G(d‖k).take 32`. -/
theorem kr_rho (d : List UInt8) : (kpkeKeyGenRing d).2.2 = rhoOf d := by
  unfold rhoOf kpkeKeyGenRing
  simp only [paramK, Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_one_sub_one,
    Nat.div_one]
  rfl

/-- Reading an element off a `push`-fold from `#[]`. -/
theorem pushEmptyFold_get {β} [Inhabited β] (f : Nat → β) (n i : Nat) (hi : i < n) :
    (List.foldl (fun out j => out.push (f j)) (#[] : Array β) (List.range' 0 n 1))[i]! = f i := by
  have h := (pushIdxFold_spec f n #[]).2.2 i hi
  simpa using h

/-- The size of a `push`-fold from `#[]`. -/
theorem pushEmptyFold_size {β} [Inhabited β] (f : Nat → β) (n : Nat) :
    (List.foldl (fun out j => out.push (f j)) (#[] : Array β) (List.range' 0 n 1)).size = n := by
  have h := (pushIdxFold_spec f n #[]).1
  simpa using h

/-- **Each `t̂ᵢ` is an `addPoly`** — the matvec accumulator plus `êᵢ`. The two operands are left existential:
`addPoly _ _` is all that the bound below needs (`addPoly` reduces every coefficient mod `q`). -/
theorem kr_tHat_get (d : List UInt8) (i : Nat) (hi : i < paramK) :
    ∃ A B, (kpkeKeyGenRing d).1[i]! = addPoly A B := by
  unfold kpkeKeyGenRing
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_one_sub_one,
    Nat.div_one]
  exact ⟨_, _, pushEmptyFold_get _ paramK i hi⟩

/-- `t̂` has exactly `paramK` polynomials. -/
theorem kr_tHat_size (d : List UInt8) : (kpkeKeyGenRing d).1.size = paramK := by
  unfold kpkeKeyGenRing
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_one_sub_one,
    Nat.div_one]
  exact pushEmptyFold_size _ paramK

/-- `ŝ` has exactly `paramK = 3` polynomials. -/
theorem kr_sHat_size (d : List UInt8) : (kpkeKeyGenRing d).2.1.size = paramK := by
  rw [kr_sHat]; rfl

/-- **Bound + shape on `t̂`.** Each `t̂ᵢ` is a size-256 poly with every coefficient `< q` — unconditionally,
because `t̂ᵢ = addPoly _ _` and `addPoly` reduces every coefficient mod `q` (`MlKemRing.addPoly_lt`). -/
theorem kr_tHat_coeff (d : List UInt8) (i : Nat) (hi : i < paramK) :
    ((kpkeKeyGenRing d).1[i]!).size = 256 ∧ ∀ j, j < 256 → ((kpkeKeyGenRing d).1[i]!)[j]! < q := by
  obtain ⟨A, B, hAB⟩ := kr_tHat_get d i hi
  rw [hAB]
  exact ⟨MlKemRing.addPoly_size A B, fun j _ => MlKemRing.addPoly_lt A B j⟩

/-- **Bound + shape on `ŝ`.** Each `ŝᵢ = NTT(sᵢ)` is a size-256 poly with coefficients `< q`, because
`sᵢ = SamplePolyCBD_η1(…)` is a canonical `R_q` element (`samplePolyCBD_size`/`_lt`) and `NTT` preserves the
`< q` codomain (`MlKemRing.ntt_size`/`_lt`). -/
theorem kr_sHat_coeff (d : List UInt8) (i : Nat) (hi : i < paramK) :
    ((kpkeKeyGenRing d).2.1[i]!).size = 256 ∧ ∀ j, j < 256 → ((kpkeKeyGenRing d).2.1[i]!)[j]! < q := by
  rw [kr_sHat]
  have hi3 : i < 3 := hi
  have hsz : ∀ p : List UInt8, (ntt (samplePolyCBD 2 p)).size = 256 := fun p =>
    MlKemRing.ntt_size _ (MlKemFips203FullDim.samplePolyCBD_size 2 p)
  have hlt : ∀ (p : List UInt8) j, j < 256 → (ntt (samplePolyCBD 2 p))[j]! < q := fun p j _ =>
    MlKemRing.ntt_lt _ (MlKemFips203FullDim.samplePolyCBD_lt 2 p) j
  interval_cases i <;>
    exact ⟨hsz _, fun j hj => hlt _ j hj⟩

/-! ## §3 — the `ek` codec round-trip (byte `ek` decodes to the ring `(t̂, ρ)`). -/

/-- `ekEncode` as an explicit block-append array (`t̂₀ ‖ t̂₁ ‖ t̂₂ ‖ ρ`). -/
theorem ekEncode_toArray (tHat : Array Poly) (rho : List UInt8) :
    (ekEncode (tHat, rho)).toArray =
      (List.foldl (fun out i => out ++ (byteEncode dCoeff tHat[i]!).toArray)
        (Array.mkEmpty ekLen) (List.range' 0 paramK 1)) ++ rho.toArray := by
  unfold ekEncode
  simp only [paramK, Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_one_sub_one,
    Nat.div_one]
  rfl

/-- `ekDecode`'s `t̂` array (an indexed push of `byteDecodeAt` at the block offsets). -/
theorem ekDecode_fst (ek : List UInt8) :
    (ekDecode ek).1 =
      List.foldl (fun t i => t.push (byteDecodeAt dCoeff ek.toArray (i * polyBytes dCoeff)))
        (Array.mkEmpty paramK) (List.range' 0 paramK 1) := by
  unfold ekDecode
  simp only [paramK, Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_one_sub_one,
    Nat.div_one]
  rfl

/-- `ekDecode`'s `ρ` (the trailing 32 bytes). -/
theorem ekDecode_snd (ek : List UInt8) :
    (ekDecode ek).2 =
      (ek.toArray.extract (paramK * polyBytes dCoeff) (paramK * polyBytes dCoeff + 32)).toList := by
  unfold ekDecode
  simp only [paramK, Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_one_sub_one,
    Nat.div_one]
  rfl

/-- **`ekDecode ∘ ekEncode = id`** for any `t̂` of exactly `paramK` size-256 `< q` polys and any `ρ` of
length 32. Rides `byteDecodeAt_byteEncode` through the `t̂₀ ‖ t̂₁ ‖ t̂₂ ‖ ρ` block layout — a real
byte↔ring identity, NOT `rfl`. -/
theorem ekDecode_ekEncode (tHat : Array Poly) (rho : List UInt8)
    (hsz : tHat.size = paramK) (hrho : rho.length = 32)
    (hpsz : ∀ i, i < paramK → (tHat[i]!).size = 256)
    (hplt : ∀ i, i < paramK → ∀ j, j < 256 → (tHat[i]!)[j]! < q) :
    ekDecode (ekEncode (tHat, rho)) = (tHat, rho) := by
  set b := (ekEncode (tHat, rho)).toArray with hb
  set P := List.foldl (fun out i => out ++ (byteEncode dCoeff tHat[i]!).toArray)
    (Array.mkEmpty ekLen) (List.range' 0 paramK 1) with hP
  have hbeq : b = P ++ rho.toArray := by rw [hP, hb, ekEncode_toArray]
  have hgsz : ∀ i, i < paramK → (byteEncode dCoeff tHat[i]!).toArray.size = polyBytes dCoeff := by
    intro i _; exact byteEncode_size dCoeff (tHat[i]!)
  obtain ⟨hPsz0, _, hPhi⟩ :=
    appendFold_spec (fun i => (byteEncode dCoeff tHat[i]!).toArray) (polyBytes dCoeff)
      (Array.mkEmpty ekLen) paramK hgsz
  rw [MlKemCodecSpec.size_mkEmpty, Nat.zero_add] at hPsz0
  have hPsz' : P.size = paramK * polyBytes dCoeff := hPsz0
  have hrhosz : rho.toArray.size = 32 := by simp [hrho]
  have hbtoarr : (ekEncode (tHat, rho)).toArray = b := hb.symm
  have hblock : ∀ j, j < paramK → ∀ jj, jj < polyBytes dCoeff →
      P[j * polyBytes dCoeff + jj]! = (byteEncode dCoeff tHat[j]!).toArray[jj]! := by
    intro j hj jj hjj
    have := hPhi j hj jj hjj
    simpa [MlKemCodecSpec.size_mkEmpty] using this
  have hidxlt : ∀ j, j < paramK → ∀ jj, jj < polyBytes dCoeff →
      j * polyBytes dCoeff + jj < paramK * polyBytes dCoeff := by
    intro j hj jj hjj
    calc j * polyBytes dCoeff + jj < j * polyBytes dCoeff + polyBytes dCoeff := by omega
      _ = (j + 1) * polyBytes dCoeff := by ring
      _ ≤ paramK * polyBytes dCoeff := Nat.mul_le_mul_right _ (by omega)
  refine Prod.ext ?_ ?_
  · -- t̂ recovery
    rw [ekDecode_fst]
    obtain ⟨hQsz, _, hQhi⟩ :=
      pushIdxFold_spec (fun i => byteDecodeAt dCoeff (ekEncode (tHat, rho)).toArray (i * polyBytes dCoeff))
        paramK (Array.mkEmpty paramK)
    simp only [MlKemCodecSpec.size_mkEmpty, Nat.zero_add] at hQsz hQhi
    apply arrayExtAll
    · rw [hQsz, hsz]
    · intro j hj
      rw [hQsz] at hj
      rw [hQhi j hj, hbtoarr]
      -- the window at offset j·384 is exactly byteEncode dCoeff tHat[j]!
      have hwin : byteDecodeAt dCoeff b (j * polyBytes dCoeff)
          = byteDecodeAt dCoeff (byteEncode dCoeff tHat[j]!).toArray 0 := by
        apply byteDecodeAt_eq_of_window
        intro jj hjj
        rw [Nat.zero_add, hbeq,
          getElem!_append_left _ _ _ (by rw [hPsz']; exact hidxlt j hj jj hjj)]
        exact hblock j hj jj hjj
      rw [hwin]
      exact byteDecodeAt_byteEncode dCoeff (tHat[j]!) (hpsz j hj)
        (by simpa [decMod, dCoeff] using hplt j hj)
  · -- ρ recovery
    rw [ekDecode_snd, hbtoarr]
    have hbsz : b.size = paramK * polyBytes dCoeff + 32 := by
      rw [hbeq, Array.size_append, hPsz', hrhosz]
    have hext : b.extract (paramK * polyBytes dCoeff) (paramK * polyBytes dCoeff + 32) = rho.toArray := by
      apply arrayExtAll
      · rw [Array.size_extract, hbsz, hrhosz]; omega
      · intro k hk
        rw [Array.size_extract, hbsz] at hk
        rw [getElem!_extract _ _ _ _ (by rw [hbsz]; omega)]
        rw [hbeq, getElem!_append_right _ _ _ (by rw [hPsz']; omega)
              (by rw [hPsz', hrhosz]; omega)]
        rw [show paramK * polyBytes dCoeff + k - P.size = k from by rw [hPsz']; omega]
    rw [hext]

/-! ## §4 — the `dkPKE` codec round-trip (byte `dkPKE` decodes to the ring `ŝ`). -/

/-- `ByteEncode₁₂(ŝ₀) ‖ ByteEncode₁₂(ŝ₁) ‖ ByteEncode₁₂(ŝ₂)` — the `dkPKE` body `kpkeKeyGen` emits, as a
function of `ŝ` alone. -/
def dkPkeEncode (sHat : Array Poly) : List UInt8 := Id.run do
  let mut dkPke : List UInt8 := []
  for i in [0:paramK] do
    dkPke := dkPke ++ byteEncode dCoeff sHat[i]!
  return dkPke

/-- **Bridge**: the byte `ek` is `ekEncode` of the ring `(t̂, ρ)` (definitional — `kpkeKeyGen` IS
`kpkeKeyGenRing` composed with the codec). -/
theorem kpkeKeyGen_ek_eq (d : List UInt8) :
    (kpkeKeyGen d).1 = ekEncode ((kpkeKeyGenRing d).1, (kpkeKeyGenRing d).2.2) := by
  rfl

/-- **Bridge**: the byte `dkPKE` is `dkPkeEncode` of the ring `ŝ` (definitional). -/
theorem kpkeKeyGen_dk_eq (d : List UInt8) :
    (kpkeKeyGen d).2 = dkPkeEncode (kpkeKeyGenRing d).2.1 := by
  rfl

/-- List-append fold commutes with `toArray` into an array-append fold. -/
theorem listAppendFold_toArray (g : Nat → List UInt8) :
    ∀ (n : Nat) (init : List UInt8),
      (List.foldl (fun dk i => dk ++ g i) init (List.range' 0 n 1)).toArray =
        List.foldl (fun out i => out ++ (g i).toArray) init.toArray (List.range' 0 n 1) := by
  intro n
  induction n with
  | zero => intro init; simp
  | succ k ih =>
    intro init
    simp only [List.range'_1_concat, List.foldl_concat, ← List.append_toArray, ih]

/-- `dkPkeEncode` as a `List`-append fold. -/
theorem dkPkeEncode_eq (sHat : Array Poly) :
    dkPkeEncode sHat =
      List.foldl (fun dk i => dk ++ byteEncode dCoeff sHat[i]!) [] (List.range' 0 paramK 1) := by
  unfold dkPkeEncode
  simp only [paramK, Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_one_sub_one,
    Nat.div_one]
  rfl

/-- `dkPkeEncode` as an explicit block-append array. -/
theorem dkPkeEncode_toArray (sHat : Array Poly) :
    (dkPkeEncode sHat).toArray =
      List.foldl (fun out i => out ++ (byteEncode dCoeff sHat[i]!).toArray)
        (#[] : Array UInt8) (List.range' 0 paramK 1) := by
  rw [dkPkeEncode_eq, listAppendFold_toArray]

/-- **decode of `dkPKE` at block `i` recovers `ŝᵢ`** — for any `ŝ` of exactly `paramK` size-256 `< q` polys.
Rides `byteDecodeAt_byteEncode` through the `ŝ₀ ‖ ŝ₁ ‖ ŝ₂` layout. A real byte↔ring identity. -/
theorem dkPkeEncode_decode (sHat : Array Poly) (_hsz : sHat.size = paramK)
    (hpsz : ∀ i, i < paramK → (sHat[i]!).size = 256)
    (hplt : ∀ i, i < paramK → ∀ j, j < 256 → (sHat[i]!)[j]! < q)
    (i : Nat) (hi : i < paramK) :
    byteDecodeAt dCoeff (dkPkeEncode sHat).toArray (i * polyBytes dCoeff) = sHat[i]! := by
  rw [dkPkeEncode_toArray]
  have hgsz : ∀ i, i < paramK → (byteEncode dCoeff sHat[i]!).toArray.size = polyBytes dCoeff :=
    fun i _ => byteEncode_size dCoeff (sHat[i]!)
  obtain ⟨_, _, hQhi⟩ :=
    appendFold_spec (fun i => (byteEncode dCoeff sHat[i]!).toArray) (polyBytes dCoeff)
      (#[] : Array UInt8) paramK hgsz
  have hwin : byteDecodeAt dCoeff
        (List.foldl (fun out i => out ++ (byteEncode dCoeff sHat[i]!).toArray)
          (#[] : Array UInt8) (List.range' 0 paramK 1)) (i * polyBytes dCoeff)
        = byteDecodeAt dCoeff (byteEncode dCoeff sHat[i]!).toArray 0 := by
    apply byteDecodeAt_eq_of_window
    intro jj hjj
    rw [Nat.zero_add]
    have := hQhi i hi jj hjj
    simpa using this
  rw [hwin]
  exact byteDecodeAt_byteEncode dCoeff (sHat[i]!) (hpsz i hi)
    (by simpa [decMod, dCoeff] using hplt i hi)

/-! ## §5 — the KeyGen byte↔ring refinement.

The `ρ`-length side condition `(rhoOf d).length = 32` is the SHA-3 fixed-output-length fact
(`ρ = G(d‖k).take 32`, `|G| = 64`): pure FIPS 202 Keccak `squeeze`-loop bookkeeping, no crypto content. It is
carried as a named hypothesis in `kpkeKeyGen_refines_ring_of_rholen` and DISCHARGED by `rhoOf_length` (§0's
`sha3_512_length`) into the UNCONDITIONAL `kpkeKeyGen_refines_ring`. -/

/-- **THE KeyGen REFINEMENT (given the `ρ`-length fact).** Decoding the emitted `ek` recovers the abstract
`(t̂, ρ)`, and decoding `dkPKE` at block `i` recovers the abstract `ŝᵢ` — the byte impl is the ring generator
composed with the codec. A genuine `∀`-refinement (spec = the RING KeyGen), not the impl restated. -/
theorem kpkeKeyGen_refines_ring_of_rholen (d : List UInt8) (hrho : (rhoOf d).length = 32) :
    ekDecode (kpkeKeyGen d).1 = ((kpkeKeyGenRing d).1, (kpkeKeyGenRing d).2.2)
    ∧ (∀ i, i < paramK →
         byteDecodeAt dCoeff (kpkeKeyGen d).2.toArray (i * polyBytes dCoeff) = (kpkeKeyGenRing d).2.1[i]!) := by
  refine ⟨?_, ?_⟩
  · rw [kpkeKeyGen_ek_eq]
    exact ekDecode_ekEncode (kpkeKeyGenRing d).1 (kpkeKeyGenRing d).2.2
      (kr_tHat_size d) (by rw [kr_rho]; exact hrho)
      (fun i hi => (kr_tHat_coeff d i hi).1) (fun i hi j hj => (kr_tHat_coeff d i hi).2 j hj)
  · intro i hi
    rw [kpkeKeyGen_dk_eq]
    exact dkPkeEncode_decode (kpkeKeyGenRing d).2.1 (kr_sHat_size d)
      (fun i hi => (kr_sHat_coeff d i hi).1) (fun i hi j hj => (kr_sHat_coeff d i hi).2 j hj) i hi

/-- **THE `ρ`-LENGTH FACT, DISCHARGED.** `ρ = G(d‖k).take 32` has length 32, because `G = SHA3-512` emits 64
bytes for every input (§0's `sha3_512_length`, itself the `∀` FIPS 202 squeeze-length theorem). No hypothesis,
no KAT, no `native_decide`. -/
theorem rhoOf_length (d : List UInt8) : (rhoOf d).length = 32 := by
  unfold rhoOf
  rw [List.length_take, sha3_512_length]
  omega

/-- **THE KeyGen REFINEMENT — UNCONDITIONAL.** For EVERY seed `d`: decoding the emitted byte `ek` recovers the
abstract ring `(t̂, ρ)`, and decoding `dkPKE` at block `i` recovers the abstract `ŝᵢ`. The byte implementation
IS the ring generator composed with the codec.

This is `kpkeKeyGen_refines_ring_of_rholen` with its ONE side condition discharged by `rhoOf_length`. A genuine
`∀`-refinement: the specification side is the RING KeyGen (`kpkeKeyGenRing` — sample / NTT / matvec over
`R_q`), NOT the byte implementation restated, and the two are related through the real codec round trip
`byteDecodeAt_byteEncode`, not by `rfl`. FIPS 203 §4.2.1 / §6 / §8; FIPS 202 for `G`. -/
theorem kpkeKeyGen_refines_ring (d : List UInt8) :
    ekDecode (kpkeKeyGen d).1 = ((kpkeKeyGenRing d).1, (kpkeKeyGenRing d).2.2)
    ∧ (∀ i, i < paramK →
         byteDecodeAt dCoeff (kpkeKeyGen d).2.toArray (i * polyBytes dCoeff) = (kpkeKeyGenRing d).2.1[i]!) :=
  kpkeKeyGen_refines_ring_of_rholen d (rhoOf_length d)

/-! ## Trusted base — the ∀-refinement legs, the discharged side condition, and the unconditional keystone. -/

#print axioms squeeze_length
#print axioms sha3_512_length
#print axioms rhoOf_length
#print axioms ekDecode_ekEncode
#print axioms dkPkeEncode_decode
#print axioms kr_tHat_coeff
#print axioms kr_sHat_coeff
#print axioms kpkeKeyGen_refines_ring_of_rholen
#print axioms kpkeKeyGen_refines_ring

end Dregg2.Crypto.MlKemKeygenRefine
