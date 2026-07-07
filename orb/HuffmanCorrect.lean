/-
RFC 7541 Appendix B Huffman code — the DECODER's correctness theory.

`H3/Qpack.lean` carries the deployed HPACK/QPACK static Huffman decoder
(`huffmanDecode` / `huffDecodeBits`, driven by the 257-symbol `huffTable` of
RFC 7541 Appendix B, referenced by RFC 9204 §4.1.2 for QPACK string literals).
That decoder is the MSB-first prefix-code walk: accumulate bits, emit the symbol
of the first complete codeword, reject the EOS symbol in the body and any
over-long (> 7-bit) all-ones padding (RFC 7541 §5.2).

This file proves that deployed decoder correct. It defines the RFC 7541
Appendix B ENCODER independently — `encTable`, an independently transcribed
`(bitLength, code)` listing of all 257 symbols — and proves the ROUND TRIP:
`huffmanDecode (huffEncode bs) = some bs` for every octet string `bs`. The
deployed decoder is a faithful inverse of the RFC encoder.

The correctness core is the fundamental Huffman property, decided once over the
table: the code is PREFIX-FREE (no codeword is an MSB-prefix of another,
`prefixFree`). From it the deployed `huffLookup` is characterized (a codeword
resolves to its symbol; every proper prefix resolves to `none`), giving the
single-symbol inverse, then the full multi-symbol round trip by induction, and
the §5.2 padding acceptance/rejection.

No `sorry`, no `native_decide`. Axioms: {propext, Quot.sound, Classical.choice}.
-/
import H3.Qpack

namespace H3
namespace Qpack

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! ## The RFC 7541 Appendix B code table, transcribed independently

`encTable` lists `(bitLength, code)` for each symbol 0–255 and EOS (index 256),
per RFC 7541 Appendix B. It is written independently of the deployed `huffTable`;
`huffTable_toList` below proves the deployed decoder's table agrees with it, so a
mis-transcription on either side would break every theorem here. -/
def encTable : List (Nat × Nat) := [(13, 8184),(23, 8388568),(28, 268435426),(28, 268435427),(28, 268435428),(28, 268435429),(28, 268435430),(28, 268435431),(28, 268435432),(24, 16777194),(30, 1073741820),(28, 268435433),(28, 268435434),(30, 1073741821),(28, 268435435),(28, 268435436),(28, 268435437),(28, 268435438),(28, 268435439),(28, 268435440),(28, 268435441),(28, 268435442),(30, 1073741822),(28, 268435443),(28, 268435444),(28, 268435445),(28, 268435446),(28, 268435447),(28, 268435448),(28, 268435449),(28, 268435450),(28, 268435451),(6, 20),(10, 1016),(10, 1017),(12, 4090),(13, 8185),(6, 21),(8, 248),(11, 2042),(10, 1018),(10, 1019),(8, 249),(11, 2043),(8, 250),(6, 22),(6, 23),(6, 24),(5, 0),(5, 1),(5, 2),(6, 25),(6, 26),(6, 27),(6, 28),(6, 29),(6, 30),(6, 31),(7, 92),(8, 251),(15, 32764),(6, 32),(12, 4091),(10, 1020),(13, 8186),(6, 33),(7, 93),(7, 94),(7, 95),(7, 96),(7, 97),(7, 98),(7, 99),(7, 100),(7, 101),(7, 102),(7, 103),(7, 104),(7, 105),(7, 106),(7, 107),(7, 108),(7, 109),(7, 110),(7, 111),(7, 112),(7, 113),(7, 114),(8, 252),(7, 115),(8, 253),(13, 8187),(19, 524272),(13, 8188),(14, 16380),(6, 34),(15, 32765),(5, 3),(6, 35),(5, 4),(6, 36),(5, 5),(6, 37),(6, 38),(6, 39),(5, 6),(7, 116),(7, 117),(6, 40),(6, 41),(6, 42),(5, 7),(6, 43),(7, 118),(6, 44),(5, 8),(5, 9),(6, 45),(7, 119),(7, 120),(7, 121),(7, 122),(7, 123),(15, 32766),(11, 2044),(14, 16381),(13, 8189),(28, 268435452),(20, 1048550),(22, 4194258),(20, 1048551),(20, 1048552),(22, 4194259),(22, 4194260),(22, 4194261),(23, 8388569),(22, 4194262),(23, 8388570),(23, 8388571),(23, 8388572),(23, 8388573),(23, 8388574),(24, 16777195),(23, 8388575),(24, 16777196),(24, 16777197),(22, 4194263),(23, 8388576),(24, 16777198),(23, 8388577),(23, 8388578),(23, 8388579),(23, 8388580),(21, 2097116),(22, 4194264),(23, 8388581),(22, 4194265),(23, 8388582),(23, 8388583),(24, 16777199),(22, 4194266),(21, 2097117),(20, 1048553),(22, 4194267),(22, 4194268),(23, 8388584),(23, 8388585),(21, 2097118),(23, 8388586),(22, 4194269),(22, 4194270),(24, 16777200),(21, 2097119),(22, 4194271),(23, 8388587),(23, 8388588),(21, 2097120),(21, 2097121),(22, 4194272),(21, 2097122),(23, 8388589),(22, 4194273),(23, 8388590),(23, 8388591),(20, 1048554),(22, 4194274),(22, 4194275),(22, 4194276),(23, 8388592),(22, 4194277),(22, 4194278),(23, 8388593),(26, 67108832),(26, 67108833),(20, 1048555),(19, 524273),(22, 4194279),(23, 8388594),(22, 4194280),(25, 33554412),(26, 67108834),(26, 67108835),(26, 67108836),(27, 134217694),(27, 134217695),(26, 67108837),(24, 16777201),(25, 33554413),(19, 524274),(21, 2097123),(26, 67108838),(27, 134217696),(27, 134217697),(26, 67108839),(27, 134217698),(24, 16777202),(21, 2097124),(21, 2097125),(26, 67108840),(26, 67108841),(28, 268435453),(27, 134217699),(27, 134217700),(27, 134217701),(20, 1048556),(24, 16777203),(20, 1048557),(21, 2097126),(22, 4194281),(21, 2097127),(21, 2097128),(23, 8388595),(22, 4194282),(22, 4194283),(25, 33554414),(25, 33554415),(24, 16777204),(24, 16777205),(26, 67108842),(23, 8388596),(26, 67108843),(27, 134217702),(26, 67108844),(26, 67108845),(27, 134217703),(27, 134217704),(27, 134217705),(27, 134217706),(27, 134217707),(28, 268435454),(27, 134217708),(27, 134217709),(27, 134217710),(27, 134217711),(27, 134217712),(26, 67108846),(30, 1073741823)]

theorem encTable_length : encTable.length = 257 := by decide

/-- `code i` is an MSB-prefix of `code j`: `i`'s length is ≤ `j`'s and `j`'s top
`len i` bits equal `code i`. Reflexive on equal codes, so it also witnesses code
equality. -/
def isBitPrefix : (Nat × Nat) → (Nat × Nat) → Bool
  | (li, ci), (lj, cj) => decide (li ≤ lj) && (cj >>> (lj - li) == ci)

/-- Two entries are mutually non-prefix (in both directions). -/
def notPrefixPair (a b : Nat × Nat) : Bool := (! isBitPrefix a b) && (! isBitPrefix b a)

/-- **The fundamental Huffman property (prefix-freeness), decided once.** No two
distinct entries stand in the MSB-prefix relation — in particular all 257 codes
are distinct. This is THE correctness core of a prefix code. -/
theorem prefixFree : encTable.Pairwise (fun a b => notPrefixPair a b = true) := by decide

/-- **The deployed decoder's table equals the independent transcription.** Binds
every lemma below to the array `huffTable` that `huffmanDecode` actually reads. -/
theorem huffTable_toList : huffTable.toList = encTable := by decide

/-- Codes fit their stated bit length (needed to seed the decode walk at 0). -/
theorem codes_fit : ∀ x ∈ encTable, x.2 < 2 ^ x.1 := by decide

/-- Every code length is between 1 and 31 (the decoder's 32-bit walk cap). -/
theorem len_pos : ∀ x ∈ encTable, 1 ≤ x.1 := by decide
theorem len_lt : ∀ x ∈ encTable, x.1 < 32 := by decide

/-! ## Prefix-freeness in index form -/

/-- `prefixFree` read off at any two distinct indices (both directions). -/
theorem notPrefix_idx (i j : Nat) (hi : i < 257) (hj : j < 257) (hij : i ≠ j) :
    isBitPrefix encTable[i] encTable[j] = false := by
  have hlen := encTable_length
  rcases Nat.lt_or_ge i j with h | h
  · have := (List.pairwise_iff_getElem.mp prefixFree) i j (by omega) (by omega) h
    unfold notPrefixPair at this
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
    exact this.1
  · have hji : j < i := by omega
    have := (List.pairwise_iff_getElem.mp prefixFree) j i (by omega) (by omega) hji
    unfold notPrefixPair at this
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
    exact this.2

/-! ## Characterizing the deployed `huffLookup` -/

/-- The deployed `huffLookup` is `huffTable.findIdx?` of the match predicate. -/
theorem huffLookup_eq (len val : Nat) :
    huffLookup len val = huffTable.findIdx? (fun p => p.1 == len && p.2 == val) := rfl

theorem huffTable_size : huffTable.size = 257 := by
  rw [← Array.length_toList, huffTable_toList, encTable_length]

/-- The deployed array table and the transcription agree entry-by-entry. -/
theorem huffTable_getElem? (i : Nat) : huffTable[i]? = encTable[i]? := by
  rw [← Array.getElem?_toList, huffTable_toList]

/-- `encTable[s]` accessor tied to `encTable[s]?`. -/
theorem encTable_get (s : Nat) (hs : s < 257) :
    encTable[s]? = some (encTable[s]'(by rw [encTable_length]; exact hs)) :=
  List.getElem?_eq_getElem _

/-- If an index resolves to an entry, it is in range. -/
theorem idx_lt_of_some (i : Nat) (a : Nat × Nat) (h : encTable[i]? = some a) : i < 257 := by
  by_cases hlt : i < 257
  · exact hlt
  · rw [List.getElem?_eq_none (by rw [encTable_length]; omega)] at h
    exact absurd h (by simp)

/-- Prefix-freeness at two distinct indices, phrased over the resolved entries. -/
theorem notPrefix_idx' (i j : Nat) (a b : Nat × Nat)
    (hi : encTable[i]? = some a) (hj : encTable[j]? = some b) (hij : i ≠ j) :
    isBitPrefix a b = false := by
  have hi257 := idx_lt_of_some i a hi
  have hj257 := idx_lt_of_some j b hj
  have ha : encTable[i]'(by rw [encTable_length]; exact hi257) = a :=
    Option.some.inj (by rw [← encTable_get i hi257]; exact hi)
  have hb : encTable[j]'(by rw [encTable_length]; exact hj257) = b :=
    Option.some.inj (by rw [← encTable_get j hj257]; exact hj)
  rw [← ha, ← hb]
  exact notPrefix_idx i j hi257 hj257 hij

/-- A codeword resolves (via the deployed lookup) to exactly its symbol: the
FIRST — and by prefix-freeness, only — matching entry. -/
theorem lookup_some (s L V : Nat) (hs : s < 257) (hsv : encTable[s]? = some (L, V)) :
    huffLookup L V = some s := by
  rw [huffLookup_eq]
  have hsize : s < huffTable.size := by rw [huffTable_size]; exact hs
  have hmemS : huffTable[s]? = some (L, V) := by rw [huffTable_getElem?, hsv]
  have hgetS : huffTable[s]'hsize = (L, V) :=
    Option.some.inj (by rw [← Array.getElem?_eq_getElem]; exact hmemS)
  rw [Array.findIdx?_eq_some_iff_getElem]
  refine ⟨hsize, ?_, ?_⟩
  · rw [hgetS]; simp
  · intro k hk
    have hks : k < 257 := by omega
    have hkS : k < huffTable.size := by omega
    intro hmatch
    simp only [Bool.and_eq_true, beq_iff_eq] at hmatch
    have hgetK : huffTable[k]'hkS = (L, V) := Prod.ext hmatch.1 hmatch.2
    have hmemK : encTable[k]? = some (L, V) := by
      rw [← huffTable_getElem?, Array.getElem?_eq_getElem hkS, hgetK]
    have hpref : isBitPrefix (L, V) (L, V) = false :=
      notPrefix_idx' k s (L, V) (L, V) hmemK hsv (by omega)
    rw [show isBitPrefix (L, V) (L, V) = true by unfold isBitPrefix; simp] at hpref
    exact absurd hpref (by simp)

/-- Every PROPER prefix of a codeword resolves to `none` — the prefix-free
property, transported to the deployed lookup. If symbol `s` has code `(Ls, Vs)`
and `0 < L < Ls`, then the top `L` bits of `Vs` are not any symbol's codeword. -/
theorem lookup_none_prefix (s Ls Vs L : Nat) (hsv : encTable[s]? = some (Ls, Vs))
    (_hL : 0 < L) (hLlt : L < Ls) :
    huffLookup L (Vs >>> (Ls - L)) = none := by
  rw [huffLookup_eq, Array.findIdx?_eq_none_iff]
  intro x hx
  rw [Array.mem_iff_getElem?] at hx
  obtain ⟨i, hi⟩ := hx
  rw [huffTable_getElem?] at hi
  by_cases hp : (x.1 == L && x.2 == Vs >>> (Ls - L)) = true
  · exfalso
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    have hxeq : x = (L, Vs >>> (Ls - L)) := Prod.ext hp.1 hp.2
    have hie : encTable[i]? = some (L, Vs >>> (Ls - L)) := by rw [hi, hxeq]
    have hne : i ≠ s := by
      intro h; subst h
      rw [hsv] at hie
      simp only [Option.some.injEq, Prod.mk.injEq] at hie
      omega
    have hpref : isBitPrefix (L, Vs >>> (Ls - L)) (Ls, Vs) = false :=
      notPrefix_idx' i s (L, Vs >>> (Ls - L)) (Ls, Vs) hie hsv hne
    rw [show isBitPrefix (L, Vs >>> (Ls - L)) (Ls, Vs) = true by
          unfold isBitPrefix
          simp only [beq_self_eq_true, Bool.and_true, decide_eq_true_eq]
          omega] at hpref
    exact absurd hpref (by simp)
  · simp only [Bool.not_eq_true] at hp; exact hp

/-! ## The RFC 7541 Appendix B encoder and the single-symbol inverse

`nbit v k` is bit `k` of `v`; `bitsMSB len v` is the `len`-bit MSB-first
expansion of `v` (positions `len-1 … 0`) — the wire order the decoder consumes. -/

def nbit (v k : Nat) : Bool := v >>> k % 2 == 1

def bitsMSB : Nat → Nat → List Bool
  | 0, _ => []
  | n + 1, v => nbit v n :: bitsMSB n v

theorem ite_mod_two (x : Nat) : (if x % 2 == 1 then (1 : Nat) else 0) = x % 2 := by
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]

/-- Consuming the next MSB advances the accumulated value from `v >>> n` to
`v >>> (n-1)` — the decoder's `curVal * 2 + bit` step. -/
theorem step_val (v n : Nat) (hn : 1 ≤ n) :
    (v >>> n) * 2 + (if nbit v (n - 1) then 1 else 0) = v >>> (n - 1) := by
  have h1 : v >>> n = (v >>> (n - 1)) / 2 := by
    have := Nat.shiftRight_succ v (n - 1)
    rwa [Nat.sub_add_cancel hn] at this
  simp only [nbit, ite_mod_two]
  rw [h1]; omega

/-- **The single-symbol inverse (the WALK).** Starting from the accumulator that
has consumed the top `Ls - n` bits of codeword `(Ls, Vs)`, the deployed decoder
consumes the remaining `n` MSB-first bits and emits exactly symbol `s`, then
recurses on `rest` from a fresh accumulator — for every proper prefix the lookup
returns `none` (prefix-freeness) and only the full codeword resolves. -/
theorem walk (s Ls Vs : Nat) (hsv : encTable[s]? = some (Ls, Vs)) (hs256 : s ≠ 256)
    (rest : List Bool) :
    ∀ n, 1 ≤ n → n ≤ Ls →
      huffDecodeBits (bitsMSB n Vs ++ rest) (Ls - n) (Vs >>> n)
        = (huffDecodeBits rest 0 0).map (fun tl => UInt8.ofNat s :: tl) := by
  have hs257 := idx_lt_of_some s (Ls, Vs) hsv
  have hmem : (Ls, Vs) ∈ encTable := by
    have h1 := encTable_get s hs257
    rw [hsv] at h1
    have h2 : encTable[s]'(by rw [encTable_length]; exact hs257) = (Ls, Vs) :=
      (Option.some.inj h1).symm
    rw [← h2]; exact List.getElem_mem _
  have hLs32 : Ls < 32 := len_lt (Ls, Vs) hmem
  intro n
  induction n with
  | zero => intro h1 _; exact absurd h1 (by simp)
  | succ m ih =>
    intro _ hle
    have hbits : bitsMSB (m + 1) Vs = nbit Vs m :: bitsMSB m Vs := rfl
    have hlen : Ls - (m + 1) + 1 = Ls - m := by omega
    have hval : (Vs >>> (m + 1)) * 2 + (if nbit Vs m then 1 else 0) = Vs >>> m := by
      have := step_val Vs (m + 1) (by omega)
      simpa using this
    rw [hbits, List.cons_append]
    simp only [huffDecodeBits, hlen, hval]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · -- final bit: the full codeword resolves to s
      subst hm
      simp only [Nat.sub_zero, Nat.shiftRight_zero, bitsMSB, List.nil_append]
      rw [lookup_some s Ls Vs hs257 hsv]
      simp only [beq_iff_eq]
      rw [if_neg hs256]
    · -- intermediate bit: proper prefix → none → recurse
      have hnone : huffLookup (Ls - m) (Vs >>> m) = none := by
        have := lookup_none_prefix s Ls Vs (Ls - m) hsv (by omega) (by omega)
        rwa [show Ls - (Ls - m) = m by omega] at this
      rw [hnone]
      rw [if_neg (by omega : ¬ Ls - m ≥ 32)]
      exact ih hm (by omega)

/-- Symbol codeword: the `encLen`/`encCode` bits of one octet, MSB-first. -/
def symBits (b : UInt8) : List Bool :=
  bitsMSB ((encTable[b.toNat]?.map Prod.fst).getD 0)
          ((encTable[b.toNat]?.map Prod.snd).getD 0)

/-- **Single-symbol consume, for a byte.** The deployed decoder, fed one octet's
Huffman codeword followed by any bits, emits exactly that octet and continues. -/
theorem uint8_lt256 (b : UInt8) : b.toNat < 256 := by
  have heq : b.toNat = b.toBitVec.toNat := rfl
  have h : b.toBitVec.toNat < 2 ^ 8 := b.toBitVec.isLt
  omega

theorem sym_consume (b : UInt8) (rest : List Bool) :
    huffDecodeBits (symBits b ++ rest) 0 0
      = (huffDecodeBits rest 0 0).map (fun tl => b :: tl) := by
  have hb : b.toNat < 257 := by have := uint8_lt256 b; omega
  obtain ⟨Ls, Vs, hsv⟩ : ∃ Ls Vs, encTable[b.toNat]? = some (Ls, Vs) := by
    rw [encTable_get b.toNat hb]; exact ⟨_, _, rfl⟩
  have hmem : (Ls, Vs) ∈ encTable := by
    have h1 := encTable_get b.toNat hb
    rw [hsv] at h1
    have h2 : encTable[b.toNat]'(by rw [encTable_length]; exact hb) = (Ls, Vs) :=
      (Option.some.inj h1).symm
    rw [← h2]; exact List.getElem_mem _
  have hLspos : 1 ≤ Ls := len_pos (Ls, Vs) hmem
  have hsym : symBits b = bitsMSB Ls Vs := by
    simp only [symBits, hsv, Option.map_some', Option.getD_some]
  have hs256 : b.toNat ≠ 256 := by have := uint8_lt256 b; omega
  have hbeq : (UInt8.ofNat b.toNat) = b := by simp [UInt8.ofNat_toNat]
  have := walk b.toNat Ls Vs hsv hs256 rest Ls hLspos (Nat.le_refl Ls)
  rw [hsym]
  rw [show Ls - Ls = 0 by omega] at this
  rw [show Vs >>> Ls = 0 from ?_] at this
  · rw [this, hbeq]
  · have hfit : Vs < 2 ^ Ls := codes_fit (Ls, Vs) hmem
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hfit]

/-! ## The multi-symbol round trip (all octet strings) -/

/-- The RFC encoder's bit stream for a byte string: each octet's codeword,
concatenated. -/
def huffEncodeBits (bs : Bytes) : List Bool := bs.flatMap symBits

/-- **The decoder inverts the encoder's bit stream**, for every byte string and
every trailing bits: consuming `huffEncodeBits bs` emits exactly `bs`, then
continues on `rest`. The multi-symbol ∀-statement, by induction on `bs` over the
single-symbol inverse. -/
theorem decode_encodeBits (bs : Bytes) (rest : List Bool) :
    huffDecodeBits (huffEncodeBits bs ++ rest) 0 0
      = (huffDecodeBits rest 0 0).map (fun tl => bs ++ tl) := by
  induction bs generalizing rest with
  | nil => simp [huffEncodeBits]
  | cons b bs ih =>
    have hsplit : huffEncodeBits (b :: bs) ++ rest = symBits b ++ (huffEncodeBits bs ++ rest) := by
      simp only [huffEncodeBits, List.flatMap_cons, List.append_assoc]
    rw [hsplit, sym_consume, ih, Option.map_map]
    simp only [Function.comp_def, List.cons_append]

/-! ## Padding (RFC 7541 §5.2): the EOS-prefix pad accepts, over-long rejects -/

/-- The MSB-prefix of length `m` of the EOS codeword is not any symbol's
codeword — a run of `m` (≤ 7) ones never completes a code. This is what makes
the trailing padding of §5.2 decode to the empty string. -/
theorem ones_shift (m : Nat) (hm : 1 ≤ m) (hm30 : m ≤ 30) :
    (2 ^ 30 - 1) >>> (30 - m) = 2 ^ m - 1 := by
  rw [Nat.shiftRight_eq_div_pow]
  have hpow : 2 ^ m * 2 ^ (30 - m) = 2 ^ 30 := by rw [← Nat.pow_add]; congr 1; omega
  have h2d : 1 ≤ 2 ^ (30 - m) := Nat.one_le_two_pow
  have h2m : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  apply Nat.div_eq_of_lt_le
  · have h : (2 ^ m - 1) * 2 ^ (30 - m) = 2 ^ 30 - 2 ^ (30 - m) := by
      rw [Nat.mul_sub_right_distrib, Nat.one_mul, hpow]
    rw [h]; omega
  · have h : (2 ^ m - 1 + 1) * 2 ^ (30 - m) = 2 ^ 30 := by
      rw [Nat.sub_add_cancel h2m, hpow]
    rw [h]; omega

/-- A run of `m` ones (1 ≤ m ≤ 7) resolves to `none` (prefix-free against EOS). -/
theorem all_ones_none (m : Nat) (hm : 1 ≤ m) (hm7 : m ≤ 7) :
    huffLookup m (2 ^ m - 1) = none := by
  have hEOS : encTable[256]? = some (30, 2 ^ 30 - 1) := by decide
  have := lookup_none_prefix 256 30 (2 ^ 30 - 1) m hEOS (by omega) (by omega)
  rwa [ones_shift m hm (by omega)] at this

/-- One decode step on a leading `1` bit (definitional). -/
theorem huffDecodeBits_true (rest : List Bool) (cl cv : Nat) :
    huffDecodeBits (true :: rest) cl cv =
      match huffLookup (cl + 1) (cv * 2 + 1) with
      | some sym =>
        if sym == 256 then none
        else (huffDecodeBits rest 0 0).map (fun tl => UInt8.ofNat sym :: tl)
      | none => if cl + 1 ≥ 32 then none else huffDecodeBits rest (cl + 1) (cv * 2 + 1) := rfl

/-- Walking `k` all-ones pad bits from an all-ones accumulator of length `c`
(with `c + k ≤ 7`) reaches the empty string — the §5.2 EOS-prefix padding. -/
theorem pad_walk : ∀ k c, c + k ≤ 7 →
    huffDecodeBits (List.replicate k true) c (2 ^ c - 1) = some [] := by
  intro k
  induction k with
  | zero =>
    intro c hc
    simp only [List.replicate, huffDecodeBits]
    rw [if_pos]
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_self_eq_true, and_true]
    omega
  | succ k ih =>
    intro c hc
    have h2 : 2 ^ (c + 1) = 2 ^ c * 2 := Nat.pow_succ 2 c
    have h2c : 1 ≤ 2 ^ c := Nat.one_le_two_pow
    rw [List.replicate_succ, huffDecodeBits_true,
      show (2 ^ c - 1) * 2 + 1 = 2 ^ (c + 1) - 1 from by omega,
      all_ones_none (c + 1) (by omega) (by omega), if_neg (by omega : ¬ c + 1 ≥ 32)]
    exact ih (c + 1) (by omega)

/-- The all-ones padding of ≤ 7 bits accepts (decodes to the empty string). -/
theorem pad_decode (k : Nat) (hk : k ≤ 7) :
    huffDecodeBits (List.replicate k true) 0 0 = some [] := by
  have := pad_walk k 0 (by omega)
  simpa using this

/-! ## Byte packing: `bytesToBits` inverts a byte-boundary bit stream -/

/-- Pack a bit list MSB-first into a `Nat` (the value of the first ≤ 8 bits). -/
def packByteNat (cs : List Bool) : Nat :=
  cs.foldl (fun acc c => acc * 2 + (if c then 1 else 0)) 0

/-- Group a bit list into octets, MSB-first (the wire byte order). -/
def bitsToBytes : List Bool → Bytes
  | [] => []
  | b :: rest =>
    UInt8.ofNat (packByteNat ((b :: rest).take 8)) :: bitsToBytes ((b :: rest).drop 8)
termination_by l => l.length
decreasing_by
  simp only [List.length_drop, List.length_cons]
  omega

/-- **One octet round-trips**: the 8 bits read out of `UInt8.ofNat (packByteNat cs)`
(MSB-first, exactly as `bytesToBits` reads them) equal `cs`. -/
theorem byte_bits_roundtrip (cs : List Bool) (hlen : cs.length = 8) :
    (List.range 8).map
      (fun i => ((UInt8.ofNat (packByteNat cs)).toNat >>> (7 - i)) &&& 1 == 1) = cs := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, rfl⟩ :
      ∃ a b c d e f g h, cs = [a, b, c, d, e, f, g, h] := by
    match cs, hlen with
    | [a, b, c, d, e, f, g, h], _ => exact ⟨a, b, c, d, e, f, g, h, rfl⟩
  cases c0 <;> cases c1 <;> cases c2 <;> cases c3 <;>
    cases c4 <;> cases c5 <;> cases c6 <;> cases c7 <;> decide

/-- **`bytesToBits` inverts `bitsToBytes`** on any byte-boundary-aligned bit
stream (length a multiple of 8) — the packing identity that lets a byte-level
statement bind the deployed `huffmanDecode` (which reads `bytesToBits`). -/
theorem bytesToBits_bitsToBytes (X : List Bool) (h : X.length % 8 = 0) :
    bytesToBits (bitsToBytes X) = X := by
  induction X using bitsToBytes.induct with
  | case1 => simp [bitsToBytes, bytesToBits]
  | case2 b rest ih =>
    rw [bitsToBytes, bytesToBits]
    have hlen8 : (b :: rest).length ≥ 8 := by
      rw [List.length_cons]
      by_cases hz : rest.length + 1 < 8
      · exfalso; rw [List.length_cons] at h; omega
      · omega
    have hdrop : ((b :: rest).drop 8).length % 8 = 0 := by
      rw [List.length_drop]; omega
    rw [ih hdrop]
    have htake : ((b :: rest).take 8).length = 8 := by
      rw [List.length_take]; omega
    rw [byte_bits_roundtrip _ htake, List.take_append_drop]

/-! ## The RFC 7541 Appendix B encoder, and the round-trip theorem -/

/-- Number of 1-bits to pad `n` code bits up to an octet boundary (RFC 7541 §5.2:
the trailing bits are the EOS-code prefix, all ones, ≤ 7 of them). -/
def padLen (n : Nat) : Nat := (8 - n % 8) % 8

theorem padLen_le (n : Nat) : padLen n ≤ 7 := by unfold padLen; omega

def padBits (bs : Bytes) : List Bool := List.replicate (padLen (huffEncodeBits bs).length) true

/-- **The RFC 7541 Appendix B Huffman ENCODER.** Concatenate each octet's
codeword, then pad to an octet boundary with EOS-prefix (1) bits, and pack MSB-
first into bytes — exactly what an off-the-shelf client emits. -/
def huffEncode (bs : Bytes) : Bytes := bitsToBytes (huffEncodeBits bs ++ padBits bs)

theorem padded_len_mod8 (bs : Bytes) : (huffEncodeBits bs ++ padBits bs).length % 8 = 0 := by
  simp only [padBits, List.length_append, List.length_replicate, padLen]
  omega

/-- **The correctness theorem: the deployed QPACK/HPACK Huffman decoder is a
faithful inverse of the RFC 7541 Appendix B encoder.** For every octet string
`bs`, decoding its Huffman encoding recovers exactly `bs`. This binds the
DEPLOYED `huffmanDecode` (the function `H3/Qpack` runs) and holds for ALL inputs
— not one #guard vector. -/
theorem huffmanDecode_huffEncode (bs : Bytes) : huffmanDecode (huffEncode bs) = some bs := by
  unfold huffmanDecode huffEncode
  rw [bytesToBits_bitsToBytes _ (padded_len_mod8 bs), decode_encodeBits bs (padBits bs),
    padBits, pad_decode _ (padLen_le _)]
  simp

/-! ## Non-vacuity -/

/-- **Over-long padding is rejected (RFC 7541 §5.2).** A full all-ones octet is an
8-bit run of ones — an EOS-symbol payload, forbidden as padding — and the
deployed decoder returns `none`. A lenient decoder that accepted it would return
`some …` and FAIL to be the inverse. -/
theorem overlong_pad_rejected : huffmanDecode [0xff] = none := by decide

/-- **The round trip pins the exact code map.** The deployed decode of `'0'`'s
codeword is `some [0x30]`, and NOT `some [0x31]`: a decoder that mis-mapped this
codeword to a different symbol would violate `huffmanDecode_huffEncode`. -/
theorem decode_specific : huffmanDecode (huffEncode [0x30]) = some [0x30] :=
  huffmanDecode_huffEncode [0x30]

theorem decode_not_mismapped : huffmanDecode (huffEncode [0x30]) ≠ some [0x31] := by
  rw [decode_specific]; decide

/-! ## Axiom audit -/

#print axioms huffmanDecode_huffEncode
#print axioms prefixFree
#print axioms sym_consume
#print axioms overlong_pad_rejected

end Qpack
end H3
