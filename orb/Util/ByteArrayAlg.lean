/-!
# Util.ByteArrayAlg — the wire-field `++`/`extract` algebra for `ByteArray`

Reusable lemmas for proving that a **fixed-layout wire parser recovers exactly
the fields its builder concatenated**: a message is built `f1 ++ f2 ++ f3` and
parsed by `extract` at cumulative byte offsets.

## Honest scope — read this before citing the module

An earlier residual note (`Control/Channel.lean` §2b) claimed drorb had *no*
`++`/`extract` algebra for `ByteArray` and that one had to be built from
scratch. **That claim was wrong.** Lean 4.30 core already ships a substantially
complete `ByteArray` algebra, verified present in this toolchain:

  `size_append`, `append_assoc`, `append_empty`, `empty_append`,
  `append_left_inj`, `append_right_inj`, `data_append`, `data_extract`,
  `size_extract`, `extract_append`, `extract_append_eq_left`,
  `extract_append_eq_right`, `extract_append_size_add`,
  `extract_append_size_left`, `extract_extract`, `extract_zero_size`,
  `extract_same`, `extract_eq_empty_iff`, `getElem_append_left`,
  `getElem_append_right`, `getElem_extract`.

So this module is **not** a foundational build. It is a small set of *composite*
lemmas core does not state — the ones phrased at the offsets a wire parser
actually uses (a slice strictly inside the left component; the three-field and
two-field splits with the field sizes given as hypotheses). Everything here is
proved from the core lemmas above; nothing is axiomatic.

`extract i j` is the half-open slice `[i, j)`, clamped to the size.
-/

namespace ByteArray

/-! ## §1  A slice strictly inside the left component

Core gives `extract_append_size_left` only for the slice ending exactly at
`a.size`. A parser reading an early field of a longer message needs the general
`j ≤ a.size` form. -/

/-- A slice entirely inside the first component sees only that component. -/
theorem extract_append_left_of_le {a b : ByteArray} {i j : Nat} (h : j ≤ a.size) :
    (a ++ b).extract i j = a.extract i j := by
  rw [extract_append]
  have hb : b.extract (i - a.size) (j - a.size) = ByteArray.empty := by
    rw [extract_eq_empty_iff]; omega
  rw [hb, append_empty]

/-- The size of a slice that lies within the array is exactly its span. -/
theorem size_extract_of_le {a : ByteArray} {i j : Nat} (h : j ≤ a.size) :
    (a.extract i j).size = j - i := by
  rw [size_extract, Nat.min_eq_left h]

/-! ## §2  The two-field split

`msg = f1 ++ f2` with `f1.size = n1`: the parser slices `[0, n1)` and
`[n1, size)`. -/

theorem extract_split2_fst (f1 f2 : ByteArray) {n1 : Nat} (h1 : f1.size = n1) :
    (f1 ++ f2).extract 0 n1 = f1 :=
  extract_append_eq_left h1.symm

theorem extract_split2_snd (f1 f2 : ByteArray) {n1 : Nat} (h1 : f1.size = n1) :
    (f1 ++ f2).extract n1 (f1 ++ f2).size = f2 :=
  extract_append_eq_right h1.symm (by rw [size_append, h1])

/-! ## §3  The three-field split

`msg = f1 ++ f2 ++ f3` — note `++` is left-associated, so this is
`(f1 ++ f2) ++ f3` — with `f1.size = n1`, `f2.size = n2`. The parser slices
`[0, n1)`, `[n1, n1+n2)`, `[n1+n2, size)`. This is exactly the shape of the
Noise handshake message `e ‖ enc(s) ‖ enc(payload)`. -/

theorem extract_split3_fst (f1 f2 f3 : ByteArray) {n1 : Nat} (h1 : f1.size = n1) :
    (f1 ++ f2 ++ f3).extract 0 n1 = f1 := by
  rw [extract_append_left_of_le (b := f3) (by rw [size_append]; omega),
      extract_append_eq_left h1.symm]

theorem extract_split3_snd (f1 f2 f3 : ByteArray) {n1 n2 : Nat}
    (h1 : f1.size = n1) (h2 : f2.size = n2) :
    (f1 ++ f2 ++ f3).extract n1 (n1 + n2) = f2 := by
  rw [extract_append_left_of_le (b := f3) (by rw [size_append]; omega),
      extract_append_eq_right h1.symm (by rw [h1, h2])]

theorem extract_split3_thd (f1 f2 f3 : ByteArray) {n1 n2 : Nat}
    (h1 : f1.size = n1) (h2 : f2.size = n2) :
    (f1 ++ f2 ++ f3).extract (n1 + n2) (f1 ++ f2 ++ f3).size = f3 :=
  extract_append_eq_right (by rw [size_append, h1, h2])
    (by rw [size_append, size_append, h1, h2])

/-! ### Absolute-offset forms

Real parsers slice at *absolute literal* offsets (`extract 32 80`), not at
`n1 + n2`. These variants take the offset arithmetic as a side condition so the
caller can discharge it by `omega` instead of relying on defeq unification of
the literals. -/

theorem extract_split3_snd' (f1 f2 f3 : ByteArray) {n1 n2 n3 : Nat}
    (h1 : f1.size = n1) (h2 : f2.size = n2) (h3 : n1 + n2 = n3) :
    (f1 ++ f2 ++ f3).extract n1 n3 = f2 := by
  subst h3; exact extract_split3_snd f1 f2 f3 h1 h2

theorem extract_split3_thd' (f1 f2 f3 : ByteArray) {n1 n2 n3 : Nat}
    (h1 : f1.size = n1) (h2 : f2.size = n2) (h3 : n1 + n2 = n3) :
    (f1 ++ f2 ++ f3).extract n3 (f1 ++ f2 ++ f3).size = f3 := by
  subst h3; exact extract_split3_thd f1 f2 f3 h1 h2

/-! ## §4  Field sizes of a built message -/

theorem size_append3 (f1 f2 f3 : ByteArray) :
    (f1 ++ f2 ++ f3).size = f1.size + f2.size + f3.size := by
  rw [size_append, size_append]

end ByteArray
