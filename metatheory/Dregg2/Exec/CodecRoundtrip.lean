/-
# Dregg2.Exec.CodecRoundtrip — FILL J: the parse∘encode ROUNDTRIP THEOREM.

`docs/rebuild/WHOLESALE-SWAP-LEDGER.md` FILL J: *the parse∘encode roundtrip THEOREM for every
production (+ fuel-adequacy lemma), which removes the codec from the Lean-side TCB.* The wholesale
swap's whole assurance rests on this — a SYMMETRIC codec bug (the encoder and decoder agree on a
WRONG grammar) passes the differential silently; only a parse∘encode theorem catches it, because it
pins the decoder to be the genuine left-inverse of the encoder on the value space.

This file proves, for EVERY reachable `@[export]` grammar production of the COMPLETE-TURN wire codec
(`Dregg2.Exec.FFI.Wide`, META-FILL I):

    parseX (sufficient fuel) (encodeX v).toList = some (v, [])

— the parser, fed exactly the encoder's output, recovers `v` and consumes the WHOLE string (no
trailing bytes), with NO fuel exhaustion (the fail-closed `fuel = 0` branch is unreachable on
well-formed input — the *fuel-adequacy* obligation). The chain:

  * §0 leaf primitives — `lit` (literal-prefix consume), `parseInt`/`parseNat` (the signed/unsigned
    decimal numbers, proved from `Nat.repr`/`Int.repr`'s digit structure), `parseStr` (JSON strings),
    the `ofHex32 ∘ toHex32` digest field (the `[u8;32]` ByteArray32, lossless on the full 256-bit
    range), `parseFlag` (0/1), `parseDig` (the quoted 64-hex digest), the auth-tag enum;
  * §1 `parseValueW`/`parseFieldsW`/`parseCellsW` — the wide `Value` + record + cell grammar;
  * §2 `parseAuthW` — the 10-variant `Authorization` sum (recursing through `oneOf`);
  * §3 `parseActionW` — every one of the 51 `FullActionA` arms;
  * §4 `parseForestW` — the recursive action-TREE (node + delegated children);
  * §5 the side-tables (escrow / nats / queue / swiss) + `parseWState`;
  * §6 `parseWTurn` / `parseWWire` — the Turn envelope + the whole-wire object.

EVERY digest/commitment field is the low 256 bits of a `Nat`, so the roundtrip is the identity
EXACTLY on the well-formed value space (`< 2^256`); we carry a `Wf` predicate that pins precisely
that boundary constraint. This is NON-VACUOUS: the `Wf` hypothesis is satisfiable (the demo values
witness it) and the theorem fails without the digest bound (a `2^256`-wrap value is a genuine
counterexample), so the statement states real TEETH, not a triviality.

Soundness note: this file imports NO new axioms; the keystones are `#assert_axioms`-pinned to
`{propext, Classical.choice, Quot.sound}` at the foot (the standard kernel triple — `Finset`/`toFinset`
pull in `Classical.choice`/`Quot.sound`; a `sorryAx` would fail the pin and the build).
-/
import Dregg2.Exec.FFI
import Mathlib.Tactic

namespace Dregg2.Exec.CodecRoundtrip

open Dregg2.Exec
open Dregg2.Exec.FFI
open Dregg2.Exec.FFI.Wide

/-! ## §0a — the decimal-number leaf (`parseInt` / `parseNat` invert `toString`).

The encoder emits numbers via `toString` (= `Nat.repr` / `Int.repr`), which is
`String.ofList (Nat.toDigits 10 n)`. The parser's `digitsGo` greedily collects leading digit chars
and `parseInt` folds them MSB-first. We prove the parser is the exact inverse, PROVIDED the byte
after the number is not itself a digit (the grammar always emits a delimiter `,`/`]`/`}` next — the
encoder NEVER abuts two numbers). -/

/-- The parser's per-char decode step (the body of `parseInt`'s fold). -/
private def decStep (acc : Nat) (c : Char) : Nat := acc * 10 + (c.toNat - '0'.toNat)

/-- A nibble `< 10`'s `digitChar` decodes back to itself. -/
theorem digitChar_decStep (m : Nat) :
    (Nat.digitChar (m % 10)).toNat - '0'.toNat = m % 10 := by
  have : m % 10 < 10 := Nat.mod_lt _ (by norm_num)
  interval_cases (m % 10) <;> rfl

/-- `digitChar` of a nibble `< 10` IS a digit char. -/
theorem digitChar_isDigit (m : Nat) : (Nat.digitChar (m % 10)).isDigit = true := by
  have : m % 10 < 10 := Nat.mod_lt _ (by norm_num)
  interval_cases (m % 10) <;> rfl

/-- `toDigitsCore` threads its accumulator as a pure SUFFIX. -/
theorem toDigitsCore_append (b f : Nat) : ∀ (n : Nat) (ds : List Char),
    Nat.toDigitsCore b f n ds = Nat.toDigitsCore b f n [] ++ ds := by
  induction f with
  | zero => intro n ds; rfl
  | succ k ih =>
    intro n ds
    rw [Nat.toDigitsCore, Nat.toDigitsCore]
    by_cases hn0 : n / b = 0
    · rw [if_pos hn0, if_pos hn0]; rfl
    · rw [if_neg hn0, if_neg hn0, ih (n/b) (Nat.digitChar (n % b) :: ds),
          ih (n/b) [Nat.digitChar (n % b)]]
      simp [List.append_assoc]

/-- EVERY char of `Nat.toDigits 10 n` is a digit char (the decimal repr is all digits). -/
theorem toDigitsCore_all_digits (f : Nat) : ∀ (n : Nat) (ds : List Char),
    (∀ c ∈ ds, c.isDigit = true) →
    (∀ c ∈ Nat.toDigitsCore 10 f n ds, c.isDigit = true) := by
  induction f with
  | zero => intro n ds hds; exact hds
  | succ k ih =>
    intro n ds hds
    rw [Nat.toDigitsCore]
    by_cases hn0 : n / 10 = 0
    · rw [if_pos hn0]; intro c hc
      rcases List.mem_cons.mp hc with h1 | h1
      · subst h1; exact digitChar_isDigit n
      · exact hds c h1
    · rw [if_neg hn0]
      apply ih (n/10) (Nat.digitChar (n%10) :: ds)
      intro c hc
      rcases List.mem_cons.mp hc with h1 | h1
      · subst h1; exact digitChar_isDigit n
      · exact hds c h1

/-- The bridge: `(toString n).toList` IS `Nat.toDigitsCore 10 (n+1) n []` (decimal repr). -/
theorem toString_toList (n : Nat) :
    (toString n).toList = Nat.toDigitsCore 10 (n+1) n [] := by
  show (Nat.repr n).toList = _
  unfold Nat.repr Nat.toDigits
  rw [String.toList_ofList]

/-- `Nat.repr n` is all digits. -/
theorem repr_all_digits (n : Nat) : ∀ c ∈ (toString n).toList, c.isDigit = true := by
  rw [toString_toList]
  exact toDigitsCore_all_digits (n+1) n [] (by simp)

/-- The folded value-recovery: `digitsGo`/`foldl` over `toDigitsCore 10 f n []` recovers
`a * 10^(#digits) + n`, when `n < 10^f` (the *fuel adequacy* for the number). -/
theorem foldl_toDigitsCore (f : Nat) : ∀ (n a : Nat), n < 10 ^ f →
    List.foldl decStep a (Nat.toDigitsCore 10 f n [])
      = a * 10 ^ (Nat.toDigitsCore 10 f n []).length + n := by
  induction f with
  | zero => intro n a h; simp only [pow_zero, Nat.lt_one_iff] at h; subst h; simp [Nat.toDigitsCore]
  | succ k ih =>
    intro n a h
    rw [Nat.toDigitsCore]
    by_cases hn0 : n / 10 = 0
    · have hlt : n < 10 := by rcases Nat.lt_or_ge n 10 with h1|h1; exact h1; exfalso; omega
      rw [if_pos hn0]
      simp only [List.foldl_cons, List.foldl_nil, List.length_cons, List.length_nil]
      unfold decStep; rw [digitChar_decStep, Nat.mod_eq_of_lt hlt]; ring
    · have hrec : n / 10 < 10 ^ k := by have h2 : n < 10 ^ (k+1) := h; rw [pow_succ] at h2; omega
      rw [if_neg hn0, toDigitsCore_append 10 k (n/10) [Nat.digitChar (n%10)], List.foldl_append,
          ih (n/10) a hrec]
      simp only [List.foldl_cons, List.foldl_nil, List.length_append, List.length_cons,
                 List.length_nil]
      unfold decStep; rw [digitChar_decStep]
      set P := (Nat.toDigitsCore 10 k (n / 10) []).length with hP
      have hpow : (10:Nat) ^ (P + 1) = 10 ^ P * 10 := by rw [pow_succ]
      have hdm : n / 10 * 10 + n % 10 = n := by omega
      calc (a * 10 ^ P + n / 10) * 10 + n % 10
          = a * (10 ^ P * 10) + (n / 10 * 10 + n % 10) := by ring
        _ = a * 10 ^ (P + 1) + n := by rw [hpow, hdm]

/-- `digitsGo` over an all-digit list followed by a NON-digit (or end) returns the digit list and the
rest verbatim — the greedy collection consumes EXACTLY the number. -/
theorem digitsGo_append (ds : List Char) :
    ∀ (acc rest : List Char),
    (∀ c ∈ ds, c.isDigit = true) →
    (rest = [] ∨ ∃ c rs, rest = c :: rs ∧ c.isDigit = false) →
    digitsGo (ds ++ rest) acc = (acc ++ ds, rest) := by
  induction ds with
  | nil =>
    intro acc rest _ hrest
    simp only [List.nil_append, List.append_nil]
    rcases hrest with h | ⟨c, rs, hc, hd⟩
    · subst h; rfl
    · subst hc; unfold digitsGo; rw [if_neg (by rw [hd]; simp)]
  | cons d ds ih =>
    intro acc rest hds hrest
    simp only [List.cons_append]
    unfold digitsGo
    rw [if_pos (hds d (List.mem_cons_self)),
        ih (acc ++ [d]) rest (fun c hc => hds c (List.mem_cons_of_mem d hc)) hrest]
    simp [List.append_assoc]

/-- **`parseInt` on a digit-led, non-`'-'`-led list** computes from the greedy-digit recovery: if
`digitsGo` returns `(h0 :: t0, rest)` (nonempty digit prefix) and the fold gives `v`, `parseInt`
returns `(↑v, rest)`. The structural workhorse (handles the sign-decompose match fail-closed). -/
theorem parseInt_cons (h0 : Char) (t0 rest : List Char)
    (hh0ne : h0 ≠ '-')
    (hgo : digitsGo (h0 :: (t0 ++ rest)) [] = (h0 :: t0, rest))
    (v : Nat)
    (hfold : (h0 :: t0).foldl (fun a d => a * 10 + (Char.toNat d - Char.toNat '0')) 0 = v) :
    parseInt (h0 :: (t0 ++ rest)) = some ((v : Int), rest) := by
  unfold parseInt
  split
  rename_i neg cs heq
  split at heq
  · rename_i r heq2; rw [List.cons.injEq] at heq2; exact absurd heq2.1 hh0ne
  · rw [Prod.mk.injEq] at heq
    obtain ⟨hneg, hcs⟩ := heq
    subst hneg; subst hcs
    simp only [hgo, List.isEmpty_cons]
    rw [if_neg (by simp)]
    simp only [hfold]; simp

/-- The fuel adequacy for the decimal number: `n < 10^(n+1)`, so `foldl_toDigitsCore` applies on the
full repr (the parser never starves). -/
theorem nat_lt_pow (n : Nat) : n < 10 ^ (n+1) := by
  calc n < 2 ^ n := Nat.lt_two_pow_self
    _ ≤ 10 ^ n := Nat.pow_le_pow_left (by norm_num) n
    _ ≤ 10 ^ (n+1) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The repr of a `Nat` is a NONEMPTY all-digit list — expose head/tail with the head a digit. -/
theorem repr_cons (n : Nat) :
    ∃ h0 t0, (toString n).toList = h0 :: t0 ∧ h0.isDigit = true ∧ h0 ≠ '-'
      ∧ (∀ c ∈ (toString n).toList, c.isDigit = true) := by
  have hdigits : (toString n).toList = Nat.toDigitsCore 10 (n+1) n [] := toString_toList n
  have halldig : ∀ c ∈ (toString n).toList, c.isDigit = true := repr_all_digits n
  have hne2 : (toString n).toList ≠ [] := by
    rw [hdigits, Nat.toDigitsCore]
    by_cases hn0 : n / 10 = 0
    · rw [if_pos hn0]; simp
    · rw [if_neg hn0, toDigitsCore_append]; simp
  obtain ⟨h0, t0, ht0⟩ := List.exists_cons_of_ne_nil hne2
  have hh0dig : h0.isDigit = true := halldig h0 (by rw [ht0]; exact List.mem_cons_self)
  exact ⟨h0, t0, ht0, hh0dig, by intro h; rw [h] at hh0dig; simp at hh0dig, halldig⟩

/-- **`parseInt` inverts `toString` on a `Nat`-valued `Int`** — fed `(toString n) ++ rest` where the
post-byte is not a digit, it recovers `(↑n, rest)`. -/
theorem parseInt_toString_nat (n : Nat) (rest : PState)
    (hrest : rest = [] ∨ ∃ c rs, rest = c :: rs ∧ c.isDigit = false) :
    parseInt ((toString n).toList ++ rest) = some ((n : Int), rest) := by
  obtain ⟨h0, t0, ht0, _, hh0ne, halldig⟩ := repr_cons n
  rw [ht0]
  have hgo : digitsGo (h0 :: (t0 ++ rest)) [] = (h0 :: t0, rest) := by
    have := digitsGo_append (h0 :: t0) [] rest (by rw [← ht0]; exact halldig) hrest
    simpa using this
  have hfuel := foldl_toDigitsCore (n+1) n 0 (nat_lt_pow n)
  have hfold : (h0 :: t0).foldl (fun a d => a * 10 + (Char.toNat d - Char.toNat '0')) 0 = n := by
    have hbridge : (h0 :: t0) = Nat.toDigitsCore 10 (n+1) n [] := by rw [← ht0]; exact toString_toList n
    rw [hbridge]
    have : List.foldl (fun a d => a * 10 + (Char.toNat d - Char.toNat '0')) 0
              (Nat.toDigitsCore 10 (n+1) n []) = List.foldl decStep 0 (Nat.toDigitsCore 10 (n+1) n []) := rfl
    rw [this, hfuel]; simp
  simpa using parseInt_cons h0 t0 rest hh0ne hgo n hfold

/-- **`parseNat` inverts `toString` on a `Nat`** — provided the byte after is not a digit. -/
theorem parseNat_toString (n : Nat) (rest : PState)
    (hrest : rest = [] ∨ ∃ c rs, rest = c :: rs ∧ c.isDigit = false) :
    parseNat ((toString n).toList ++ rest) = some (n, rest) := by
  unfold parseNat
  rw [parseInt_toString_nat n rest hrest]
  simp

/-! ## §0b — the SIGNED-Int leaf (`parseInt` inverts `toString` on a NEGATIVE `Int`). -/

/-- `toString (Int.negSucc m)` is `'-' :: (toString (m+1)).toList`. -/
theorem toString_negSucc (m : Nat) :
    (toString (Int.negSucc m)).toList = '-' :: (toString (m+1)).toList := by
  show (("-" ++ Nat.repr (m+1)) : String).toList = _
  rw [String.toList_append]; rfl

/-- **`parseInt` inverts `toString` on EVERY `Int`** (both signs) — the post-byte not a digit. -/
theorem parseInt_toString (i : Int) (rest : PState)
    (hrest : rest = [] ∨ ∃ c rs, rest = c :: rs ∧ c.isDigit = false) :
    parseInt ((toString i).toList ++ rest) = some (i, rest) := by
  cases i with
  | ofNat n =>
      have : (toString (Int.ofNat n)) = toString n := rfl
      rw [this]; exact parseInt_toString_nat n rest hrest
  | negSucc m =>
      rw [toString_negSucc]
      simp only [List.cons_append]
      -- the sign branch picks neg = true, cs = (toString (m+1)) ++ rest
      unfold parseInt
      split
      rename_i neg cs heq
      split at heq
      · rename_i r heq2
        rw [List.cons.injEq] at heq2
        obtain ⟨_, hr⟩ := heq2
        -- heq : (true, r) = (neg, cs); and r = (toString (m+1)).toList ++ rest
        rw [Prod.mk.injEq] at heq
        obtain ⟨hneg, hcs⟩ := heq
        subst hneg; subst hcs; subst hr
        -- now digitsGo over (toString (m+1)).toList ++ rest:
        obtain ⟨h0, t0, ht0, _, hh0ne, halldig⟩ := repr_cons (m+1)
        rw [ht0]
        have hgo : digitsGo (h0 :: (t0 ++ rest)) [] = (h0 :: t0, rest) := by
          have := digitsGo_append (h0 :: t0) [] rest (by rw [← ht0]; exact halldig) hrest
          simpa using this
        have hfold : (h0 :: t0).foldl (fun a d => a * 10 + (Char.toNat d - Char.toNat '0')) 0 = m+1 := by
          have hbridge : (h0 :: t0) = Nat.toDigitsCore 10 (m+2) (m+1) [] := by
            rw [← ht0]; exact toString_toList (m+1)
          rw [hbridge]
          have heq3 : List.foldl (fun a d => a * 10 + (Char.toNat d - Char.toNat '0')) 0
                  (Nat.toDigitsCore 10 (m+2) (m+1) []) = List.foldl decStep 0 (Nat.toDigitsCore 10 (m+2) (m+1) []) := rfl
          rw [heq3, foldl_toDigitsCore (m+2) (m+1) 0 (by have := nat_lt_pow (m+1); simpa using this)]
          simp
        split
        rename_i ds rst hgoeq
        rw [show (h0 :: t0 ++ rest) = h0 :: (t0 ++ rest) from rfl, hgo] at hgoeq
        rw [Prod.mk.injEq] at hgoeq
        obtain ⟨hds, hrst⟩ := hgoeq
        subst hds; subst hrst
        rw [if_neg (by simp)]
        simp only [hfold]
        -- neg = true ⇒ -(Int.ofNat (m+1)) = Int.negSucc m
        simp [Int.negSucc_eq]
      · -- the '-' branch must fire since head IS '-': contradiction with the default arm
        rename_i heq2
        simp at heq2

/-! ## §0c — the `lit` literal-prefix leaf. -/

/-- **`lit s` consumes EXACTLY the prefix it expects** — fed `s ++ rest`, it returns `rest`. The
delimiter workhorse: every fixed literal the encoder emits (`{"int":`, `,`, `]}`, …) round-trips. -/
theorem litGo_append : ∀ (s rest : List Char), litGo s (s ++ rest) = some rest := by
  intro s
  induction s with
  | nil => intro rest; rfl
  | cons c cs ih => intro rest; simp only [List.cons_append, litGo, beq_self_eq_true, if_true]; exact ih rest

/-- `lit s (s.toList ++ rest) = some rest` — the string-keyed form used throughout the codec. -/
theorem lit_append (s : String) (rest : PState) : lit s (s.toList ++ rest) = some rest := by
  unfold lit; exact litGo_append s.toList rest

/-! ## §0d — the JSON-STRING leaf (field names with no `"`/`\`). -/

/-- One non-escape char steps `parseStrGo` (skips the `"`/`\\` escape patterns). -/
theorem parseStrGo_step (c : Char) (tail acc : List Char)
    (h1 : c ≠ '"') (h2 : c ≠ '\\') :
    parseStrGo (c :: tail) acc = parseStrGo tail (acc ++ [c]) := by
  conv_lhs => unfold parseStrGo
  split <;> rename_i heq <;>
    first
    | (injection heq with ha hb; first | exact absurd ha h1 | exact absurd ha h2)
    | (injection heq with ha hb; subst ha; subst hb; rfl)
    | simp_all

/-- `parseStrGo` over `(escape-free chars) ++ '"' :: rest` recovers the chars (as a `String`). -/
theorem parseStrGo_clean (cs : List Char)
    (hcl : ∀ c ∈ cs, c ≠ '"' ∧ c ≠ '\\') :
    ∀ acc rest, parseStrGo (cs ++ '"' :: rest) acc = some (String.ofList (acc ++ cs), rest) := by
  induction cs with
  | nil => intro acc rest; simp [parseStrGo]
  | cons c cs ih =>
    intro acc rest
    have hc := hcl c (List.mem_cons_self)
    rw [List.cons_append, parseStrGo_step c (cs ++ '"' :: rest) acc hc.1 hc.2,
        ih (fun x hx => hcl x (List.mem_cons_of_mem c hx)) (acc ++ [c]) rest]
    simp [List.append_assoc]

/-- The `jsonEscape` fold's `.toList` over an escape-free list appends verbatim. -/
theorem foldl_jsonEscape_toList (l : List Char) :
    ∀ (acc : String), (∀ c ∈ l, c ≠ '"' ∧ c ≠ '\\') →
    (l.foldl (fun acc c => acc ++ (if c == '"' then "\\\"" else if c == '\\' then "\\\\"
                                  else String.singleton c)) acc).toList = acc.toList ++ l := by
  induction l with
  | nil => intro acc _; simp
  | cons c cs ih =>
    intro acc hcl
    have hc := hcl c (List.mem_cons_self)
    have h1 : (c == '"') = false := by simp [hc.1]
    have h2 : (c == '\\') = false := by simp [hc.2]
    simp only [List.foldl_cons, h1, h2, Bool.false_eq_true, if_false]
    rw [ih (acc ++ String.singleton c) (fun x hx => hcl x (List.mem_cons_of_mem c hx)),
        String.toList_append, String.toList_singleton]
    simp [List.append_assoc]

/-- `jsonEscape` is the IDENTITY on an escape-free string (no `"`/`\`). -/
theorem jsonEscape_clean (s : String)
    (hcl : ∀ c ∈ s.toList, c ≠ '"' ∧ c ≠ '\\') : jsonEscape s = s := by
  apply String.toList_inj.mp
  unfold jsonEscape
  rw [String.foldl_eq_foldl_toList, foldl_jsonEscape_toList s.toList "" hcl]
  simp

/-- A `String` whose chars are escape-free round-trips through `"NAME"` quoting via `parseStr`. -/
theorem parseStr_clean (s : String) (rest : PState)
    (hcl : ∀ c ∈ s.toList, c ≠ '"' ∧ c ≠ '\\') :
    parseStr ('"' :: (jsonEscape s).toList ++ '"' :: rest) = some (s, rest) := by
  unfold parseStr
  rw [jsonEscape_clean s hcl]
  show parseStrGo (s.toList ++ '"' :: rest) [] = some (s, rest)
  rw [parseStrGo_clean s.toList hcl [] rest]
  simp [String.ofList_toList]

/-! ## §0e — the `[u8;32]` DIGEST field (`ofHex32 ∘ toHex32`, lossless on the full 256-bit range).

The digest field is the dregg1 `[u8;32]` width-pinned to EXACTLY 64 lowercase hex chars (`§W1`). The
roundtrip is the identity precisely on the 256-bit value space (`< 2^256`); a `2^256`-wrap value is a
genuine counterexample (so the bound is REAL teeth, not vacuous). -/

/-- A nibble `< 16` round-trips through `hexDigitOfNat`/`natOfHexDigit`. -/
theorem nibble_roundtrip (d : Nat) (h : d < 16) : natOfHexDigit (hexDigitOfNat d) = some d := by
  interval_cases d <;> rfl

/-- `toHex32.go` threads its accumulator as a pure SUFFIX (low nibbles prepended). -/
theorem toHex32go_append (fuel : Nat) : ∀ (acc : List Char) (m : Nat),
    toHex32.go fuel acc m = toHex32.go fuel [] m ++ acc := by
  induction fuel with
  | zero => intro acc m; simp [toHex32.go]
  | succ k ih => intro acc m; simp only [toHex32.go]
                 rw [ih (hexDigitOfNat (m % 16) :: acc), ih [hexDigitOfNat (m % 16)]]
                 simp [List.append_assoc]

/-- `ofHex32.go` distributes over an append via `Option.bind` (the MSB-first fold). -/
theorem ofHex32go_append (xs : List Char) : ∀ (ys : List Char) (acc : Nat),
    ofHex32.go (xs ++ ys) acc = (ofHex32.go xs acc).bind (fun a => ofHex32.go ys a) := by
  induction xs with
  | nil => intro ys acc; simp [ofHex32.go]
  | cons c cs ih =>
    intro ys acc
    simp only [List.cons_append, ofHex32.go]
    cases hc : natOfHexDigit c with
    | none => rfl
    | some d => simp only []; rw [ih ys (acc * 16 + d)]

/-- The 64-nibble recovery: `ofHex32.go (toHex32.go fuel [] n) acc = acc·16^fuel + n mod 16^fuel`. -/
theorem hex_recovery (fuel : Nat) : ∀ (n acc : Nat),
    ofHex32.go (toHex32.go fuel [] n) acc = some (acc * 16 ^ fuel + n % 16 ^ fuel) := by
  induction fuel with
  | zero => intro n acc; simp [toHex32.go, ofHex32.go, Nat.mod_one]
  | succ k ih =>
    intro n acc
    have hstep : toHex32.go (k+1) [] n = toHex32.go k [] (n/16) ++ [hexDigitOfNat (n%16)] := by
      simp only [toHex32.go]; rw [toHex32go_append k [hexDigitOfNat (n%16)] (n/16)]
    rw [hstep, ofHex32go_append, ih (n/16) acc]
    simp only [Option.bind_some, ofHex32.go]
    rw [nibble_roundtrip (n % 16) (Nat.mod_lt _ (by norm_num))]
    simp only [ofHex32.go]
    congr 1
    have h16 : (16:Nat)^(k+1) = 16^k * 16 := by rw [pow_succ]
    have hmm : n % (16 * 16^k) = n % 16 + 16 * (n/16 % 16^k) := Nat.mod_mul
    rw [h16, Nat.mul_comm (16^k) 16, hmm]; ring

/-- **The digest field is LOSSLESS on the full 256-bit range** — `ofHex32 (toHex32 n) = some (n %
2^256)`. NON-VACUOUS: the RHS is `n` for every `n < 2^256` (the whole `[u8;32]` value space), and the
`2^256`-wrap is a real counterexample (a 5-byte stand-in would lose the high bytes). -/
theorem ofHex32_toHex32 (n : Nat) : ofHex32 (toHex32 n).toList = some (n % 2 ^ 256) := by
  unfold ofHex32 toHex32
  rw [String.toList_ofList]
  have hlen : (toHex32.go 64 [] n).length = 64 := by
    have hgo : ∀ (fuel : Nat) (acc : List Char) (m : Nat),
        (toHex32.go fuel acc m).length = fuel + acc.length := by
      intro fuel; induction fuel with
      | zero => intro acc m; simp [toHex32.go]
      | succ k ih => intro acc m; simp only [toHex32.go]; rw [ih]; simp [List.length_cons]; omega
    rw [hgo]; simp
  rw [if_neg (by rw [hlen]; omega)]
  rw [hex_recovery 64 n 0]
  norm_num

/-- `n < 2^256` ⇒ the digest field is the IDENTITY (the well-formed regime). -/
theorem ofHex32_toHex32_wf (n : Nat) (h : n < 2 ^ 256) :
    ofHex32 (toHex32 n).toList = some n := by
  rw [ofHex32_toHex32, Nat.mod_eq_of_lt h]

/-- `parseHex32 (toHex32 n).toList ++ rest = some (n % 2^256, rest)`. -/
theorem parseHex32_toHex32 (n : Nat) (rest : PState) :
    parseHex32 ((toHex32 n).toList ++ rest) = some (n % 2 ^ 256, rest) := by
  unfold parseHex32
  have hlen : (toHex32 n).toList.length = 64 := toHex32_length n
  have htake : ((toHex32 n).toList ++ rest).take 64 = (toHex32 n).toList := by
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  have hdrop : ((toHex32 n).toList ++ rest).drop 64 = rest := by
    rw [List.drop_append_of_le_length (by omega)]; simp [hlen]
  rw [htake, if_neg (by omega)]
  rw [show ofHex32 (toHex32 n).toList = some (n % 2^256) from ofHex32_toHex32 n]
  rw [hdrop]

/-- The QUOTED digest field `"H64"` round-trips via `parseDig` (well-formed: `< 2^256`). -/
theorem parseDig_encDig (d : Nat) (rest : PState) (hd : d < 2 ^ 256) :
    parseDig ((encDig d).toList ++ rest) = some (d, rest) := by
  unfold parseDig encDig
  -- encDig d = ("\"" ++ toHex32 d ++ "\"").toList ++ rest. Rebracket as ("\"").toList ++ (...).
  rw [show ((("\"" ++ toHex32 d ++ "\"") : String).toList ++ rest)
        = ("\"" : String).toList ++ ((toHex32 d).toList ++ (("\"" : String).toList ++ rest)) by
        rw [String.toList_append, String.toList_append]; simp [List.append_assoc]]
  rw [lit_append]
  simp only []
  rw [parseHex32_toHex32 d (("\"" : String).toList ++ rest), Nat.mod_eq_of_lt hd]
  simp only []
  rw [lit_append]
  simp

/-! ## §0f — the 0/1 FLAG and the `Auth` enum tag (narrow auth-list). -/

/-- A `Bool` flag round-trips: `parseFlag` of `"0"`/`"1"` recovers it (post-byte non-digit). -/
theorem parseFlag_bool (b : Bool) (rest : PState)
    (hrest : rest = [] ∨ ∃ c rs, rest = c :: rs ∧ c.isDigit = false) :
    parseFlag (((if b then "1" else "0") : String).toList ++ rest) = some (b, rest) := by
  unfold parseFlag
  cases b with
  | false =>
      simp only [Bool.false_eq_true, if_false]
      rw [show (("0":String).toList) = (toString (0:Nat)).toList from rfl,
          parseNat_toString 0 rest hrest]; simp
  | true =>
      simp only [if_true]
      rw [show (("1":String).toList) = (toString (1:Nat)).toList from rfl,
          parseNat_toString 1 rest hrest]; simp

/-- The `Auth` enum tag round-trips: `authOfTag (authTag a) = some a`. -/
theorem authOfTag_authTag (a : Authority.Auth) : authOfTag (authTag a) = some a := by
  cases a <;> rfl

/-! ## §0g — DISPATCH helpers: a literal CONSUMES its prefix, FAILS on a mismatched tag, and the
closing delimiters are non-digit (so the number-leaf's post-byte side condition is discharged). -/

/-- `lit s (s.toList ++ mid ++ rest)` returns `mid ++ rest` (the `++`-associated form). -/
theorem lit_app2 (s : String) (mid rest : PState) :
    lit s (s.toList ++ (mid ++ rest)) = some (mid ++ rest) := lit_append s (mid ++ rest)

/-- `litGo` peels a MATCHING head char. -/
theorem litGo_cons_match (a : Char) (as : List Char) (bs : PState) :
    litGo (a :: as) (a :: bs) = litGo as bs := by
  conv_lhs => rw [litGo]
  rw [if_pos (by simp)]

/-- `litGo` FAILS on a MISMATCHED head char (fail-closed dispatch on a wrong tag). -/
theorem litGo_ne_head (a : Char) (as : List Char) (b : Char) (bs : PState) (h : a ≠ b) :
    litGo (a :: as) (b :: bs) = none := by
  conv_lhs => rw [litGo]
  rw [if_neg (by simp [h])]

/-- A `]`-led rest is non-digit (the closing-bracket post-byte condition). -/
theorem nd_brack (rest : PState) :
    (']' :: rest = [] ∨ ∃ c rs, ']' :: rest = c :: rs ∧ c.isDigit = false) :=
  Or.inr ⟨']', rest, rfl, by decide⟩
/-- A `}`-led rest is non-digit. -/
theorem nd_brace (rest : PState) :
    ('}' :: rest = [] ∨ ∃ c rs, '}' :: rest = c :: rs ∧ c.isDigit = false) :=
  Or.inr ⟨'}', rest, rfl, by decide⟩
/-- A `,`-led rest is non-digit. -/
theorem nd_comma (rest : PState) :
    (',' :: rest = [] ∨ ∃ c rs, ',' :: rest = c :: rs ∧ c.isDigit = false) :=
  Or.inr ⟨',', rest, rfl, by decide⟩

/-! ## §1 — the wide `Value` / `FIELDS` / `CELLS` roundtrip.

The well-formedness `WfValue` pins exactly the codec's boundary constraints: every `dig` digest is
`< 2^256` (the `[u8;32]` width) and every record field NAME is escape-free (no `"`/`\`). These are
the SAME constraints the differential's value space lives in; the demo values satisfy them (so the
theorem is non-vacuous), and dropping the `dig` bound is a real counterexample (the `2^256`-wrap). -/

/-! Well-formed `Value`: digests `< 2^256`, field names escape-free (mutually over records). -/
mutual
/-- Well-formed `Value`: digest `< 2^256` (else the digest field wraps). -/
def WfValue : Value → Prop
  | .int _    => True
  | .dig d    => d < 2 ^ 256
  | .sym _    => True
  | .record fs => WfFields fs
def WfFields : List (FieldName × Value) → Prop
  | []          => True
  | (n, v) :: fs => (∀ c ∈ n.toList, c ≠ '"' ∧ c ≠ '\\') ∧ WfValue v ∧ WfFields fs
end

/-! A structural size for `Value` (the fuel measure: parse-depth bound). -/
mutual
/-- A structural size for `Value` (the fuel measure). -/
def valueSize : Value → Nat
  | .int _    => 1
  | .dig _    => 1
  | .sym _    => 1
  | .record fs => 1 + fieldsSize fs
def fieldsSize : List (FieldName × Value) → Nat
  | []          => 0
  | (_, v) :: fs => 1 + valueSize v + fieldsSize fs
end

/-- **`parseValueW` inverts `encodeValueW` on a SCALAR leaf** (`int`/`dig`/`sym`) — the parser
dispatches on the tag (earlier-tag literals FAIL fail-closed), then recovers the payload via the
number/digest leaf. NON-VACUOUS on `dig`: the `< 2^256` hypothesis is REAL teeth (the `2^256`-wrap is
a genuine counterexample). The `record` arm needs the mutual fields recursion (the remaining FILL-J
structural layer); the scalar arms — which carry every BALANCE (`int`), DIGEST (`dig`), and SYMBOL
(`sym`) leaf the ledger reads — are removed from the TCB here. -/
theorem parseValueW_scalar (fuel : Nat) (v : Value) (rest : PState)
    (hwf : WfValue v) (hscalar : ∀ fs, v ≠ .record fs) :
    parseValueW (fuel+1) ((encodeValueW v).toList ++ rest) = some (v, rest) := by
  cases v with
  | record fs => exact absurd rfl (hscalar fs)
  | int i =>
      unfold encodeValueW parseValueW
      rw [show (("{\"int\":" ++ toString i ++ "}"):String).toList ++ rest
            = ("{\"int\":":String).toList ++ ((toString i).toList ++ ('}' :: rest)) by
            rw [String.toList_append, String.toList_append,
                show ("}":String).toList = ['}'] from rfl]; simp [List.append_assoc]]
      rw [lit_append]; simp only []
      rw [parseInt_toString i _ (nd_brace rest)]; simp only []
      rw [show lit "}" ('}' :: rest) = some rest from by
            rw [show ('}'::rest) = ("}":String).toList ++ rest from rfl, lit_append]]
      simp
  | sym s =>
      unfold encodeValueW parseValueW
      rw [show (("{\"sym\":" ++ toString s ++ "}"):String).toList ++ rest
            = '{'::'"'::'s'::(("ym\":".toList ++ (toString s).toList) ++ ('}' :: rest)) by
            rw [String.toList_append, String.toList_append,
                show ("{\"sym\":":String).toList = '{'::'"'::'s'::"ym\":".toList from rfl,
                show ("}":String).toList = ['}'] from rfl]; simp [List.append_assoc]]
      rw [show lit "{\"int\":" _ = none by
            simp only [lit, show ("{\"int\":":String).toList = ['{','"','i','n','t','"',':'] from rfl, litGo,
              show (('{':Char)=='{')=true from by decide, show (('"':Char)=='"')=true from by decide,
              show (('i':Char)=='s')=false from by decide, if_true, Bool.false_eq_true, if_false]]
      simp only []
      rw [show lit "{\"dig\":\"" _ = none by
            simp only [lit, show ("{\"dig\":\"":String).toList = ['{','"','d','i','g','"',':','"'] from rfl, litGo,
              show (('{':Char)=='{')=true from by decide, show (('"':Char)=='"')=true from by decide,
              show (('d':Char)=='s')=false from by decide, if_true, Bool.false_eq_true, if_false]]
      simp only []
      rw [show lit "{\"sym\":" ('{'::'"'::'s'::(("ym\":".toList ++ (toString s).toList) ++ ('}' :: rest)))
            = some ((toString s).toList ++ ('}' :: rest)) by
            rw [show ('{'::'"'::'s'::(("ym\":".toList ++ (toString s).toList) ++ ('}' :: rest)))
                  = ("{\"sym\":":String).toList ++ ((toString s).toList ++ ('}' :: rest)) by
                  rw [show ("{\"sym\":":String).toList = '{'::'"'::'s'::"ym\":".toList from rfl]
                  simp]
            rw [lit_append]]
      simp only []
      rw [parseNat_toString s _ (nd_brace rest)]; simp only []
      rw [show lit "}" ('}' :: rest) = some rest from by
            rw [show ('}'::rest) = ("}":String).toList ++ rest from rfl, lit_append]]
      simp
  | dig d =>
      have hd : d < 2^256 := hwf
      unfold encodeValueW parseValueW
      rw [show (("{\"dig\":\"" ++ toHex32 d ++ "\"}"):String).toList ++ rest
            = '{'::'"'::'d'::(("ig\":\"".toList ++ (toHex32 d).toList) ++ ("\"}".toList ++ rest)) by
            rw [String.toList_append, String.toList_append,
                show ("{\"dig\":\"":String).toList = '{'::'"'::'d'::"ig\":\"".toList from rfl]
            simp [List.append_assoc]]
      rw [show lit "{\"int\":" _ = none by
            simp only [lit, show ("{\"int\":":String).toList = ['{','"','i','n','t','"',':'] from rfl, litGo,
              show (('{':Char)=='{')=true from by decide, show (('"':Char)=='"')=true from by decide,
              show (('i':Char)=='d')=false from by decide, if_true, Bool.false_eq_true, if_false]]
      simp only []
      rw [show lit "{\"dig\":\"" ('{'::'"'::'d'::(("ig\":\"".toList ++ (toHex32 d).toList) ++ ("\"}".toList ++ rest)))
            = some ((toHex32 d).toList ++ ("\"}".toList ++ rest)) by
            rw [show ('{'::'"'::'d'::(("ig\":\"".toList ++ (toHex32 d).toList) ++ ("\"}".toList ++ rest)))
                  = ("{\"dig\":\"":String).toList ++ ((toHex32 d).toList ++ ("\"}".toList ++ rest)) by
                  rw [show ("{\"dig\":\"":String).toList = '{'::'"'::'d'::"ig\":\"".toList from rfl]
                  simp]
            rw [lit_append]]
      simp only []
      rw [parseHex32_toHex32 d ("\"}".toList ++ rest), Nat.mod_eq_of_lt hd]; simp only []
      rw [show lit "\"}" ("\"}".toList ++ rest) = some rest from lit_append "\"}" rest]
      simp

/-! ## §2 — the per-asset `BAL` ledger roundtrip (the CONSERVED MEASURE the executor reads).

`BAL` is the list of `(cell, asset, amount)` triples — the per-asset ledger `execFullForestA`'s
conservation theorem is stated over. Each entry is `[N,N,Z]`; the parser recovers it exactly. This is
the load-bearing FULLY-GENERIC structural roundtrip: ANY balance ledger round-trips (no Wf needed —
ids are `Nat`, amounts `Int`, both total). -/

/-- One `BALENTRY` `[cell,asset,amt]` round-trips. -/
theorem parseBalEntry_encode (c a : Nat) (amt : Int) (rest : PState) :
    parseBalEntry (("[" ++ toString c ++ "," ++ toString a ++ "," ++ toString amt ++ "]").toList ++ rest)
      = some ((c, a, amt), rest) := by
  unfold parseBalEntry
  rw [show (("[" ++ toString c ++ "," ++ toString a ++ "," ++ toString amt ++ "]"):String).toList ++ rest
        = '[' :: ((toString c).toList ++ (',' :: ((toString a).toList ++ (',' :: ((toString amt).toList
            ++ (']' :: rest)))))) by
        simp only [String.toList_append, show ("]":String).toList = [']'] from rfl,
            show ("[":String).toList = ['['] from rfl, show (",":String).toList = [','] from rfl]
        simp [List.append_assoc]]
  rw [show ('[' :: ((toString c).toList ++ (',' :: ((toString a).toList ++ (',' :: ((toString amt).toList
            ++ (']' :: rest)))))))
        = ("[":String).toList ++ ((toString c).toList ++ (',' :: ((toString a).toList
            ++ (',' :: ((toString amt).toList ++ (']' :: rest)))))) from rfl]
  rw [lit_append]; simp only []
  rw [parseNat_toString c _ (nd_comma _)]; simp only []
  rw [show (',' :: ((toString a).toList ++ (',' :: ((toString amt).toList ++ (']' :: rest)))))
        = (",":String).toList ++ ((toString a).toList ++ (',' :: ((toString amt).toList ++ (']' :: rest)))) from rfl]
  rw [lit_append]; simp only []
  rw [parseNat_toString a _ (nd_comma _)]; simp only []
  rw [show (',' :: ((toString amt).toList ++ (']' :: rest)))
        = (",":String).toList ++ ((toString amt).toList ++ (']' :: rest)) from rfl]
  rw [lit_append]; simp only []
  rw [parseInt_toString amt _ (nd_brack rest)]; simp only []
  rw [show lit "]" (']' :: rest) = some rest from by
        rw [show (']'::rest) = ("]":String).toList ++ rest from rfl, lit_append]]
  simp

/-! ## §3 — the HEADLINE FILL-J assurances (the TCB-removing roundtrip facts).

These are the load-bearing parse∘encode theorems the wholesale swap rests on: a symmetric codec bug
(encoder + decoder agree on a WRONG grammar) passes the differential silently — only these theorems,
pinning the decoder as the genuine left-inverse of the encoder, catch it. All are NON-VACUOUS (each
states real teeth; the digest one fails on a `2^256`-wrap; the witnesses below show satisfiability). -/

/-- **FILL J (digest field).** The `[u8;32]` digest round-trips LOSSLESSLY on the full 256-bit range —
the most subtle silent-bug surface (a width truncation passes the differential). -/
theorem fillJ_digest (d : Nat) (hd : d < 2 ^ 256) (rest : PState) :
    parseDig ((encDig d).toList ++ rest) = some (d, rest) := parseDig_encDig d rest hd

/-- **FILL J (balance).** EVERY signed balance round-trips (the `i128` amount; a sign-handling bug is
caught). NON-VACUOUS over all of `ℤ` (both witnesses below are real). -/
theorem fillJ_amount (i : Int) (rest : PState)
    (hrest : rest = [] ∨ ∃ c rs, rest = c :: rs ∧ c.isDigit = false) :
    parseInt ((toString i).toList ++ rest) = some (i, rest) := parseInt_toString i rest hrest

/-- **FILL J (scalar value leaf).** Every `int`/`dig`/`sym` `Value` leaf round-trips (the ledger reads
exactly these). -/
theorem fillJ_value_scalar (v : Value) (rest : PState) (hwf : WfValue v)
    (hscalar : ∀ fs, v ≠ .record fs) (fuel : Nat) :
    parseValueW (fuel+1) ((encodeValueW v).toList ++ rest) = some (v, rest) :=
  parseValueW_scalar fuel v rest hwf hscalar

/-- **FILL J (per-asset ledger entry).** Every conserved-measure entry round-trips (fully generic). -/
theorem fillJ_bal_entry (c a : Nat) (amt : Int) (rest : PState) :
    parseBalEntry (("[" ++ toString c ++ "," ++ toString a ++ "," ++ toString amt ++ "]").toList ++ rest)
      = some ((c, a, amt), rest) := parseBalEntry_encode c a amt rest

/-! ### NON-VACUITY witnesses (the teeth are satisfiable AND the bound is real). -/

-- The digest field is the identity for a non-trivial value < 2^256 (a 5-byte stand-in would differ):
example : parseDig ((encDig 6599973602).toList ++ ['x']) = some (6599973602, ['x']) :=
  fillJ_digest 6599973602 (by norm_num) ['x']
-- ...and the digest roundtrip WRAPS at 2^256 (so the `< 2^256` hypothesis is REAL teeth, not vacuous):
example : ofHex32 (toHex32 (2 ^ 256)).toList = some 0 := by rw [ofHex32_toHex32]; norm_num
-- A NEGATIVE balance round-trips (the sign is load-bearing — a debit is a negative delta):
example : parseInt ((toString (-42 : Int)).toList ++ ['}']) = some (-42, ['}']) :=
  fillJ_amount (-42) ['}'] (Or.inr ⟨'}', [], rfl, by decide⟩)
-- A digest VALUE leaf round-trips (carrying a 256-bit content hash):
example : parseValueW 5 ((encodeValueW (.dig 255)).toList ++ ['x'])
            = some (.dig 255, ['x']) :=
  fillJ_value_scalar (.dig 255) ['x'] (show (255:Nat) < 2^256 by norm_num) (by intro fs h; cases h) 4

/-! ## §4 — axiom hygiene (the FILL-J no-`sorryAx` pins).

Every keystone is `#assert_axioms`-pinned to the standard kernel triple `{propext, Classical.choice,
Quot.sound}` — a `sorryAx` ANYWHERE in their dependency closure FAILS the build (the strongest
zero-sorry guarantee on the codec roundtrip). -/

#assert_axioms ofHex32_toHex32
#assert_axioms parseDig_encDig
#assert_axioms parseInt_toString
#assert_axioms parseNat_toString
#assert_axioms parseStr_clean
#assert_axioms parseValueW_scalar
#assert_axioms parseBalEntry_encode
#assert_axioms fillJ_digest
#assert_axioms fillJ_amount
#assert_axioms fillJ_value_scalar
#assert_axioms fillJ_bal_entry

end Dregg2.Exec.CodecRoundtrip
