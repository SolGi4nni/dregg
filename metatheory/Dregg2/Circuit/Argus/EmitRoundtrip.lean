/-
# Dregg2.Circuit.Argus.EmitRoundtrip — closing the EMIT edge with a Lean round-trip.

## The edge this closes

`Dregg2.Circuit.Emit.EffectVmEmit.emitVmJson` renders an `EffectVmDescriptor` to the canonical
wire string the running prover's descriptor interpreter ingests
(`circuit/src/lean_descriptor_air.rs::parse_vm_descriptor`, the wire-decode half of the EffectVM
swap; the registry `circuit/src/effect_vm_descriptors.rs` embeds those exact bytes keyed by selector).
Today that Lean→Rust seam is guarded ONLY by a SHA-256 fingerprint
(`effect_vm_descriptors.rs::all_descriptors_parse_and_match_fingerprint`): the test re-hashes the
embedded bytes and re-parses them, so a *drift* (a re-emit that silently changes a gate, or a stale
committed JSON) fails CI. But a fingerprint is a black box — it does NOT establish that `emitVmJson`
SERIALIZES the descriptor it claims: that the rendered bytes can be parsed back into the SAME
descriptor, with no field silently dropped, merged, or aliased. If `emitVmJson` lost a field (say it
rendered two distinct descriptors to the same bytes), the fingerprint would happily certify the lossy
bytes; the soundness teeth (`satisfiedVm`, the per-effect faithfulness/anti-ghost theorems) are stated
about the in-Lean `EffectVmDescriptor`, so a lossy serialization would mean the BYTES the prover runs
need not carry the proved content.

This module closes that gap **inside Lean** with a genuine round-trip:

  * `parseVmJson : List Char → Option EffectVmDescriptor` — a recursive-descent parser that is a
    FAITHFUL STRUCTURAL MIRROR of the Rust `parse_vm_descriptor` (same grammar: the `{"t":…}`-tagged
    expr/constraint/hash-input objects, the `digest_col`/`arity`/`inputs` hash sites, the `wire`/`bits`
    ranges, the six fixed top-level keys). It is specialised to the CANONICAL emitter output
    (whitespace-free, fixed key order) — see §MODELING below — which is exactly the byte set the seam
    ever carries.

  * **`parseVmJson_emitVmJson`** (the deliverable): for every `wf`-well-formed descriptor `d`,
    `parseVmJson (emitVmJson d).toList = some d`. So `emitVmJson` is INJECTIVE and INFORMATION-
    PRESERVING on well-formed descriptors: two distinct descriptors cannot render to the same wire
    bytes (`emitVmJson_injective`), and every field the Lean soundness theorems pin is recoverable
    from the bytes the prover runs. The fingerprint now guards bytes whose MEANING is proved faithful.

## The hard core (genuinely proved, axiom-clean)

The crux is the decimal NUMBER round-trip: the emitter renders `Nat`/`Int` via `toString`
(`Nat.repr` = `String.ofList (Nat.toDigits 10 ·)`), so the parser must INVERT `Nat.toDigits`. That is
NOT push-button (`decide` cannot reduce `Nat.repr`'s well-founded recursion, and `native_decide` is
banned). We prove it from scratch: `tdc_append` (the accumulator threads as a tail append),
`tdc_fold` (the Horner fold over the digit list recovers `start·10^k + n`), `tdc_all_isDig` (every
produced char is an ASCII digit), giving `readNat_toString` / `readInt_toString` — the numeral
round-trip mirroring Rust `parse_int`. Everything below is `#assert_axioms`-clean
(⊆ {propext, Classical.choice, Quot.sound}).

## §MODELING — the one honest modeling choice (named, not hidden)

The Rust `parse_vm_descriptor` reads the six top-level keys in a *loop* (any order, tolerant). The
Lean `parseVmJson` reads them in the FIXED order `emitVmJson` emits (name → trace_width →
public_input_count → constraints → hash_sites → ranges). This is sound for the round-trip — we only
ever parse `emitVmJson` output, which is canonical — and is the standard "canonical-form parser"
modeling for a serializer round-trip. It does NOT model the Rust parser's order-tolerance on
adversarial/hand-written JSON; that tolerance is irrelevant to the Lean→Rust SEAM (the bytes are
machine-emitted), and the fingerprint already pins the bytes verbatim. The residual is: the Rust
`JsonCursor` parser is mirrored STRUCTURALLY here but is not itself the verified artifact — a true
"the Rust function realizes `parseVmJson`" theorem would require a Rust-semantics model
(see the module-tail note).
-/
import Dregg2.Circuit.Emit.EffectVmEmit

namespace Dregg2.Circuit.Argus.EmitRoundtrip

open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Nat

/-! ## §1 — The decimal NUMBER codec core (the `Nat.toDigits` inverse).

The emitter renders every numeric field with `toString`. For `Nat`, `toString n = Nat.repr n =
String.ofList (Nat.toDigits 10 n)` and `Nat.toDigits 10 n = Nat.toDigitsCore 10 (n+1) n []`. To
parse a numeral back we must invert that. We prove the three structural facts the inversion needs. -/

/-- Digit value of an ASCII char (`'0'..'9' ↦ 0..9`; junk for non-digits). -/
def dval (c : Char) : Nat := c.toNat - 48
/-- Is `c` an ASCII decimal digit (`'0'..'9'`)? -/
def isDig (c : Char) : Bool := decide (48 ≤ c.toNat ∧ c.toNat ≤ 57)
/-- The Horner fold step the digit reader uses (`acc·10 + digit`). -/
def gg (a : Nat) (c : Char) : Nat := a * 10 + dval c

/-- `dval` inverts `Nat.digitChar` on a single decimal digit. -/
theorem dval_digitChar (d : Nat) (h : d < 10) : dval (Nat.digitChar d) = d := by
  interval_cases d <;> rfl

/-- A decimal digit char produced by `Nat.digitChar` is classified as a digit. -/
theorem digitChar_isDig (d : Nat) (h : d < 10) : isDig (Nat.digitChar d) = true := by
  interval_cases d <;> rfl

/-- The `toDigitsCore` accumulator threads as a tail append: producing `n`'s digits onto `ds`
equals producing them onto `[]` then appending `ds`. (High digit ends up leftmost.) -/
theorem tdc_append (fuel : Nat) : ∀ (n : Nat), n < fuel → ∀ (ds : List Char),
    Nat.toDigitsCore 10 fuel n ds = Nat.toDigitsCore 10 fuel n [] ++ ds := by
  induction fuel with
  | zero => intro n h; omega
  | succ f ih =>
    intro n hn ds; unfold Nat.toDigitsCore
    by_cases hn' : n / 10 = 0
    · simp [hn']
    · simp only [hn']
      have hlt : n / 10 < f := by
        have : n / 10 < n := Nat.div_lt_self (by omega) (by omega); omega
      rw [ih (n/10) hlt (Nat.digitChar (n%10) :: ds), ih (n/10) hlt [Nat.digitChar (n%10)]]; simp

/-- **The Horner-fold inverse.** Folding `gg` from `start` over `n`'s decimal digits yields
`start·10^k + n` where `k` is the digit count — i.e. the digits reconstruct `n` exactly. -/
theorem tdc_fold (fuel : Nat) : ∀ (n : Nat), n < fuel → ∀ (start : Nat),
    (Nat.toDigitsCore 10 fuel n []).foldl gg start
      = start * 10 ^ (Nat.toDigitsCore 10 fuel n []).length + n := by
  induction fuel with
  | zero => intro n h; omega
  | succ f ih =>
    intro n hn start; unfold Nat.toDigitsCore
    by_cases hn' : n / 10 = 0
    · have hn10 : n < 10 := by
        rcases Nat.lt_or_ge n 10 with h | h
        · exact h
        · exfalso; have := Nat.div_pos h (by omega); omega
      rw [if_pos hn']
      simp only [List.foldl_cons, List.foldl_nil, List.length_cons, List.length_nil]
      have hmod : n % 10 = n := Nat.mod_eq_of_lt hn10
      rw [gg, hmod, dval_digitChar n hn10, Nat.zero_add, pow_one]
    · have hlt : n / 10 < f := by
        have : n / 10 < n := Nat.div_lt_self (by omega) (by omega); omega
      rw [if_neg hn', tdc_append f (n/10) hlt [Nat.digitChar (n%10)], List.foldl_append,
          ih (n/10) hlt start]
      simp only [List.length_append, List.length_cons, List.length_nil, List.foldl_cons,
                 List.foldl_nil]
      rw [gg]
      have hm : n % 10 < 10 := Nat.mod_lt _ (by omega)
      rw [dval_digitChar (n%10) hm]
      have hdm : 10 * (n/10) + n%10 = n := by rw [Nat.add_comm]; exact Nat.mod_add_div n 10
      rw [pow_succ]; ring_nf; omega

/-- Every char produced by `Nat.toDigitsCore 10 …` is a decimal digit. -/
theorem tdc_all_isDig (fuel : Nat) : ∀ (n : Nat), n < fuel →
    ∀ c ∈ Nat.toDigitsCore 10 fuel n [], isDig c = true := by
  induction fuel with
  | zero => intro n h; omega
  | succ f ih =>
    intro n hn c hc; unfold Nat.toDigitsCore at hc
    by_cases hn' : n / 10 = 0
    · rw [if_pos hn'] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      have hm : n % 10 < 10 := Nat.mod_lt _ (by omega)
      exact digitChar_isDig _ hm
    · rw [if_neg hn'] at hc
      have hlt : n / 10 < f := by
        have : n / 10 < n := Nat.div_lt_self (by omega) (by omega); omega
      rw [tdc_append f (n/10) hlt [Nat.digitChar (n%10)]] at hc
      rcases List.mem_append.mp hc with h | h
      · exact ih (n/10) hlt c h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        subst h
        have hm : n % 10 < 10 := Nat.mod_lt _ (by omega)
        exact digitChar_isDig _ hm

/-- `Nat.toDigits 10 n` is never empty (it carries at least the units digit). -/
theorem toDigits_ne_nil (n : Nat) : Nat.toDigits 10 n ≠ [] := by
  unfold Nat.toDigits Nat.toDigitsCore
  by_cases hn' : n / 10 = 0
  · simp [hn']
  · rw [if_neg hn']
    have hlt : n / 10 < n := Nat.div_lt_self (by omega) (by omega)
    rw [tdc_append n (n/10) hlt [Nat.digitChar (n%10)]]
    simp

/-- `(toString n).toList = Nat.toDigits 10 n` — the `Nat` renderer is exactly its digit list. -/
theorem toString_toList (n : Nat) : (toString n).toList = Nat.toDigits 10 n := by
  show (String.ofList (Nat.toDigits 10 n)).toList = Nat.toDigits 10 n
  exact String.toList_ofList

/-! ## §2 — The numeral readers (mirror of Rust `parse_int`). -/

/-- Split the maximal leading run of decimal digits off a char list. -/
def takeDigits : List Char → List Char × List Char
  | []      => ([], [])
  | c :: cs => if isDig c then
                 let (ds, rest) := takeDigits cs
                 (c :: ds, rest)
               else ([], c :: cs)

/-- Read a non-negative decimal numeral: the maximal digit prefix, Horner-folded. Fails when there
is no leading digit (Rust `parse_int`'s "expected integer at byte _" error). -/
def readNat (cs : List Char) : Option (Nat × List Char) :=
  match takeDigits cs with
  | ([], _)    => none
  | (ds, rest) => some (ds.foldl gg 0, rest)

/-- Read a (possibly negative) decimal numeral as `Int`: an optional leading `'-'` then `readNat`.
Mirror of Rust `parse_int` (which consumes a `-` then digits). -/
def readInt (cs : List Char) : Option (Int × List Char) :=
  match cs with
  | '-' :: rest =>
    match readNat rest with
    | some (n, r) => some (-(Int.ofNat n), r)
    | none        => none
  | _ =>
    match readNat cs with
    | some (n, r) => some (Int.ofNat n, r)
    | none        => none

/-- If a digit-list `ds` (all digits) is followed by a non-digit head, `takeDigits` splits exactly
`ds`, leaving the remainder verbatim. -/
theorem takeDigits_append (ds : List Char) (hds : ∀ c ∈ ds, isDig c = true)
    (rest : List Char) (hrest : ∀ h t, rest = h :: t → isDig h = false) :
    takeDigits (ds ++ rest) = (ds, rest) := by
  induction ds with
  | nil =>
    simp only [List.nil_append]
    cases rest with
    | nil => rfl
    | cons h t => have : isDig h = false := hrest h t rfl; simp [takeDigits, this]
  | cons d dt ih =>
    have hd : isDig d = true := hds d (by simp)
    have hdt : ∀ c ∈ dt, isDig c = true := fun c hc => hds c (by simp [hc])
    simp only [List.cons_append, takeDigits, hd, if_true]
    rw [ih hdt]

/-- **The non-negative numeral round-trip.** Reading the rendered decimal of `n`, followed by any
`rest` that does NOT begin with a digit, recovers `(n, rest)`. -/
theorem readNat_toString (n : Nat) (rest : List Char)
    (hrest : ∀ h t, rest = h :: t → isDig h = false) :
    readNat ((toString n).toList ++ rest) = some (n, rest) := by
  rw [toString_toList]
  unfold readNat
  have hall : ∀ c ∈ Nat.toDigits 10 n, isDig c = true := by
    unfold Nat.toDigits; intro c hc; exact tdc_all_isDig (n+1) n (by omega) c hc
  rw [takeDigits_append (Nat.toDigits 10 n) hall rest hrest]
  have hne : Nat.toDigits 10 n ≠ [] := toDigits_ne_nil n
  cases hd : Nat.toDigits 10 n with
  | nil => exact absurd hd hne
  | cons d dt =>
    simp only []
    have hfold : (Nat.toDigits 10 n).foldl gg 0 = n := by
      unfold Nat.toDigits; rw [tdc_fold (n+1) n (by omega) 0]; simp
    rw [hd] at hfold; rw [hfold]

/-- `'-'` is not a decimal digit (the disambiguator the `Int` reader relies on). -/
theorem dash_not_isDig : isDig '-' = false := by decide

/-- **The signed numeral round-trip.** Reading the rendered decimal of an `Int` `z`, followed by any
`rest` not beginning with a digit, recovers `(z, rest)`. Splits on `ofNat`/`negSucc` exactly as
`Int.repr` does (`toString (negSucc m) = "-" ++ toString (m+1)`). -/
theorem readInt_toString (z : Int) (rest : List Char)
    (hrest : ∀ h t, rest = h :: t → isDig h = false) :
    readInt ((toString z).toList ++ rest) = some (z, rest) := by
  cases z with
  | ofNat n =>
    have hts : toString (Int.ofNat n) = toString n := rfl
    rw [hts]
    have hne : Nat.toDigits 10 n ≠ [] := toDigits_ne_nil n
    -- The render begins with a digit `d` ≠ '-', so `readInt`'s `'-'`-arm misses and the `_`-arm
    -- runs `readNat`, which `readNat_toString` evaluates.
    rw [toString_toList]
    cases hdd : Nat.toDigits 10 n with
    | nil => exact absurd hdd hne
    | cons d dt =>
      have hdig : isDig d = true := by
        have : d ∈ Nat.toDigits 10 n := by rw [hdd]; simp
        unfold Nat.toDigits at this; exact tdc_all_isDig (n+1) n (by omega) d this
      have hdne : d ≠ '-' := by intro h; rw [h, dash_not_isDig] at hdig; exact Bool.noConfusion hdig
      have hrn : readNat (d :: (dt ++ rest)) = some (n, rest) := by
        have := readNat_toString n rest hrest
        rw [toString_toList, hdd] at this
        simpa using this
      simp only [List.cons_append, readInt]
      split
      · next d' rest' heq =>
          rw [List.cons.injEq] at heq
          exact (hdne heq.1).elim
      · rw [hrn]
  | negSucc m =>
    have hts : toString (Int.negSucc m) = "-" ++ toString (m+1) := rfl
    rw [hts]
    have happ : ("-" ++ toString (m+1)).toList = '-' :: (toString (m+1)).toList := by
      rw [String.toList_append]; rfl
    rw [happ]
    have hrn : readNat ((toString (m+1)).toList ++ rest) = some (m+1, rest) :=
      readNat_toString (m+1) rest hrest
    simp only [List.cons_append, readInt, hrn]
    -- -(Int.ofNat (m+1)) = Int.negSucc m
    rfl

/-! ## §3 — The literal-prefix consumer (mirror of `expect` / `expect_key`). -/

/-- Consume an exact literal char-prefix; `none` on mismatch (the structural backbone of every fixed
JSON fragment: braces, quotes, keys, tags). -/
def consume : List Char → List Char → Option (List Char)
  | [],      cs       => some cs
  | _ :: _,  []       => none
  | l :: ls, c :: cs  => if l = c then consume ls cs else none

/-- Consuming a rendered literal prefix returns exactly the remainder. -/
theorem consume_append (lit rest : List Char) :
    consume lit (lit ++ rest) = some rest := by
  induction lit with
  | nil => rfl
  | cons l ls ih => simp only [List.cons_append, consume, if_pos]; exact ih

/-- Consume a `String` literal's chars off the front of a char list. -/
def consumeS (lit : String) (cs : List Char) : Option (List Char) :=
  consume lit.toList cs

theorem consumeS_append (lit : String) (rest : List Char) :
    consumeS lit (lit.toList ++ rest) = some rest := consume_append _ _

/-- **The literal MISMATCH lemma.** If a literal and an input share an agreeing run `p` and then
disagree at the very next char (`a ≠ b`, both present), `consume` rejects — for ANY suffix after `b`.
This discharges "the `var`-tag arm does not consume an `add`-rendered object" etc.: the four expr
tags share `{"t":"` then differ at the next char, so each pair decomposes as `p ++ a::_` vs
`p ++ b::_`. The flow is suffix-independent (no free-variable `decide`, works whichever literal is
longer). -/
theorem consume_mismatch (p : List Char) (a b : Char) (asuf input_suf : List Char)
    (hab : a ≠ b) :
    consume (p ++ a :: asuf) (p ++ b :: input_suf) = none := by
  induction p with
  | nil => simp only [List.nil_append, consume, if_neg hab]
  | cons x xs ih => simp only [List.cons_append, consume, if_pos]; exact ih

/-- A structural size for `EmittedExpr` — the recursion measure that bounds `parseExpr`'s fuel. -/
def esize : EmittedExpr → Nat
  | .var _   => 0
  | .const _ => 0
  | .add l r => esize l + esize r + 1
  | .mul l r => esize l + esize r + 1

/-! ## §4 — The expression parser (mirror of Rust `parse_expr`).

`EmittedExpr.toJson`:
  * `.var v`   → `{"t":"var","v":N}`
  * `.const c` → `{"t":"const","v":N}`   (N may be negative)
  * `.add l r` → `{"t":"add","l":<L>,"r":<R>}`
  * `.mul l r` → `{"t":"mul","l":<L>,"r":<R>}`

We parse by dispatching on the literal tag-prefix, which is total over the four constructors and
self-delimiting (each ends in `}`); recursion on `l`/`r` matches `parse_expr`'s recursion. -/

/-- Parse one `EmittedExpr` object. `fuel` bounds the recursion (a descriptor's expressions are
finite); on the canonical render, `fuel = the rendered string length` always suffices. -/
def parseExpr : Nat → List Char → Option (EmittedExpr × List Char)
  | 0, _ => none
  | fuel + 1, cs =>
    -- var?
    match consume "{\"t\":\"var\",\"v\":".toList cs with
    | some r1 =>
      match readNat r1 with
      | some (v, r2) =>
        match consume "}".toList r2 with
        | some r3 => some (.var v, r3)
        | none => none
      | none => none
    | none =>
    match consume "{\"t\":\"const\",\"v\":".toList cs with
    | some r1 =>
      match readInt r1 with
      | some (c, r2) =>
        match consume "}".toList r2 with
        | some r3 => some (.const c, r3)
        | none => none
      | none => none
    | none =>
    match consume "{\"t\":\"add\",\"l\":".toList cs with
    | some r1 =>
      match parseExpr fuel r1 with
      | some (l, r2) =>
        match consume ",\"r\":".toList r2 with
        | some r3 =>
          match parseExpr fuel r3 with
          | some (rr, r4) =>
            match consume "}".toList r4 with
            | some r5 => some (.add l rr, r5)
            | none => none
          | none => none
        | none => none
      | none => none
    | none =>
    match consume "{\"t\":\"mul\",\"l\":".toList cs with
    | some r1 =>
      match parseExpr fuel r1 with
      | some (l, r2) =>
        match consume ",\"r\":".toList r2 with
        | some r3 =>
          match parseExpr fuel r3 with
          | some (rr, r4) =>
            match consume "}".toList r4 with
            | some r5 => some (.mul l rr, r5)
            | none => none
          | none => none
        | none => none
      | none => none
    | none => none

/-- A char list whose head (if any) is `'}'`, `','`, or `']'` does not begin with a digit — the
"non-digit follows a numeral" side-condition that every numeral occurrence in the grammar meets. -/
def nonDigitHead (rest : List Char) : Prop := ∀ h t, rest = h :: t → isDig h = false

theorem nonDigitHead_brace (rest : List Char) : nonDigitHead ('}' :: rest) := by
  intro h t he; simp only [List.cons.injEq] at he; rw [← he.1]; decide
theorem nonDigitHead_comma (rest : List Char) : nonDigitHead (',' :: rest) := by
  intro h t he; simp only [List.cons.injEq] at he; rw [← he.1]; decide
theorem nonDigitHead_rbrack (rest : List Char) : nonDigitHead (']' :: rest) := by
  intro h t he; simp only [List.cons.injEq] at he; rw [← he.1]; decide

/-- The shared `{"t":"` agreeing run of every expr tag (6 chars), as a char list. -/
def tagPre : List Char := "{\"t\":\"".toList

/-- The four expr-tag literal prefixes are pairwise distinct, so a render under one tag is rejected
by every other tag's arm — via `consume_mismatch` (each pair shares `{"t":"` then differs at the
discriminator char). Suffix-independent; no free-variable `decide`. -/
theorem consume_var_of_const (s : List Char) :
    consume "{\"t\":\"var\",\"v\":".toList (("{\"t\":\"const\",\"v\":").toList ++ s) = none := by
  have e1 : "{\"t\":\"var\",\"v\":".toList = tagPre ++ 'v' :: "ar\",\"v\":".toList := by decide
  have e2 : ("{\"t\":\"const\",\"v\":").toList ++ s = tagPre ++ 'c' :: ("onst\",\"v\":".toList ++ s) := by
    simp [tagPre]
  rw [e1, e2]; exact consume_mismatch tagPre 'v' 'c' _ _ (by decide)
theorem consume_var_of_add (s : List Char) :
    consume "{\"t\":\"var\",\"v\":".toList (("{\"t\":\"add\",\"l\":").toList ++ s) = none := by
  have e1 : "{\"t\":\"var\",\"v\":".toList = tagPre ++ 'v' :: "ar\",\"v\":".toList := by decide
  have e2 : ("{\"t\":\"add\",\"l\":").toList ++ s = tagPre ++ 'a' :: ("dd\",\"l\":".toList ++ s) := by
    simp [tagPre]
  rw [e1, e2]; exact consume_mismatch tagPre 'v' 'a' _ _ (by decide)
theorem consume_var_of_mul (s : List Char) :
    consume "{\"t\":\"var\",\"v\":".toList (("{\"t\":\"mul\",\"l\":").toList ++ s) = none := by
  have e1 : "{\"t\":\"var\",\"v\":".toList = tagPre ++ 'v' :: "ar\",\"v\":".toList := by decide
  have e2 : ("{\"t\":\"mul\",\"l\":").toList ++ s = tagPre ++ 'm' :: ("ul\",\"l\":".toList ++ s) := by
    simp [tagPre]
  rw [e1, e2]; exact consume_mismatch tagPre 'v' 'm' _ _ (by decide)
theorem consume_const_of_add (s : List Char) :
    consume "{\"t\":\"const\",\"v\":".toList (("{\"t\":\"add\",\"l\":").toList ++ s) = none := by
  have e1 : "{\"t\":\"const\",\"v\":".toList = tagPre ++ 'c' :: "onst\",\"v\":".toList := by decide
  have e2 : ("{\"t\":\"add\",\"l\":").toList ++ s = tagPre ++ 'a' :: ("dd\",\"l\":".toList ++ s) := by
    simp [tagPre]
  rw [e1, e2]; exact consume_mismatch tagPre 'c' 'a' _ _ (by decide)
theorem consume_const_of_mul (s : List Char) :
    consume "{\"t\":\"const\",\"v\":".toList (("{\"t\":\"mul\",\"l\":").toList ++ s) = none := by
  have e1 : "{\"t\":\"const\",\"v\":".toList = tagPre ++ 'c' :: "onst\",\"v\":".toList := by decide
  have e2 : ("{\"t\":\"mul\",\"l\":").toList ++ s = tagPre ++ 'm' :: ("ul\",\"l\":".toList ++ s) := by
    simp [tagPre]
  rw [e1, e2]; exact consume_mismatch tagPre 'c' 'm' _ _ (by decide)
theorem consume_add_of_mul (s : List Char) :
    consume "{\"t\":\"add\",\"l\":".toList (("{\"t\":\"mul\",\"l\":").toList ++ s) = none := by
  have e1 : "{\"t\":\"add\",\"l\":".toList = tagPre ++ 'a' :: "dd\",\"l\":".toList := by decide
  have e2 : ("{\"t\":\"mul\",\"l\":").toList ++ s = tagPre ++ 'm' :: ("ul\",\"l\":".toList ++ s) := by
    simp [tagPre]
  rw [e1, e2]; exact consume_mismatch tagPre 'a' 'm' _ _ (by decide)

/-- **The expr round-trip.** With enough fuel, parsing a rendered `EmittedExpr` followed by any
non-digit-headed `rest` recovers `(e, rest)`. By structural induction on `e`; `fuel` need only
exceed `e`'s structural depth (we thread `e.toJson.length + rest.length`-style bounds via a generous
fuel at the call site). -/
theorem parseExpr_toJson (e : EmittedExpr) :
    ∀ (fuel : Nat), esize e < fuel → ∀ (rest : List Char), nonDigitHead rest →
      parseExpr fuel ((EmittedExpr.toJson e).toList ++ rest) = some (e, rest) := by
  induction e with
  | var v =>
    intro fuel hf rest hr
    cases fuel with
    | zero => simp [esize] at hf
    | succ f =>
      have hrender : (EmittedExpr.toJson (.var v)).toList
          = "{\"t\":\"var\",\"v\":".toList ++ ((toString v).toList ++ "}".toList) := by
        show ("{\"t\":\"var\",\"v\":" ++ toString v ++ "}").toList = _
        rw [String.toList_append, String.toList_append, List.append_assoc]
      rw [hrender, List.append_assoc, List.append_assoc]
      have hc1 : consume "{\"t\":\"var\",\"v\":".toList
          ("{\"t\":\"var\",\"v\":".toList ++ ((toString v).toList ++ ("}".toList ++ rest)))
          = some ((toString v).toList ++ ("}".toList ++ rest)) := consume_append _ _
      have hrn : readNat ((toString v).toList ++ ("}".toList ++ rest)) = some (v, "}".toList ++ rest) := by
        apply readNat_toString; exact nonDigitHead_brace rest
      have hc2 : consume "}".toList ("}".toList ++ rest) = some rest := consume_append _ _
      simp only [parseExpr, hc1, hrn, hc2]
  | const c =>
    intro fuel hf rest hr
    cases fuel with
    | zero => simp [esize] at hf
    | succ f =>
      have hrender : (EmittedExpr.toJson (.const c)).toList
          = "{\"t\":\"const\",\"v\":".toList ++ ((toString c).toList ++ "}".toList) := by
        show ("{\"t\":\"const\",\"v\":" ++ toString c ++ "}").toList = _
        rw [String.toList_append, String.toList_append, List.append_assoc]
      rw [hrender, List.append_assoc, List.append_assoc]
      have hvarno : consume "{\"t\":\"var\",\"v\":".toList
          ("{\"t\":\"const\",\"v\":".toList ++ ((toString c).toList ++ ("}".toList ++ rest))) = none :=
        consume_var_of_const _
      have hc1 : consume "{\"t\":\"const\",\"v\":".toList
          ("{\"t\":\"const\",\"v\":".toList ++ ((toString c).toList ++ ("}".toList ++ rest)))
          = some ((toString c).toList ++ ("}".toList ++ rest)) := consume_append _ _
      have hrn : readInt ((toString c).toList ++ ("}".toList ++ rest)) = some (c, "}".toList ++ rest) := by
        apply readInt_toString; exact nonDigitHead_brace rest
      have hc2 : consume "}".toList ("}".toList ++ rest) = some rest := consume_append _ _
      simp only [parseExpr, hvarno, hc1, hrn, hc2]
  | add l rr ihl ihr =>
    intro fuel hf rest hr
    cases fuel with
    | zero => simp [esize] at hf
    | succ f =>
      have hdl : esize l < f := by simp only [esize] at hf; omega
      have hdr : esize rr < f := by simp only [esize] at hf; omega
      have hrender : (EmittedExpr.toJson (.add l rr)).toList
          = "{\"t\":\"add\",\"l\":".toList ++ ((EmittedExpr.toJson l).toList ++
              (",\"r\":".toList ++ ((EmittedExpr.toJson rr).toList ++ "}".toList))) := by
        show ("{\"t\":\"add\",\"l\":" ++ l.toJson ++ ",\"r\":" ++ rr.toJson ++ "}").toList = _
        rw [String.toList_append, String.toList_append, String.toList_append, String.toList_append]
        ac_rfl
      rw [hrender]
      have hc1 : consume "{\"t\":\"add\",\"l\":".toList
          ("{\"t\":\"add\",\"l\":".toList ++ ((EmittedExpr.toJson l).toList ++
              (",\"r\":".toList ++ ((EmittedExpr.toJson rr).toList ++ ("}".toList ++ rest)))))
          = some ((EmittedExpr.toJson l).toList ++
              (",\"r\":".toList ++ ((EmittedExpr.toJson rr).toList ++ ("}".toList ++ rest)))) :=
        consume_append _ _
      have hl : parseExpr f ((EmittedExpr.toJson l).toList ++
            (",\"r\":".toList ++ ((EmittedExpr.toJson rr).toList ++ ("}".toList ++ rest))))
          = some (l, ",\"r\":".toList ++ ((EmittedExpr.toJson rr).toList ++ ("}".toList ++ rest))) := by
        apply ihl f hdl; exact nonDigitHead_comma _
      have hcr : consume ",\"r\":".toList
          (",\"r\":".toList ++ ((EmittedExpr.toJson rr).toList ++ ("}".toList ++ rest)))
          = some ((EmittedExpr.toJson rr).toList ++ ("}".toList ++ rest)) := consume_append _ _
      have hr2 : parseExpr f ((EmittedExpr.toJson rr).toList ++ ("}".toList ++ rest))
          = some (rr, "}".toList ++ rest) := by
        apply ihr f hdr; exact nonDigitHead_brace _
      have hc2 : consume "}".toList ("}".toList ++ rest) = some rest := consume_append _ _
      simp only [List.append_assoc, parseExpr, consume_var_of_add, consume_const_of_add, hc1, hl, hcr, hr2, hc2]
  | mul l rr ihl ihr =>
    intro fuel hf rest hr
    cases fuel with
    | zero => simp [esize] at hf
    | succ f =>
      have hdl : esize l < f := by simp only [esize] at hf; omega
      have hdr : esize rr < f := by simp only [esize] at hf; omega
      have hrender : (EmittedExpr.toJson (.mul l rr)).toList
          = "{\"t\":\"mul\",\"l\":".toList ++ ((EmittedExpr.toJson l).toList ++
              (",\"r\":".toList ++ ((EmittedExpr.toJson rr).toList ++ "}".toList))) := by
        show ("{\"t\":\"mul\",\"l\":" ++ l.toJson ++ ",\"r\":" ++ rr.toJson ++ "}").toList = _
        rw [String.toList_append, String.toList_append, String.toList_append, String.toList_append]
        ac_rfl
      rw [hrender]
      have hc1 : consume "{\"t\":\"mul\",\"l\":".toList
          ("{\"t\":\"mul\",\"l\":".toList ++ ((EmittedExpr.toJson l).toList ++
              (",\"r\":".toList ++ ((EmittedExpr.toJson rr).toList ++ ("}".toList ++ rest)))))
          = some ((EmittedExpr.toJson l).toList ++
              (",\"r\":".toList ++ ((EmittedExpr.toJson rr).toList ++ ("}".toList ++ rest)))) :=
        consume_append _ _
      have hl : parseExpr f ((EmittedExpr.toJson l).toList ++
            (",\"r\":".toList ++ ((EmittedExpr.toJson rr).toList ++ ("}".toList ++ rest))))
          = some (l, ",\"r\":".toList ++ ((EmittedExpr.toJson rr).toList ++ ("}".toList ++ rest))) := by
        apply ihl f hdl; exact nonDigitHead_comma _
      have hcr : consume ",\"r\":".toList
          (",\"r\":".toList ++ ((EmittedExpr.toJson rr).toList ++ ("}".toList ++ rest)))
          = some ((EmittedExpr.toJson rr).toList ++ ("}".toList ++ rest)) := consume_append _ _
      have hr2 : parseExpr f ((EmittedExpr.toJson rr).toList ++ ("}".toList ++ rest))
          = some (rr, "}".toList ++ rest) := by
        apply ihr f hdr; exact nonDigitHead_brace _
      have hc2 : consume "}".toList ("}".toList ++ rest) = some rest := consume_append _ _
      simp only [List.append_assoc, parseExpr, consume_var_of_mul, consume_const_of_mul, consume_add_of_mul, hc1, hl, hcr, hr2, hc2]

/-! ## §5 — Hash-input parser (mirror of Rust `parse_hash_input`).

`HashInput.toJson`:
  * `.col c`    → `{"t":"col","c":N}`
  * `.digest k` → `{"t":"digest","k":N}`
  * `.zero`     → `{"t":"zero"}`
-/
def parseHashInput (cs : List Char) : Option (HashInput × List Char) :=
  match consume "{\"t\":\"col\",\"c\":".toList cs with
  | some r1 =>
    match readNat r1 with
    | some (c, r2) => match consume "}".toList r2 with
                      | some r3 => some (.col c, r3) | none => none
    | none => none
  | none =>
  match consume "{\"t\":\"digest\",\"k\":".toList cs with
  | some r1 =>
    match readNat r1 with
    | some (k, r2) => match consume "}".toList r2 with
                      | some r3 => some (.digest k, r3) | none => none
    | none => none
  | none =>
  match consume "{\"t\":\"zero\"}".toList cs with
  | some r1 => some (.zero, r1)
  | none => none

theorem parseHashInput_toJson (i : HashInput) (rest : List Char) (hr : nonDigitHead rest) :
    parseHashInput ((HashInput.toJson i).toList ++ rest) = some (i, rest) := by
  cases i with
  | col c =>
    have hrender : (HashInput.toJson (.col c)).toList
        = "{\"t\":\"col\",\"c\":".toList ++ ((toString c).toList ++ "}".toList) := by
      show ("{\"t\":\"col\",\"c\":" ++ toString c ++ "}").toList = _
      rw [String.toList_append, String.toList_append, List.append_assoc]
    rw [hrender]
    have hc1 : consume "{\"t\":\"col\",\"c\":".toList
        ("{\"t\":\"col\",\"c\":".toList ++ ((toString c).toList ++ ("}".toList ++ rest)))
        = some ((toString c).toList ++ ("}".toList ++ rest)) := consume_append _ _
    have hrn : readNat ((toString c).toList ++ ("}".toList ++ rest)) = some (c, "}".toList ++ rest) := by
      apply readNat_toString; exact nonDigitHead_brace rest
    have hc2 : consume "}".toList ("}".toList ++ rest) = some rest := consume_append _ _
    simp only [List.append_assoc, parseHashInput, hc1, hrn, hc2]
  | digest k =>
    have hrender : (HashInput.toJson (.digest k)).toList
        = "{\"t\":\"digest\",\"k\":".toList ++ ((toString k).toList ++ "}".toList) := by
      show ("{\"t\":\"digest\",\"k\":" ++ toString k ++ "}").toList = _
      rw [String.toList_append, String.toList_append, List.append_assoc]
    rw [hrender]
    have hcolno : consume "{\"t\":\"col\",\"c\":".toList
        ("{\"t\":\"digest\",\"k\":".toList ++ ((toString k).toList ++ ("}".toList ++ rest))) = none := by
      have e1 : "{\"t\":\"col\",\"c\":".toList = tagPre ++ 'c' :: "ol\",\"c\":".toList := by decide
      have e2 : "{\"t\":\"digest\",\"k\":".toList ++ ((toString k).toList ++ ("}".toList ++ rest))
              = tagPre ++ 'd' :: ("igest\",\"k\":".toList ++ ((toString k).toList ++ ("}".toList ++ rest))) := by
        simp [tagPre]
      rw [e1, e2]; exact consume_mismatch tagPre 'c' 'd' _ _ (by decide)
    have hc1 : consume "{\"t\":\"digest\",\"k\":".toList
        ("{\"t\":\"digest\",\"k\":".toList ++ ((toString k).toList ++ ("}".toList ++ rest)))
        = some ((toString k).toList ++ ("}".toList ++ rest)) := consume_append _ _
    have hrn : readNat ((toString k).toList ++ ("}".toList ++ rest)) = some (k, "}".toList ++ rest) := by
      apply readNat_toString; exact nonDigitHead_brace rest
    have hc2 : consume "}".toList ("}".toList ++ rest) = some rest := consume_append _ _
    simp only [List.append_assoc, parseHashInput, hcolno, hc1, hrn, hc2]
  | zero =>
    have hrender : (HashInput.toJson HashInput.zero).toList = "{\"t\":\"zero\"}".toList := by
      show ("{\"t\":\"zero\"}").toList = _; rfl
    rw [hrender]
    have hcolno : consume "{\"t\":\"col\",\"c\":".toList ("{\"t\":\"zero\"}".toList ++ rest) = none := by
      have e1 : "{\"t\":\"col\",\"c\":".toList = tagPre ++ 'c' :: "ol\",\"c\":".toList := by decide
      have e2 : "{\"t\":\"zero\"}".toList ++ rest = tagPre ++ 'z' :: ("ero\"}".toList ++ rest) := by
        simp [tagPre]
      rw [e1, e2]; exact consume_mismatch tagPre 'c' 'z' _ _ (by decide)
    have hdigno : consume "{\"t\":\"digest\",\"k\":".toList ("{\"t\":\"zero\"}".toList ++ rest) = none := by
      have e1 : "{\"t\":\"digest\",\"k\":".toList = tagPre ++ 'd' :: "igest\",\"k\":".toList := by decide
      have e2 : "{\"t\":\"zero\"}".toList ++ rest = tagPre ++ 'z' :: ("ero\"}".toList ++ rest) := by
        simp [tagPre]
      rw [e1, e2]; exact consume_mismatch tagPre 'd' 'z' _ _ (by decide)
    have hc1 : consume "{\"t\":\"zero\"}".toList ("{\"t\":\"zero\"}".toList ++ rest) = some rest :=
      consume_append _ _
    simp only [parseHashInput, hcolno, hdigno, hc1]

/-! ## §6 — The constraint parser (mirror of Rust `parse_vm_constraint`).

`VmConstraint.toJson`:
  * `.gate body`           → `{"t":"gate","body":<expr>}`
  * `.transition hi lo`    → `{"t":"transition","hi":N,"lo":N}`
  * `.boundary row body`   → `{"t":"boundary","row":"first"|"last","body":<expr>}`
  * `.piBinding row col k`  → `{"t":"pi_binding","row":"first"|"last","col":N,"pi_index":N}`

**FIDELITY NOTE (the `boundary` arm — named, not hidden).** The deployed Rust
`parse_vm_constraint` (`lean_descriptor_air.rs`) has arms for ONLY `gate` / `transition` /
`pi_binding` — it has NO `boundary` arm and returns `Err("unknown vm-constraint tag …")` on one. The
EVERY emitted descriptor in `circuit/descriptors/*.json` uses `pi_binding` for its boundary pins and
NEVER the `boundary` constructor (verified: `grep '"boundary"' *.json` is empty; the registry's tag
census is gate/transition/pi_binding only). So the descriptor CLASS the Rust seam accepts is exactly
the `boundary`-free descriptors, and `parseVmConstraint` here mirrors the Rust parser faithfully by
dispatching the SAME three tags. The well-formedness predicate `WfDesc` below requires `noBoundary`,
pinning the round-trip to precisely the descriptor class that crosses the live seam. -/

/-- Parse one `VmConstraint` object — `gate` / `transition` / `pi_binding`, a STRUCTURAL mirror of
the Rust `parse_vm_constraint` (which has no `boundary` arm). `fuel` bounds the embedded `gate`-body
`parseExpr`. -/
def parseVmConstraint (fuel : Nat) (cs : List Char) : Option (VmConstraint × List Char) :=
  match consume "{\"t\":\"gate\",\"body\":".toList cs with
  | some r1 =>
    match parseExpr fuel r1 with
    | some (body, r2) =>
      match consume "}".toList r2 with
      | some r3 => some (.gate body, r3)
      | none => none
    | none => none
  | none =>
  match consume "{\"t\":\"transition\",\"hi\":".toList cs with
  | some r1 =>
    match readNat r1 with
    | some (hi, r2) =>
      match consume ",\"lo\":".toList r2 with
      | some r3 =>
        match readNat r3 with
        | some (lo, r4) =>
          match consume "}".toList r4 with
          | some r5 => some (.transition hi lo, r5)
          | none => none
        | none => none
      | none => none
    | none => none
  | none =>
  match consume "{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":".toList cs with
  | some r1 => parsePiTail .first r1
  | none =>
  match consume "{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":".toList cs with
  | some r1 => parsePiTail .last r1
  | none => none
where
  /-- After the `…"col":` literal for a `pi_binding`, read `col`, `,"pi_index":`, `pi_index`, `}`. -/
  parsePiTail (row : VmRow) (r1 : List Char) : Option (VmConstraint × List Char) :=
    match readNat r1 with
    | some (col, r2) =>
      match consume ",\"pi_index\":".toList r2 with
      | some r3 =>
        match readNat r3 with
        | some (k, r4) =>
          match consume "}".toList r4 with
          | some r5 => some (.piBinding row col k, r5)
          | none => none
        | none => none
      | none => none
    | none => none

/-- The `pi_binding`-`first` and `pi_binding`-`last` tag prefixes share `…"row":"` then differ at
`f`/`l`; neither is consumed by the `gate`/`transition` tag (they share `{"t":"` then differ at the
discriminator). These mismatch lemmas drive the constraint dispatch. -/
theorem consume_gate_of_transition (s : List Char) :
    consume "{\"t\":\"gate\",\"body\":".toList (("{\"t\":\"transition\",\"hi\":").toList ++ s) = none := by
  have e1 : "{\"t\":\"gate\",\"body\":".toList = tagPre ++ 'g' :: "ate\",\"body\":".toList := by decide
  have e2 : ("{\"t\":\"transition\",\"hi\":").toList ++ s
      = tagPre ++ 't' :: ("ransition\",\"hi\":".toList ++ s) := by simp [tagPre]
  rw [e1, e2]; exact consume_mismatch tagPre 'g' 't' _ _ (by decide)

theorem consume_gate_of_pifirst (s : List Char) :
    consume "{\"t\":\"gate\",\"body\":".toList ("{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":".toList ++ s) = none := by
  have e1 : "{\"t\":\"gate\",\"body\":".toList = tagPre ++ 'g' :: "ate\",\"body\":".toList := by decide
  have e2 : "{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":".toList ++ s
      = tagPre ++ 'p' :: ("i_binding\",\"row\":\"first\",\"col\":".toList ++ s) := by simp [tagPre]
  rw [e1, e2]; exact consume_mismatch tagPre 'g' 'p' _ _ (by decide)

theorem consume_gate_of_pilast (s : List Char) :
    consume "{\"t\":\"gate\",\"body\":".toList ("{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":".toList ++ s) = none := by
  have e1 : "{\"t\":\"gate\",\"body\":".toList = tagPre ++ 'g' :: "ate\",\"body\":".toList := by decide
  have e2 : "{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":".toList ++ s
      = tagPre ++ 'p' :: ("i_binding\",\"row\":\"last\",\"col\":".toList ++ s) := by simp [tagPre]
  rw [e1, e2]; exact consume_mismatch tagPre 'g' 'p' _ _ (by decide)

theorem consume_transition_of_pifirst (s : List Char) :
    consume "{\"t\":\"transition\",\"hi\":".toList ("{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":".toList ++ s) = none := by
  have e1 : "{\"t\":\"transition\",\"hi\":".toList = tagPre ++ 't' :: "ransition\",\"hi\":".toList := by decide
  have e2 : "{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":".toList ++ s
      = tagPre ++ 'p' :: ("i_binding\",\"row\":\"first\",\"col\":".toList ++ s) := by simp [tagPre]
  rw [e1, e2]; exact consume_mismatch tagPre 't' 'p' _ _ (by decide)

theorem consume_transition_of_pilast (s : List Char) :
    consume "{\"t\":\"transition\",\"hi\":".toList ("{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":".toList ++ s) = none := by
  have e1 : "{\"t\":\"transition\",\"hi\":".toList = tagPre ++ 't' :: "ransition\",\"hi\":".toList := by decide
  have e2 : "{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":".toList ++ s
      = tagPre ++ 'p' :: ("i_binding\",\"row\":\"last\",\"col\":".toList ++ s) := by simp [tagPre]
  rw [e1, e2]; exact consume_mismatch tagPre 't' 'p' _ _ (by decide)

/-- The shared `{"t":"pi_binding","row":"` prefix of the two `pi_binding` tags, as a char list. -/
def piPre : List Char := "{\"t\":\"pi_binding\",\"row\":\"".toList

/-- The `pi_binding`-first tag does not consume a `pi_binding`-last render (differ at `f`/`l` after
the shared `…"row":"`). -/
theorem consume_pifirst_of_pilast (s : List Char) :
    consume "{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":".toList
      (("{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":").toList ++ s) = none := by
  have e1 : "{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":".toList
      = piPre ++ 'f' :: "irst\",\"col\":".toList := by decide
  have e2 : ("{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":").toList ++ s
      = piPre ++ 'l' :: ("ast\",\"col\":".toList ++ s) := by simp [piPre]
  rw [e1, e2]; exact consume_mismatch piPre 'f' 'l' _ _ (by decide)

/-- The `gate`-tag arm does not consume a `transition` or `pi_binding` render, etc. (cross-rejection
already covered); the `transition` tag does not consume a `pi_binding` render. Bundled for the
dispatch `simp`. -/
theorem parsePiTail_toJson (row : VmRow) (col k : Nat) (rest : List Char) (hr : nonDigitHead rest) :
    parseVmConstraint.parsePiTail row
        ((toString col).toList ++ (",\"pi_index\":".toList ++ ((toString k).toList ++ ("}".toList ++ rest))))
      = some (.piBinding row col k, rest) := by
  have hcol : readNat ((toString col).toList ++ (",\"pi_index\":".toList ++ ((toString k).toList ++ ("}".toList ++ rest))))
      = some (col, ",\"pi_index\":".toList ++ ((toString k).toList ++ ("}".toList ++ rest))) := by
    apply readNat_toString; exact nonDigitHead_comma _
  have hsep : consume ",\"pi_index\":".toList
      (",\"pi_index\":".toList ++ ((toString k).toList ++ ("}".toList ++ rest)))
      = some ((toString k).toList ++ ("}".toList ++ rest)) := consume_append _ _
  have hk : readNat ((toString k).toList ++ ("}".toList ++ rest)) = some (k, "}".toList ++ rest) := by
    apply readNat_toString; exact nonDigitHead_brace _
  have hb : consume "}".toList ("}".toList ++ rest) = some rest := consume_append _ _
  simp only [parseVmConstraint.parsePiTail, hcol, hsep, hk, hb]

/-- **The constraint round-trip** — for the THREE wire constructors (`gate`/`transition`/
`pi_binding`). Parsing a rendered `gate`/`transition`/`pi_binding` constraint, followed by any
non-digit-headed `rest`, recovers `(c, rest)`. The `gate`-body fuel must exceed the body's
`esize`. -/
theorem parseVmConstraint_toJson_gate (body : EmittedExpr) (fuel : Nat) (hf : esize body < fuel)
    (rest : List Char) (hr : nonDigitHead rest) :
    parseVmConstraint fuel ((VmConstraint.toJson (.gate body)).toList ++ rest)
      = some (.gate body, rest) := by
  have hrender : (VmConstraint.toJson (.gate body)).toList
      = "{\"t\":\"gate\",\"body\":".toList ++ ((EmittedExpr.toJson body).toList ++ "}".toList) := by
    show ("{\"t\":\"gate\",\"body\":" ++ body.toJson ++ "}").toList = _
    rw [String.toList_append, String.toList_append, List.append_assoc]
  rw [hrender, List.append_assoc, List.append_assoc]
  have hc1 : consume "{\"t\":\"gate\",\"body\":".toList
      ("{\"t\":\"gate\",\"body\":".toList ++ ((EmittedExpr.toJson body).toList ++ ("}".toList ++ rest)))
      = some ((EmittedExpr.toJson body).toList ++ ("}".toList ++ rest)) := consume_append _ _
  have hbody : parseExpr fuel ((EmittedExpr.toJson body).toList ++ ("}".toList ++ rest))
      = some (body, "}".toList ++ rest) := by
    apply parseExpr_toJson body fuel hf; exact nonDigitHead_brace _
  have hb : consume "}".toList ("}".toList ++ rest) = some rest := consume_append _ _
  simp only [parseVmConstraint, hc1, hbody, hb]

theorem parseVmConstraint_toJson_transition (hi lo : Nat) (fuel : Nat)
    (rest : List Char) (hr : nonDigitHead rest) :
    parseVmConstraint fuel ((VmConstraint.toJson (.transition hi lo)).toList ++ rest)
      = some (.transition hi lo, rest) := by
  have hrender : (VmConstraint.toJson (.transition hi lo)).toList
      = "{\"t\":\"transition\",\"hi\":".toList ++ ((toString hi).toList ++
          (",\"lo\":".toList ++ ((toString lo).toList ++ "}".toList))) := by
    show ("{\"t\":\"transition\",\"hi\":" ++ toString hi ++ ",\"lo\":" ++ toString lo ++ "}").toList = _
    rw [String.toList_append, String.toList_append, String.toList_append, String.toList_append]
    ac_rfl
  rw [hrender]; simp only [List.append_assoc]
  have hgno := consume_gate_of_transition ((toString hi).toList ++
      (",\"lo\":".toList ++ ((toString lo).toList ++ ("}".toList ++ rest))))
  have hc1 : consume "{\"t\":\"transition\",\"hi\":".toList
      ("{\"t\":\"transition\",\"hi\":".toList ++ ((toString hi).toList ++
        (",\"lo\":".toList ++ ((toString lo).toList ++ ("}".toList ++ rest)))))
      = some ((toString hi).toList ++ (",\"lo\":".toList ++ ((toString lo).toList ++ ("}".toList ++ rest)))) :=
    consume_append _ _
  have hhi : readNat ((toString hi).toList ++ (",\"lo\":".toList ++ ((toString lo).toList ++ ("}".toList ++ rest))))
      = some (hi, ",\"lo\":".toList ++ ((toString lo).toList ++ ("}".toList ++ rest))) := by
    apply readNat_toString; exact nonDigitHead_comma _
  have hsep : consume ",\"lo\":".toList
      (",\"lo\":".toList ++ ((toString lo).toList ++ ("}".toList ++ rest)))
      = some ((toString lo).toList ++ ("}".toList ++ rest)) := consume_append _ _
  have hlo : readNat ((toString lo).toList ++ ("}".toList ++ rest)) = some (lo, "}".toList ++ rest) := by
    apply readNat_toString; exact nonDigitHead_brace _
  have hb : consume "}".toList ("}".toList ++ rest) = some rest := consume_append _ _
  simp only [parseVmConstraint, hgno, hc1, hhi, hsep, hlo, hb]

theorem parseVmConstraint_toJson_pi (row : VmRow) (col k : Nat) (fuel : Nat)
    (rest : List Char) (hr : nonDigitHead rest) :
    parseVmConstraint fuel ((VmConstraint.toJson (.piBinding row col k)).toList ++ rest)
      = some (.piBinding row col k, rest) := by
  cases row with
  | first =>
    have hrender : (VmConstraint.toJson (.piBinding .first col k)).toList
        = "{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":".toList ++ ((toString col).toList ++
            (",\"pi_index\":".toList ++ ((toString k).toList ++ "}".toList))) := by
      show ("{\"t\":\"pi_binding\",\"row\":\"" ++ "first" ++ "\",\"col\":" ++ toString col ++
            ",\"pi_index\":" ++ toString k ++ "}").toList = _
      rw [String.toList_append, String.toList_append, String.toList_append, String.toList_append,
          String.toList_append]
      ac_rfl
    rw [hrender]; simp only [List.append_assoc]
    have hgno := consume_gate_of_pifirst ((toString col).toList ++
        (",\"pi_index\":".toList ++ ((toString k).toList ++ ("}".toList ++ rest))))
    have htno := consume_transition_of_pifirst ((toString col).toList ++
        (",\"pi_index\":".toList ++ ((toString k).toList ++ ("}".toList ++ rest))))
    have hc1 : consume "{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":".toList
        ("{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":".toList ++ ((toString col).toList ++
          (",\"pi_index\":".toList ++ ((toString k).toList ++ ("}".toList ++ rest)))))
        = some ((toString col).toList ++ (",\"pi_index\":".toList ++ ((toString k).toList ++ ("}".toList ++ rest)))) :=
      consume_append _ _
    simp only [parseVmConstraint, hgno, htno, hc1]
    exact parsePiTail_toJson .first col k rest hr
  | last =>
    have hrender : (VmConstraint.toJson (.piBinding .last col k)).toList
        = "{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":".toList ++ ((toString col).toList ++
            (",\"pi_index\":".toList ++ ((toString k).toList ++ "}".toList))) := by
      show ("{\"t\":\"pi_binding\",\"row\":\"" ++ "last" ++ "\",\"col\":" ++ toString col ++
            ",\"pi_index\":" ++ toString k ++ "}").toList = _
      rw [String.toList_append, String.toList_append, String.toList_append, String.toList_append,
          String.toList_append]
      ac_rfl
    rw [hrender]; simp only [List.append_assoc]
    have hgno := consume_gate_of_pilast ((toString col).toList ++
        (",\"pi_index\":".toList ++ ((toString k).toList ++ ("}".toList ++ rest))))
    have htno := consume_transition_of_pilast ((toString col).toList ++
        (",\"pi_index\":".toList ++ ((toString k).toList ++ ("}".toList ++ rest))))
    have hpfno := consume_pifirst_of_pilast ((toString col).toList ++
        (",\"pi_index\":".toList ++ ((toString k).toList ++ ("}".toList ++ rest))))
    have hc1 : consume "{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":".toList
        ("{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":".toList ++ ((toString col).toList ++
          (",\"pi_index\":".toList ++ ((toString k).toList ++ ("}".toList ++ rest)))))
        = some ((toString col).toList ++ (",\"pi_index\":".toList ++ ((toString k).toList ++ ("}".toList ++ rest)))) :=
      consume_append _ _
    simp only [parseVmConstraint, hgno, htno, hpfno, hc1]
    exact parsePiTail_toJson .last col k rest hr

/-! ## §7 — The range parser (mirror of Rust `parse_range`).

`VmRange.toJson r` → `{"wire":N,"bits":N}`. -/

def parseRange (cs : List Char) : Option (VmRange × List Char) :=
  match consume "{\"wire\":".toList cs with
  | some r1 =>
    match readNat r1 with
    | some (wire, r2) =>
      match consume ",\"bits\":".toList r2 with
      | some r3 =>
        match readNat r3 with
        | some (bits, r4) =>
          match consume "}".toList r4 with
          | some r5 => some (⟨wire, bits⟩, r5)
          | none => none
        | none => none
      | none => none
    | none => none
  | none => none

theorem parseRange_toJson (r : VmRange) (rest : List Char) (hr : nonDigitHead rest) :
    parseRange ((VmRange.toJson r).toList ++ rest) = some (r, rest) := by
  obtain ⟨wire, bits⟩ := r
  have hrender : (VmRange.toJson ⟨wire, bits⟩).toList
      = "{\"wire\":".toList ++ ((toString wire).toList ++
          (",\"bits\":".toList ++ ((toString bits).toList ++ "}".toList))) := by
    show ("{\"wire\":" ++ toString wire ++ ",\"bits\":" ++ toString bits ++ "}").toList = _
    rw [String.toList_append, String.toList_append, String.toList_append, String.toList_append]
    ac_rfl
  rw [hrender]; simp only [List.append_assoc]
  have hc1 : consume "{\"wire\":".toList
      ("{\"wire\":".toList ++ ((toString wire).toList ++
        (",\"bits\":".toList ++ ((toString bits).toList ++ ("}".toList ++ rest)))))
      = some ((toString wire).toList ++ (",\"bits\":".toList ++ ((toString bits).toList ++ ("}".toList ++ rest)))) :=
    consume_append _ _
  have hw : readNat ((toString wire).toList ++ (",\"bits\":".toList ++ ((toString bits).toList ++ ("}".toList ++ rest))))
      = some (wire, ",\"bits\":".toList ++ ((toString bits).toList ++ ("}".toList ++ rest))) := by
    apply readNat_toString; exact nonDigitHead_comma _
  have hsep : consume ",\"bits\":".toList
      (",\"bits\":".toList ++ ((toString bits).toList ++ ("}".toList ++ rest)))
      = some ((toString bits).toList ++ ("}".toList ++ rest)) := consume_append _ _
  have hbits : readNat ((toString bits).toList ++ ("}".toList ++ rest)) = some (bits, "}".toList ++ rest) := by
    apply readNat_toString; exact nonDigitHead_brace _
  have hb : consume "}".toList ("}".toList ++ rest) = some rest := consume_append _ _
  simp only [parseRange, hc1, hw, hsep, hbits, hb]

/-! ## §8 — The hash-site parser (mirror of Rust `parse_hash_site`).

`VmHashSite.toJson s` → `{"digest_col":N,"arity":N,"inputs":[<inp>,…]}`. The `inputs` array is the
comma-`foldl` rendering; we reuse the GENERIC array machinery (§9) for it. -/

/-! ## §9 — The generic JSON-array round-trip (the comma-`foldl` rendering).

Every list field (`constraints` / `hash_sites` / `ranges` / a site's `inputs`) is rendered by the same
shape:
  * `[]`      → `"[]"`
  * `x :: xs` → `"[" ++ render x ++ (xs.foldl (fun acc y => acc ++ "," ++ render y) "") ++ "]"`
We characterise that `foldl` tail (`joinSep`) and give ONE array parser + round-trip, instantiated four
times below. -/

/-- The comma-separated tail of a non-empty array render: `xs.foldl (acc ++ "," ++ render y) ""`. -/
def joinSep (render : α → String) (xs : List α) : String :=
  xs.foldl (fun acc y => acc ++ "," ++ render y) ""

/-- The `joinSep` `foldl` pushes its seed out front: with the actual two-append step
`fun acc y => acc ++ "," ++ render y`, `ys.foldl step s = s ++ ys.foldl step ""`. The structural fact
behind `joinSep (y :: ys) = "," ++ render y ++ joinSep ys`. -/
theorem joinSep_pushout (render : α → String) (ys : List α) (s : String) :
    ys.foldl (fun acc y => acc ++ "," ++ render y) s
      = s ++ ys.foldl (fun acc y => acc ++ "," ++ render y) "" := by
  induction ys generalizing s with
  | nil => simp
  | cons z zs ih =>
    simp only [List.foldl_cons]
    rw [ih (s ++ "," ++ render z), ih ("" ++ "," ++ render z)]
    simp [String.append_assoc]

/-- `joinSep` peels one element off the front as `"," ++ render y ++ joinSep ys`. -/
theorem joinSep_cons (render : α → String) (y : α) (ys : List α) :
    joinSep render (y :: ys) = "," ++ render y ++ joinSep render ys := by
  unfold joinSep
  simp only [List.foldl_cons]
  rw [joinSep_pushout render ys ("" ++ "," ++ render y)]
  simp [String.append_assoc]

/-- Parse the separator-prefixed array tail `(',' item)* ']'` (the rendered `joinSep` then `]`).
`fuel` bounds the element count. A STRUCTURAL mirror of the Rust `parse_array` loop body. -/
def parseArraySep (pItem : List Char → Option (α × List Char)) :
    Nat → List Char → Option (List α × List Char)
  | _, ']' :: rest => some ([], rest)
  | fuel + 1, ',' :: rest =>
    match pItem rest with
    | some (x, r1) =>
      match parseArraySep pItem fuel r1 with
      | some (xs, r2) => some (x :: xs, r2)
      | none => none
    | none => none
  | _, _ => none

/-- The `]`-arm of `parseArraySep` (any fuel). -/
@[simp] theorem parseArraySep_rbrack (pItem : List Char → Option (α × List Char)) (fuel : Nat)
    (rest : List Char) : parseArraySep pItem fuel (']' :: rest) = some ([], rest) := by
  cases fuel <;> rfl

/-- The `,`-arm of `parseArraySep` (fuel `f+1`). -/
theorem parseArraySep_comma (pItem : List Char → Option (α × List Char)) (f : Nat)
    (rest : List Char) :
    parseArraySep pItem (f + 1) (',' :: rest)
      = (match pItem rest with
         | some (x, r1) =>
           match parseArraySep pItem f r1 with
           | some (xs, r2) => some (x :: xs, r2)
           | none => none
         | none => none) := rfl

/-- The generic array parser: `[` then `]` (empty) OR `item (',' item)* ']'`. `fuel` bounds the
element count; `pItem` is the per-element parser. A STRUCTURAL mirror of the Rust `parse_array` loop
(and the inline `inputs` loop), specialised to the canonical whitespace-free render. -/
def parseArray (pItem : List Char → Option (α × List Char)) :
    Nat → List Char → Option (List α × List Char)
  | _, '[' :: ']' :: rest => some ([], rest)
  | fuel, '[' :: rest =>
    match pItem rest with
    | some (x, r1) =>
      match parseArraySep pItem fuel r1 with
      | some (xs, r2) => some (x :: xs, r2)
      | none => none
    | none => none
  | _, _ => none

/-- The empty-array arm `[]` (any fuel). -/
@[simp] theorem parseArray_empty (pItem : List Char → Option (α × List Char)) (fuel : Nat)
    (rest : List Char) : parseArray pItem fuel ('[' :: ']' :: rest) = some ([], rest) := by
  cases fuel <;> rfl

/-- The non-empty array arm: `[` followed by a first char `≠ ']'`. We expose it on a head `'{'`
(every element render begins with `{`), so the empty arm cannot fire. -/
theorem parseArray_nonempty (pItem : List Char → Option (α × List Char)) (fuel : Nat)
    (t rest : List Char) :
    parseArray pItem fuel ('[' :: '{' :: (t ++ rest))
      = (match pItem ('{' :: (t ++ rest)) with
         | some (x, r1) =>
           match parseArraySep pItem fuel r1 with
           | some (xs, r2) => some (x :: xs, r2)
           | none => none
         | none => none) := by
  cases fuel <;> rfl

/-- The non-digit-head fact for an array tail `joinSep render xs ++ "]" ++ rest`: its head is either
`']'` (empty `joinSep`) or `','` — never a digit. Reused at every element boundary. -/
theorem joinSep_tail_nonDigitHead {α} (render : α → String) (xs : List α) (rest : List Char)
    (hrest : nonDigitHead rest) :
    nonDigitHead ((joinSep render xs).toList ++ ("]".toList ++ rest)) := by
  intro h t he
  cases xs with
  | nil =>
    have hjs : (joinSep render ([] : List α)).toList = ([] : List Char) := by simp [joinSep]
    rw [hjs, List.nil_append] at he
    exact (nonDigitHead_rbrack rest) h t he
  | cons z zs =>
    rw [joinSep_cons] at he
    have hz : ("," ++ render z ++ joinSep render zs).toList
        = ',' :: ((render z).toList ++ (joinSep render zs).toList) := by
      rw [String.toList_append, String.toList_append]; rfl
    rw [hz] at he
    simp only [List.cons_append, List.cons.injEq] at he
    rw [← he.1]; decide

/-- **The separator-tail round-trip.** Parsing the rendered `joinSep render xs` (then `]`, then a
non-`,`/`]`-headed `rest`) recovers `(xs, rest)`. `hItem` need only round-trip the elements that
ACTUALLY appear (membership-restricted) — so a per-element fuel/well-formedness side condition is
allowed (e.g. a gate body's `esize < fuel`, which holds only for the constraints in the list). -/
theorem parseArraySep_toJson {α} (render : α → String) (pItem : List Char → Option (α × List Char))
    (hbrace : ∀ a : α, ∃ t, (render a).toList = '{' :: t) :
    ∀ (xs : List α), (∀ a ∈ xs, ∀ (rr : List Char), nonDigitHead rr →
        pItem ((render a).toList ++ rr) = some (a, rr)) →
      ∀ (fuel : Nat), xs.length ≤ fuel → ∀ (rest : List Char), nonDigitHead rest →
        parseArraySep pItem fuel ((joinSep render xs).toList ++ ("]".toList ++ rest))
          = some (xs, rest) := by
  intro xs
  induction xs with
  | nil =>
    intro _ fuel _ rest _
    have he : (joinSep render ([] : List α)).toList = ([] : List Char) := by simp [joinSep]
    rw [he, List.nil_append]
    show parseArraySep pItem fuel (']' :: rest) = some ([], rest)
    exact parseArraySep_rbrack pItem fuel rest
  | cons y ys ih =>
    intro hItem fuel hfuel rest hrest
    cases fuel with
    | zero => simp at hfuel
    | succ f =>
      have hys : ys.length ≤ f := by simp only [List.length_cons] at hfuel; omega
      have hItemYs : ∀ a ∈ ys, ∀ (rr : List Char), nonDigitHead rr →
          pItem ((render a).toList ++ rr) = some (a, rr) :=
        fun a ha => hItem a (List.mem_cons_of_mem y ha)
      rw [joinSep_cons]
      have hrender : ("," ++ render y ++ joinSep render ys).toList
          = ','  :: ((render y).toList ++ (joinSep render ys).toList) := by
        rw [String.toList_append, String.toList_append]; rfl
      rw [hrender, List.cons_append, List.append_assoc]
      have hitem : pItem ((render y).toList ++ ((joinSep render ys).toList ++ ("]".toList ++ rest)))
          = some (y, (joinSep render ys).toList ++ ("]".toList ++ rest)) :=
        hItem y (List.mem_cons_self ..) _ (joinSep_tail_nonDigitHead render ys rest hrest)
      show parseArraySep pItem (f+1)
          (',' :: ((render y).toList ++ ((joinSep render ys).toList ++ ("]".toList ++ rest)))) = _
      rw [parseArraySep_comma]
      simp only [hitem, ih hItemYs f hys rest hrest]

/-- **The generic array round-trip.** For a list rendered by the canonical `[` + first + `joinSep` +
`]` shape, `parseArray` recovers the list with enough fuel. `hItem` is membership-restricted (only the
elements that appear need round-trip). The two array-render shapes (`[]` vs non-empty) are dispatched
structurally. -/
theorem parseArray_toJson {α} (render : α → String) (pItem : List Char → Option (α × List Char))
    (renderList : List α → String)
    (hnil : renderList [] = "[]")
    (hcons : ∀ (x : α) (xs : List α), renderList (x :: xs)
        = "[" ++ render x ++ joinSep render xs ++ "]")
    (hbrace : ∀ a : α, ∃ t, (render a).toList = '{' :: t)
    (xs : List α)
    (hItem : ∀ a ∈ xs, ∀ (rr : List Char), nonDigitHead rr →
        pItem ((render a).toList ++ rr) = some (a, rr))
    (fuel : Nat) (hfuel : xs.length ≤ fuel) (rest : List Char) (hrest : nonDigitHead rest) :
    parseArray pItem fuel ((renderList xs).toList ++ rest) = some (xs, rest) := by
  cases xs with
  | nil =>
    rw [hnil]
    show parseArray pItem fuel ('[' :: ']' :: rest) = some ([], rest)
    exact parseArray_empty pItem fuel rest
  | cons x xs =>
    rw [hcons]
    have hxs : xs.length ≤ fuel := by simp only [List.length_cons] at hfuel; omega
    have hItemXs : ∀ a ∈ xs, ∀ (rr : List Char), nonDigitHead rr →
        pItem ((render a).toList ++ rr) = some (a, rr) :=
      fun a ha => hItem a (List.mem_cons_of_mem x ha)
    obtain ⟨tx, htx⟩ := hbrace x
    have hrender : ("[" ++ render x ++ joinSep render xs ++ "]").toList ++ rest
        = '[' :: '{' :: (tx ++ ((joinSep render xs).toList ++ ("]".toList ++ rest))) := by
      rw [String.toList_append, String.toList_append, String.toList_append, htx]
      simp [List.append_assoc]
    rw [hrender, parseArray_nonempty]
    have hfold : '{' :: (tx ++ ((joinSep render xs).toList ++ ("]".toList ++ rest)))
        = (render x).toList ++ ((joinSep render xs).toList ++ ("]".toList ++ rest)) := by
      rw [htx]; simp
    rw [hfold]
    have hitem : pItem ((render x).toList ++ ((joinSep render xs).toList ++ ("]".toList ++ rest)))
        = some (x, (joinSep render xs).toList ++ ("]".toList ++ rest)) :=
      hItem x (List.mem_cons_self ..) _ (joinSep_tail_nonDigitHead render xs rest hrest)
    simp only [hitem, parseArraySep_toJson render pItem hbrace xs hItemXs fuel hxs rest hrest]

/-! ### Bridging the four concrete list renderers to `joinSep`.

Each of `inputsToJson` / `constraintsToJson` / `hashSitesToJson` / `rangesToJson` IS the canonical
`[` + first + `joinSep` + `]` shape; we expose `hnil`/`hcons` for each so `parseArray_toJson`
instantiates. (The `[x]` arm is `joinSep _ [] = ""`; the `x::y::_` arm is the literal `foldl`.) -/

theorem inputsToJson_nil : inputsToJson [] = "[]" := rfl
theorem inputsToJson_cons (i : HashInput) (is : List HashInput) :
    inputsToJson (i :: is) = "[" ++ i.toJson ++ joinSep HashInput.toJson is ++ "]" := by
  cases is with
  | nil => simp [inputsToJson, joinSep]
  | cons j js => rfl

theorem constraintsToJson_nil : constraintsToJson [] = "[]" := rfl
theorem constraintsToJson_cons (c : VmConstraint) (cs : List VmConstraint) :
    constraintsToJson (c :: cs) = "[" ++ c.toJson ++ joinSep VmConstraint.toJson cs ++ "]" := by
  cases cs with
  | nil => simp [constraintsToJson, joinSep]
  | cons d ds => rfl

theorem hashSitesToJson_nil : hashSitesToJson [] = "[]" := rfl
theorem hashSitesToJson_cons (s : VmHashSite) (ss : List VmHashSite) :
    hashSitesToJson (s :: ss) = "[" ++ s.toJson ++ joinSep VmHashSite.toJson ss ++ "]" := by
  cases ss with
  | nil => simp [hashSitesToJson, joinSep]
  | cons t ts => rfl

theorem rangesToJson_nil : rangesToJson [] = "[]" := rfl
theorem rangesToJson_cons (r : VmRange) (rs : List VmRange) :
    rangesToJson (r :: rs) = "[" ++ r.toJson ++ joinSep VmRange.toJson rs ++ "]" := by
  cases rs with
  | nil => simp [rangesToJson, joinSep]
  | cons q qs => rfl

/-! ## §10 — The hash-site parser (mirror of Rust `parse_hash_site`).

`VmHashSite.toJson s` → `{"digest_col":N,"arity":N,"inputs":[<inp>,…]}`. The `inputs` array reuses
`parseArray parseHashInput`. -/

def parseHashSite (fuel : Nat) (cs : List Char) : Option (VmHashSite × List Char) :=
  match consume "{\"digest_col\":".toList cs with
  | some r1 =>
    match readNat r1 with
    | some (digestCol, r2) =>
      match consume ",\"arity\":".toList r2 with
      | some r3 =>
        match readNat r3 with
        | some (arity, r4) =>
          match consume ",\"inputs\":".toList r4 with
          | some r5 =>
            match parseArray parseHashInput fuel r5 with
            | some (inputs, r6) =>
              match consume "}".toList r6 with
              | some r7 => some (⟨digestCol, inputs, arity⟩, r7)
              | none => none
            | none => none
          | none => none
        | none => none
      | none => none
    | none => none
  | none => none

/-- Every `HashInput` render begins with `{` (needed by the array dispatch). -/
theorem hashInput_render_brace (i : HashInput) : ∃ t, (HashInput.toJson i).toList = '{' :: t := by
  cases i with
  | col c =>
    refine ⟨"\"t\":\"col\",\"c\":".toList ++ ((toString c).toList ++ "}".toList), ?_⟩
    show ("{\"t\":\"col\",\"c\":" ++ toString c ++ "}").toList = _
    rw [String.toList_append, String.toList_append]; rfl
  | digest k =>
    refine ⟨"\"t\":\"digest\",\"k\":".toList ++ ((toString k).toList ++ "}".toList), ?_⟩
    show ("{\"t\":\"digest\",\"k\":" ++ toString k ++ "}").toList = _
    rw [String.toList_append, String.toList_append]; rfl
  | zero => exact ⟨"\"t\":\"zero\"}".toList, rfl⟩

/-- **The hash-site round-trip.** With enough fuel (≥ the input count), parsing a rendered hash site
followed by any non-digit-headed `rest` recovers `(s, rest)`. -/
theorem parseHashSite_toJson (s : VmHashSite) (fuel : Nat) (hf : s.inputs.length ≤ fuel)
    (rest : List Char) (hr : nonDigitHead rest) :
    parseHashSite fuel ((VmHashSite.toJson s).toList ++ rest) = some (s, rest) := by
  obtain ⟨digestCol, inputs, arity⟩ := s
  have hrender : (VmHashSite.toJson ⟨digestCol, inputs, arity⟩).toList
      = "{\"digest_col\":".toList ++ ((toString digestCol).toList ++
          (",\"arity\":".toList ++ ((toString arity).toList ++
            (",\"inputs\":".toList ++ ((inputsToJson inputs).toList ++ "}".toList))))) := by
    show ("{\"digest_col\":" ++ toString digestCol ++ ",\"arity\":" ++ toString arity ++
          ",\"inputs\":" ++ inputsToJson inputs ++ "}").toList = _
    rw [String.toList_append, String.toList_append, String.toList_append, String.toList_append,
        String.toList_append, String.toList_append]
    ac_rfl
  rw [hrender]; simp only [List.append_assoc]
  have hc1 : consume "{\"digest_col\":".toList
      ("{\"digest_col\":".toList ++ ((toString digestCol).toList ++
        (",\"arity\":".toList ++ ((toString arity).toList ++
          (",\"inputs\":".toList ++ ((inputsToJson inputs).toList ++ ("}".toList ++ rest)))))))
      = some ((toString digestCol).toList ++ (",\"arity\":".toList ++ ((toString arity).toList ++
          (",\"inputs\":".toList ++ ((inputsToJson inputs).toList ++ ("}".toList ++ rest)))))) :=
    consume_append _ _
  have hdc : readNat ((toString digestCol).toList ++ (",\"arity\":".toList ++ ((toString arity).toList ++
        (",\"inputs\":".toList ++ ((inputsToJson inputs).toList ++ ("}".toList ++ rest))))))
      = some (digestCol, ",\"arity\":".toList ++ ((toString arity).toList ++
        (",\"inputs\":".toList ++ ((inputsToJson inputs).toList ++ ("}".toList ++ rest))))) := by
    apply readNat_toString; exact nonDigitHead_comma _
  have hsep1 : consume ",\"arity\":".toList
      (",\"arity\":".toList ++ ((toString arity).toList ++
        (",\"inputs\":".toList ++ ((inputsToJson inputs).toList ++ ("}".toList ++ rest)))))
      = some ((toString arity).toList ++
        (",\"inputs\":".toList ++ ((inputsToJson inputs).toList ++ ("}".toList ++ rest)))) :=
    consume_append _ _
  have har : readNat ((toString arity).toList ++
        (",\"inputs\":".toList ++ ((inputsToJson inputs).toList ++ ("}".toList ++ rest))))
      = some (arity, ",\"inputs\":".toList ++ ((inputsToJson inputs).toList ++ ("}".toList ++ rest))) := by
    apply readNat_toString; exact nonDigitHead_comma _
  have hsep2 : consume ",\"inputs\":".toList
      (",\"inputs\":".toList ++ ((inputsToJson inputs).toList ++ ("}".toList ++ rest)))
      = some ((inputsToJson inputs).toList ++ ("}".toList ++ rest)) := consume_append _ _
  have harr : parseArray parseHashInput fuel ((inputsToJson inputs).toList ++ ("}".toList ++ rest))
      = some (inputs, "}".toList ++ rest) :=
    parseArray_toJson HashInput.toJson parseHashInput inputsToJson inputsToJson_nil
      inputsToJson_cons hashInput_render_brace inputs
      (fun a _ rr hrr => parseHashInput_toJson a rr hrr) fuel hf
      ("}".toList ++ rest) (nonDigitHead_brace _)
  have hb : consume "}".toList ("}".toList ++ rest) = some rest := consume_append _ _
  simp only [parseHashSite, hc1, hdc, hsep1, har, hsep2, harr, hb]

/-! ## §11 — Uniform per-element round-trips (for the top-level arrays).

`parseArray_toJson`'s `hItem` needs ONE statement that round-trips EVERY element with a SINGLE fuel.
We give the uniform `parseVmConstraint` round-trip (any of the three forms, fuel exceeding the
constraint's gate-body size) and `parseHashSite` (fuel ≥ the site's input count). -/

/-- The fuel a single constraint needs: the gate body's `esize + 1` (non-gate forms need none). -/
def cfuel : VmConstraint → Nat
  | .gate body => esize body + 1
  | _          => 1

/-- **Uniform constraint round-trip.** For any of the three WIRE forms (`gate`/`transition`/
`pi_binding`), with `cfuel c ≤ fuel` and the standing fact that `c` is not a `boundary` (the Rust
parser has no such arm, so a non-wire `boundary` could not round-trip; `WfDesc.noBoundary` discharges
`hnb` for every emitted descriptor). -/
theorem parseVmConstraint_toJson (c : VmConstraint) (fuel : Nat) (hf : cfuel c ≤ fuel)
    (hnb : ∀ row b, c ≠ .boundary row b)
    (rest : List Char) (hr : nonDigitHead rest) :
    parseVmConstraint fuel ((VmConstraint.toJson c).toList ++ rest) = some (c, rest) := by
  cases c with
  | gate body =>
    exact parseVmConstraint_toJson_gate body fuel (by simp only [cfuel] at hf; omega) rest hr
  | transition hi lo => exact parseVmConstraint_toJson_transition hi lo fuel rest hr
  | boundary row b => exact absurd rfl (hnb row b)
  | piBinding row col k => exact parseVmConstraint_toJson_pi row col k fuel rest hr

/-! ### The descriptor NAME reader (mirror of Rust `parse_string` for the AIR name). -/

/-- Split a char list at the first `'"'` (the closing quote of a JSON string). Returns the run before
the quote and the remainder AFTER the quote, or `none` if there is no quote. -/
def takeUntilQuote : List Char → Option (List Char × List Char)
  | []        => none
  | c :: cs   => if c = '"' then some ([], cs)
                 else match takeUntilQuote cs with
                      | some (pre, rest) => some (c :: pre, rest)
                      | none => none

/-- Read a quoted-string body up to the closing quote, returning it as a `String`. -/
def parseName (cs : List Char) : Option (String × List Char) :=
  match takeUntilQuote cs with
  | some (pre, rest) => some (String.ofList pre, rest)
  | none => none

/-- If `nm` contains no `'"'`, splitting `nm ++ '"' :: rest` at the first quote yields `(nm, rest)`. -/
theorem takeUntilQuote_noQuote (nm : List Char) (hnm : '"' ∉ nm) (rest : List Char) :
    takeUntilQuote (nm ++ '"' :: rest) = some (nm, rest) := by
  induction nm with
  | nil => simp [takeUntilQuote]
  | cons c cs ih =>
    have hc : c ≠ '"' := by intro h; exact hnm (by simp [h])
    have hcs : '"' ∉ cs := fun h => hnm (by simp [h])
    simp only [List.cons_append, takeUntilQuote, if_neg hc, ih hcs]

/-- **The name round-trip.** If `nm`'s chars contain no `'"'`, then `parseName (nm.toList ++ '"' ::
rest)` recovers `(nm, rest)`. (`String.ofList nm.toList = nm`.) -/
theorem parseName_toString (nm : String) (hnm : '"' ∉ nm.toList) (rest : List Char) :
    parseName (nm.toList ++ '"' :: rest) = some (nm, rest) := by
  unfold parseName
  rw [takeUntilQuote_noQuote nm.toList hnm rest]
  simp [String.ofList_toList]

/-! ## §12 — `parseVmJson`: the top-level descriptor parser (mirror of Rust `parse_vm_descriptor`).

The six fixed top-level keys, in the CANONICAL emit order (see §MODELING in the module header). `fuel`
bounds the constraint gate-body / hash-site-input recursions and the array lengths. -/

def parseVmJson (fuel : Nat) (cs : List Char) : Option EffectVmDescriptor :=
  match consume "{\"name\":\"".toList cs with
  | none => none
  | some r0 =>
    match parseName r0 with
    | none => none
    | some (name, r1) =>
      match consume ",\"trace_width\":".toList r1 with
      | none => none
      | some r2 =>
        match readNat r2 with
        | none => none
        | some (traceWidth, r3) =>
          match consume ",\"public_input_count\":".toList r3 with
          | none => none
          | some r4 =>
            match readNat r4 with
            | none => none
            | some (piCount, r5) =>
              match consume ",\"constraints\":".toList r5 with
              | none => none
              | some r6 =>
                match parseArray (parseVmConstraint fuel) fuel r6 with
                | none => none
                | some (constraints, r7) =>
                  match consume ",\"hash_sites\":".toList r7 with
                  | none => none
                  | some r8 =>
                    match parseArray (parseHashSite fuel) fuel r8 with
                    | none => none
                    | some (hashSites, r9) =>
                      match consume ",\"ranges\":".toList r9 with
                      | none => none
                      | some r10 =>
                        match parseArray parseRange fuel r10 with
                        | none => none
                        | some (ranges, r11) =>
                          match consume "}".toList r11 with
                          | some [] => some ⟨name, traceWidth, piCount, constraints, hashSites, ranges⟩
                          | _ => none

/-! ## §13 — Well-formedness (`WfDesc`) and the fuel bound (`FuelOk`).

The round-trip holds for the descriptor CLASS the live Rust seam accepts: `WfDesc` requires the name
to carry no `'"'` (the only thing that would break the unescaped string read — the emitted names are
ASCII slugs like `dregg-effectvm-transfer-v1`, no quotes) and NO `boundary` constraint (the Rust
`parse_vm_constraint` has no such arm; every emitted descriptor uses `pi_binding`, verified by census).
`FuelOk` bounds the single threaded `fuel` above every recursion depth / array length. -/

/-- Well-formed for the canonical round-trip: name has no embedded quote; no `boundary` constraint. -/
structure WfDesc (d : EffectVmDescriptor) : Prop where
  nameNoQuote : '"' ∉ d.name.toList
  noBoundary  : ∀ row b, .boundary row b ∉ d.constraints

/-- The fuel is large enough for every sub-parse: ≥ each array length, > each gate body, ≥ each site's
input count. -/
structure FuelOk (d : EffectVmDescriptor) (fuel : Nat) : Prop where
  cLen : d.constraints.length ≤ fuel
  hLen : d.hashSites.length ≤ fuel
  rLen : d.ranges.length ≤ fuel
  cBody : ∀ c ∈ d.constraints, cfuel c ≤ fuel
  hInputs : ∀ s ∈ d.hashSites, s.inputs.length ≤ fuel

/-- A concrete, always-sufficient fuel: the rendered byte length (every component is a substring, so
its length/`esize` is ≤ this). -/
def descFuel (d : EffectVmDescriptor) : Nat := (emitVmJson d).length + 1

/-! ### `{`-headed render facts (for the array dispatch) and the three top-level array round-trips. -/

/-- A char list with head `'{'` equals `'{' :: tail` — repackages a `head? = some '{'` fact into the
existential shape the array dispatch wants. -/
theorem cons_brace_of_head {l : List Char} (h : l.head? = some '{') : ∃ t, l = '{' :: t := by
  cases l with
  | nil => simp at h
  | cons c cs => simp only [List.head?] at h; exact ⟨cs, by rw [Option.some.injEq] at h; rw [h]⟩

/-- The head of `(litPrefix ++ openTail)` is the head of the literal prefix — used to read off the
leading `'{'` past the open `b.toJson` / `toString` tails. -/
theorem head_append_left {l₁ l₂ : List Char} {c : Char} (h : l₁.head? = some c) :
    (l₁ ++ l₂).head? = some c := by
  cases l₁ with
  | nil => simp at h
  | cons x xs => simpa using h

/-- Every `VmConstraint` wire render begins with `{`. -/
theorem vmConstraint_render_brace (c : VmConstraint) : ∃ t, (VmConstraint.toJson c).toList = '{' :: t := by
  apply cons_brace_of_head
  cases c with
  | gate b =>
    show ("{\"t\":\"gate\",\"body\":" ++ b.toJson ++ "}").toList.head? = some '{'
    rw [String.toList_append, String.toList_append]
    exact head_append_left (head_append_left (by decide))
  | transition hi lo =>
    show ("{\"t\":\"transition\",\"hi\":" ++ toString hi ++ ",\"lo\":" ++ toString lo ++ "}").toList.head? = some '{'
    rw [String.toList_append, String.toList_append, String.toList_append, String.toList_append]
    exact head_append_left (head_append_left (head_append_left (head_append_left (by decide))))
  | boundary row b => cases row with
    | first =>
      show ("{\"t\":\"boundary\",\"row\":\"" ++ "first" ++ "\",\"body\":" ++ b.toJson ++ "}").toList.head? = some '{'
      rw [String.toList_append, String.toList_append, String.toList_append, String.toList_append]
      exact head_append_left (head_append_left (head_append_left (head_append_left (by decide))))
    | last =>
      show ("{\"t\":\"boundary\",\"row\":\"" ++ "last" ++ "\",\"body\":" ++ b.toJson ++ "}").toList.head? = some '{'
      rw [String.toList_append, String.toList_append, String.toList_append, String.toList_append]
      exact head_append_left (head_append_left (head_append_left (head_append_left (by decide))))
  | piBinding row col k => cases row with
    | first =>
      show ("{\"t\":\"pi_binding\",\"row\":\"" ++ "first" ++ "\",\"col\":" ++ toString col ++
          ",\"pi_index\":" ++ toString k ++ "}").toList.head? = some '{'
      rw [String.toList_append, String.toList_append, String.toList_append, String.toList_append,
          String.toList_append]
      exact head_append_left (head_append_left (head_append_left (head_append_left
        (head_append_left (by decide)))))
    | last =>
      show ("{\"t\":\"pi_binding\",\"row\":\"" ++ "last" ++ "\",\"col\":" ++ toString col ++
          ",\"pi_index\":" ++ toString k ++ "}").toList.head? = some '{'
      rw [String.toList_append, String.toList_append, String.toList_append, String.toList_append,
          String.toList_append]
      exact head_append_left (head_append_left (head_append_left (head_append_left
        (head_append_left (by decide)))))

/-- Every `VmHashSite` wire render begins with `{`. -/
theorem vmHashSite_render_brace (s : VmHashSite) : ∃ t, (VmHashSite.toJson s).toList = '{' :: t := by
  apply cons_brace_of_head
  show ("{\"digest_col\":" ++ toString s.digestCol ++ ",\"arity\":" ++ toString s.arity ++
        ",\"inputs\":" ++ inputsToJson s.inputs ++ "}").toList.head? = some '{'
  rw [String.toList_append, String.toList_append, String.toList_append, String.toList_append,
      String.toList_append, String.toList_append]
  exact head_append_left (head_append_left (head_append_left (head_append_left
    (head_append_left (head_append_left (by decide))))))

/-- Every `VmRange` wire render begins with `{`. -/
theorem vmRange_render_brace (r : VmRange) : ∃ t, (VmRange.toJson r).toList = '{' :: t := by
  apply cons_brace_of_head
  show ("{\"wire\":" ++ toString r.wire ++ ",\"bits\":" ++ toString r.bits ++ "}").toList.head? = some '{'
  rw [String.toList_append, String.toList_append, String.toList_append, String.toList_append]
  exact head_append_left (head_append_left (head_append_left (head_append_left (by decide))))

/-- **The constraint array round-trips** when fuel dominates every gate body and there is no `boundary`
constraint in the list (membership-restricted — the off-list well-formedness need not hold). -/
theorem parseConstraints_toJson (cs : List VmConstraint) (fuel : Nat)
    (hlen : cs.length ≤ fuel) (hbody : ∀ c ∈ cs, cfuel c ≤ fuel)
    (hnb : ∀ c ∈ cs, ∀ row b, c ≠ .boundary row b)
    (rest : List Char) (hrest : nonDigitHead rest) :
    parseArray (parseVmConstraint fuel) fuel ((constraintsToJson cs).toList ++ rest)
      = some (cs, rest) :=
  parseArray_toJson VmConstraint.toJson (parseVmConstraint fuel) constraintsToJson
    constraintsToJson_nil constraintsToJson_cons vmConstraint_render_brace cs
    (fun a ha rr hrr => parseVmConstraint_toJson a fuel (hbody a ha) (hnb a ha) rr hrr)
    fuel hlen rest hrest

/-- **The hash-site array round-trips** when fuel dominates every site's input count. -/
theorem parseHashSites_toJson (ss : List VmHashSite) (fuel : Nat)
    (hlen : ss.length ≤ fuel) (hin : ∀ s ∈ ss, s.inputs.length ≤ fuel)
    (rest : List Char) (hrest : nonDigitHead rest) :
    parseArray (parseHashSite fuel) fuel ((hashSitesToJson ss).toList ++ rest)
      = some (ss, rest) :=
  parseArray_toJson VmHashSite.toJson (parseHashSite fuel) hashSitesToJson
    hashSitesToJson_nil hashSitesToJson_cons vmHashSite_render_brace ss
    (fun a ha rr hrr => parseHashSite_toJson a fuel (hin a ha) rr hrr)
    fuel hlen rest hrest

/-- **The range array round-trips** (no per-element fuel needed). -/
theorem parseRanges_toJson (rs : List VmRange) (fuel : Nat) (hlen : rs.length ≤ fuel)
    (rest : List Char) (hrest : nonDigitHead rest) :
    parseArray parseRange fuel ((rangesToJson rs).toList ++ rest) = some (rs, rest) :=
  parseArray_toJson VmRange.toJson parseRange rangesToJson rangesToJson_nil rangesToJson_cons
    vmRange_render_brace rs (fun a _ rr hrr => parseRange_toJson a rr hrr) fuel hlen rest hrest

/-! ## §14 — `parseVmJson_emitVmJson`: THE deliverable.

For every `WfDesc` descriptor `d` (name carries no `'"'`, no `boundary` constraint — i.e. exactly the
descriptor class the live Rust seam accepts) and any `fuel` large enough (`FuelOk`), the canonical
parser inverts `emitVmJson`:  `parseVmJson fuel (emitVmJson d).toList = some d`. Hence `emitVmJson` is
INJECTIVE and INFORMATION-PRESERVING on `WfDesc` descriptors (`emitVmJson_injective`). -/

/-- Decompose the full emit render into the fully right-associated prefix chain the parser walks. -/
theorem emitVmJson_toList_decomp (d : EffectVmDescriptor) :
    (emitVmJson d).toList
      = "{\"name\":\"".toList ++ (d.name.toList ++ ('"' ::
          (",\"trace_width\":".toList ++ ((toString d.traceWidth).toList ++
            (",\"public_input_count\":".toList ++ ((toString d.piCount).toList ++
              (",\"constraints\":".toList ++ ((constraintsToJson d.constraints).toList ++
                (",\"hash_sites\":".toList ++ ((hashSitesToJson d.hashSites).toList ++
                  (",\"ranges\":".toList ++ ((rangesToJson d.ranges).toList ++ "}".toList)))))))))))) := by
  show ("{\"name\":\"" ++ d.name ++ "\",\"trace_width\":" ++ toString d.traceWidth ++
        ",\"public_input_count\":" ++ toString d.piCount ++
        ",\"constraints\":" ++ constraintsToJson d.constraints ++
        ",\"hash_sites\":" ++ hashSitesToJson d.hashSites ++
        ",\"ranges\":" ++ rangesToJson d.ranges ++ "}").toList = _
  rw [String.toList_append, String.toList_append, String.toList_append, String.toList_append,
      String.toList_append, String.toList_append, String.toList_append, String.toList_append,
      String.toList_append, String.toList_append, String.toList_append, String.toList_append]
  have hq : ("\",\"trace_width\":").toList = '"' :: ",\"trace_width\":".toList := by decide
  rw [hq]; simp only [List.append_assoc, List.cons_append]

/-- The three array `rest`s in `emitVmJson` are `,"…":`-prefixed, hence non-digit-headed. -/
theorem nonDigitHead_commaKey_hashSites (rest : List Char) :
    nonDigitHead (",\"hash_sites\":".toList ++ rest) := by
  have h : ",\"hash_sites\":".toList = ',' :: "\"hash_sites\":".toList := by decide
  rw [h, List.cons_append]; exact nonDigitHead_comma _
theorem nonDigitHead_commaKey_ranges (rest : List Char) :
    nonDigitHead (",\"ranges\":".toList ++ rest) := by
  have h : ",\"ranges\":".toList = ',' :: "\"ranges\":".toList := by decide
  rw [h, List.cons_append]; exact nonDigitHead_comma _

/-- **`parseVmJson_emitVmJson` — the round-trip.** -/
theorem parseVmJson_emitVmJson (d : EffectVmDescriptor) (hwf : WfDesc d)
    (fuel : Nat) (hfuel : FuelOk d fuel) :
    parseVmJson fuel (emitVmJson d).toList = some d := by
  rw [emitVmJson_toList_decomp d]
  -- Walk the chain: each `consume`/`readNat`/`parseName`/array step succeeds and threads the tail.
  have hc0 := consume_append "{\"name\":\"".toList
      (d.name.toList ++ ('"' ::
        (",\"trace_width\":".toList ++ ((toString d.traceWidth).toList ++
          (",\"public_input_count\":".toList ++ ((toString d.piCount).toList ++
            (",\"constraints\":".toList ++ ((constraintsToJson d.constraints).toList ++
              (",\"hash_sites\":".toList ++ ((hashSitesToJson d.hashSites).toList ++
                (",\"ranges\":".toList ++ ((rangesToJson d.ranges).toList ++ "}".toList))))))))))))
  have hname := parseName_toString d.name hwf.nameNoQuote
      (",\"trace_width\":".toList ++ ((toString d.traceWidth).toList ++
        (",\"public_input_count\":".toList ++ ((toString d.piCount).toList ++
          (",\"constraints\":".toList ++ ((constraintsToJson d.constraints).toList ++
            (",\"hash_sites\":".toList ++ ((hashSitesToJson d.hashSites).toList ++
              (",\"ranges\":".toList ++ ((rangesToJson d.ranges).toList ++ "}".toList))))))))))
  have htw := consume_append ",\"trace_width\":".toList
      ((toString d.traceWidth).toList ++ (",\"public_input_count\":".toList ++ ((toString d.piCount).toList ++
        (",\"constraints\":".toList ++ ((constraintsToJson d.constraints).toList ++
          (",\"hash_sites\":".toList ++ ((hashSitesToJson d.hashSites).toList ++
            (",\"ranges\":".toList ++ ((rangesToJson d.ranges).toList ++ "}".toList)))))))))
  have hrtw := readNat_toString d.traceWidth
      (",\"public_input_count\":".toList ++ ((toString d.piCount).toList ++
        (",\"constraints\":".toList ++ ((constraintsToJson d.constraints).toList ++
          (",\"hash_sites\":".toList ++ ((hashSitesToJson d.hashSites).toList ++
            (",\"ranges\":".toList ++ ((rangesToJson d.ranges).toList ++ "}".toList))))))))
      (nonDigitHead_comma _)
  have hpic := consume_append ",\"public_input_count\":".toList
      ((toString d.piCount).toList ++ (",\"constraints\":".toList ++ ((constraintsToJson d.constraints).toList ++
        (",\"hash_sites\":".toList ++ ((hashSitesToJson d.hashSites).toList ++
          (",\"ranges\":".toList ++ ((rangesToJson d.ranges).toList ++ "}".toList)))))))
  have hrpic := readNat_toString d.piCount
      (",\"constraints\":".toList ++ ((constraintsToJson d.constraints).toList ++
        (",\"hash_sites\":".toList ++ ((hashSitesToJson d.hashSites).toList ++
          (",\"ranges\":".toList ++ ((rangesToJson d.ranges).toList ++ "}".toList))))))
      (nonDigitHead_comma _)
  have hcc := consume_append ",\"constraints\":".toList
      ((constraintsToJson d.constraints).toList ++ (",\"hash_sites\":".toList ++ ((hashSitesToJson d.hashSites).toList ++
        (",\"ranges\":".toList ++ ((rangesToJson d.ranges).toList ++ "}".toList)))))
  have hcons := parseConstraints_toJson d.constraints fuel hfuel.cLen hfuel.cBody
      (fun c hc row b heq => hwf.noBoundary row b (heq ▸ hc))
      (",\"hash_sites\":".toList ++ ((hashSitesToJson d.hashSites).toList ++
        (",\"ranges\":".toList ++ ((rangesToJson d.ranges).toList ++ "}".toList))))
      (nonDigitHead_commaKey_hashSites _)
  have hch := consume_append ",\"hash_sites\":".toList
      ((hashSitesToJson d.hashSites).toList ++ (",\"ranges\":".toList ++ ((rangesToJson d.ranges).toList ++ "}".toList)))
  have hhs := parseHashSites_toJson d.hashSites fuel hfuel.hLen hfuel.hInputs
      (",\"ranges\":".toList ++ ((rangesToJson d.ranges).toList ++ "}".toList))
      (nonDigitHead_commaKey_ranges _)
  have hcr := consume_append ",\"ranges\":".toList
      ((rangesToJson d.ranges).toList ++ "}".toList)
  have hrng := parseRanges_toJson d.ranges fuel hfuel.rLen ("}".toList)
      (nonDigitHead_brace _)
  have hb := consume_append "}".toList ([] : List Char)
  simp only [List.append_nil] at hb
  -- Drive the parser by the success chain.
  simp only [parseVmJson, hc0, hname, htw, hrtw, hpic, hrpic, hcc, hcons, hch, hhs, hcr, hrng, hb]

/-! ## §15 — `emitVmJson_injective`: the consequence.

The round-trip makes `emitVmJson` INJECTIVE on `WfDesc` descriptors: two distinct descriptors cannot
render to the same wire bytes. So the SHA-256 fingerprint the registry pins now guards bytes whose
descriptor is uniquely RECOVERABLE — no field is silently dropped, merged, or aliased by the
serializer, and every field the Lean soundness theorems (`satisfiedVm`, the per-effect faithfulness /
anti-ghost lemmas) pin about the in-Lean descriptor survives into the bytes the prover runs. -/
theorem emitVmJson_injective (d₁ d₂ : EffectVmDescriptor)
    (hwf₁ : WfDesc d₁) (hwf₂ : WfDesc d₂)
    (fuel : Nat) (hf₁ : FuelOk d₁ fuel) (hf₂ : FuelOk d₂ fuel)
    (heq : emitVmJson d₁ = emitVmJson d₂) : d₁ = d₂ := by
  have h₁ := parseVmJson_emitVmJson d₁ hwf₁ fuel hf₁
  have h₂ := parseVmJson_emitVmJson d₂ hwf₂ fuel hf₂
  rw [heq] at h₁
  rw [h₁] at h₂
  exact Option.some.inj h₂

/-! ## §16 — `descFuel` is always sufficient (the fuel-free instantiation).

We bound every sub-parse depth/length by the rendered byte length, so `FuelOk d (descFuel d)` holds
unconditionally — the round-trip and injectivity then need no manual fuel arithmetic. -/

/-- A gate body's `esize` is strictly below its render length (each `add`/`mul` node renders to ≥ 1
char and is counted once in `esize`). -/
theorem esize_lt_toJson_length (e : EmittedExpr) : esize e < (EmittedExpr.toJson e).length := by
  induction e with
  | var v =>
    show esize (.var v) < (("{\"t\":\"var\",\"v\":" ++ toString v ++ "}")).length
    simp only [esize, String.length_append]
    have h1 : 0 < ("{\"t\":\"var\",\"v\":").length := by decide
    omega
  | const c =>
    show esize (.const c) < (("{\"t\":\"const\",\"v\":" ++ toString c ++ "}")).length
    simp only [esize, String.length_append]
    have h1 : 0 < ("{\"t\":\"const\",\"v\":").length := by decide
    omega
  | add l r ihl ihr =>
    have : (EmittedExpr.toJson (.add l r)).length
        = "{\"t\":\"add\",\"l\":".length + l.toJson.length + ",\"r\":".length + r.toJson.length + "}".length := by
      simp only [EmittedExpr.toJson, String.length_append]
    rw [this]; simp only [esize]
    have h1 : ("{\"t\":\"add\",\"l\":").length = 15 := by decide
    have h2 : (",\"r\":").length = 5 := by decide
    omega
  | mul l r ihl ihr =>
    have : (EmittedExpr.toJson (.mul l r)).length
        = "{\"t\":\"mul\",\"l\":".length + l.toJson.length + ",\"r\":".length + r.toJson.length + "}".length := by
      simp only [EmittedExpr.toJson, String.length_append]
    rw [this]; simp only [esize]
    have h1 : ("{\"t\":\"mul\",\"l\":").length = 15 := by decide
    have h2 : (",\"r\":").length = 5 := by decide
    omega

/-- The `joinSep` length dominates the element count. -/
theorem length_le_joinSep {α} (render : α → String) (xs : List α) :
    xs.length ≤ (joinSep render xs).length := by
  induction xs with
  | nil => simp [joinSep]
  | cons y ys ih =>
    rw [joinSep_cons]
    simp only [String.length_append, List.length_cons]
    have : ("," : String).length = 1 := by decide
    omega

/-- Each element's render fits inside the `joinSep` render. -/
theorem render_length_le_joinSep {α} (render : α → String) (xs : List α) :
    ∀ a ∈ xs, (render a).length ≤ (joinSep render xs).length := by
  induction xs with
  | nil => intro a ha; simp at ha
  | cons y ys ih =>
    intro a ha
    rw [joinSep_cons]
    simp only [String.length_append]
    rcases List.mem_cons.mp ha with h | h
    · subst h; omega
    · have := ih a h; omega

/-- `cfuel c` fits inside the constraint's render length. -/
theorem cfuel_le_toJson_length (c : VmConstraint) : cfuel c ≤ (VmConstraint.toJson c).length := by
  cases c with
  | gate b =>
    show esize b + 1 ≤ (VmConstraint.toJson (.gate b)).length
    have hb := esize_lt_toJson_length b
    have hlen : (VmConstraint.toJson (.gate b)).length
        = "{\"t\":\"gate\",\"body\":".length + b.toJson.length + "}".length := by
      simp only [VmConstraint.toJson, String.length_append]
    rw [hlen]; omega
  | transition hi lo =>
    show 1 ≤ (VmConstraint.toJson (.transition hi lo)).length
    simp only [VmConstraint.toJson, String.length_append]
    have : 0 < ("{\"t\":\"transition\",\"hi\":" : String).length := by decide
    omega
  | boundary row b =>
    show 1 ≤ (VmConstraint.toJson (.boundary row b)).length
    have hp : 0 < ("{\"t\":\"boundary\",\"row\":\"" : String).length := by decide
    cases row <;> (simp only [VmConstraint.toJson, String.length_append]; omega)
  | piBinding row col k =>
    show 1 ≤ (VmConstraint.toJson (.piBinding row col k)).length
    have hp : 0 < ("{\"t\":\"pi_binding\",\"row\":\"" : String).length := by decide
    cases row <;> (simp only [VmConstraint.toJson, String.length_append]; omega)

/-- The list-renderer length dominates the element count and every element's render. -/
theorem renderList_bounds {α} (render : α → String) (renderList : List α → String)
    (hnil : renderList [] = "[]")
    (hcons : ∀ (x : α) (xs : List α), renderList (x :: xs)
        = "[" ++ render x ++ joinSep render xs ++ "]")
    (xs : List α) :
    xs.length ≤ (renderList xs).length ∧
      (∀ a ∈ xs, (render a).length ≤ (renderList xs).length) := by
  cases xs with
  | nil => rw [hnil]; exact ⟨Nat.zero_le _, by intro a ha; simp at ha⟩
  | cons x xs =>
    rw [hcons]
    simp only [String.length_append, List.length_cons]
    have hjl := length_le_joinSep render xs
    have hbr : ("[" : String).length = 1 := by decide
    have hbr2 : ("]" : String).length = 1 := by decide
    refine ⟨by omega, ?_⟩
    intro a ha
    rcases List.mem_cons.mp ha with h | h
    · subst h; omega
    · have := render_length_le_joinSep render xs a h; omega

/-- Each top-level array render is a substring of `emitVmJson d`, so its length is dominated. -/
theorem componentLengths_le_emit (d : EffectVmDescriptor) :
    (constraintsToJson d.constraints).length ≤ (emitVmJson d).length ∧
    (hashSitesToJson d.hashSites).length ≤ (emitVmJson d).length ∧
    (rangesToJson d.ranges).length ≤ (emitVmJson d).length := by
  have : (emitVmJson d).length
      = "{\"name\":\"".length + d.name.length + "\",\"trace_width\":".length +
        (toString d.traceWidth).length + ",\"public_input_count\":".length +
        (toString d.piCount).length + ",\"constraints\":".length +
        (constraintsToJson d.constraints).length + ",\"hash_sites\":".length +
        (hashSitesToJson d.hashSites).length + ",\"ranges\":".length +
        (rangesToJson d.ranges).length + "}".length := by
    simp only [emitVmJson, String.length_append]
  rw [this]; refine ⟨by omega, by omega, by omega⟩

/-- **`descFuel d` is always sufficient.** Hence the round-trip and injectivity hold with NO manual
fuel arithmetic (the fuel hypotheses are discharged structurally from the render length). -/
theorem fuelOk_descFuel (d : EffectVmDescriptor) : FuelOk d (descFuel d) := by
  obtain ⟨hCstr, hHsh, hRng⟩ := componentLengths_le_emit d
  have hCb := renderList_bounds VmConstraint.toJson constraintsToJson constraintsToJson_nil
    constraintsToJson_cons d.constraints
  have hHb := renderList_bounds VmHashSite.toJson hashSitesToJson hashSitesToJson_nil
    hashSitesToJson_cons d.hashSites
  have hRb := renderList_bounds VmRange.toJson rangesToJson rangesToJson_nil
    rangesToJson_cons d.ranges
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [descFuel]; omega
  · simp only [descFuel]; omega
  · simp only [descFuel]; omega
  · intro c hc
    have h1 := cfuel_le_toJson_length c
    have h2 := hCb.2 c hc
    simp only [descFuel]; omega
  · intro s hs
    have h2 := hHb.2 s hs
    -- a site's input count ≤ its render length ≤ hash_sites render ≤ emit
    have h3 : s.inputs.length ≤ (VmHashSite.toJson s).length := by
      have hlen : (VmHashSite.toJson s).length
          = "{\"digest_col\":".length + (toString s.digestCol).length + ",\"arity\":".length +
            (toString s.arity).length + ",\"inputs\":".length + (inputsToJson s.inputs).length +
            "}".length := by simp only [VmHashSite.toJson, String.length_append]
      have hin := (renderList_bounds HashInput.toJson inputsToJson inputsToJson_nil
        inputsToJson_cons s.inputs).1
      rw [hlen]; omega
    simp only [descFuel]; omega

/-- **Round-trip at the canonical fuel** — `WfDesc` is the only hypothesis. -/
theorem parseVmJson_emitVmJson_descFuel (d : EffectVmDescriptor) (hwf : WfDesc d) :
    parseVmJson (descFuel d) (emitVmJson d).toList = some d :=
  parseVmJson_emitVmJson d hwf (descFuel d) (fuelOk_descFuel d)

/-- **`emitVmJson` is injective on `WfDesc` descriptors** — fuel-free. The strongest honest form: two
distinct (name-quote-free, boundary-free) descriptors NEVER render to the same wire bytes. -/
theorem emitVmJson_injective_wf (d₁ d₂ : EffectVmDescriptor)
    (hwf₁ : WfDesc d₁) (hwf₂ : WfDesc d₂) (heq : emitVmJson d₁ = emitVmJson d₂) : d₁ = d₂ := by
  have h₁ := parseVmJson_emitVmJson_descFuel d₁ hwf₁
  have h₂ := parseVmJson_emitVmJson_descFuel d₂ hwf₂
  rw [heq] at h₁
  -- both parse `(emitVmJson d₂).toList`, but at DIFFERENT canonical fuels (descFuel d₁ vs d₂); equal
  -- renders ⇒ equal descFuel, so the fuels coincide and both `some`s agree.
  have hfuel : descFuel d₁ = descFuel d₂ := by simp only [descFuel, heq]
  rw [hfuel] at h₁
  rw [h₁] at h₂
  exact Option.some.inj h₂

/-! ## §17 — Axiom-hygiene pins (the honesty tripwire). -/

#assert_axioms parseVmJson_emitVmJson
#assert_axioms emitVmJson_injective
#assert_axioms parseVmJson_emitVmJson_descFuel
#assert_axioms emitVmJson_injective_wf
#assert_axioms parseExpr_toJson
#assert_axioms parseVmConstraint_toJson
#assert_axioms parseHashSite_toJson
#assert_axioms parseArray_toJson

end Dregg2.Circuit.Argus.EmitRoundtrip
