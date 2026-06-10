import Dregg2.Exec.CodecRoundtrip.Leaves
import Dregg2.Exec.CodecRoundtrip.Value

/-!
Submodule of `Dregg2.Exec.CodecRoundtrip` — split for parallel compilation.
-/

namespace Dregg2.Exec.CodecRoundtrip

open Dregg2.Exec
open Dregg2.Exec.FFI
open Dregg2.Exec.FFI.Wide

/-! ## §6 — the `Authorization` (WHO) decoder roundtrip (FILL-J production (b): the 10-variant sum +
the recursive `oneOf` candidate list).

The WHO decoder is the SECURITY-CRITICAL wire layer — a symmetric codec bug here forges authority
silently past the differential (the encoder and decoder agree on a wrong grammar, so a round-trip
`#eval` passes; only a parse∘encode THEOREM, pinning the decoder as the genuine left-inverse, catches
it). This §6 removes `parseAuthW` from the Lean-side TCB.

It mirrors §5's `valueGoal_all` exactly: a bundled mutual goal (`parseAuthW` / `parseAuthListW` / the
loop body), strong-induction on fuel, the recursive `oneOf` arm threading fuel through the candidate
list as `record` threads it through the fields. The 10-arm fail-closed DISPATCH is discharged
MECHANICALLY by `lit_ne_pre` (failure-monotonicity over the two concrete tag strings); the per-arm
payload WALK is three tactic macros. `WfAuth` pins the codec boundary (every digest `< 2^256`, the
`[u8;32]` width), recursively over `oneOf`. -/

/-! ### §6a — the per-arm tactic combinators (the payload walk + the fail-closed dispatch).
`lit_ok` consumes the literal at the head; `lit_fail k b` discharges a WRONG-tag `lit k` on input that
begins with the concrete tag `b` (both `decide`-checkable); `dig_ok h` consumes a `"H64"` digest field
(`h : d < 2^256`); `nat_ok` consumes a decimal number whose post-byte is `,`/`]}`/`]` (the three
non-digit closers, tried in turn). After the big `String.toList_append`/`List.append_assoc`
right-association, exactly one of these fires per parser step — turning the 10×(dispatch+walk) into a
mechanical script rather than O(n²) hand-work. -/

/-- A `,`-led closer (after right-association the byte after a number is this) is non-digit. -/
theorem nd_litComma (X : PState) :
    ((",":String).toList ++ X = [] ∨ ∃ c rs, (",":String).toList ++ X = c :: rs ∧ c.isDigit = false) :=
  Or.inr ⟨',', X, rfl, by decide⟩
/-- A `]}`-led closer is non-digit. -/
theorem nd_litClose (X : PState) :
    (("]}":String).toList ++ X = [] ∨ ∃ c rs, ("]}":String).toList ++ X = c :: rs ∧ c.isDigit = false) :=
  Or.inr ⟨']', '}' :: X, rfl, by decide⟩
/-- A `]`-led closer is non-digit. -/
theorem nd_litBrack (X : PState) :
    (("]":String).toList ++ X = [] ∨ ∃ c rs, ("]":String).toList ++ X = c :: rs ∧ c.isDigit = false) :=
  Or.inr ⟨']', X, rfl, by decide⟩

/-- `cN` (read `,` then a `Nat`) on a `toString`-led tail whose post-byte is a non-digit closer. -/
theorem cN_step (n : Nat) (rest : PState)
    (hnd : rest = [] ∨ ∃ c rs, rest = c :: rs ∧ c.isDigit = false) :
    cN ((",":String).toList ++ ((toString n).toList ++ rest)) = some (n, rest) := by
  unfold cN; rw [lit_append]; simp only []; exact parseNat_toString n rest hnd

/-- `cI` (read `,` then an `Int`) on a `toString`-led tail whose post-byte is a non-digit closer. -/
theorem cI_step (i : Int) (rest : PState)
    (hnd : rest = [] ∨ ∃ c rs, rest = c :: rs ∧ c.isDigit = false) :
    cI ((",":String).toList ++ ((toString i).toList ++ rest)) = some (i, rest) := by
  unfold cI; rw [lit_append]; simp only []; exact parseInt_toString i rest hnd

/-- Consume the literal at the head and reduce the resulting `some`-match. -/
local macro "lit_ok" : tactic => `(tactic| (rw [lit_append]; try simp only []))
/-- Discharge a WRONG-tag dispatch: `lit k` fails on input beginning with the concrete tag `b`. -/
local macro "lit_fail" k:str b:str : tactic =>
  `(tactic| (rw [lit_ne_pre $k $b _ (by decide) (by decide)]; simp only []))
/-- Consume a `"H64"` digest field (`h : d < 2^256`) and reduce the `some`-match. -/
local macro "dig_ok" h:term : tactic => `(tactic| (rw [parseDig_encDig _ _ $h]; simp only []))
/-- Consume a decimal number whose post-byte is a non-digit closer (`,` / `]}` / `]`). -/
local macro "nat_ok" : tactic =>
  `(tactic| ((first
    | rw [parseNat_toString _ _ (nd_litComma _)]
    | rw [parseNat_toString _ _ (nd_litClose _)]
    | rw [parseNat_toString _ _ (nd_litBrack _)]); simp only []))

/-! ### §6b — well-formedness and the structural fuel measure (mutual over `oneOf`). -/

/-! Well-formed `AuthW`: every digest field `< 2^256` (the `[u8;32]` width), recursively over `oneOf`. -/
mutual
/-- Well-formed `AuthW`: every digest field `< 2^256` (the `[u8;32]` width), recursively over `oneOf`. -/
def WfAuth : AuthW → Prop
  | .signature pk _            => pk < 2 ^ 256
  | .proof vk _ _ _            => vk < 2 ^ 256
  | .breadstuff _              => True
  | .bearer dm _ _             => dm < 2 ^ 256
  | .unchecked                 => True
  | .capTpDelivered im sm _ _  => im < 2 ^ 256 ∧ sm < 2 ^ 256
  | .custom st _               => st < 2 ^ 256
  | .oneOf cands _             => WfAuthList cands
  | .stealth otp eph _         => otp < 2 ^ 256 ∧ eph < 2 ^ 256
  | .token key _               => key < 2 ^ 256
def WfAuthList : List AuthW → Prop
  | []      => True
  | a :: as => WfAuth a ∧ WfAuthList as
end

/-! Structural size (the fuel measure): `oneOf` is `1 + Σ candidates`; every other arm is `1`. -/
mutual
/-- Structural size (the fuel measure): `oneOf` is `1 + Σ candidates`; every other arm is `1`. -/
def authSize : AuthW → Nat
  | .oneOf cands _ => 1 + authListSize cands
  | _              => 1
def authListSize : List AuthW → Nat
  | []      => 0
  | a :: as => 1 + authSize a + authListSize as
end

/-! ### §6c — the 9 NON-recursive arms (no induction; the dispatch+walk script per arm).
This standalone helper closes every arm EXCEPT `oneOf`; the bundled `authGoal_all` (§6e) delegates its
9 flat cases straight to here, so the recursive proof carries no duplication. -/

/-- **`parseAuthW` inverts `encodeAuthW` on the 9 non-recursive arms.** Each is a fixed dispatch
(earlier tags fail fail-closed) then a fixed payload walk (digest/number fields, closer). -/
theorem parseAuthW_flat (a : AuthW) (rest : PState) (fuel : Nat)
    (hwf : WfAuth a) (hno : ∀ cs i, a ≠ .oneOf cs i) :
    parseAuthW (fuel + 1) ((encodeAuthW a).toList ++ rest) = some (a, rest) := by
  cases a with
  | oneOf cs i => exact absurd rfl (hno cs i)
  | signature pk sig =>
      have hpk : pk < 2 ^ 256 := hwf
      unfold parseAuthW
      simp only [encodeAuthW, String.toList_append, List.append_assoc]
      lit_ok; dig_ok hpk; lit_ok; nat_ok; lit_ok; rfl
  | proof vk pf ba br =>
      have hvk : vk < 2 ^ 256 := hwf
      unfold parseAuthW
      simp only [encodeAuthW, String.toList_append, List.append_assoc]
      lit_fail "{\"sig\":[" "{\"pf\":["
      lit_ok; dig_ok hvk; lit_ok; nat_ok; lit_ok; nat_ok; lit_ok; nat_ok; lit_ok; rfl
  | breadstuff tok =>
      unfold parseAuthW
      simp only [encodeAuthW, String.toList_append, List.append_assoc]
      lit_fail "{\"sig\":[" "{\"bread\":["
      lit_fail "{\"pf\":[" "{\"bread\":["
      lit_ok; nat_ok; lit_ok; rfl
  | bearer dm ds stark =>
      have hdm : dm < 2 ^ 256 := hwf
      unfold parseAuthW
      simp only [encodeAuthW, String.toList_append, List.append_assoc]
      lit_fail "{\"sig\":[" "{\"bearer\":["
      lit_fail "{\"pf\":[" "{\"bearer\":["
      lit_fail "{\"bread\":[" "{\"bearer\":["
      lit_ok; dig_ok hdm; lit_ok; nat_ok; lit_ok
      cases stark with
      | true =>
          rw [show ((if true then "1" else "0" : String)) = "1" from rfl,
              show (("1":String).toList) = (toString (1:Nat)).toList from rfl,
              parseNat_toString 1 _ (nd_litClose _)]
          simp only []
          rw [if_pos (by norm_num : (1:Nat) ≤ 1)]
          lit_ok; rfl
      | false =>
          rw [show ((if false then "1" else "0" : String)) = "0" from rfl,
              show (("0":String).toList) = (toString (0:Nat)).toList from rfl,
              parseNat_toString 0 _ (nd_litClose _)]
          simp only []
          rw [if_pos (by norm_num : (0:Nat) ≤ 1)]
          lit_ok; rfl
  | unchecked =>
      unfold parseAuthW
      simp only [encodeAuthW]
      lit_fail "{\"sig\":[" "{\"unchecked\":0}"
      lit_fail "{\"pf\":[" "{\"unchecked\":0}"
      lit_fail "{\"bread\":[" "{\"unchecked\":0}"
      lit_fail "{\"bearer\":[" "{\"unchecked\":0}"
      lit_ok
  | capTpDelivered im sm isig ss =>
      obtain ⟨him, hsm⟩ : im < 2 ^ 256 ∧ sm < 2 ^ 256 := hwf
      unfold parseAuthW
      simp only [encodeAuthW, String.toList_append, List.append_assoc]
      lit_fail "{\"sig\":[" "{\"captp\":["
      lit_fail "{\"pf\":[" "{\"captp\":["
      lit_fail "{\"bread\":[" "{\"captp\":["
      lit_fail "{\"bearer\":[" "{\"captp\":["
      lit_fail "{\"unchecked\":0}" "{\"captp\":["
      lit_ok; dig_ok him; lit_ok; dig_ok hsm; lit_ok; nat_ok; lit_ok; nat_ok; lit_ok; rfl
  | custom st pf =>
      have hst : st < 2 ^ 256 := hwf
      unfold parseAuthW
      simp only [encodeAuthW, String.toList_append, List.append_assoc]
      lit_fail "{\"sig\":[" "{\"custom\":["
      lit_fail "{\"pf\":[" "{\"custom\":["
      lit_fail "{\"bread\":[" "{\"custom\":["
      lit_fail "{\"bearer\":[" "{\"custom\":["
      lit_fail "{\"unchecked\":0}" "{\"custom\":["
      lit_fail "{\"captp\":[" "{\"custom\":["
      lit_ok; dig_ok hst; lit_ok; nat_ok; lit_ok; rfl
  | stealth otp eph sig =>
      obtain ⟨hotp, heph⟩ : otp < 2 ^ 256 ∧ eph < 2 ^ 256 := hwf
      unfold parseAuthW
      simp only [encodeAuthW, String.toList_append, List.append_assoc]
      lit_fail "{\"sig\":[" "{\"stealth\":["
      lit_fail "{\"pf\":[" "{\"stealth\":["
      lit_fail "{\"bread\":[" "{\"stealth\":["
      lit_fail "{\"bearer\":[" "{\"stealth\":["
      lit_fail "{\"unchecked\":0}" "{\"stealth\":["
      lit_fail "{\"captp\":[" "{\"stealth\":["
      lit_fail "{\"custom\":[" "{\"stealth\":["
      lit_fail "{\"oneof\":[" "{\"stealth\":["
      lit_ok; dig_ok hotp; lit_ok; dig_ok heph; lit_ok; nat_ok; lit_ok; rfl
  | token key sig =>
      have hkey : key < 2 ^ 256 := hwf
      unfold parseAuthW
      simp only [encodeAuthW, String.toList_append, List.append_assoc]
      lit_fail "{\"sig\":[" "{\"token\":["
      lit_fail "{\"pf\":[" "{\"token\":["
      lit_fail "{\"bread\":[" "{\"token\":["
      lit_fail "{\"bearer\":[" "{\"token\":["
      lit_fail "{\"unchecked\":0}" "{\"token\":["
      lit_fail "{\"captp\":[" "{\"token\":["
      lit_fail "{\"custom\":[" "{\"token\":["
      lit_fail "{\"oneof\":[" "{\"token\":["
      lit_fail "{\"stealth\":[" "{\"token\":["
      lit_ok; dig_ok hkey; lit_ok; nat_ok; lit_ok; rfl

/-! ### §6d — the candidate-list encoder shape (normalizing the `foldl` into peelable cons form).
`encodeAuthListW`'s tail is a left-`foldl` accumulator (FFI.lean:1384), which does NOT syntactically
expose the `","`-prefixed head the cons-recursive `parseAuthLoopW` peels. So — unlike §5, whose
`encodeFieldsTailW` was already cons-recursive at the FFI site — we must NORMALIZE the fold. The
accumulator-pull-out lemma (`foldl_authtail`) turns it into the clean `',' :: enc b ++ tail` shape. This
is the one genuinely-new structural lemma with no §5 analogue. -/

/-- Every `encodeAuthW` arm opens with `'{'` — the head char that makes `lit "[]"` fail on a `[{`-led
list body. (`String ++` is opaque to defeq, so the head is exposed via `String.toList_append` + a
`decide` on the concrete tag literal — the same `decide`-evaluates-`toList` route the dispatch uses.) -/
theorem encodeAuthW_head (a : AuthW) : ∃ t, (encodeAuthW a).toList = '{' :: t := by
  cases a <;> exact ⟨_, by
    simp only [encodeAuthW, String.toList_append, List.cons_append,
      show ("{\"sig\":[":String).toList = '{' :: "\"sig\":[".toList from by decide,
      show ("{\"pf\":[":String).toList = '{' :: "\"pf\":[".toList from by decide,
      show ("{\"bread\":[":String).toList = '{' :: "\"bread\":[".toList from by decide,
      show ("{\"bearer\":[":String).toList = '{' :: "\"bearer\":[".toList from by decide,
      show ("{\"unchecked\":0}":String).toList = '{' :: "\"unchecked\":0}".toList from by decide,
      show ("{\"captp\":[":String).toList = '{' :: "\"captp\":[".toList from by decide,
      show ("{\"custom\":[":String).toList = '{' :: "\"custom\":[".toList from by decide,
      show ("{\"oneof\":[":String).toList = '{' :: "\"oneof\":[".toList from by decide,
      show ("{\"stealth\":[":String).toList = '{' :: "\"stealth\":[".toList from by decide,
      show ("{\"token\":[":String).toList = '{' :: "\"token\":[".toList from by decide]
    rfl⟩

/-- The `oneOf` candidate-list TAIL encoder (the `foldl` body, named for the cons-recursion). -/
private def encodeAuthTailW (as : List AuthW) : String :=
  as.foldl (fun acc x => acc ++ "," ++ encodeAuthW x) ""

/-- **The accumulator pulls OUT of the tail fold** (the standard `foldl`-with-`++` factoring) — proved
at the `List Char` level (`String` is not a `simp`-known free monoid). -/
private theorem foldl_authtail (as : List AuthW) : ∀ (acc : String),
    as.foldl (fun s x => s ++ "," ++ encodeAuthW x) acc
      = acc ++ as.foldl (fun s x => s ++ "," ++ encodeAuthW x) "" := by
  induction as with
  | nil =>
      intro acc
      apply String.toList_inj.mp
      simp
  | cons b bs ih =>
      intro acc
      simp only [List.foldl_cons]
      rw [ih (acc ++ "," ++ encodeAuthW b), ih ("" ++ "," ++ encodeAuthW b)]
      apply String.toList_inj.mp
      simp [String.toList_append, List.append_assoc]

/-- Rebracket a NON-EMPTY candidate TAIL `,AUTH ++ TAIL` into comma-then-auth-then-tail (peelable). -/
theorem encAuthTailW_cons_shape (b : AuthW) (bs : List AuthW) (rest : PState) :
    (encodeAuthTailW (b :: bs)).toList ++ rest
      = ',' :: ((encodeAuthW b).toList ++ ((encodeAuthTailW bs).toList ++ rest)) := by
  conv_lhs => rw [show encodeAuthTailW (b :: bs)
                    = ("" ++ "," ++ encodeAuthW b) ++ encodeAuthTailW bs from by
                  show (b :: bs).foldl (fun s x => s ++ "," ++ encodeAuthW x) "" = _
                  rw [List.foldl_cons]; exact foldl_authtail bs ("" ++ "," ++ encodeAuthW b)]
  simp only [String.toList_append, show ("":String).toList = [] from rfl,
    show (",":String).toList = [','] from rfl, List.nil_append, List.cons_append, List.append_assoc]

/-- Rebracket a NON-EMPTY candidate LIST `[AUTH ++ TAIL ++ ]` into open-`[`-then-body form. -/
theorem encAuthListW_cons_shape (a : AuthW) (as : List AuthW) (rest : PState) :
    (encodeAuthListW (a :: as)).toList ++ rest
      = '[' :: ((encodeAuthW a).toList ++ ((encodeAuthTailW as).toList ++ (']' :: rest))) := by
  simp only [encodeAuthListW]
  rw [show (as.foldl (fun acc x => acc ++ "," ++ encodeAuthW x) "") = encodeAuthTailW as from rfl]
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl,
    show ("]":String).toList = [']'] from rfl]
  simp [List.append_assoc]

/-! ### §6e — the bundled fuel-adequate roundtrip (`parseAuthW`/`parseAuthListW`/loop, by strong
induction on fuel). Mirrors §5's `valueGoal_all`: establish the LOOP clause (depends on the IH at
strictly-smaller fuel), then the LIST clause re-uses it at the same fuel, then the AUTH clause delegates
its 9 flat arms to `parseAuthW_flat` and routes `oneOf` through the LIST clause at decremented fuel. -/

/-- The bundled mutual goal at a given fuel: the auth parser, the list parser, and the loop body all
recover their argument whenever the fuel meets the structural `authSize`/`authListSize` bound. -/
private def AuthGoal (fuel : Nat) : Prop :=
  (∀ (a : AuthW) (rest : PState), WfAuth a → authSize a ≤ fuel →
      parseAuthW fuel ((encodeAuthW a).toList ++ rest) = some (a, rest))
  ∧ (∀ (as : List AuthW) (rest : PState), WfAuthList as → authListSize as ≤ fuel →
      parseAuthListW fuel ((encodeAuthListW as).toList ++ rest) = some (as, rest))
  ∧ (∀ (a : AuthW) (as' : List AuthW) (rest : PState), WfAuth a → WfAuthList as' →
        authListSize (a :: as') ≤ fuel →
      parseAuthLoopW fuel ((encodeAuthW a).toList ++ ((encodeAuthTailW as').toList ++ (']' :: rest)))
        = some (a :: as', rest))

/-- **The combined `Authorization` fuel-adequate roundtrip.** By STRONG induction on fuel; each
recursive sub-call lands at strictly-smaller fuel, so the IH applies. The engine; the public
`parseAuthW_roundtrip` / `parseAuthListW_roundtrip` below unwrap it. -/
private theorem authGoal_all : ∀ fuel, AuthGoal fuel := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel IH =>
    -- LOOP clause first (depends only on IH at strictly-smaller fuel).
    have hloop : ∀ (a : AuthW) (as' : List AuthW) (rest : PState), WfAuth a → WfAuthList as' →
        authListSize (a :: as') ≤ fuel →
        parseAuthLoopW fuel ((encodeAuthW a).toList ++ ((encodeAuthTailW as').toList ++ (']' :: rest)))
          = some (a :: as', rest) := by
      intro a as' rest hwfa hwfas hsz
      have hsz' : 1 + authSize a + authListSize as' ≤ fuel := by
        simpa only [authListSize] using hsz
      obtain ⟨g, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      have hsza : authSize a ≤ g := by omega
      unfold parseAuthLoopW
      rw [(IH g (by omega)).1 a ((encodeAuthTailW as').toList ++ (']' :: rest)) hwfa hsza]
      simp only []
      cases as' with
      | nil =>
          simp only [show (encodeAuthTailW ([] : List AuthW)).toList = [] from rfl, List.nil_append]
          rw [show lit "," (']' :: rest) = none from by
                rw [show (']' :: rest) = ("]":String).toList ++ rest from rfl]
                exact lit_ne_pre "," "]" rest (by decide) (by decide)]
          simp only []
          rw [lit_brack]
      | cons a2 as2 =>
          obtain ⟨hwfa2, hwfas2⟩ : WfAuth a2 ∧ WfAuthList as2 := hwfas
          rw [encAuthTailW_cons_shape a2 as2 (']' :: rest), lit_commaC]
          simp only []
          have hszrec : authListSize (a2 :: as2) ≤ g := by omega
          rw [(IH g (by omega)).2.2 a2 as2 rest hwfa2 hwfas2 hszrec]
    -- LIST clause (re-uses `hloop` at the SAME fuel).
    have hlistW : ∀ (as : List AuthW) (rest : PState), WfAuthList as → authListSize as ≤ fuel →
        parseAuthListW fuel ((encodeAuthListW as).toList ++ rest) = some (as, rest) := by
      intro as rest hwf hsz
      match as with
      | [] =>
          unfold encodeAuthListW parseAuthListW
          rw [show (("[]":String).toList ++ rest) = ("[]":String).toList ++ rest from rfl, lit_append]
      | a :: as' =>
          obtain ⟨hwfa, hwfas⟩ : WfAuth a ∧ WfAuthList as' := hwf
          unfold parseAuthListW
          rw [encAuthListW_cons_shape a as' rest]
          have hempty : lit "[]"
              ('[' :: ((encodeAuthW a).toList ++ ((encodeAuthTailW as').toList ++ (']' :: rest)))) = none := by
            obtain ⟨t, ht⟩ := encodeAuthW_head a
            rw [ht, List.cons_append]; rfl
          rw [hempty]; simp only []
          rw [show ('[' :: ((encodeAuthW a).toList ++ ((encodeAuthTailW as').toList ++ (']' :: rest))))
                = ("[":String).toList ++ ((encodeAuthW a).toList ++ ((encodeAuthTailW as').toList ++ (']' :: rest)))
                from rfl, lit_append]
          simp only []
          exact hloop a as' rest hwfa hwfas hsz
    refine ⟨?_, hlistW, hloop⟩
    -- AUTH clause: flat arms delegate to `parseAuthW_flat`; `oneOf` routes through `hlistW` at `f'`.
    intro a rest hwf hsz
    have ha1 : 1 ≤ authSize a := by cases a <;> simp [authSize]
    obtain ⟨f', rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    by_cases hoo : ∃ cands i, a = .oneOf cands i
    · obtain ⟨cands, i, rfl⟩ := hoo
      have hwfc : WfAuthList cands := hwf
      have hszc : authListSize cands ≤ f' := by simp only [authSize] at hsz; omega
      unfold parseAuthW
      simp only [encodeAuthW, String.toList_append, List.append_assoc]
      lit_fail "{\"sig\":[" "{\"oneof\":["
      lit_fail "{\"pf\":[" "{\"oneof\":["
      lit_fail "{\"bread\":[" "{\"oneof\":["
      lit_fail "{\"bearer\":[" "{\"oneof\":["
      lit_fail "{\"unchecked\":0}" "{\"oneof\":["
      lit_fail "{\"captp\":[" "{\"oneof\":["
      lit_fail "{\"custom\":[" "{\"oneof\":["
      lit_ok
      rw [(IH f' (by omega)).2.1 cands _ hwfc hszc]
      simp only []
      lit_ok; nat_ok; lit_ok; rfl
    · exact parseAuthW_flat a rest f' hwf (fun cs i h => hoo ⟨cs, i, h⟩)

/-! ### §6f — the public FILL-J `Authorization` roundtrip facts (the WHO decoder leaves the TCB). -/

/-- **FILL J production (b): the FULL `Authorization` roundtrip.** Every well-formed `AuthW` — including
the recursive `oneOf` candidate disjunction — round-trips through `encodeAuthW`/`parseAuthW`, given fuel
`≥ authSize a`. This REMOVES the security-critical WHO decoder from the codec TCB. -/
theorem parseAuthW_roundtrip (a : AuthW) (rest : PState) (hwf : WfAuth a) (fuel : Nat)
    (hfuel : authSize a ≤ fuel) :
    parseAuthW fuel ((encodeAuthW a).toList ++ rest) = some (a, rest) :=
  (authGoal_all fuel).1 a rest hwf hfuel

/-- **The candidate-LIST roundtrip** (`parseAuthListW ∘ encodeAuthListW = id`) — the `oneOf` body,
empty or non-empty, given fuel `≥ authListSize as`. -/
theorem parseAuthListW_roundtrip (as : List AuthW) (rest : PState) (hwf : WfAuthList as) (fuel : Nat)
    (hfuel : authListSize as ≤ fuel) :
    parseAuthListW fuel ((encodeAuthListW as).toList ++ rest) = some (as, rest) :=
  (authGoal_all fuel).2.1 as rest hwf hfuel

/-! ### NON-VACUITY witnesses for the WHO decoder (the teeth are satisfiable AND the recursion real). -/

-- A digest-bearing auth round-trips (the `< 2^256` bound is REAL teeth):
example : parseAuthW 5 ((encodeAuthW (.signature 7 9)).toList ++ ['x']) = some (.signature 7 9, ['x']) :=
  parseAuthW_roundtrip (.signature 7 9) ['x'] (show (7:Nat) < 2^256 by norm_num) 5 (by decide)
-- A NESTED `oneOf` round-trips (the recursion is real — `oneOf` calls back into the list/loop/auth):
private def witNestedAuth : AuthW := .oneOf [.oneOf [.unchecked] 0, .breadstuff 3] 1
example : parseAuthW 10 ((encodeAuthW witNestedAuth).toList ++ ['x']) = some (witNestedAuth, ['x']) :=
  parseAuthW_roundtrip witNestedAuth ['x'] (by unfold witNestedAuth WfAuth WfAuthList; trivial) 10
    (by unfold witNestedAuth; decide)

/-! Each charge in `authSize`/`authListSize` is paid by ≥1 encoded byte. Mutual: the `oneOf` body's `+1`
by the `{"oneof":[` prefix, each candidate by its own encoding (recursively), each tail comma by `,`. -/
mutual
theorem authSize_le_encode (a : AuthW) : authSize a ≤ (encodeAuthW a).toList.length := by
  obtain ⟨t, ht⟩ := encodeAuthW_head a
  cases a with
  | oneOf cands i =>
      have hl := authListSize_le_encode cands
      show 1 + authListSize cands ≤ (encodeAuthW (.oneOf cands i)).toList.length
      simp only [encodeAuthW, String.toList_append, List.length_append,
        show ("{\"oneof\":[":String).toList.length = 10 from by decide]
      omega
  | _ =>
      rw [ht]; simp only [authSize, List.length_cons]; omega
theorem authListSize_le_encode (as : List AuthW) : authListSize as ≤ (encodeAuthListW as).toList.length := by
  cases as with
  | nil => simp [authListSize]
  | cons a as' =>
      have ha := authSize_le_encode a
      have ht := authTailSize_le_encode as'
      have hshape := encAuthListW_cons_shape a as' []
      simp only [List.append_nil] at hshape
      show 1 + authSize a + authListSize as' ≤ (encodeAuthListW (a :: as')).toList.length
      rw [hshape]
      simp only [List.length_cons, List.length_append]
      omega
theorem authTailSize_le_encode (as : List AuthW) : authListSize as ≤ (encodeAuthTailW as).toList.length := by
  cases as with
  | nil => simp [authListSize, encodeAuthTailW]
  | cons a as' =>
      have ha := authSize_le_encode a
      have ht := authTailSize_le_encode as'
      have hshape := encAuthTailW_cons_shape a as' []
      simp only [List.append_nil] at hshape
      show 1 + authSize a + authListSize as' ≤ (encodeAuthTailW (a :: as')).toList.length
      rw [hshape]
      simp only [List.length_cons, List.length_append]
      omega
end

end Dregg2.Exec.CodecRoundtrip
