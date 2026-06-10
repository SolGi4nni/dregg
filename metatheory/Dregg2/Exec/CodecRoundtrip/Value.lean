import Dregg2.Exec.CodecRoundtrip.Leaves

/-!
Submodule of `Dregg2.Exec.CodecRoundtrip` — split for parallel compilation.
-/

namespace Dregg2.Exec.CodecRoundtrip

open Dregg2.Exec
open Dregg2.Exec.FFI
open Dregg2.Exec.FFI.Wide

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

/-! ## §2b — the DISPATCH toolkit: a TAG literal FAILS fail-closed on a DIFFERENT tag's encoding.

The recursive productions (`Value`, `Authorization`, `FullActionA`, the action-TREE) are all
fail-closed per-tag DISPATCHES: the parser tries `lit TAG₀`, then on `none` tries `lit TAG₁`, …. To
reach arm `J`'s body we must discharge that `lit TAGₖ` FAILS for every EARLIER arm `k < J` when fed
arm `J`'s encoding (which begins with the concrete string `TAGⱼ`). The workhorse is *failure
monotonicity*: if `lit p` already fails on a CONCRETE finite prefix `q`, it fails on `q ++ rest` for
any tail — so each (k, J) obligation reduces to a `decide` over the two SHORT concrete tag strings.
This is what makes the 10-arm and 45-arm case-splits MECHANICAL rather than O(n²) hand-work. -/

/-- **Failure monotonicity for `litGo` (clash form).** If `litGo p q = none` because of a GENUINE
char CLASH — i.e. `litGo q p = none` ALSO fails (so `q` is NOT a prefix of `p`; the failure is a real
mismatch, not `q` simply running out) — then `litGo p (q ++ rest) = none` for ANY tail. Both
directions failing is exactly "neither is a prefix of the other", the precise condition under which
extra bytes can't rescue the mismatch. (For two concrete distinct tag strings, BOTH `litGo` directions
are `decide`-checkable.) -/
theorem litGo_none_mono : ∀ (p q : List Char) (rest : PState),
    litGo p q = none → litGo q p = none → litGo p (q ++ rest) = none := by
  intro p
  induction p with
  | nil => intro q rest h _; simp [litGo] at h
  | cons c cs ih =>
    intro q rest h hsym
    cases q with
    | nil => simp [litGo] at hsym  -- `litGo [] (c::cs) = some _`, contradicting `hsym`
    | cons d ds =>
      simp only [List.cons_append]
      unfold litGo at h hsym ⊢
      by_cases hcd : (c == d) = true
      · rw [if_pos hcd] at h ⊢
        have hdc : (d == c) = true := by rw [beq_iff_eq] at hcd ⊢; exact hcd.symm
        rw [if_pos hdc] at hsym
        exact ih ds rest h hsym
      · rw [if_neg hcd]

/-- The dispatch obligation in its USABLE form: `tag` (the literal the parser is currently trying) FAILS
on input that BEGINS with the concrete string `b` (a DIFFERENT arm's tag), for any tail. Both `litGo`
directions are concrete; the two hypotheses are closed by `decide`. -/
theorem lit_ne_pre (tag b : String) (rest : PState)
    (h : litGo tag.toList b.toList = none)
    (hsym : litGo b.toList tag.toList = none) :
    lit tag (b.toList ++ rest) = none := by
  unfold lit; exact litGo_none_mono tag.toList b.toList rest h hsym

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

/-! ## §5 — the RECURSIVE `Value` / `FIELDS` production (FILL-J production (a)).

This COMPLETES the scalar leaf into the FULL `parseValueW ∘ encodeValueW = id` on the WHOLE `Value`
algebra — including the `record` arm, which is mutually recursive with the fields list (a fold of
`["name",valueW]` pairs). The fuel is threaded as the structural `valueSize`/`fieldsSize` measure; the
*fuel-adequacy* obligation is that this measure DOMINATES the parse depth, so the fail-closed `fuel=0`
branch is unreachable on well-formed input. We prove the pair by mutual structural induction, mirroring
the `parseValueW`/`parseFieldsLoopW` recursion exactly: lit-the-tag, subparse, close-the-delimiter.

`WfValue` (§1) pins the codec's boundary: digests `< 2^256` and field names escape-free. Both are
satisfied by the demo values (non-vacuous) and load-bearing (the digest wrap / a `"`-bearing name are
genuine counterexamples). -/

/-- The three EARLIER `Value` tags (`int`/`dig`/`sym`) all FAIL on a `{"rec":…` prefix — the dispatch
discharge for the `record` arm. -/
private theorem value_tags_fail_on_rec (rest : PState) :
    lit "{\"int\":" (("{\"rec\":" : String).toList ++ rest) = none
    ∧ lit "{\"dig\":\"" (("{\"rec\":" : String).toList ++ rest) = none
    ∧ lit "{\"sym\":" (("{\"rec\":" : String).toList ++ rest) = none := by
  refine ⟨?_, ?_, ?_⟩
  · exact lit_ne_pre "{\"int\":" "{\"rec\":" rest (by decide) (by decide)
  · exact lit_ne_pre "{\"dig\":\"" "{\"rec\":" rest (by decide) (by decide)
  · exact lit_ne_pre "{\"sym\":" "{\"rec\":" rest (by decide) (by decide)

/-- Rebracket the `int` value's encoding into `lit`-then-`parseInt`-then-`}` shape. -/
private theorem encInt_shape (i : Int) (rest : PState) :
    (encodeValueW (.int i)).toList ++ rest
      = ("{\"int\":":String).toList ++ ((toString i).toList ++ ('}' :: rest)) := by
  unfold encodeValueW
  rw [String.toList_append, String.toList_append, show ("}":String).toList = ['}'] from rfl]
  simp [List.append_assoc]

/-- `lit "}" ('}' :: rest) = some rest` — the closing-brace consume. -/
theorem lit_brace (rest : PState) : lit "}" ('}' :: rest) = some rest := by
  rw [show ('}'::rest) = ("}":String).toList ++ rest from rfl, lit_append]

/-- `lit "]" (']' :: rest) = some rest` — the closing-bracket consume. -/
theorem lit_brack (rest : PState) : lit "]" (']' :: rest) = some rest := by
  rw [show (']'::rest) = ("]":String).toList ++ rest from rfl, lit_append]

/-- `lit "," (',' :: rest) = some rest`. -/
theorem lit_commaC (rest : PState) : lit "," (',' :: rest) = some rest := by
  rw [show (','::rest) = (",":String).toList ++ rest from rfl, lit_append]

/-- Rebracket a NON-EMPTY fields array's encoding `[FIELD ++ TAIL ++ ]` into open-`[`-then-body form. -/
private theorem encFieldsW_cons_shape (n : FieldName) (v : Value) (gs : List (FieldName × Value)) (rest : PState) :
    (encodeFieldsW ((n, v) :: gs)).toList ++ rest
      = '[' :: ((("[\"" ++ jsonEscape n ++ "\"," ++ encodeValueW v ++ "]"):String).toList
          ++ ((encodeFieldsTailW gs).toList ++ (']' :: rest))) := by
  unfold encodeFieldsW
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl,
    show ("]":String).toList = [']'] from rfl]
  simp [List.append_assoc]

/-- Rebracket a NON-EMPTY fields TAIL `,FIELD ++ TAIL` into comma-then-field-then-tail form. -/
private theorem encFieldsTailW_cons_shape (n2 : FieldName) (v2 : Value) (gs2 : List (FieldName × Value)) (rest : PState) :
    (encodeFieldsTailW ((n2, v2) :: gs2)).toList ++ rest
      = ',' :: ((("[\"" ++ jsonEscape n2 ++ "\"," ++ encodeValueW v2 ++ "]"):String).toList
          ++ ((encodeFieldsTailW gs2).toList ++ rest)) := by
  rw [show encodeFieldsTailW ((n2, v2) :: gs2)
        = ",[\"" ++ jsonEscape n2 ++ "\"," ++ encodeValueW v2 ++ "]" ++ encodeFieldsTailW gs2 from rfl]
  simp only [String.toList_append, show (",[\"":String).toList = ',' :: ("[\"":String).toList from rfl,
    show ("]":String).toList = [']'] from rfl]
  simp [List.append_assoc]

/-! ### The combined `Value`/`FIELDS` roundtrip, proved by induction on FUEL with the value case-split
inside. Fuel is bounded BELOW by the structural `valueSize`/`fieldsSize` (the *fuel-adequacy*); the
`≥` form gives fuel-MONOTONICITY for free (any sufficient fuel works), which is exactly what the loop's
`parseValueW fuel` sub-call needs. -/

/-- The mutual roundtrip statement at a given fuel: BOTH the value parser AND the fields loop recover
their argument whenever the fuel meets the structural bound. The fields clause is stated over the LOOP
BODY (post opening-`[`): the first field, the comma-prefixed tail of the rest, then the closing `]`. -/
private def ValueGoal (fuel : Nat) : Prop :=
  (∀ (v : Value) (rest : PState), WfValue v → valueSize v ≤ fuel →
      parseValueW fuel ((encodeValueW v).toList ++ rest) = some (v, rest))
  ∧ (∀ (fs : List (FieldName × Value)) (rest : PState), WfFields fs → fieldsSize fs ≤ fuel →
      parseFieldsW fuel ((encodeFieldsW fs).toList ++ rest) = some (fs, rest))
  ∧ (∀ (fs : List (FieldName × Value)) (rest : PState), WfFields fs → fs ≠ [] → fieldsSize fs ≤ fuel →
      parseFieldsLoopW fuel
        ((("[\"" ++ jsonEscape (fs.headD default).1 ++ "\"," ++ encodeValueW (fs.headD default).2 ++ "]"):String).toList
          ++ ((encodeFieldsTailW fs.tail).toList ++ (']' :: rest))) = some (fs, rest))

/-- **The combined `Value`/`FIELDS` fuel-adequate roundtrip.** By STRONG induction on fuel: each
recursive sub-call lands at strictly-smaller fuel, so the IH applies. This is the engine; the public
`parseValueW_roundtrip` / `parseFieldsW_roundtrip` below unwrap it. -/
private theorem valueGoal_all : ∀ fuel, ValueGoal fuel := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel IH =>
    -- FIRST establish the LOOP clause (depends only on IH at strictly-smaller fuel), then the
    -- fields-W and value clauses can re-use it at the SAME fuel.
    have hloop : ∀ (fs : List (FieldName × Value)) (rest : PState), WfFields fs → fs ≠ [] → fieldsSize fs ≤ fuel →
        parseFieldsLoopW fuel
          ((("[\"" ++ jsonEscape (fs.headD default).1 ++ "\"," ++ encodeValueW (fs.headD default).2 ++ "]"):String).toList
            ++ ((encodeFieldsTailW fs.tail).toList ++ (']' :: rest))) = some (fs, rest) := by
      intro fs rest hwf hne hsz
      match fs, hwf, hne, hsz with
      | (n, v) :: gs, hwf, _, hsz =>
        obtain ⟨hn, hv, hgs⟩ := hwf
        have hszsplit : fieldsSize ((n,v)::gs) = 1 + valueSize v + fieldsSize gs := by simp only [fieldsSize]
        have hfpos : 0 < fuel := by rw [hszsplit] at hsz; omega
        obtain ⟨fuel', rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
        have hsz' : 1 + valueSize v + fieldsSize gs ≤ fuel' + 1 := by rw [hszsplit] at hsz; exact hsz
        have hvfuel : valueSize v ≤ fuel' := by omega
        have hgsfuel : fieldsSize gs ≤ fuel' := by omega
        simp only [List.headD, List.tail]
        unfold parseFieldsLoopW
        rw [show (("[\"" ++ jsonEscape n ++ "\"," ++ encodeValueW v ++ "]"):String).toList
                  ++ ((encodeFieldsTailW gs).toList ++ (']' :: rest))
              = ("[":String).toList ++ (('"' :: (jsonEscape n).toList) ++ ('"' :: (','
                  :: ((encodeValueW v).toList ++ (']' :: ((encodeFieldsTailW gs).toList ++ (']' :: rest)))))) ) by
              simp only [String.toList_append, show ("[":String).toList = ['['] from rfl,
                show ("\"":String).toList = ['"'] from rfl, show (",":String).toList = [','] from rfl,
                show ("]":String).toList = [']'] from rfl]
              simp [List.append_assoc]]
        rw [lit_append]; simp only []
        rw [parseStr_clean n (',' :: ((encodeValueW v).toList ++ (']' :: ((encodeFieldsTailW gs).toList ++ (']' :: rest))))) hn]
        simp only []
        rw [lit_commaC]; simp only []
        have hval := (IH fuel' (by omega)).1 v (']' :: ((encodeFieldsTailW gs).toList ++ (']' :: rest))) hv hvfuel
        rw [hval]; simp only []
        rw [lit_brack]; simp only []
        match gs, hgs, hgsfuel with
        | [], _, _ =>
            show (match lit "," ((encodeFieldsTailW ([]:List (FieldName × Value))).toList ++ (']' :: rest)) with
                  | some r5 => match parseFieldsLoopW fuel' r5 with
                               | some (rest', r6) => some ((n, v) :: rest', r6)
                               | none => none
                  | none => match lit "]" ((encodeFieldsTailW ([]:List (FieldName × Value))).toList ++ (']' :: rest)) with
                            | some r6 => some ([(n, v)], r6)
                            | none => none) = _
            simp only [encodeFieldsTailW, show ("":String).toList = [] from rfl, List.nil_append]
            rw [show lit "," (']' :: rest) = none from by
                  rw [show (']'::rest) = ("]":String).toList ++ rest from rfl]
                  exact lit_ne_pre "," "]" rest (by decide) (by decide)]
            simp only []
            rw [lit_brack]
        | (n2, v2) :: gs2, hgs', hgsfuel' =>
            obtain ⟨hn2, hv2, hgs2⟩ := hgs'
            rw [encFieldsTailW_cons_shape n2 v2 gs2 (']' :: rest)]
            rw [show (',' :: ((("[\"" ++ jsonEscape n2 ++ "\"," ++ encodeValueW v2 ++ "]"):String).toList
                      ++ ((encodeFieldsTailW gs2).toList ++ (']' :: rest))))
                  = (",":String).toList ++ ((("[\"" ++ jsonEscape n2 ++ "\"," ++ encodeValueW v2 ++ "]"):String).toList
                      ++ ((encodeFieldsTailW gs2).toList ++ (']' :: rest))) from rfl]
            rw [lit_append]; simp only []
            -- the loop RECURSES at the DECREMENTED fuel `fuel'` (see `parseFieldsLoopW`); the IH at
            -- `fuel' < fuel'+1` supplies the loop clause of `ValueGoal fuel'`:
            have hrec := (IH fuel' (by omega)).2.2 ((n2,v2)::gs2) rest ⟨hn2, hv2, hgs2⟩ (by simp) hgsfuel'
            simp only [List.headD, List.tail] at hrec
            rw [hrec]
    -- now the FIELDS-W clause (`[]` vs `[FIELD...]`), reducing to `hloop`:
    have hfieldsW : ∀ (fs : List (FieldName × Value)) (rest : PState), WfFields fs → fieldsSize fs ≤ fuel →
        parseFieldsW fuel ((encodeFieldsW fs).toList ++ rest) = some (fs, rest) := by
      intro fs rest hwf hsz
      match fs with
      | [] =>
          unfold encodeFieldsW parseFieldsW
          rw [show (("[]":String).toList ++ rest) = ("[]":String).toList ++ rest from rfl, lit_append]
      | (n, v) :: gs =>
          unfold parseFieldsW
          rw [encFieldsW_cons_shape n v gs rest]
          -- the body is `'[' :: '[' :: '"' :: …` (the field's own open bracket follows): so `lit "[]"`
          -- mismatches at the 2nd char (`[` ≠ `]`) — fail-closed via the `[[`-prefix dispatch:
          have hbody : ('[' :: ((("[\"" ++ jsonEscape n ++ "\"," ++ encodeValueW v ++ "]"):String).toList
                ++ ((encodeFieldsTailW gs).toList ++ (']' :: rest))))
              = ("[[":String).toList ++ (('"' :: (jsonEscape n).toList ++ '"' :: ',' :: (encodeValueW v).toList)
                  ++ (']' :: ((encodeFieldsTailW gs).toList ++ (']' :: rest)))) := by
            simp only [String.toList_append, show ("[[":String).toList = ['[','['] from rfl,
              show ("[\"":String).toList = ['[','"'] from rfl, show ("\",":String).toList = ['"',','] from rfl,
              show ("]":String).toList = [']'] from rfl, show ("\"":String).toList = ['"'] from rfl,
              show (",":String).toList = [','] from rfl]
            simp [List.append_assoc]
          rw [hbody]
          have hlitempty := lit_ne_pre "[]" "[["
              (('"' :: (jsonEscape n).toList ++ '"' :: ',' :: (encodeValueW v).toList)
                  ++ (']' :: ((encodeFieldsTailW gs).toList ++ (']' :: rest))))
              (by decide) (by decide)
          rw [hlitempty]; simp only []
          rw [← hbody]
          rw [show ('[' :: ((("[\"" ++ jsonEscape n ++ "\"," ++ encodeValueW v ++ "]"):String).toList
                    ++ ((encodeFieldsTailW gs).toList ++ (']' :: rest))))
                = ("[":String).toList ++ ((("[\"" ++ jsonEscape n ++ "\"," ++ encodeValueW v ++ "]"):String).toList
                    ++ ((encodeFieldsTailW gs).toList ++ (']' :: rest))) from rfl]
          rw [lit_append]; simp only []
          have := hloop ((n,v)::gs) rest hwf (by simp) hsz
          simp only [List.headD, List.tail] at this
          exact this
    refine ⟨?_, hfieldsW, hloop⟩
    -- the VALUE clause, reducing the record arm to `hfieldsW`:
    intro v rest hwf hsz
    have hfpos : 0 < fuel := lt_of_lt_of_le (by cases v <;> simp [valueSize] <;> omega) hsz
    obtain ⟨fuel', rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    match v with
      | .int i =>
          unfold parseValueW
          rw [encInt_shape i rest, lit_append]; simp only []
          rw [parseInt_toString i _ (nd_brace rest)]; simp only []
          rw [lit_brace rest]; simp
      | .sym s =>
          exact parseValueW_scalar fuel' (.sym s) rest hwf (by intro fs h; cases h)
      | .dig d =>
          exact parseValueW_scalar fuel' (.dig d) rest hwf (by intro fs h; cases h)
      | .record fs =>
          have hwff : WfFields fs := hwf
          have hfssz : fieldsSize fs ≤ fuel' := by simp only [valueSize] at hsz; omega
          unfold encodeValueW parseValueW
          obtain ⟨h1, h2, h3⟩ := value_tags_fail_on_rec ((encodeFieldsW fs).toList ++ ('}' :: rest))
          rw [show (("{\"rec\":" ++ encodeFieldsW fs ++ "}"):String).toList ++ rest
                = ("{\"rec\":":String).toList ++ ((encodeFieldsW fs).toList ++ ('}' :: rest)) by
                rw [String.toList_append, String.toList_append,
                    show ("}":String).toList = ['}'] from rfl]; simp [List.append_assoc]]
          rw [h1]; simp only []
          rw [h2]; simp only []
          rw [h3]; simp only []
          rw [lit_append]; simp only []
          -- the parser calls `parseFieldsW fuel'` (the DECREMENTED fuel); use the IH's fields clause:
          rw [(IH fuel' (by omega)).2.1 fs ('}' :: rest) hwff hfssz]; simp only []
          rw [lit_brace rest]; rfl

/-- **FILL J production (a): the FULL `Value`/`record` roundtrip.** Every reachable `Value` —
including the recursive `record`/fields fold — round-trips through `encodeValueW`/`parseValueW`, given
enough fuel (`valueSize v`, the structural depth bound). The `record` arm was the missing piece beyond
the scalar leaf; this REMOVES the whole `Value` algebra from the codec TCB. -/
theorem parseValueW_roundtrip (v : Value) (rest : PState) (hwf : WfValue v) (fuel : Nat)
    (hfuel : valueSize v ≤ fuel) :
    parseValueW fuel ((encodeValueW v).toList ++ rest) = some (v, rest) :=
  (valueGoal_all fuel).1 v rest hwf hfuel

/-- **The `FIELDS` array roundtrip** (`parseFieldsW ∘ encodeFieldsW = id`) — the record body, empty or
non-empty, given fuel ≥ `fieldsSize fs`. -/
theorem parseFieldsW_roundtrip (fs : List (FieldName × Value)) (rest : PState) (hwf : WfFields fs)
    (fuel : Nat) (hfuel : fieldsSize fs ≤ fuel) :
    parseFieldsW fuel ((encodeFieldsW fs).toList ++ rest) = some (fs, rest) :=
  (valueGoal_all fuel).2.1 fs rest hwf hfuel

/-! ### NON-VACUITY witnesses for the record recursion (the teeth are satisfiable AND non-trivial). -/

-- A NESTED record (record-inside-record, with a digest field) round-trips — the recursion is real
-- (the `record` arm calls back into `parseFieldsW`, which calls back into `parseValueW`):
private def witNestedRec : Value :=
  .record [("a", .int 7), ("b", .record [("h", .dig 255), ("k", .sym 3)])]

private theorem witNestedRec_wf : WfValue witNestedRec := by
  show WfFields [("a", .int 7), ("b", .record [("h", .dig 255), ("k", .sym 3)])]
  refine ⟨?_, trivial, ?_, ?_, trivial⟩
  · intro c h; fin_cases h <;> decide   -- name "a" escape-free
  · intro c h; fin_cases h <;> decide   -- name "b" escape-free
  · -- WfValue (.record [("h", .dig 255), ("k", .sym 3)])
    show WfFields [("h", .dig 255), ("k", .sym 3)]
    refine ⟨?_, show (255:Nat) < 2^256 by norm_num, ?_, trivial, trivial⟩
    · intro c h; fin_cases h <;> decide  -- name "h"
    · intro c h; fin_cases h <;> decide  -- name "k"

example : parseValueW 10 ((encodeValueW witNestedRec).toList ++ ['x']) = some (witNestedRec, ['x']) :=
  parseValueW_roundtrip witNestedRec ['x'] witNestedRec_wf 10 (by unfold witNestedRec; decide)


end Dregg2.Exec.CodecRoundtrip
