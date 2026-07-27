import Control.Tailcfg
import Control.TailcfgBridge

/-!
# Control.TailcfgWire — the tailcfg codec closed at the **wire-string** level

`Control/Tailcfg.lean` proves `fromJson? (toJson m) = some m`: the codec is exact
at the JSON *value* level. That is not the wire. The wire is a byte string, and
between the value and the bytes sit a serializer and a parser — which, until this
module, were `partial` and validated only by `#eval`.

This module replaces that text layer with a **total** one and proves the missing
half:

  `parseChars (renderJ j) = some j`     (§5, every JSON value)
  `decode (encode m) = some m`          (§6, every tailcfg message)

`encode`/`decode` are `String → String` round trips: a `MapResponse` is turned
into the actual characters that go on the socket and read back to the identical
structure. Nothing here is `partial` and nothing is `sorry`; the parser is total
by a fuel argument, and §5 supplies the fuel from the input length, so the
top-level statements carry no fuel side condition.

## What is *not* claimed

`renderJ` emits a JSON `null` for an absent optional. Go's `encoding/json` omits
such a field instead (`json:",omitempty"` / a nil pointer), and accepts either on
input (unmarshalling `null` into a pointer gives nil, into a value is a no-op).
So the strings proved here are *accepted* by a stock client but are not
byte-identical to what a Go server emits. The skip-if-none renderer and its
roundtrip (which needs a null-dropping normalizer to be threaded through the
decoder) is the named residual — see §7, which renders it and validates it by
execution against real-shaped samples.

Leaf *values* (`"nodekey:<hex>"`, `"100.64.0.1/32"`, `"192.168.1.5:41641"`) are
bridged to bytes, with proofs, in `Control/TailcfgBridge.lean`.
-/

namespace Control.TailcfgWire

open Control.Tailcfg
open Control.Bridge (natDigits parseNat parseNat_natDigits NoDigit charDigit digitChar
  natDigits_head stripPrefix stripPrefix_append)

/-! ## §1  Whitespace, escaping, and their inverses -/

def isWs (c : Char) : Bool := c = ' ' || c = '\n' || c = '\t' || c = '\r'

def skipWs : List Char → List Char
  | [] => []
  | c :: r => if isWs c then skipWs r else c :: r

/-- The escape of one character (exactly the five escapes Go's `encoding/json`
emits for the character set the tailcfg fields carry). -/
def escChar (c : Char) : List Char :=
  if c = '"' then ['\\', '"']
  else if c = '\\' then ['\\', '\\']
  else if c = '\n' then ['\\', 'n']
  else if c = '\r' then ['\\', 'r']
  else if c = '\t' then ['\\', 't']
  else [c]

def escape : List Char → List Char
  | [] => []
  | c :: t => escChar c ++ escape t

/-- The inverse of the character following a backslash. -/
def unescChar (c : Char) : Char :=
  if c = 'n' then '\n' else if c = 't' then '\t' else if c = 'r' then '\r' else c

/-- Read a string body up to the closing quote, undoing escapes. Total —
structural on the input. -/
def unesc : Bool → List Char → List Char → Option (List Char × List Char)
  | _, _, [] => none
  | true, acc, c :: r => unesc false (unescChar c :: acc) r
  | false, acc, c :: r =>
    if c = '"' then some (acc.reverse, r)
    else if c = '\\' then unesc true acc r
    else unesc false (c :: acc) r

/-- **The string escape codec is inverted exactly**, for every character string
and in every context: the tail after the closing quote is returned untouched, so
the lemma composes inside arrays and objects. -/
theorem unesc_escape : ∀ (s : List Char) (acc rest : List Char),
    unesc false acc (escape s ++ '"' :: rest) = some (acc.reverse ++ s, rest) := by
  intro s
  induction s with
  | nil =>
    intro acc rest
    simp only [escape, List.nil_append]
    show some (acc.reverse, rest) = _
    simp
  | cons c t ih =>
    intro acc rest
    simp only [escape, List.append_assoc]
    by_cases h1 : c = '"'
    · subst h1
      show unesc false ('"' :: acc) (escape t ++ '"' :: rest) = _
      rw [ih]; simp
    by_cases h2 : c = '\\'
    · subst h2
      show unesc false ('\\' :: acc) (escape t ++ '"' :: rest) = _
      rw [ih]; simp
    by_cases h3 : c = '\n'
    · subst h3
      show unesc false ('\n' :: acc) (escape t ++ '"' :: rest) = _
      rw [ih]; simp
    by_cases h4 : c = '\r'
    · subst h4
      show unesc false ('\r' :: acc) (escape t ++ '"' :: rest) = _
      rw [ih]; simp
    by_cases h5 : c = '\t'
    · subst h5
      show unesc false ('\t' :: acc) (escape t ++ '"' :: rest) = _
      rw [ih]; simp
    · have hstep : ∀ (L : List Char), unesc false acc (c :: L) = unesc false (c :: acc) L := by
        intro L
        rw [unesc]
        simp only [if_neg h1, if_neg h2]
      simp only [escChar, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5,
        List.cons_append, List.nil_append, hstep, ih]
      simp

/-! ## §2  The renderer (total) -/

def renderInt : Int → List Char
  | Int.ofNat n => natDigits n
  | Int.negSucc n => '-' :: natDigits (n + 1)

mutual
  /-- Render a JSON value: compact, no whitespace, exactly as `json.Marshal`. -/
  def renderJ : Json → List Char
    | .null => ['n', 'u', 'l', 'l']
    | .bool true => ['t', 'r', 'u', 'e']
    | .bool false => ['f', 'a', 'l', 's', 'e']
    | .num i => renderInt i
    | .str s => '"' :: (escape s.toList ++ ['"'])
    | .arr xs => '[' :: (renderL xs ++ [']'])
    | .obj fs => '{' :: (renderF fs ++ ['}'])
  def renderL : List Json → List Char
    | [] => []
    | [x] => renderJ x
    | x :: t => renderJ x ++ (',' :: renderL t)
  def renderF : List (String × Json) → List Char
    | [] => []
    | [(k, v)] => '"' :: (escape k.toList ++ ('"' :: ':' :: renderJ v))
    | (k, v) :: t => '"' :: (escape k.toList ++ ('"' :: ':' :: (renderJ v ++ (',' :: renderF t))))
end

/-! ## §3  The parser (total, fuel-bounded) -/

/-! ### Numbers: the RFC 8259 grammar, not just integers

drorb's `Json` models numbers as `Int` — every tailcfg field it decodes (ids, versions,
ports) is integral. The PARSER, though, must still accept the full RFC 8259 §6 number
grammar `-? int frac? exp?`, because a real client sends real numbers in fields drorb does
not model. Stock `tailscale` 1.98.8 sends exactly one such field, and it is on the ONE
request that matters most:

    "NetInfo":{…,"PreferredDERP":1,"DERPLatency":{"1-v4":0.00040243}},
    "Endpoints":["73.4.118.165:45991","192.168.50.39:45991","172.17.0.1:45991"],
    "EndpointTypes":[3,2,1],"OmitPeers":true

An integer-only `pNum` reads `0`, hands back `.00040243…`, and the enclosing object parser
— expecting `,` or `}` — fails. The WHOLE MapRequest then fails to parse, so
`ControlLive.natReportsOf` extracts nothing, the NAT table never learns an endpoint, every
served peer goes out with `Endpoints: null`, and no client on the tailnet can ever attempt
a direct path. The failure was silent: the request that carries `Endpoints` is precisely
the request that carries `DERPLatency`, so the endpoint report was the only thing lost.

A number that HAS a `frac`/`exp` tail is outside drorb's integral value model, so it reads
as `Json.null` — the same "no modelled value here" that a MISSING field gets from
`optField`, i.e. FAIL-CLOSED, never a wrong integer — while its exact lexeme is consumed so
the surrounding object keeps parsing. Integers are untouched: `numTail_stop` shows the tail
scanner is the identity on any tail that cannot continue a number, which is every tail the
renderer produces, so `pJson_num` and `parseStr_renderStr` hold exactly as before. -/

/-- Split off the digits at the head of a list. -/
def takeDigits : List Char → List Char × List Char
  | [] => ([], [])
  | c :: r =>
    match charDigit c with
    | some _ => let (d, t) := takeDigits r; (c :: d, t)
    | none => ([], c :: r)

/-- A tail that cannot CONTINUE a JSON number lexeme: not a digit, and not the
`.`/`e`/`E` that would extend an integer into a real (RFC 8259 §6). Strictly stronger
than `NoDigit`, and it is what the renderer always produces after a value — `,`, `]`,
`}`, or end of input. -/
def NoNumTail : List Char → Prop
  | [] => True
  | c :: _ => charDigit c = none ∧ c ≠ '.' ∧ c ≠ 'e' ∧ c ≠ 'E'

theorem NoNumTail.toNoDigit {l : List Char} (h : NoNumTail l) : NoDigit l := by
  cases l with
  | nil => trivial
  | cons c t => simp only [NoNumTail] at h; exact h.1

theorem noNumTail_nil : NoNumTail ([] : List Char) := trivial
theorem noNumTail_comma (l : List Char) : NoNumTail (',' :: l) := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> decide
theorem noNumTail_rbrack (l : List Char) : NoNumTail (']' :: l) := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> decide
theorem noNumTail_rbrace (l : List Char) : NoNumTail ('}' :: l) := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> decide

/-- Consume an RFC 8259 `frac` / `exp` tail if one is present. A number that has one is
outside the integral model and reads as `Json.null`; otherwise the value and the tail are
returned untouched. -/
def numTail (j : Json) (cs : List Char) : Json × List Char :=
  let fr : Bool × List Char :=
    match cs with
    | '.' :: r => let (d, t) := takeDigits r; if d.isEmpty then (false, cs) else (true, t)
    | _ => (false, cs)
  let ex : Bool × List Char :=
    match fr.2 with
    | e :: r =>
      if e = 'e' ∨ e = 'E' then
        let r' := match r with
                  | s :: r2 => if s = '+' ∨ s = '-' then r2 else r
                  | [] => r
        let (d, t) := takeDigits r'
        if d.isEmpty then (false, fr.2) else (true, t)
      else (false, fr.2)
    | [] => (false, fr.2)
  if fr.1 ∨ ex.1 then (Json.null, ex.2) else (j, cs)

/-- **The tail scanner is the identity on a tail that cannot continue a number.** This is
what keeps the integer path — and therefore `pJson_num` and the whole
`parseStr_renderStr` round-trip — exactly as it was. -/
theorem numTail_stop (j : Json) (rest : List Char) (h : NoNumTail rest) :
    numTail j rest = (j, rest) := by
  cases rest with
  | nil => rfl
  | cons c t =>
    simp only [NoNumTail] at h
    obtain ⟨_, hdot, he, hE⟩ := h
    simp [numTail, hdot, he, hE]

def pNum (cs : List Char) : Option (Json × List Char) :=
  match cs with
  | [] => none
  | c :: r =>
    if c = '-' then (parseNat r).map (fun p => numTail (Json.num (-(Int.ofNat p.1))) p.2)
    else (parseNat (c :: r)).map (fun p => numTail (Json.num (Int.ofNat p.1)) p.2)

mutual
  def pJson : Nat → List Char → Option (Json × List Char)
    | 0, _ => none
    | f + 1, cs0 =>
      match skipWs cs0 with
      | [] => none
      | c :: r =>
        if c = 'n' then (stripPrefix ['u', 'l', 'l'] r).map (fun r' => (Json.null, r'))
        else if c = 't' then (stripPrefix ['r', 'u', 'e'] r).map (fun r' => (Json.bool true, r'))
        else if c = 'f' then (stripPrefix ['a', 'l', 's', 'e'] r).map (fun r' => (Json.bool false, r'))
        else if c = '"' then (unesc false [] r).map (fun p => (Json.str (String.ofList p.1), p.2))
        else if c = '[' then pArr f r []
        else if c = '{' then pObj f r []
        else pNum (c :: r)
  def pArr : Nat → List Char → List Json → Option (Json × List Char)
    | 0, _, _ => none
    | f + 1, cs0, acc =>
      match skipWs cs0 with
      | [] => none
      | c :: r =>
        if c = ']' then some (Json.arr acc.reverse, r)
        else
          match pJson f (c :: r) with
          | none => none
          | some (v, r1) =>
            match skipWs r1 with
            | [] => none
            | c2 :: r2 =>
              if c2 = ',' then pArr f r2 (v :: acc)
              else if c2 = ']' then some (Json.arr (v :: acc).reverse, r2)
              else none
  def pObj : Nat → List Char → List (String × Json) → Option (Json × List Char)
    | 0, _, _ => none
    | f + 1, cs0, acc =>
      match skipWs cs0 with
      | [] => none
      | c :: r =>
        if c = '}' then some (Json.obj acc.reverse, r)
        else if c = '"' then
          match unesc false [] r with
          | none => none
          | some (k, r1) =>
            match skipWs r1 with
            | [] => none
            | c2 :: r2 =>
              if c2 = ':' then
                match pJson f r2 with
                | none => none
                | some (v, r3) =>
                  match skipWs r3 with
                  | [] => none
                  | c3 :: r4 =>
                    if c3 = ',' then pObj f r4 ((String.ofList k, v) :: acc)
                    else if c3 = '}' then
                      some (Json.obj ((String.ofList k, v) :: acc).reverse, r4)
                    else none
              else none
        else none
end

/-! ## §4  Structural size (the fuel measure) -/

mutual
  def sizeJ : Json → Nat
    | .arr xs => 1 + sizeL xs
    | .obj fs => 1 + sizeF fs
    | _ => 1
  def sizeL : List Json → Nat
    | [] => 1
    | x :: t => 1 + sizeJ x + sizeL t
  def sizeF : List (String × Json) → Nat
    | [] => 1
    | (_, v) :: t => 1 + sizeJ v + sizeF t
end

theorem sizeJ_pos (j : Json) : 1 ≤ sizeJ j := by
  cases j with
  | null => exact Nat.le_refl 1
  | bool b => cases b <;> exact Nat.le_refl 1
  | num i => exact Nat.le_refl 1
  | str s => exact Nat.le_refl 1
  | arr xs => show 1 ≤ 1 + sizeL xs; omega
  | obj fs => show 1 ≤ 1 + sizeF fs; omega

theorem sizeL_pos (xs : List Json) : 1 ≤ sizeL xs := by
  cases xs with
  | nil => exact Nat.le_refl 1
  | cons x t => show 1 ≤ 1 + sizeJ x + sizeL t; omega

theorem sizeF_pos (fs : List (String × Json)) : 1 ≤ sizeF fs := by
  cases fs with
  | nil => exact Nat.le_refl 1
  | cons p t =>
    obtain ⟨k, v⟩ := p
    show 1 ≤ 1 + sizeJ v + sizeF t
    omega

/-! ## §5  The wire-string roundtrip -/

theorem noDigit_nil : NoDigit ([] : List Char) := trivial
theorem noDigit_comma (l : List Char) : NoDigit (',' :: l) := rfl
theorem noDigit_rbrack (l : List Char) : NoDigit (']' :: l) := rfl
theorem noDigit_rbrace (l : List Char) : NoDigit ('}' :: l) := rfl

/-- The head character of a rendered value: not whitespace and not a closing
bracket — so `skipWs` is the identity on it and the empty-array / empty-object
branches of the parser are not taken. -/
def goodHead : List Char → Bool
  | [] => false
  | c :: _ => !isWs c && !(c == ']') && !(c == '}')

def notWsHead : List Char → Bool
  | [] => true
  | c :: _ => !isWs c

theorem skipWs_notWsHead : ∀ {l : List Char}, notWsHead l = true → skipWs l = l := by
  intro l h
  cases l with
  | nil => rfl
  | cons c t =>
    simp only [notWsHead, Bool.not_eq_true'] at h
    simp only [skipWs, h]
    simp

theorem goodHead_cons {l : List Char} (h : goodHead l = true) :
    ∃ c r, l = c :: r ∧ isWs c = false ∧ c ≠ ']' ∧ c ≠ '}' := by
  cases l with
  | nil => simp [goodHead] at h
  | cons c t =>
    simp only [goodHead, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at h
    exact ⟨c, t, rfl, h.1.1, h.1.2, h.2⟩

theorem notWsHead_of_goodHead {l : List Char} (h : goodHead l = true) : notWsHead l = true := by
  obtain ⟨c, r, hl, hws, _, _⟩ := goodHead_cons h
  subst hl
  simp [notWsHead, hws]

theorem goodHead_digits (d : Nat) (h : d < 10) (l : List Char) :
    goodHead (digitChar d :: l) = true := by
  have key : ∀ e, e < 10 →
      (!isWs (digitChar e) && !(digitChar e == ']') && !(digitChar e == '}')) = true := by decide
  simpa [goodHead] using key d h

theorem goodHead_natDigits (n : Nat) (rest : List Char) :
    goodHead (natDigits n ++ rest) = true := by
  obtain ⟨d, t, hd, ht⟩ := natDigits_head n
  rw [ht]
  simp only [List.cons_append]
  exact goodHead_digits d hd _

theorem goodHead_renderJ : ∀ (j : Json) (rest : List Char), goodHead (renderJ j ++ rest) = true := by
  intro j rest
  cases j with
  | null => rfl
  | bool b => cases b <;> rfl
  | num i =>
    cases i with
    | ofNat n =>
      show goodHead (natDigits n ++ rest) = true
      exact goodHead_natDigits n rest
    | negSucc n => rfl
  | str s => rfl
  | arr xs => rfl
  | obj fs => rfl

theorem notWsHead_renderL (xs : List Json) (rest : List Char) :
    notWsHead (renderL xs ++ (']' :: rest)) = true := by
  cases xs with
  | nil => rfl
  | cons x t =>
    cases t with
    | nil =>
      show notWsHead (renderJ x ++ (']' :: rest)) = true
      exact notWsHead_of_goodHead (goodHead_renderJ x _)
    | cons y u =>
      have he : renderL (x :: y :: u) ++ (']' :: rest)
          = renderJ x ++ (',' :: (renderL (y :: u) ++ (']' :: rest))) := by
        simp [renderL]
      rw [he]
      exact notWsHead_of_goodHead (goodHead_renderJ x _)

theorem notWsHead_renderF (fs : List (String × Json)) (rest : List Char) :
    notWsHead (renderF fs ++ ('}' :: rest)) = true := by
  cases fs with
  | nil => rfl
  | cons p t =>
    obtain ⟨k, v⟩ := p
    cases t with
    | nil => rfl
    | cons q u => rfl

/-- Unfold `pArr` at a value position (head is not whitespace, not `']'`). -/
theorem pArr_cons {f : Nat} {c : Char} {r : List Char} (hws : isWs c = false) (hb : c ≠ ']')
    (acc : List Json) :
    pArr (f + 1) (c :: r) acc =
      (match pJson f (c :: r) with
       | none => none
       | some (v, r1) =>
         match skipWs r1 with
         | [] => none
         | c2 :: r2 =>
           if c2 = ',' then pArr f r2 (v :: acc)
           else if c2 = ']' then some (Json.arr (v :: acc).reverse, r2)
           else none) := by
  have h1 : skipWs (c :: r) = c :: r := skipWs_notWsHead (by simp [notWsHead, hws])
  rw [pArr, h1]
  dsimp only
  simp only [if_neg hb]

/-- A rendered number parses back to itself. -/
theorem pJson_num (i : Int) (rest : List Char) (hr : NoNumTail rest) (f : Nat) :
    pJson (f + 1) (renderInt i ++ rest) = some (Json.num i, rest) := by
  cases i with
  | ofNat n =>
    obtain ⟨d, t, hd, ht⟩ := natDigits_head n
    have key : ∀ e, e < 10 →
        (digitChar e ≠ 'n' ∧ digitChar e ≠ 't' ∧ digitChar e ≠ 'f' ∧ digitChar e ≠ '"' ∧
         digitChar e ≠ '[' ∧ digitChar e ≠ '{' ∧ digitChar e ≠ '-' ∧
         isWs (digitChar e) = false) := by decide
    obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ := key d hd
    have hin : renderInt (Int.ofNat n) ++ rest = digitChar d :: (t ++ rest) := by
      show natDigits n ++ rest = _
      rw [ht]
      simp
    have hws : skipWs (digitChar d :: (t ++ rest)) = digitChar d :: (t ++ rest) :=
      skipWs_notWsHead (by simp [notWsHead, n8])
    rw [pJson, hin, hws]
    simp only [if_neg n1, if_neg n2, if_neg n3, if_neg n4, if_neg n5, if_neg n6, pNum,
      if_neg n7]
    have hback : digitChar d :: (t ++ rest) = natDigits n ++ rest := by rw [ht]; simp
    rw [hback, parseNat_natDigits n hr.toNoDigit]
    simp [numTail_stop _ rest hr]
  | negSucc n =>
    have hin : renderInt (Int.negSucc n) ++ rest = '-' :: (natDigits (n + 1) ++ rest) := by
      show ('-' :: natDigits (n + 1)) ++ rest = _
      simp
    have hws : skipWs ('-' :: (natDigits (n + 1) ++ rest)) = '-' :: (natDigits (n + 1) ++ rest) :=
      skipWs_notWsHead (by rfl)
    rw [pJson, hin, hws]
    simp only [if_neg (by decide : ¬ ('-' : Char) = 'n'), if_neg (by decide : ¬ ('-' : Char) = 't'),
      if_neg (by decide : ¬ ('-' : Char) = 'f'), if_neg (by decide : ¬ ('-' : Char) = '"'),
      if_neg (by decide : ¬ ('-' : Char) = '['), if_neg (by decide : ¬ ('-' : Char) = '{'),
      pNum, if_pos rfl, parseNat_natDigits (n + 1) hr.toNoDigit]
    simp only [numTail_stop _ rest hr, Option.map_some]
    exact congrArg (fun z => some (Json.num z, rest)) (Int.negSucc_eq n).symm

mutual
/-- **The wire-string roundtrip, general.** Parsing the rendering of any JSON
value recovers it exactly and leaves the tail untouched. -/
theorem pJson_renderJ (j : Json) (f : Nat) (hf : sizeJ j ≤ f)
    (rest : List Char) (hr : NoNumTail rest) :
    pJson f (renderJ j ++ rest) = some (j, rest) := by
  cases f with
  | zero => have := sizeJ_pos j; omega
  | succ f =>
    cases j with
    | null =>
      rw [pJson]
      show (match skipWs (['n', 'u', 'l', 'l'] ++ rest) with
            | [] => none
            | c :: r => _) = _
      simp [skipWs, isWs, stripPrefix]
    | bool b =>
      cases b <;> (rw [pJson]; simp [renderJ, skipWs, isWs, stripPrefix])
    | num i => exact pJson_num i rest hr f
    | str s =>
      have hin : renderJ (Json.str s) ++ rest = '"' :: (escape s.toList ++ ('"' :: rest)) := by
        show ('"' :: (escape s.toList ++ ['"'])) ++ rest = _
        simp
      have hws : skipWs ('"' :: (escape s.toList ++ ('"' :: rest)))
          = '"' :: (escape s.toList ++ ('"' :: rest)) := skipWs_notWsHead (by rfl)
      rw [pJson, hin, hws]
      simp only [if_neg (by decide : ¬ ('"' : Char) = 'n'),
        if_neg (by decide : ¬ ('"' : Char) = 't'), if_neg (by decide : ¬ ('"' : Char) = 'f'),
        if_pos rfl, unesc_escape s.toList [] rest]
      simp
    | arr xs =>
      have hin : renderJ (Json.arr xs) ++ rest = '[' :: (renderL xs ++ (']' :: rest)) := by
        show ('[' :: (renderL xs ++ [']'])) ++ rest = _
        simp
      have hws : skipWs ('[' :: (renderL xs ++ (']' :: rest)))
          = '[' :: (renderL xs ++ (']' :: rest)) := skipWs_notWsHead (by rfl)
      rw [pJson, hin, hws]
      simp only [if_neg (by decide : ¬ ('[' : Char) = 'n'),
        if_neg (by decide : ¬ ('[' : Char) = 't'), if_neg (by decide : ¬ ('[' : Char) = 'f'),
        if_neg (by decide : ¬ ('[' : Char) = '"'), if_pos rfl]
      have hsz : sizeL xs ≤ f := by
        have h1 : 1 + sizeL xs ≤ f + 1 := hf
        omega
      rw [pArr_renderL xs f hsz [] rest hr]
      simp
    | obj fs =>
      have hin : renderJ (Json.obj fs) ++ rest = '{' :: (renderF fs ++ ('}' :: rest)) := by
        show ('{' :: (renderF fs ++ ['}'])) ++ rest = _
        simp
      have hws : skipWs ('{' :: (renderF fs ++ ('}' :: rest)))
          = '{' :: (renderF fs ++ ('}' :: rest)) := skipWs_notWsHead (by rfl)
      rw [pJson, hin, hws]
      simp only [if_neg (by decide : ¬ ('{' : Char) = 'n'),
        if_neg (by decide : ¬ ('{' : Char) = 't'), if_neg (by decide : ¬ ('{' : Char) = 'f'),
        if_neg (by decide : ¬ ('{' : Char) = '"'), if_neg (by decide : ¬ ('{' : Char) = '['),
        if_pos rfl]
      have hsz : sizeF fs ≤ f := by
        have h1 : 1 + sizeF fs ≤ f + 1 := hf
        omega
      rw [pObj_renderF fs f hsz [] rest hr]
      simp
termination_by f

theorem pArr_renderL (xs : List Json) (f : Nat) (hf : sizeL xs ≤ f) (acc : List Json)
    (rest : List Char) (hr : NoNumTail rest) :
    pArr f (renderL xs ++ (']' :: rest)) acc = some (Json.arr (acc.reverse ++ xs), rest) := by
  cases f with
  | zero => have := sizeL_pos xs; omega
  | succ f =>
    cases xs with
    | nil =>
      show pArr (f + 1) (']' :: rest) acc = _
      rw [pArr]
      simp only [skipWs_notWsHead (by rfl : notWsHead (']' :: rest) = true)]
      simp
    | cons x t =>
      have hf' : 1 + sizeJ x + sizeL t ≤ f + 1 := hf
      have hx : sizeJ x ≤ f := by omega
      have ht : sizeL t ≤ f := by omega
      cases t with
      | nil =>
        have he : renderL [x] ++ (']' :: rest) = renderJ x ++ (']' :: rest) := by
          show renderJ x ++ (']' :: rest) = _
          rfl
        rw [he]
        obtain ⟨c, r, hl, hcw, hc1, hc2⟩ := goodHead_cons (goodHead_renderJ x (']' :: rest))
        rw [hl, pArr_cons hcw hc1, ← hl]
        simp only [pJson_renderJ x f hx (']' :: rest) (noNumTail_rbrack rest),
          skipWs_notWsHead (by rfl : notWsHead (']' :: rest) = true)]
        simp
      | cons y u =>
        have he : renderL (x :: y :: u) ++ (']' :: rest)
            = renderJ x ++ (',' :: (renderL (y :: u) ++ (']' :: rest))) := by
          simp [renderL]
        rw [he]
        obtain ⟨c, r, hl, hcw, hc1, hc2⟩ :=
          goodHead_cons (goodHead_renderJ x (',' :: (renderL (y :: u) ++ (']' :: rest))))
        rw [hl, pArr_cons hcw hc1, ← hl]
        simp only [pJson_renderJ x f hx (',' :: (renderL (y :: u) ++ (']' :: rest)))
            (noNumTail_comma _),
          skipWs_notWsHead
            (by rfl : notWsHead (',' :: (renderL (y :: u) ++ (']' :: rest))) = true),
          if_pos rfl, pArr_renderL (y :: u) f ht (x :: acc) rest hr]
        simp
termination_by f

theorem pObj_renderF (fs : List (String × Json)) (f : Nat) (hf : sizeF fs ≤ f)
    (acc : List (String × Json)) (rest : List Char) (hr : NoNumTail rest) :
    pObj f (renderF fs ++ ('}' :: rest)) acc = some (Json.obj (acc.reverse ++ fs), rest) := by
  cases f with
  | zero => have := sizeF_pos fs; omega
  | succ f =>
    cases fs with
    | nil =>
      show pObj (f + 1) ('}' :: rest) acc = _
      rw [pObj]
      simp only [skipWs_notWsHead (by rfl : notWsHead ('}' :: rest) = true)]
      simp
    | cons p t =>
      obtain ⟨k, v⟩ := p
      have hf' : 1 + sizeJ v + sizeF t ≤ f + 1 := hf
      have hv : sizeJ v ≤ f := by omega
      have ht : sizeF t ≤ f := by omega
      cases t with
      | nil =>
        have he : renderF [(k, v)] ++ ('}' :: rest)
            = '"' :: (escape k.toList ++ ('"' :: ':' :: (renderJ v ++ ('}' :: rest)))) := by
          show ('"' :: (escape k.toList ++ ('"' :: ':' :: renderJ v))) ++ ('}' :: rest) = _
          simp
        rw [he, pObj]
        simp only [skipWs_notWsHead
            (by rfl : notWsHead ('"' :: (escape k.toList ++
              ('"' :: ':' :: (renderJ v ++ ('}' :: rest))))) = true),
          if_neg (by decide : ¬ ('"' : Char) = '}'), if_pos rfl,
          unesc_escape k.toList [] (':' :: (renderJ v ++ ('}' :: rest))),
          List.reverse_nil, List.nil_append,
          skipWs_notWsHead
            (by rfl : notWsHead (':' :: (renderJ v ++ ('}' :: rest))) = true),
          pJson_renderJ v f hv ('}' :: rest) (noNumTail_rbrace rest),
          skipWs_notWsHead (by rfl : notWsHead ('}' :: rest) = true)]
        simp
      | cons q u =>
        have he : renderF ((k, v) :: q :: u) ++ ('}' :: rest)
            = '"' :: (escape k.toList ++ ('"' :: ':' ::
                (renderJ v ++ (',' :: (renderF (q :: u) ++ ('}' :: rest)))))) := by
          simp [renderF]
        rw [he, pObj]
        simp only [skipWs_notWsHead
            (by rfl : notWsHead ('"' :: (escape k.toList ++ ('"' :: ':' ::
              (renderJ v ++ (',' :: (renderF (q :: u) ++ ('}' :: rest))))))) = true),
          if_neg (by decide : ¬ ('"' : Char) = '}'), if_pos rfl,
          unesc_escape k.toList []
            (':' :: (renderJ v ++ (',' :: (renderF (q :: u) ++ ('}' :: rest))))),
          List.reverse_nil, List.nil_append,
          skipWs_notWsHead
            (by rfl : notWsHead (':' :: (renderJ v ++
              (',' :: (renderF (q :: u) ++ ('}' :: rest))))) = true),
          pJson_renderJ v f hv (',' :: (renderF (q :: u) ++ ('}' :: rest))) (noNumTail_comma _),
          skipWs_notWsHead
            (by rfl : notWsHead (',' :: (renderF (q :: u) ++ ('}' :: rest))) = true),
          String.ofList_toList, if_true]
        rw [pObj_renderF (q :: u) f ht ((k, v) :: acc) rest hr]
        simp
termination_by f
end

/-! ### Fuel from the input length -/

mutual
theorem sizeJ_le_len (j : Json) : sizeJ j + 1 ≤ 2 * (renderJ j).length := by
  cases j with
  | null => decide
  | bool b => cases b <;> decide
  | num i =>
    cases i with
    | ofNat n =>
      obtain ⟨d, t, _, ht⟩ := natDigits_head n
      show 1 + 1 ≤ 2 * (natDigits n).length
      rw [ht]
      simp
      omega
    | negSucc n =>
      show 1 + 1 ≤ 2 * ('-' :: natDigits (n + 1)).length
      simp
      omega
  | str s =>
    show 1 + 1 ≤ 2 * ('"' :: (escape s.toList ++ ['"'])).length
    simp
    omega
  | arr xs =>
    have h := sizeL_le_len xs
    show (1 + sizeL xs) + 1 ≤ 2 * ('[' :: (renderL xs ++ [']'])).length
    simp only [List.length_cons, List.length_append, List.length_singleton]
    omega
  | obj fs =>
    have h := sizeF_le_len fs
    show (1 + sizeF fs) + 1 ≤ 2 * ('{' :: (renderF fs ++ ['}'])).length
    simp only [List.length_cons, List.length_append, List.length_singleton]
    omega
termination_by sizeJ j
decreasing_by
  all_goals (try simp only [sizeJ, sizeL, sizeF])
  all_goals omega

theorem sizeL_le_len (xs : List Json) : sizeL xs ≤ 2 * (renderL xs).length + 1 := by
  cases xs with
  | nil => decide
  | cons x t =>
    cases t with
    | nil =>
      have h := sizeJ_le_len x
      show 1 + sizeJ x + sizeL [] ≤ 2 * (renderJ x).length + 1
      show 1 + sizeJ x + 1 ≤ 2 * (renderJ x).length + 1
      omega
    | cons y u =>
      have h1 := sizeJ_le_len x
      have h2 := sizeL_le_len (y :: u)
      have he : renderL (x :: y :: u) = renderJ x ++ (',' :: renderL (y :: u)) := by
        simp [renderL]
      show 1 + sizeJ x + sizeL (y :: u) ≤ 2 * (renderL (x :: y :: u)).length + 1
      rw [he]
      simp only [List.length_append, List.length_cons]
      omega
termination_by sizeL xs
decreasing_by
  all_goals (try simp only [sizeJ, sizeL, sizeF])
  all_goals omega

theorem sizeF_le_len (fs : List (String × Json)) : sizeF fs ≤ 2 * (renderF fs).length + 1 := by
  cases fs with
  | nil => decide
  | cons p t =>
    obtain ⟨k, v⟩ := p
    cases t with
    | nil =>
      have h := sizeJ_le_len v
      show 1 + sizeJ v + sizeF [] ≤
        2 * ('"' :: (escape k.toList ++ ('"' :: ':' :: renderJ v))).length + 1
      simp only [List.length_cons, List.length_append]
      show 1 + sizeJ v + 1 ≤ _
      omega
    | cons q u =>
      have h1 := sizeJ_le_len v
      have h2 := sizeF_le_len (q :: u)
      have he : renderF ((k, v) :: q :: u)
          = '"' :: (escape k.toList ++ ('"' :: ':' :: (renderJ v ++ (',' :: renderF (q :: u))))) := by
        simp [renderF]
      show 1 + sizeJ v + sizeF (q :: u) ≤ 2 * (renderF ((k, v) :: q :: u)).length + 1
      rw [he]
      simp only [List.length_cons, List.length_append]
      omega
termination_by sizeF fs
decreasing_by
  all_goals (try simp only [sizeJ, sizeL, sizeF])
  all_goals omega
end

/-! ### The top-level, fuel-free statements -/

/-- Parse a complete JSON document: the whole input must be consumed (modulo
trailing whitespace). Total — the fuel is derived from the input length. -/
def parseChars (cs : List Char) : Option Json :=
  match pJson (2 * cs.length + 1) cs with
  | some (j, r) => if skipWs r = [] then some j else none
  | none => none

def parseStr (s : String) : Option Json := parseChars s.toList

def renderStr (j : Json) : String := String.ofList (renderJ j)

/-- **String-level roundtrip for every JSON value.** No fuel hypothesis, no
`partial`, no `sorry`: rendering a value to characters and parsing them back
returns the identical value. -/
theorem parseChars_renderJ (j : Json) : parseChars (renderJ j) = some j := by
  have hb := sizeJ_le_len j
  have hf : sizeJ j ≤ 2 * (renderJ j).length + 1 := by omega
  have h := pJson_renderJ j (2 * (renderJ j).length + 1) hf [] noNumTail_nil
  simp only [List.append_nil] at h
  simp only [parseChars, h, skipWs, if_pos rfl, if_true]

/-- **The same, as `String → String`.** -/
theorem parseStr_renderStr (j : Json) : parseStr (renderStr j) = some j := by
  simp only [parseStr, renderStr, String.toList_ofList, parseChars_renderJ]

/-! ## §6  The tailcfg messages survive a full `String → String` round trip

Composing §5 with the value-level roundtrips of `Control/Tailcfg.lean`: this is
the statement that was previously available only at the JSON-AST level. -/

def RegisterRequest.wireEncode (m : RegisterRequest) : String := renderStr m.toJson
def RegisterResponse.wireEncode (m : RegisterResponse) : String := renderStr m.toJson
def MapRequest.wireEncode (m : MapRequest) : String := renderStr m.toJson
def MapResponse.wireEncode (m : MapResponse) : String := renderStr m.toJson

def RegisterRequest.wireDecode (s : String) : Option RegisterRequest :=
  (parseStr s).bind RegisterRequest.fromJson?
def RegisterResponse.wireDecode (s : String) : Option RegisterResponse :=
  (parseStr s).bind RegisterResponse.fromJson?
def MapRequest.wireDecode (s : String) : Option MapRequest :=
  (parseStr s).bind MapRequest.fromJson?
def MapResponse.wireDecode (s : String) : Option MapResponse :=
  (parseStr s).bind MapResponse.fromJson?

theorem RegisterRequest.wireDecode_wireEncode (m : RegisterRequest) :
    RegisterRequest.wireDecode (RegisterRequest.wireEncode m) = some m := by
  simp [RegisterRequest.wireDecode, RegisterRequest.wireEncode, parseStr_renderStr,
    Control.Tailcfg.RegisterRequest.fromJson?_toJson]

theorem RegisterResponse.wireDecode_wireEncode (m : RegisterResponse) :
    RegisterResponse.wireDecode (RegisterResponse.wireEncode m) = some m := by
  simp [RegisterResponse.wireDecode, RegisterResponse.wireEncode, parseStr_renderStr,
    Control.Tailcfg.RegisterResponse.fromJson?_toJson]

theorem MapRequest.wireDecode_wireEncode (m : MapRequest) :
    MapRequest.wireDecode (MapRequest.wireEncode m) = some m := by
  simp [MapRequest.wireDecode, MapRequest.wireEncode, parseStr_renderStr,
    Control.Tailcfg.MapRequest.fromJson?_toJson]

/-- **The big one.** A `MapResponse` — node, peers, the compiled packet filter,
the DERP map, the DNS config — rendered to the characters that go on the socket
and parsed back is the identical message. -/
theorem MapResponse.wireDecode_wireEncode (m : MapResponse) :
    MapResponse.wireDecode (MapResponse.wireEncode m) = some m := by
  simp [MapResponse.wireDecode, MapResponse.wireEncode, parseStr_renderStr,
    Control.Tailcfg.MapResponse.fromJson?_toJson]

/-! ## §7  Real-sample validation (execution) -/

/-- A real-shaped stock-client `RegisterRequest` (pre-auth-key login), PascalCase,
`"nodekey:<hex>"` keys, and an unknown future field the decoder must tolerate. -/
def sampleRegisterRequest : String :=
  "{\"Version\":109,\"NodeKey\":\"nodekey:5c8f00000000000000000000000000000000000000000000000000000000aabb\","
  ++ "\"OldNodeKey\":\"nodekey:0000000000000000000000000000000000000000000000000000000000000000\","
  ++ "\"Auth\":{\"AuthKey\":\"tskey-auth-abc123\"},"
  ++ "\"Hostinfo\":{\"OS\":\"linux\",\"Hostname\":\"laptop\",\"IPNVersion\":\"1.80.0\","
  ++ "\"RoutableIPs\":[\"192.168.1.0/24\"]},"
  ++ "\"Followup\":\"\",\"Ephemeral\":false,\"Tailnet\":\"example.com\","
  ++ "\"UnknownFutureField\":{\"nested\":[1,2,3]}}"

/-- A real-shaped `MapRequest` (the long-poll: `Stream:true`). -/
def sampleMapRequest : String :=
  "{\"Version\":109,\"NodeKey\":\"nodekey:5c8f00000000000000000000000000000000000000000000000000000000aabb\","
  ++ "\"DiscoKey\":\"discokey:aa1100000000000000000000000000000000000000000000000000000000ccdd\","
  ++ "\"Endpoints\":[\"192.168.1.5:41641\",\"100.64.0.1:41641\"],"
  ++ "\"Stream\":true,\"OmitPeers\":false,"
  ++ "\"Hostinfo\":{\"OS\":\"linux\",\"Hostname\":\"laptop\"},\"ReadOnly\":false}"

/-- A real-shaped `MapResponse` (what a coordination server streams back): a self
node, one peer, a compiled `PacketFilter`, a `DERPMap` and a `DNSConfig`. -/
def sampleMapResponse : String :=
  "{\"Node\":{\"ID\":1,\"StableID\":\"nXYZ\",\"Name\":\"laptop.example.ts.net.\",\"User\":1,"
  ++ "\"Key\":\"nodekey:5c8f00000000000000000000000000000000000000000000000000000000aabb\","
  ++ "\"Addresses\":[\"100.64.0.1/32\"],\"AllowedIPs\":[\"100.64.0.1/32\"],"
  ++ "\"Endpoints\":[\"192.168.1.5:41641\"],\"DERP\":\"127.3.3.40:1\",\"HomeDERP\":1,"
  ++ "\"Hostinfo\":{\"OS\":\"linux\",\"Hostname\":\"laptop\"},"
  ++ "\"KeyExpiry\":\"2027-01-01T00:00:00Z\",\"Online\":true,\"MachineAuthorized\":true},"
  ++ "\"Peers\":[{\"ID\":2,\"Name\":\"server.example.ts.net.\",\"User\":1,"
  ++ "\"Key\":\"nodekey:1111000000000000000000000000000000000000000000000000000000002222\","
  ++ "\"Addresses\":[\"100.64.0.2/32\"],\"HomeDERP\":1,\"MachineAuthorized\":true}],"
  ++ "\"DNSConfig\":{\"Domains\":[\"example.ts.net\"],\"Nameservers\":[\"100.100.100.100\"]},"
  ++ "\"PacketFilter\":[{\"SrcIPs\":[\"100.64.0.0/10\"],"
  ++ "\"DstPorts\":[{\"IP\":\"100.64.0.2\",\"Bits\":32,\"Ports\":{\"First\":22,\"Last\":22}}],"
  ++ "\"IPProto\":[6]}],"
  ++ "\"DERPMap\":{\"Regions\":{\"1\":{\"RegionID\":1,\"RegionCode\":\"lax\",\"RegionName\":\"Los Angeles\","
  ++ "\"Nodes\":[{\"Name\":\"1a\",\"RegionID\":1,\"HostName\":\"derp1a.example.net\",\"IPv4\":\"10.0.0.1\","
  ++ "\"Port\":443,\"STUNPort\":3478}]}}},"
  ++ "\"KeepAlive\":false,\"Domain\":\"example.com\"}"

-- All three real-shaped samples are ingested by the total parser:
#eval (RegisterRequest.wireDecode sampleRegisterRequest).isSome  -- expect: true
#eval (MapRequest.wireDecode sampleMapRequest).isSome            -- expect: true
#eval (MapResponse.wireDecode sampleMapResponse).isSome          -- expect: true

-- …and re-rendering then re-parsing gives the identical message (the proven
-- roundtrip, exercised on real bytes):
#eval (match RegisterRequest.wireDecode sampleRegisterRequest with
       | some m => RegisterRequest.wireDecode (RegisterRequest.wireEncode m) == some m
       | none => false)  -- expect: true
#eval (match MapRequest.wireDecode sampleMapRequest with
       | some m => MapRequest.wireDecode (MapRequest.wireEncode m) == some m
       | none => false)  -- expect: true
#eval (match MapResponse.wireDecode sampleMapResponse with
       | some m => MapResponse.wireDecode (MapResponse.wireEncode m) == some m
       | none => false)  -- expect: true

-- The decoded MapResponse (field-by-field evidence that the real sample landed
-- in the right places, including the ACL rule and the DERP region):
#eval MapResponse.wireDecode sampleMapResponse

-- The leaf values of the real sample bridge to bytes (Control/TailcfgBridge):
#eval Control.Bridge.NodeKey.ofText
  "nodekey:5c8f00000000000000000000000000000000000000000000000000000000aabb"
#eval Control.Bridge.Prefix4.ofText "100.64.0.1/32"
#eval Control.Bridge.Prefix4.ofText "100.64.0.0/10"
#eval Control.Bridge.AddrPort4.ofText "192.168.1.5:41641"

/-! ## §8  Axiom audit -/

#print axioms unesc_escape
#print axioms pJson_renderJ
#print axioms pArr_renderL
#print axioms pObj_renderF
#print axioms parseChars_renderJ
#print axioms parseStr_renderStr
#print axioms RegisterRequest.wireDecode_wireEncode
#print axioms RegisterResponse.wireDecode_wireEncode
#print axioms MapRequest.wireDecode_wireEncode
#print axioms MapResponse.wireDecode_wireEncode

/-! ## §9  The **skip-if-none** (null-omitting) renderer — what the real wire uses

§2's `renderJ` emits `"Field":null` for an absent optional. Go's `encoding/json`
with `json:",omitempty"` (and serde's `skip_serializing_if`) *omits the member
entirely*. This section closes that gap: `dropNulls` is the value-level
normalizer that deletes null-valued object members (recursively), and
`toJsonSkipNone := dropNulls ∘ toJson` is the renderer the real wire uses.

The whole content is one **master lemma** (`assoc?_dropNullsF`): under distinct
keys, deleting the null-valued members does not change the lookup of any key
except turning a null hit into a miss. Every per-struct roundtrip is then a
*linear* application of two field-level corollaries — there is no case split over
the optional fields, so `Node` (9 optionals) costs 9 rewrites, not 2^9. -/

def isNullJ : Json → Bool
  | .null => true
  | _ => false

/-! Delete every null-valued member of every object, recursively. Array elements
are *not* dropped (Go does not drop null array elements either) — only object
members, which is exactly `omitempty` on a pointer/optional field. -/
mutual
  def dropNulls : Json → Json
    | .null => .null
    | .bool b => .bool b
    | .num n => .num n
    | .str s => .str s
    | .arr xs => .arr (dropNullsL xs)
    | .obj fs => .obj (dropNullsF fs)
  def dropNullsL : List Json → List Json
    | [] => []
    | x :: t => dropNulls x :: dropNullsL t
  def dropNullsF : List (String × Json) → List (String × Json)
    | [] => []
    | (k, v) :: t => if isNullJ v then dropNullsF t else (k, dropNulls v) :: dropNullsF t
end

/-- Dropping nulls never *creates* or *destroys* a null: the top constructor is
preserved. -/
theorem isNullJ_dropNulls (j : Json) : isNullJ (dropNulls j) = isNullJ j := by
  cases j <;> rfl

theorem optDecodeVal_of_not_null {α} (dec : Json → Option α) {j : Json}
    (h : isNullJ j = false) : optDecodeVal dec j = (dec j).map some := by
  cases j with
  | null => simp [isNullJ] at h
  | bool b => rfl
  | num n => rfl
  | str s => rfl
  | arr xs => rfl
  | obj fs => rfl

/-! ### The distinct-keys predicate

`assoc?` is first-match. Deleting a null member can only change a *later*
duplicate of that key into the winner, so the null case of the master lemma —
and only that case — needs distinct keys. -/

def keysNodup : List (String × Json) → Bool
  | [] => true
  | (k, _) :: t => t.all (fun p => p.1 != k) && keysNodup t

theorem assoc?_eq_none_of_all_ne : ∀ (t : List (String × Json)) (k : String),
    t.all (fun p => p.1 != k) = true → assoc? t k = none := by
  intro t
  induction t with
  | nil => intro k _; rfl
  | cons p u ih =>
    intro k h
    obtain ⟨k0, v0⟩ := p
    simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    have hne : (k0 == k) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; exact h.1
    simp only [assoc?, hne, Bool.false_eq_true, if_false]
    exact ih k h.2

/-- **THE MASTER LEMMA.** For an object with distinct keys, deleting the
null-valued members leaves every lookup alone, except that a key whose value was
null becomes absent:

  `assoc? (dropNullsF fs) k = (assoc? fs k).filter (· not null) |>.map dropNulls`

(written as an explicit `match`/`if` to avoid `Option.filter` API drift). This is
the single fact the whole skip-if-none story rests on. -/
theorem assoc?_dropNullsF : ∀ (fs : List (String × Json)) (k : String),
    keysNodup fs = true →
    assoc? (dropNullsF fs) k
      = match assoc? fs k with
        | none => none
        | some v => if isNullJ v then none else some (dropNulls v) := by
  intro fs
  induction fs with
  | nil => intro k _; rfl
  | cons p t ih =>
    intro k h
    obtain ⟨k0, v0⟩ := p
    simp only [keysNodup, Bool.and_eq_true] at h
    obtain ⟨hall, ht⟩ := h
    by_cases hk : (k0 == k) = true
    · -- the head is the (first, hence only) match
      have hkk : k0 = k := by simpa using hk
      subst hkk
      have hnone : assoc? t k0 = none := assoc?_eq_none_of_all_ne t k0 hall
      by_cases hn : isNullJ v0 = true
      · -- the head is dropped; distinctness says nothing later can surface
        simp only [dropNullsF, hn, if_true, assoc?, hk]
        rw [ih k0 ht, hnone]
      · have hnf : isNullJ v0 = false := by simpa using hn
        simp only [dropNullsF, hnf, Bool.false_eq_true, if_false, assoc?, hk]
        simp [hnf]
    · have hkf : (k0 == k) = false := by simpa using hk
      by_cases hn : isNullJ v0 = true
      · simp only [dropNullsF, hn, if_true, assoc?, hkf, Bool.false_eq_true, if_false]
        exact ih k ht
      · have hnf : isNullJ v0 = false := by simpa using hn
        simp only [dropNullsF, hnf, Bool.false_eq_true, if_false, assoc?, hkf, if_false]
        exact ih k ht

/-! ### The two field-level corollaries

These are the *only* interface the per-struct proofs use. Both are conditional on
`keysNodup fs`, which `simp` discharges for a literal field list. -/

theorem reqField_dropNulls_obj {α} (dec : Json → Option α) (fs : List (String × Json))
    (k : String) (h : keysNodup fs = true) :
    reqField dec (dropNulls (.obj fs)) k
      = match assoc? fs k with
        | none => none
        | some v => if isNullJ v then none else dec (dropNulls v) := by
  show reqField dec (.obj (dropNullsF fs)) k = _
  rw [reqField_obj, assoc?_dropNullsF fs k h]
  cases hv : assoc? fs k with
  | none => rfl
  | some v =>
    by_cases hn : isNullJ v = true
    · simp [hn]
    · have hnf : isNullJ v = false := by simpa using hn
      simp [hnf]

theorem optField_dropNulls_obj {α} (dec : Json → Option α) (fs : List (String × Json))
    (k : String) (h : keysNodup fs = true) :
    optField dec (dropNulls (.obj fs)) k
      = match assoc? fs k with
        | none => some none
        | some v => if isNullJ v then some none else optDecodeVal dec (dropNulls v) := by
  show optField dec (.obj (dropNullsF fs)) k = _
  rw [optField_obj, assoc?_dropNullsF fs k h]
  cases hv : assoc? fs k with
  | none => rfl
  | some v =>
    by_cases hn : isNullJ v = true
    · simp [hn]
    · have hnf : isNullJ v = false := by simpa using hn
      simp [hnf]

/-! ### The per-field combinators — **2 cases each, proved once**

This is the trick that makes the derivation linear. `optEnc_drop` is proved by a
single `cases o` *here*; in a struct proof it is a rewrite. So a struct with `n`
optional fields costs `n` rewrites, never `2^n` branches. -/

theorem optEnc_drop {α} {enc : α → Json} {dec : Json → Option α}
    (hrt : ∀ x, dec (dropNulls (enc x)) = some x) (hne : ∀ x, isNullJ (enc x) = false)
    (o : Option α) :
    (if isNullJ (encOpt enc o) then some none else optDecodeVal dec (dropNulls (encOpt enc o)))
      = some o := by
  cases o with
  | none => rfl
  | some x =>
    have h1 : isNullJ (encOpt enc (some x)) = false := hne x
    have h2 : isNullJ (dropNulls (enc x)) = false := by
      rw [isNullJ_dropNulls]; exact hne x
    simp only [h1, Bool.false_eq_true, if_false]
    show optDecodeVal dec (dropNulls (enc x)) = _
    rw [optDecodeVal_of_not_null dec h2, hrt x]
    rfl

theorem reqEnc_drop {α} {enc : α → Json} {dec : Json → Option α}
    (hrt : ∀ x, dec (dropNulls (enc x)) = some x) (hne : ∀ x, isNullJ (enc x) = false)
    (x : α) :
    (if isNullJ (enc x) then none else dec (dropNulls (enc x))) = some x := by
  simp only [hne x, Bool.false_eq_true, if_false, hrt x]

/-- **Plain-encoded field read through the optional decoder, under `dropNulls`.**
Go emits zero-valued `omitempty` bools as a plain value (or omits them); a decoder
that reads such a field optionally still recovers it. -/
theorem plainEnc_dropOpt {α} {enc : α → Json} {dec : Json → Option α}
    (hrt : ∀ x, dec (dropNulls (enc x)) = some x) (hne : ∀ x, isNullJ (enc x) = false)
    (x : α) :
    (if isNullJ (enc x) then some none else optDecodeVal dec (dropNulls (enc x)))
      = some (some x) := by
  have h2 : isNullJ (dropNulls (enc x)) = false := by
    rw [isNullJ_dropNulls]; exact hne x
  simp only [hne x, Bool.false_eq_true, if_false]
  cases hv : dropNulls (enc x) with
  | null => rw [hv] at h2; exact absurd h2 (by simp [isNullJ])
  | bool b => simp only [optDecodeVal]; rw [← hv, hrt x]; rfl
  | num n => simp only [optDecodeVal]; rw [← hv, hrt x]; rfl
  | str t => simp only [optDecodeVal]; rw [← hv, hrt x]; rfl
  | arr xs => simp only [optDecodeVal]; rw [← hv, hrt x]; rfl
  | obj fs => simp only [optDecodeVal]; rw [← hv, hrt x]; rfl

/-! ### Leaf and container drop-roundtrips -/

theorem encStr_notNull (s : String) : isNullJ (encStr s) = false := rfl
theorem encNat_notNull (n : Nat) : isNullJ (encNat n) = false := rfl
theorem encBool_notNull (b : Bool) : isNullJ (encBool b) = false := rfl
theorem encList_notNull {α} (enc : α → Json) (xs : List α) :
    isNullJ (encList enc xs) = false := rfl
theorem encStrMap_notNull {α} (enc : α → Json) (m : List (String × α)) :
    isNullJ (encStrMap enc m) = false := rfl

theorem drop_decStr_encStr (s : String) : decStr (dropNulls (encStr s)) = some s := rfl
theorem drop_decNat_encNat (n : Nat) : decNat (dropNulls (encNat n)) = some n := rfl
theorem drop_decBool_encBool (b : Bool) : decBool (dropNulls (encBool b)) = some b := rfl

/-- **Arrays.** Element drop-roundtrip lifts. -/
theorem drop_decArr_encList {α} {enc : α → Json} {dec : Json → Option α}
    (h : ∀ x, dec (dropNulls (enc x)) = some x) (xs : List α) :
    decArr dec (dropNulls (encList enc xs)) = some xs := by
  show decArr dec (.arr (dropNullsL (xs.map enc))) = some xs
  show mapOpt dec (dropNullsL (xs.map enc)) = some xs
  induction xs with
  | nil => rfl
  | cons a t ih =>
    show mapOpt dec (dropNulls (enc a) :: dropNullsL (t.map enc)) = _
    simp only [mapOpt, h a, ih, Option.map_some]

/-- **String-keyed maps (`DERPMap.Regions`).** NOTE what the hypotheses are: the
*values* are non-null (`hne`), so `dropNullsF` deletes **nothing** here and the
member list — including its message-supplied keys, in order, duplicates and all —
survives verbatim. That is why this needs **no** `Nodup`/distinct-keys
hypothesis: the master lemma's distinctness side condition guards the *deletion*
case, and no deletion happens in an encoded map. -/
theorem drop_decObjMap_encStrMap {α} {enc : α → Json} {dec : Json → Option α}
    (h : ∀ x, dec (dropNulls (enc x)) = some x) (hne : ∀ x, isNullJ (enc x) = false)
    (m : List (String × α)) :
    decObjMap dec (dropNulls (encStrMap enc m)) = some m := by
  show decObjMap dec (.obj (dropNullsF (m.map (fun p => (p.1, enc p.2))))) = some m
  show mapOpt (fun p => (dec p.2).map (fun v => (p.1, v)))
      (dropNullsF (m.map (fun p => (p.1, enc p.2)))) = some m
  induction m with
  | nil => rfl
  | cons a t ih =>
    obtain ⟨k, v⟩ := a
    show mapOpt _ (dropNullsF ((k, enc v) :: t.map (fun p => (p.1, enc p.2)))) = _
    simp only [dropNullsF, hne v, Bool.false_eq_true, if_false]
    simp [mapOpt, h v, ih]

/-! ## §10  Per-struct drop-roundtrips (derived generically, linear in fields) -/

theorem AuthInfo.fromJson?_dropNulls (m : AuthInfo) :
    AuthInfo.fromJson? (dropNulls (AuthInfo.toJson m)) = some m := by
  obtain ⟨authKey⟩ := m
  simp [AuthInfo.toJson, AuthInfo.fromJson?, optField_dropNulls_obj, keysNodup, assoc?,
    optEnc_drop drop_decStr_encStr encStr_notNull]

theorem AuthInfo.dropNulls_toJson_notNull (m : AuthInfo) :
    isNullJ (dropNulls (AuthInfo.toJson m)) = false := rfl

theorem Hostinfo.fromJson?_dropNulls (m : Hostinfo) :
    Hostinfo.fromJson? (dropNulls (Hostinfo.toJson m)) = some m := by
  obtain ⟨os, hostname, ipnVersion, routableIPs⟩ := m
  simp [Hostinfo.toJson, Hostinfo.fromJson?, optField_dropNulls_obj, keysNodup, assoc?,
    optEnc_drop drop_decStr_encStr encStr_notNull,
    optEnc_drop (drop_decArr_encList drop_decStr_encStr) (encList_notNull encStr)]

theorem Hostinfo.dropNulls_toJson_notNull (m : Hostinfo) :
    isNullJ (dropNulls (Hostinfo.toJson m)) = false := rfl

theorem PortRange.fromJson?_dropNulls (m : PortRange) :
    PortRange.fromJson? (dropNulls (PortRange.toJson m)) = some m := by
  obtain ⟨first, last⟩ := m
  simp [PortRange.toJson, PortRange.fromJson?, reqField_dropNulls_obj, keysNodup, assoc?,
    reqEnc_drop drop_decNat_encNat encNat_notNull]

theorem PortRange.dropNulls_toJson_notNull (m : PortRange) :
    isNullJ (dropNulls (PortRange.toJson m)) = false := rfl

theorem NetPortRange.fromJson?_dropNulls (m : NetPortRange) :
    NetPortRange.fromJson? (dropNulls (NetPortRange.toJson m)) = some m := by
  obtain ⟨ip, bits, ports⟩ := m
  simp [NetPortRange.toJson, NetPortRange.fromJson?, reqField_dropNulls_obj,
    optField_dropNulls_obj, keysNodup, assoc?,
    reqEnc_drop drop_decStr_encStr encStr_notNull,
    optEnc_drop drop_decNat_encNat encNat_notNull,
    reqEnc_drop PortRange.fromJson?_dropNulls PortRange.dropNulls_toJson_notNull]

theorem NetPortRange.dropNulls_toJson_notNull (m : NetPortRange) :
    isNullJ (dropNulls (NetPortRange.toJson m)) = false := rfl

theorem FilterRule.fromJson?_dropNulls (m : FilterRule) :
    FilterRule.fromJson? (dropNulls (FilterRule.toJson m)) = some m := by
  obtain ⟨srcIPs, dstPorts, ipProto⟩ := m
  simp [FilterRule.toJson, FilterRule.fromJson?, reqField_dropNulls_obj,
    optField_dropNulls_obj, keysNodup, assoc?,
    reqEnc_drop (drop_decArr_encList drop_decStr_encStr) (encList_notNull encStr),
    reqEnc_drop (drop_decArr_encList NetPortRange.fromJson?_dropNulls)
      (encList_notNull NetPortRange.toJson),
    optEnc_drop (drop_decArr_encList drop_decNat_encNat) (encList_notNull encNat)]

theorem FilterRule.dropNulls_toJson_notNull (m : FilterRule) :
    isNullJ (dropNulls (FilterRule.toJson m)) = false := rfl

theorem DERPNode.fromJson?_dropNulls (m : DERPNode) :
    DERPNode.fromJson? (dropNulls (DERPNode.toJson m)) = some m := by
  obtain ⟨name, regionID, hostName, ipv4, ipv6, port, stunPort⟩ := m
  simp [DERPNode.toJson, DERPNode.fromJson?, reqField_dropNulls_obj,
    optField_dropNulls_obj, keysNodup, assoc?,
    reqEnc_drop drop_decStr_encStr encStr_notNull,
    reqEnc_drop drop_decNat_encNat encNat_notNull,
    optEnc_drop drop_decStr_encStr encStr_notNull,
    optEnc_drop drop_decNat_encNat encNat_notNull]

theorem DERPNode.dropNulls_toJson_notNull (m : DERPNode) :
    isNullJ (dropNulls (DERPNode.toJson m)) = false := rfl

theorem DERPRegion.fromJson?_dropNulls (m : DERPRegion) :
    DERPRegion.fromJson? (dropNulls (DERPRegion.toJson m)) = some m := by
  obtain ⟨regionID, regionCode, regionName, nodes⟩ := m
  simp [DERPRegion.toJson, DERPRegion.fromJson?, reqField_dropNulls_obj,
    optField_dropNulls_obj, keysNodup, assoc?,
    reqEnc_drop drop_decNat_encNat encNat_notNull,
    reqEnc_drop drop_decStr_encStr encStr_notNull,
    optEnc_drop drop_decStr_encStr encStr_notNull,
    reqEnc_drop (drop_decArr_encList DERPNode.fromJson?_dropNulls)
      (encList_notNull DERPNode.toJson)]

theorem DERPRegion.dropNulls_toJson_notNull (m : DERPRegion) :
    isNullJ (dropNulls (DERPRegion.toJson m)) = false := rfl

/-- `DERPMap.Regions` — the one member whose object keys come from the *message*,
not from a literal. See `drop_decObjMap_encStrMap`: no distinct-keys hypothesis is
needed, because no region member is null-valued and hence none is deleted. -/
theorem DERPMap.fromJson?_dropNulls (m : DERPMap) :
    DERPMap.fromJson? (dropNulls (DERPMap.toJson m)) = some m := by
  obtain ⟨regions⟩ := m
  simp [DERPMap.toJson, DERPMap.fromJson?, reqField_dropNulls_obj, keysNodup, assoc?,
    reqEnc_drop (drop_decObjMap_encStrMap DERPRegion.fromJson?_dropNulls
      DERPRegion.dropNulls_toJson_notNull) (encStrMap_notNull DERPRegion.toJson)]

theorem DERPMap.dropNulls_toJson_notNull (m : DERPMap) :
    isNullJ (dropNulls (DERPMap.toJson m)) = false := rfl

theorem DNSRecord.fromJson?_dropNulls (m : DNSRecord) :
    DNSRecord.fromJson? (dropNulls (DNSRecord.toJson m)) = some m := by
  obtain ⟨name, type_, value⟩ := m
  simp [DNSRecord.toJson, DNSRecord.fromJson?, reqField_dropNulls_obj,
    optField_dropNulls_obj, keysNodup, assoc?,
    reqEnc_drop drop_decStr_encStr encStr_notNull,
    optEnc_drop drop_decStr_encStr encStr_notNull]

theorem DNSRecord.dropNulls_toJson_notNull (m : DNSRecord) :
    isNullJ (dropNulls (DNSRecord.toJson m)) = false := rfl

theorem DnsConfig.fromJson?_dropNulls (m : DnsConfig) :
    DnsConfig.fromJson? (dropNulls (DnsConfig.toJson m)) = some m := by
  obtain ⟨domains, proxied, nameservers, extraRecords⟩ := m
  simp [DnsConfig.toJson, DnsConfig.fromJson?, reqField_dropNulls_obj,
    optField_dropNulls_obj, keysNodup, assoc?,
    reqEnc_drop drop_decBool_encBool encBool_notNull,
    optEnc_drop (drop_decArr_encList drop_decStr_encStr) (encList_notNull encStr),
    optEnc_drop (drop_decArr_encList DNSRecord.fromJson?_dropNulls)
      (encList_notNull DNSRecord.toJson)]

theorem DnsConfig.dropNulls_toJson_notNull (m : DnsConfig) :
    isNullJ (dropNulls (DnsConfig.toJson m)) = false := rfl

/-- **`Node` — 10 optional fields** (incl. `Tags`, `omitempty`). Note the proof:
ten *rewrites*, no case split. A naive `cases` on each optional would be 2^10
branches. -/
theorem Node.fromJson?_dropNulls (m : Node) :
    Node.fromJson? (dropNulls (Node.toJson m)) = some m := by
  obtain ⟨id, stableID, name, user, key, machine, discoKey, addresses, allowedIPs,
          endpoints, derp, homeDERP, hostinfo, keyExpiry, online, machineAuthorized, tags⟩ := m
  simp [Node.toJson, Node.fromJson?, reqField_dropNulls_obj, optField_dropNulls_obj,
    keysNodup, assoc?,
    reqEnc_drop drop_decNat_encNat encNat_notNull,
    reqEnc_drop drop_decStr_encStr encStr_notNull,
    reqEnc_drop drop_decBool_encBool encBool_notNull,
    reqEnc_drop (drop_decArr_encList drop_decStr_encStr) (encList_notNull encStr),
    plainEnc_dropOpt drop_decNat_encNat encNat_notNull,
    optEnc_drop drop_decStr_encStr encStr_notNull,
    optEnc_drop drop_decBool_encBool encBool_notNull,
    optEnc_drop (drop_decArr_encList drop_decStr_encStr) (encList_notNull encStr),
    optEnc_drop Hostinfo.fromJson?_dropNulls Hostinfo.dropNulls_toJson_notNull]

theorem Node.dropNulls_toJson_notNull (m : Node) :
    isNullJ (dropNulls (Node.toJson m)) = false := rfl

theorem RegisterRequest.fromJson?_dropNulls (m : RegisterRequest) :
    RegisterRequest.fromJson? (dropNulls (RegisterRequest.toJson m)) = some m := by
  obtain ⟨version, nodeKey, oldNodeKey, auth, hostinfo, followup, ephemeral, tailnet⟩ := m
  simp [RegisterRequest.toJson, RegisterRequest.fromJson?, reqField_dropNulls_obj,
    optField_dropNulls_obj, keysNodup, assoc?,
    reqEnc_drop drop_decNat_encNat encNat_notNull,
    reqEnc_drop drop_decStr_encStr encStr_notNull,
    reqEnc_drop drop_decBool_encBool encBool_notNull,
    plainEnc_dropOpt drop_decBool_encBool encBool_notNull,
    optEnc_drop drop_decStr_encStr encStr_notNull,
    optEnc_drop AuthInfo.fromJson?_dropNulls AuthInfo.dropNulls_toJson_notNull,
    optEnc_drop Hostinfo.fromJson?_dropNulls Hostinfo.dropNulls_toJson_notNull]

theorem RegisterResponse.fromJson?_dropNulls (m : RegisterResponse) :
    RegisterResponse.fromJson? (dropNulls (RegisterResponse.toJson m)) = some m := by
  obtain ⟨authURL, nodeKeyExpired, machineAuthorized, error⟩ := m
  simp [RegisterResponse.toJson, RegisterResponse.fromJson?, reqField_dropNulls_obj,
    optField_dropNulls_obj, keysNodup, assoc?,
    reqEnc_drop drop_decBool_encBool encBool_notNull,
    optEnc_drop drop_decStr_encStr encStr_notNull]

theorem MapRequest.fromJson?_dropNulls (m : MapRequest) :
    MapRequest.fromJson? (dropNulls (MapRequest.toJson m)) = some m := by
  obtain ⟨version, nodeKey, discoKey, endpoints, stream, omitPeers, hostinfo, readOnly,
          compress⟩ := m
  simp [MapRequest.toJson, MapRequest.fromJson?, reqField_dropNulls_obj,
    optField_dropNulls_obj, keysNodup, assoc?,
    reqEnc_drop drop_decNat_encNat encNat_notNull,
    reqEnc_drop drop_decStr_encStr encStr_notNull,
    plainEnc_dropOpt drop_decBool_encBool encBool_notNull,
    optEnc_drop drop_decStr_encStr encStr_notNull,
    optEnc_drop (drop_decArr_encList drop_decStr_encStr) (encList_notNull encStr),
    optEnc_drop Hostinfo.fromJson?_dropNulls Hostinfo.dropNulls_toJson_notNull]

/-- **The big one, null-omitted.** -/
theorem MapResponse.fromJson?_dropNulls (m : MapResponse) :
    MapResponse.fromJson? (dropNulls (MapResponse.toJson m)) = some m := by
  obtain ⟨node, peers, peersChanged, peersRemoved, dnsConfig, packetFilter,
          packetFilters, derpMap, keepAlive, domain⟩ := m
  simp [MapResponse.toJson, MapResponse.fromJson?,
    optField_dropNulls_obj, keysNodup, assoc?,
    plainEnc_dropOpt drop_decBool_encBool encBool_notNull,
    plainEnc_dropOpt (drop_decArr_encList FilterRule.fromJson?_dropNulls)
      (encList_notNull FilterRule.toJson),
    optEnc_drop Node.fromJson?_dropNulls Node.dropNulls_toJson_notNull,
    optEnc_drop (drop_decArr_encList Node.fromJson?_dropNulls) (encList_notNull Node.toJson),
    optEnc_drop (drop_decArr_encList drop_decNat_encNat) (encList_notNull encNat),
    optEnc_drop DnsConfig.fromJson?_dropNulls DnsConfig.dropNulls_toJson_notNull,
    optEnc_drop DERPMap.fromJson?_dropNulls DERPMap.dropNulls_toJson_notNull,
    optEnc_drop (drop_decObjMap_encStrMap
        (drop_decArr_encList FilterRule.fromJson?_dropNulls)
        (encList_notNull FilterRule.toJson))
      (encStrMap_notNull (encList FilterRule.toJson)),
    optEnc_drop drop_decStr_encStr encStr_notNull]

/-! ## §11  ★ THE GATE: the null-omitting wire, closed String → String

`toJsonSkipNone` is the renderer the real wire uses; `wireEncodeSkipNone` puts it
on the socket. The theorems below say a null-omitted message survives the round
trip through the *same total parser* proved in §5 — no separate parser, no
normalizer threaded through the decoder. -/

def RegisterRequest.toJsonSkipNone (m : RegisterRequest) : Json := dropNulls (RegisterRequest.toJson m)
def RegisterResponse.toJsonSkipNone (m : RegisterResponse) : Json := dropNulls (RegisterResponse.toJson m)
def MapRequest.toJsonSkipNone (m : MapRequest) : Json := dropNulls (MapRequest.toJson m)
def MapResponse.toJsonSkipNone (m : MapResponse) : Json := dropNulls (MapResponse.toJson m)
def Node.toJsonSkipNone (m : Node) : Json := dropNulls (Node.toJson m)

def RegisterRequest.wireEncodeSkipNone (m : RegisterRequest) : String :=
  renderStr (RegisterRequest.toJsonSkipNone m)
def RegisterResponse.wireEncodeSkipNone (m : RegisterResponse) : String :=
  renderStr (RegisterResponse.toJsonSkipNone m)
def MapRequest.wireEncodeSkipNone (m : MapRequest) : String :=
  renderStr (MapRequest.toJsonSkipNone m)
def MapResponse.wireEncodeSkipNone (m : MapResponse) : String :=
  renderStr (MapResponse.toJsonSkipNone m)

theorem RegisterRequest.wireDecode_wireEncodeSkipNone (m : RegisterRequest) :
    RegisterRequest.wireDecode (RegisterRequest.wireEncodeSkipNone m) = some m := by
  simp [RegisterRequest.wireDecode, RegisterRequest.wireEncodeSkipNone,
    RegisterRequest.toJsonSkipNone, parseStr_renderStr, RegisterRequest.fromJson?_dropNulls]

theorem RegisterResponse.wireDecode_wireEncodeSkipNone (m : RegisterResponse) :
    RegisterResponse.wireDecode (RegisterResponse.wireEncodeSkipNone m) = some m := by
  simp [RegisterResponse.wireDecode, RegisterResponse.wireEncodeSkipNone,
    RegisterResponse.toJsonSkipNone, parseStr_renderStr, RegisterResponse.fromJson?_dropNulls]

theorem MapRequest.wireDecode_wireEncodeSkipNone (m : MapRequest) :
    MapRequest.wireDecode (MapRequest.wireEncodeSkipNone m) = some m := by
  simp [MapRequest.wireDecode, MapRequest.wireEncodeSkipNone,
    MapRequest.toJsonSkipNone, parseStr_renderStr, MapRequest.fromJson?_dropNulls]

theorem MapResponse.wireDecode_wireEncodeSkipNone (m : MapResponse) :
    MapResponse.wireDecode (MapResponse.wireEncodeSkipNone m) = some m := by
  simp [MapResponse.wireDecode, MapResponse.wireEncodeSkipNone,
    MapResponse.toJsonSkipNone, parseStr_renderStr, MapResponse.fromJson?_dropNulls]

/-! ### Evidence the renderer really omits (execution, not proof) -/

-- A MapResponse with everything optional absent: the skip-none render must carry
-- NO "null" anywhere, while the §2 renderer does.
#eval MapResponse.wireEncodeSkipNone {}
#eval MapResponse.wireEncode ({} : MapResponse)
#eval (MapResponse.wireEncodeSkipNone {}).toList.length
-- round trip on the null-omitted bytes:
#eval MapResponse.wireDecode (MapResponse.wireEncodeSkipNone {}) == some ({} : MapResponse)
#eval (match MapResponse.wireDecode sampleMapResponse with
       | some m => MapResponse.wireDecode (MapResponse.wireEncodeSkipNone m) == some m
       | none => false)  -- expect: true
#eval (match RegisterRequest.wireDecode sampleRegisterRequest with
       | some m => RegisterRequest.wireEncodeSkipNone m
       | none => "")

/-! ### §11a  The *remaining* gap, named and DEMONSTRATED (not asserted)

The §11 gate covers `omitempty` on **pointer/optional** fields — the `Option`
fields of the model, which encode to `Json.null` and are the members `dropNulls`
deletes. Go's `omitempty` is broader: on a *scalar* it also omits the zero value.
From the public source (`github.com/tailscale/tailscale`, `tailcfg/tailcfg.go`,
fetched 2026-07-19), verbatim:

    KeepAlive    bool          `json:",omitempty"`
    PacketFilter []FilterRule  `json:",omitempty"`
    Ephemeral    bool          `json:",omitempty"`

So a real Go server omits `KeepAlive` when it is `false` and `PacketFilter` when
it is empty — but this model decodes both with `reqField`, which **fails on an
absent key**. The evals below demonstrate exactly that, in both directions; the
first one is the one that would bite on a live tailnet.

This is a *decoder* gap, orthogonal to the null-omitting renderer proved above,
and it is deliberately NOT patched here: the fix is to give the zero-defaulted
scalars a `reqFieldD`-style "absent ⇒ Go zero value" accessor in
`Control/Tailcfg.lean`, which changes that file's decoders and its existing
roundtrip proofs. Naming it beats hacking it. -/

-- What a Go server actually emits for a MapResponse carrying only `Domain`
-- (KeepAlive=false and PacketFilter=[] are both omitted by `omitempty`):
#eval (MapResponse.wireDecode "{\"Domain\":\"example.com\"}").isSome
-- expect: FALSE — the gap. `KeepAlive`/`PacketFilter` are decoded as required.

-- The same message with the two zero-valued scalars present decodes fine,
-- isolating the cause to absence-vs-null rather than to anything in §9-§11:
#eval (MapResponse.wireDecode
  "{\"PacketFilter\":[],\"KeepAlive\":false,\"Domain\":\"example.com\"}").isSome
-- expect: true

-- Same shape for RegisterRequest.Ephemeral (`bool json:",omitempty"`):
#eval (RegisterRequest.wireDecode "{\"Version\":109,\"NodeKey\":\"nodekey:00\"}").isSome
-- expect: FALSE — `Ephemeral` absent.
#eval (RegisterRequest.wireDecode
  "{\"Version\":109,\"NodeKey\":\"nodekey:00\",\"Ephemeral\":false}").isSome
-- expect: true

-- By contrast, every *optional* field may be absent OR null — which is what §9-§11
-- prove, and what our own skip-none renderer produces:
#eval (MapResponse.wireDecode "{\"PacketFilter\":[],\"KeepAlive\":false}").isSome
-- expect: true (all 7 optionals absent)
#eval (MapResponse.wireDecode
  "{\"Node\":null,\"PacketFilter\":[],\"KeepAlive\":false,\"Domain\":null}").isSome
-- expect: true (the same, spelled with explicit nulls)

/-! ## §12  Axiom audit (skip-if-none) -/

#print axioms assoc?_dropNullsF
#print axioms optField_dropNulls_obj
#print axioms reqField_dropNulls_obj
#print axioms drop_decObjMap_encStrMap
#print axioms Node.fromJson?_dropNulls
#print axioms DERPMap.fromJson?_dropNulls
#print axioms RegisterRequest.fromJson?_dropNulls
#print axioms MapRequest.fromJson?_dropNulls
#print axioms MapResponse.fromJson?_dropNulls
#print axioms RegisterRequest.wireDecode_wireEncodeSkipNone
#print axioms MapRequest.wireDecode_wireEncodeSkipNone
#print axioms MapResponse.wireDecode_wireEncodeSkipNone

end Control.TailcfgWire
