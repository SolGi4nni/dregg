/-
# Pki.AcmeDriver — the sans-IO half of the RFC 8555 client

The ACME order and challenge FSMs are proven in `Acme.Order` / `Acme.Challenge`;
the JWS, the key authorization, and the thumbprint in `Pki.Acme`; the CSR in
`Pki.Csr`. What was missing between those and a real CA is the *protocol
plumbing*: reading the CA's JSON objects and its HTTP responses, and assembling
the JWS-signed request bodies. That plumbing is here, sans-IO and total, so the
executable (`AcmeIssue`) holds only sockets and files.

## Honest scope of this module

Everything here is **total and Lean-side, but it is plumbing, not cryptography
and not the state machine** — the safety properties still live in the proven
modules this feeds. Two limits are deliberate and named rather than hidden:

* The JSON reader is a **targeted member extractor**, not a general JSON parser.
  It finds `"key"` and reads the following string / array, and it does not track
  string context while brace-matching — an object whose *string values* contain
  `{`, `}` or `[` would be mis-split. ACME directory, order, authorization and
  challenge objects do not (URLs, tokens, and status words are brace-free), and
  every value this module reads is re-checked downstream: tokens flow into the
  proven `keyAuthorization`, statuses into the proven FSMs.
* `\uXXXX` escapes are not decoded (`\c` yields `c`). ACME identifiers, URLs and
  tokens are ASCII by RFC 8555 §7.1.4 / §8.3.

`jsonString_of_member` is the round-trip that justifies the extractor: for a
member encoded the ordinary way, with an escape-free value, the reader returns
exactly the value that was encoded — so a `token` or a `url` cannot come back
truncated or shifted.
-/
import Pki.Acme

namespace Pki.AcmeDriver

/-- Protocol text: ACME is ASCII on the wire. -/
abbrev Str := List Char

/-! ## Scanning primitives -/

def isWs (c : Char) : Bool := c == ' ' || c == '\n' || c == '\r' || c == '\t'

def skipWs : Str → Str
  | [] => []
  | c :: r => if isWs c then skipWs r else c :: r

/-- The suffix strictly after the first occurrence of `p`, if any. -/
def afterSub (p : Str) : Str → Option Str
  | [] => none
  | c :: r => if p.isPrefixOf (c :: r) then some ((c :: r).drop p.length)
              else afterSub p r

/-- Everything before the first occurrence of `p`, and everything after it. -/
def splitOnSub (p : Str) : Str → Option (Str × Str)
  | [] => none
  | c :: r =>
    if p.isPrefixOf (c :: r) then some ([], (c :: r).drop p.length)
    else (splitOnSub p r).map (fun (a, b) => (c :: a, b))

/-! ## JSON string literals -/

/-- Read the body of a string literal; `acc` is reversed. -/
def readQuotedGo : Str → Str → Option (Str × Str)
  | [], _ => none
  | c :: r, acc =>
    if c == '"' then some (acc.reverse, r)
    else if c == '\\' then
      match r with
      | [] => none
      | d :: r' => readQuotedGo r' (d :: acc)
    else readQuotedGo r (c :: acc)

/-- Read a JSON string literal at the head of the input: its value and the rest. -/
def readQuoted : Str → Option (Str × Str)
  | '"' :: r => readQuotedGo r []
  | _ => none

/-- The raw text following `"key" :` — the member's value, unparsed. -/
def memberRaw (key : Str) (body : Str) : Option Str :=
  match afterSub ('"' :: key ++ ['"']) body with
  | none => none
  | some r =>
    match skipWs r with
    | ':' :: r2 => some (skipWs r2)
    | _ => none

/-- A string-valued member. -/
def jsonString (key body : Str) : Option Str :=
  (memberRaw key body).bind (fun v => (readQuoted v).map Prod.fst)

/-! ## JSON arrays -/

def readStringArray : Nat → Str → List Str
  | 0, _ => []
  | fuel + 1, s =>
    match skipWs s with
    | [] => []
    | ']' :: _ => []
    | ',' :: r => readStringArray fuel r
    | '"' :: r =>
      match readQuoted ('"' :: r) with
      | some (v, rest) => v :: readStringArray fuel rest
      | none => []
    | _ => []

/-- The members of a string-array-valued member, in order. -/
def jsonStringArray (key body : Str) : List Str :=
  match memberRaw key body with
  | some ('[' :: r) => readStringArray r.length r
  | _ => []

/-- Collect the top-level `{...}` items of an array body. `acc` is reversed. -/
def readObjects : Nat → Nat → Str → Str → List Str
  | 0, _, _, _ => []
  | _ + 1, _, [], _ => []
  | fuel + 1, depth, c :: r, acc =>
    if c == '{' then
      if depth == 0 then readObjects fuel 1 r ['{']
      else readObjects fuel (depth + 1) r (c :: acc)
    else if c == '}' then
      if depth == 1 then ('}' :: acc).reverse :: readObjects fuel 0 r []
      else readObjects fuel (depth - 1) r (c :: acc)
    else if depth == 0 then
      if c == ']' then [] else readObjects fuel 0 r acc
    else readObjects fuel depth r (c :: acc)

/-- The objects of an object-array-valued member (e.g. `challenges`). -/
def jsonObjectArray (key body : Str) : List Str :=
  match memberRaw key body with
  | some ('[' :: r) => readObjects r.length 0 r []
  | _ => []

/-! ## The extractor round-trip

For a member written the ordinary way — `"key":"value"` — with an escape-free
value, the reader returns exactly `value` and leaves the rest of the object
untouched. This is what makes it safe to feed a CA-supplied `token` into the
proven `keyAuthorization`: the token is the CA's token, not a prefix of it and
not a neighbouring member. -/

/-- An escape-free value: no quote (which would end the literal early) and no
backslash (which the reader would consume as an escape). -/
def Plain (v : Str) : Prop := ∀ c ∈ v, c ≠ '"' ∧ c ≠ '\\'

theorem readQuotedGo_plain (v : Str) (h : Plain v) (rest : Str) (acc : Str) :
    readQuotedGo (v ++ '"' :: rest) acc = some (acc.reverse ++ v, rest) := by
  induction v generalizing acc with
  | nil =>
    simp only [List.nil_append]
    rw [readQuotedGo.eq_def]
    simp
  | cons c v ih =>
    have hc := h c (by simp)
    have hv : Plain v := fun x hx => h x (List.mem_cons_of_mem _ hx)
    show readQuotedGo (c :: (v ++ '"' :: rest)) acc = _
    rw [readQuotedGo.eq_def]
    simp only [beq_iff_eq, if_neg hc.1, if_neg hc.2]
    rw [ih hv (c :: acc)]
    simp

/-- **The member round-trip.** Reading `key` out of an object whose first
occurrence of `"key"` is the member we encoded returns exactly that value. -/
theorem jsonString_of_member (key v rest : Str) (h : Plain v) :
    jsonString key (('"' :: key ++ ['"']) ++ ':' :: '"' :: (v ++ '"' :: rest))
      = some v := by
  have hpre : afterSub ('"' :: key ++ ['"'])
      (('"' :: key ++ ['"']) ++ ':' :: '"' :: (v ++ '"' :: rest))
      = some (':' :: '"' :: (v ++ '"' :: rest)) := by
    show afterSub _ ('"' :: (key ++ ['"'] ++ (':' :: '"' :: (v ++ '"' :: rest)))) = _
    unfold afterSub
    rw [if_pos (by simp [List.isPrefixOf_iff_prefix])]
    simp
  have hs1 : skipWs (':' :: '"' :: (v ++ '"' :: rest))
      = ':' :: '"' :: (v ++ '"' :: rest) := by simp [skipWs, isWs]
  have hs2 : skipWs ('"' :: (v ++ '"' :: rest)) = '"' :: (v ++ '"' :: rest) := by
    simp [skipWs, isWs]
  have hmem : memberRaw key (('"' :: key ++ ['"']) ++ ':' :: '"' :: (v ++ '"' :: rest))
      = some ('"' :: (v ++ '"' :: rest)) := by
    unfold memberRaw
    rw [hpre]
    simp [hs1, hs2]
  unfold jsonString
  rw [hmem]
  show (readQuoted ('"' :: (v ++ '"' :: rest))).map Prod.fst = some v
  show (readQuotedGo (v ++ '"' :: rest) []).map Prod.fst = some v
  rw [readQuotedGo_plain v h rest []]
  simp

/-! ## HTTP/1.1 responses

The CA's replies. `Replay-Nonce` and `Location` are read from here, so header
lookup is case-insensitive (RFC 9110 §5.1). -/

structure Resp where
  status : Nat
  headers : List (Str × Str)
  body : Str
deriving Inhabited

def lower (s : Str) : Str := s.map Char.toLower

def trim (s : Str) : Str := (skipWs ((skipWs s).reverse)).reverse

/-- Split a header block into its lines (CRLF-separated). -/
def crlfLines : Nat → Str → List Str
  | 0, _ => []
  | fuel + 1, s =>
    match splitOnSub ['\r', '\n'] s with
    | some (line, rest) => line :: crlfLines fuel rest
    | none => if s.isEmpty then [] else [s]

def parseHeader (l : Str) : Option (Str × Str) :=
  match splitOnSub [':'] l with
  | some (n, v) => some (lower (trim n), trim v)
  | none => none

/-- The status code from a status line `HTTP/1.1 NNN Reason`. -/
def statusOf (l : Str) : Nat :=
  let afterVer := (l.dropWhile (· ≠ ' ')).drop 1
  let digits := afterVer.takeWhile Char.isDigit
  digits.foldl (fun n c => n * 10 + (c.toNat - 48)) 0

/-- Parse an HTTP/1.1 response: status line, headers, body. -/
def parseResp (s : Str) : Option Resp :=
  match splitOnSub ['\r', '\n', '\r', '\n'] s with
  | none => none
  | some (head, body) =>
    match crlfLines head.length head with
    | [] => none
    | statusLine :: hdrLines =>
      some { status := statusOf statusLine
           , headers := hdrLines.filterMap parseHeader
           , body := body }

/-- Case-insensitive header lookup. -/
def Resp.header (r : Resp) (name : Str) : Option Str :=
  (r.headers.find? (fun kv => kv.1 == lower name)).map Prod.snd

/-! ## URLs

`https://host[:port]/path` — the only form the CA hands out. -/

structure Url where
  host : Str
  port : Nat
  path : Str
deriving Inhabited

def parseUrl (u : Str) : Option Url :=
  match afterSub "//".toList u with
  | none => none
  | some rest =>
    let authority := rest.takeWhile (· ≠ '/')
    let path := rest.dropWhile (· ≠ '/')
    let path := if path.isEmpty then ['/'] else path
    match splitOnSub [':'] authority with
    | some (h, p) =>
      some { host := h
           , port := p.foldl (fun n c => n * 10 + (c.toNat - 48)) 0
           , path := path }
    | none => some { host := authority, port := 443, path := path }

/-! ## Request payloads (RFC 8555 §7)

Small JSON bodies. The values substituted in are URLs, DNS names and base64url
text — none of which contain a quote or a backslash — so no escaping layer is
introduced that would then need to be trusted. -/

def newAccountPayload (contact : Option Str) : Str :=
  match contact with
  | none => "{\"termsOfServiceAgreed\":true}".toList
  | some c =>
      "{\"termsOfServiceAgreed\":true,\"contact\":[\"mailto:".toList ++ c
        ++ "\"]}".toList

def newOrderPayload (domains : List Str) : Str :=
  let ids := domains.map (fun d => "{\"type\":\"dns\",\"value\":\"".toList ++ d ++ "\"}".toList)
  let joined := match ids with
    | [] => []
    | x :: xs => xs.foldl (fun acc y => acc ++ [','] ++ y) x
  "{\"identifiers\":[".toList ++ joined ++ "]}".toList

def finalizePayload (csrB64 : Str) : Str :=
  "{\"csr\":\"".toList ++ csrB64 ++ "\"}".toList

/-- `POST-as-GET` (RFC 8555 §6.3) is a POST with an empty payload. -/
def postAsGetPayload : Str := []

/-- The challenge-response payload: an empty JSON object tells the CA to
validate (RFC 8555 §7.5.1). -/
def challengeReadyPayload : Str := "{}".toList

/-- The order's identifiers appear in the payload in the order requested — the
same order the CA's `authorizations` come back in, which is what lets the driver
pair an authorization with the identifier it belongs to. -/
theorem newOrderPayload_single (d : Str) :
    newOrderPayload [d]
      = "{\"identifiers\":[".toList
        ++ ("{\"type\":\"dns\",\"value\":\"".toList ++ d ++ "\"}".toList)
        ++ "]}".toList := rfl

end Pki.AcmeDriver
