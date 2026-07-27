import Proto.Basic

/-!
# HTTP/1.0 compatibility semantics

A small, self-contained model of the persistence and body-framing rules an
HTTP/1.0 peer imposes on a server front end, proved against the request head the
core state machine already carries (`Proto.Request`, whose `version` field is the
raw protocol-version token and whose `headers` are decoded name/value byte
pairs).

The rules are the classic HTTP/1.0 compatibility contract (as fixed by RFC 1945
and re-stated for interoperability in RFC 9112 §9.3 / §7):

* **Non-persistent by default.** HTTP/1.0 has no persistent connections unless
  the client opts in with `Connection: keep-alive`. Absent that token the server
  answers and signals close.

* **Opt-in keep-alive.** An explicit `Connection: keep-alive` on a 1.0 request
  keeps the connection alive for a further request.

* **No chunked to a 1.0 peer.** `Transfer-Encoding: chunked` is a 1.1 mechanism.
  A response destined for a 1.0 client is framed by a `Content-Length` or by
  connection close, never by chunked transfer coding.

Everything here is total and decidable: the connection-token scan
(`connectionHas`) is a concrete comma-split / trim / case-fold over the header
value, and the version discriminant is exact-token equality against the two
version literals. The three headline theorems key only on the version token and
the (opaque) result of the token scan, so they hold uniformly for every possible
header set.
-/

namespace Proto.Http10

open Proto

/-! ## Byte-level literals and helpers

Version and connection tokens are given as explicit ASCII byte lists so every
supporting fact reduces in the kernel (`decide`) without unfolding
`String.toUTF8`. -/

/-- `"HTTP/1.0"` as ASCII bytes. -/
def http10Bytes : Bytes := [72, 84, 84, 80, 47, 49, 46, 48]

/-- `"HTTP/1.1"` as ASCII bytes. -/
def http11Bytes : Bytes := [72, 84, 84, 80, 47, 49, 46, 49]

/-- `"connection"` (lowercase) as ASCII bytes — the case-folded header name. -/
def connectionName : Bytes := [99, 111, 110, 110, 101, 99, 116, 105, 111, 110]

/-- `"keep-alive"` as ASCII bytes. -/
def keepAliveTok : Bytes := [107, 101, 101, 112, 45, 97, 108, 105, 118, 101]

/-- `"close"` as ASCII bytes. -/
def closeTok : Bytes := [99, 108, 111, 115, 101]

/-- The two version literals are distinct — the discriminant used below is
sharp. -/
theorem http10_ne_http11 : http10Bytes ≠ http11Bytes := by decide

/-- ASCII lowercase of a single byte (`A`–`Z` ↦ `a`–`z`, else identity). -/
def lowerByte (c : UInt8) : UInt8 :=
  if 65 ≤ c ∧ c ≤ 90 then c + 32 else c

/-- ASCII lowercase of a byte string. -/
def lowerBytes (bs : Bytes) : Bytes := bs.map lowerByte

/-- Whitespace test: SP or HTAB. -/
def isWs (c : UInt8) : Bool := c == 32 || c == 9

/-- Strip leading and trailing linear whitespace. -/
def trimBs (bs : Bytes) : Bytes :=
  ((bs.dropWhile isWs).reverse.dropWhile isWs).reverse

/-- Split a byte string on `,` (byte `44`). Always yields at least one field. -/
def splitComma (bs : Bytes) : List Bytes :=
  bs.foldr
    (fun c acc =>
      match acc with
      | cur :: rest => if c == 44 then [] :: cur :: rest else (c :: cur) :: rest
      | [] => [[c]])
    [[]]

/-- Value of the first header whose case-folded name is `nameLower`. -/
def headerValue (req : Request) (nameLower : Bytes) : Option Bytes :=
  (req.headers.find? (fun h => lowerBytes h.1 == nameLower)).map (·.2)

/-- The comma-separated, trimmed, case-folded tokens of the `Connection`
header. -/
def connectionTokens (req : Request) : List Bytes :=
  match headerValue req connectionName with
  | some v => (splitComma v).map (fun t => lowerBytes (trimBs t))
  | none => []

/-- Does the request's `Connection` header carry the given (already lowercase)
token? -/
def connectionHas (req : Request) (token : Bytes) : Bool :=
  (connectionTokens req).contains token

/-! ## Persistence decision -/

/-- Whether the request version is exactly HTTP/1.0. -/
def isHttp10 (req : Request) : Prop := req.version = http10Bytes

/-- The keep-alive decision for a request head. HTTP/1.0 is non-persistent
unless the client sent `Connection: keep-alive`; HTTP/1.1 is persistent unless
the client sent `Connection: close`; any other version is treated as
non-persistent. -/
def keepAlive (req : Request) : Bool :=
  if req.version = http10Bytes then connectionHas req keepAliveTok
  else if req.version = http11Bytes then !connectionHas req closeTok
  else false

/-- The disposition the server takes after answering: keep the connection alive
for another request, or signal close. -/
inductive Disposition where
  | keepAlive
  | close
deriving Repr, DecidableEq

/-- The disposition realized from the keep-alive decision. -/
def disposition (req : Request) : Disposition :=
  if keepAlive req then .keepAlive else .close

/-! ## Response body framing -/

/-- How a response body is delimited on the wire. -/
inductive Framing where
  | closeDelimited
  | contentLength (n : Nat)
  | chunked
deriving Repr, DecidableEq

/-- The framing chosen for a response to a client of the given version, given
whether the body length is known. Chunked transfer coding is chosen only for an
HTTP/1.1 client with an unknown-length body; a known length always frames by
`Content-Length`; anything else (notably an HTTP/1.0 client) is close-delimited. -/
def respFraming (version : Bytes) (knownLen : Option Nat) : Framing :=
  match knownLen with
  | some n => .contentLength n
  | none   => if version = http11Bytes then .chunked else .closeDelimited

/-- The framing chosen for a response to the peer that sent `req`. -/
def respFramingFor (req : Request) (knownLen : Option Nat) : Framing :=
  respFraming req.version knownLen

/-! ## Headline theorems -/

/-- **HTTP/1.0 closes by default.** A 1.0 request that does *not* carry
`Connection: keep-alive` yields a close disposition — the response signals
close. -/
theorem http10_closes_default (req : Request)
    (h10 : req.version = http10Bytes)
    (hno : connectionHas req keepAliveTok = false) :
    disposition req = Disposition.close := by
  have hk : keepAlive req = false := by simp [keepAlive, h10, hno]
  simp [disposition, hk]

/-- **HTTP/1.0 keep-alive is honored when explicit.** A 1.0 request carrying
`Connection: keep-alive` yields a keep-alive disposition — the connection stays
open for a further request. -/
theorem http10_keepalive_explicit (req : Request)
    (h10 : req.version = http10Bytes)
    (hka : connectionHas req keepAliveTok = true) :
    disposition req = Disposition.keepAlive := by
  have hk : keepAlive req = true := by simp [keepAlive, h10, hka]
  simp [disposition, hk]

/-- **No chunked to a 1.0 peer.** A response to an HTTP/1.0 request is framed by
`Content-Length` or by connection close — never by chunked transfer coding. -/
theorem http10_no_chunked (req : Request) (knownLen : Option Nat)
    (h10 : req.version = http10Bytes) :
    respFramingFor req knownLen = Framing.closeDelimited
      ∨ ∃ n, respFramingFor req knownLen = Framing.contentLength n := by
  unfold respFramingFor respFraming
  cases knownLen with
  | none =>
      left
      rw [h10, if_neg http10_ne_http11]
  | some n =>
      right
      exact ⟨n, rfl⟩

/-- Corollary in negative form: the 1.0 response framing is provably not
chunked. -/
theorem http10_never_chunked (req : Request) (knownLen : Option Nat)
    (h10 : req.version = http10Bytes) :
    respFramingFor req knownLen ≠ Framing.chunked := by
  rcases http10_no_chunked req knownLen h10 with h | ⟨n, h⟩ <;> rw [h] <;>
    simp only [ne_eq, reduceCtorEq, not_false_eq_true]

/-! ## Non-vacuity witnesses

Concrete requests exercising both branches of each rule, so none of the
headline theorems is vacuously true: the hypotheses are inhabited and the
decision functions genuinely distinguish the cases. -/

/-- A bare HTTP/1.0 GET, no `Connection` header. -/
def req10Plain : Request :=
  { version := http10Bytes }

/-- An HTTP/1.0 GET with `Connection: keep-alive`. -/
def req10KeepAlive : Request :=
  { version := http10Bytes
    headers := [([67, 111, 110, 110, 101, 99, 116, 105, 111, 110],  -- "Connection"
                 [107, 101, 101, 112, 45, 97, 108, 105, 118, 101])] }  -- "keep-alive"

/-- An HTTP/1.1 GET, no `Connection` header. -/
def req11Plain : Request :=
  { version := http11Bytes }

/-- Default 1.0 → the token scan finds nothing → close (Theorem 1 is live). -/
example : connectionHas req10Plain keepAliveTok = false := by decide
example : disposition req10Plain = Disposition.close :=
  http10_closes_default req10Plain rfl (by decide)

/-- Explicit 1.0 keep-alive → the token scan finds it → kept alive
(Theorem 2 is live; the function is not constantly `close`). -/
example : connectionHas req10KeepAlive keepAliveTok = true := by decide
example : disposition req10KeepAlive = Disposition.keepAlive :=
  http10_keepalive_explicit req10KeepAlive rfl (by decide)

/-- A 1.1 client with unknown length *can* be framed chunked — so the
"never chunked" guarantee for 1.0 is a real restriction, not a tautology of
`respFraming`. -/
example : respFramingFor req11Plain none = Framing.chunked := by decide

/-- The same unknown-length body to a 1.0 client is close-delimited. -/
example : respFramingFor req10Plain none = Framing.closeDelimited := by decide

end Proto.Http10
