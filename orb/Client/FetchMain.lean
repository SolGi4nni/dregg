import Client.Fetch

/-!
# `fetch-client` — the integrated verified HTTP client, driven on real sockets

A host around the composed `Client.Fetch` transaction. Every decision it makes —
serializing the request, parsing the response, choosing whether to follow a
redirect and to where, and reading `Set-Cookie` — is the proven client code; the
only thing outside the verified core is the raw socket byte movement (the shell's
`nc`, exactly as `h1-client` is driven).

Modes:

* `--demo` — run the composed `fetchLoop` in-process on the witness upstream
  (`https://ex/` → `302 /next` with a `Set-Cookie`) and print the transcript: a
  redirect followed and a cookie carried, all through the proven composition.

* `--emit SCHEME HOST PATH [COOKIE]` — write the verified-serialized
  `GET PATH HTTP/1.1` request (with `Host`, an optional `Cookie`, and
  `Connection: close`) to stdout. Pipe it into a socket.

* `--recv SCHEME HOST PATH METHOD` — read an upstream response off stdin, parse it
  with the verified `Proto.ResponseParse.parse`, then run the verified
  `Client.Redirect.followStep` against the current target and surface the decision
  (`FOLLOW <scheme> <host> <path> <method>` / `DELIVER`), the status, the body
  length, and any `Set-Cookie` value — a machine-readable line a driver loops on.

Chained with `nc` across two hops (`--emit … | nc | --recv …` → follow → `--emit …
Cookie | nc | --recv …`) this performs a genuine outbound HTTP/1.1 fetch that
follows a redirect and carries a cookie, over real sockets, entirely through the
proven client path.
-/

open Proto
open Proto.Client.Fetch
open Proto.Client.Redirect (Target Scheme followStep findLocation resolveLocation
  redirectMethod isRedirectStatus nameCIEq FollowResult FollowRequest)
-- The PROVEN cookie types + decision functions, composed by the exe below.
open Client.Session (Cookie Req cookieMatches domainOk)
open Client.CookieExpiry (ExpiryAttr StoredCookie resolveExpiry sendableNow)

/-- Read all remaining bytes from a stream. -/
partial def readAll (s : IO.FS.Stream) (acc : ByteArray) : IO ByteArray := do
  let chunk ← s.read 65536
  if chunk.isEmpty then return acc else readAll s (acc ++ chunk)

def s2b (s : String) : List UInt8 := s.toUTF8.toList
def b2s (b : List UInt8) : String := String.fromUTF8! ⟨b.toArray⟩

/-- `"Set-Cookie"`. -/
def setCookieName : List UInt8 := s2b "Set-Cookie"

/-- All `Set-Cookie` values in a header list (case-insensitive name). -/
def findSetCookies : List (List UInt8 × List UInt8) → List (List UInt8)
  | [] => []
  | (k, v) :: t => if nameCIEq k setCookieName then v :: findSetCookies t else findSetCookies t

/-! ## Set-Cookie ATTRIBUTE parsing → the PROVEN `StoredCookie`

`Client.CookieExpiry` proves the cookie EXPIRY + jar policy over an already-parsed
model (`ExpiryAttr`, `StoredCookie`, `Cookie`); it has no wire-string lexer, and
its `Cookie` carries `name`/`value` as opaque `Nat` tokens (matching ignores
them). So the byte-lexing of a `Set-Cookie` header line — splitting on `;`/`=`,
reading `Max-Age`/`Expires`/`Domain`/`Path`/`Secure` — lives HERE in the exe
(unverified, like the `nc` byte movement), and every DECISION it feeds is the
proven code: `resolveExpiry` computes the expiry instant, and the send-side
`sendableNow` / `cookieMatches` decide what actually goes out. The `name=value`
text is carried alongside for re-emission (the proven `Cookie` cannot hold it). -/

/-- Split a byte list on every occurrence of `sep` (structural, keeps empties). -/
def splitOnByte (sep : UInt8) : List UInt8 → List (List UInt8)
  | [] => [[]]
  | b :: bs =>
    let rest := splitOnByte sep bs
    if b == sep then [] :: rest
    else match rest with
      | [] => [[b]]
      | r :: rs => (b :: r) :: rs

/-- Split on the FIRST `sep`: `(before, some after)` if present, else `(l, none)`. -/
def splitFirst (sep : UInt8) : List UInt8 → (List UInt8 × Option (List UInt8))
  | [] => ([], none)
  | b :: bs =>
    if b == sep then ([], some bs)
    else let (a, r) := splitFirst sep bs; (b :: a, r)

def isWS (b : UInt8) : Bool := b == 32 || b == 9
def trimWS (l : List UInt8) : List UInt8 :=
  ((l.dropWhile isWS).reverse.dropWhile isWS).reverse

def lowerB (b : UInt8) : UInt8 := if b ≥ 65 && b ≤ 90 then b + 32 else b
def ciEqStr (l : List UInt8) (s : String) : Bool := l.map lowerB == (s2b s).map lowerB

/-- Unsigned decimal value of the leading digit run. -/
def dvalNat : Nat → List UInt8 → Nat
  | acc, [] => acc
  | acc, b :: bs => if b ≥ 48 && b ≤ 57 then dvalNat (acc * 10 + (b.toNat - 48)) bs else acc

/-- Signed decimal (`Max-Age` may be negative → already-expired via `resolveExpiry`). -/
def parseIntDec : List UInt8 → Int
  | 45 :: bs => -(dvalNat 0 bs : Int)   -- leading '-'
  | l        => (dvalNat 0 l : Int)

/-- A stable opaque token for a name/value byte string (the proven `Cookie` stores
`Nat`; matching never inspects it, so any injective-enough fold serves). -/
def tok (l : List UInt8) : Nat := l.foldl (fun acc b => acc * 257 + b.toNat + 1) 1

/-- Month name → 1..12 (0 if unknown). -/
def monthNum (m : List UInt8) : Nat :=
  if ciEqStr m "jan" then 1 else if ciEqStr m "feb" then 2
  else if ciEqStr m "mar" then 3 else if ciEqStr m "apr" then 4
  else if ciEqStr m "may" then 5 else if ciEqStr m "jun" then 6
  else if ciEqStr m "jul" then 7 else if ciEqStr m "aug" then 8
  else if ciEqStr m "sep" then 9 else if ciEqStr m "oct" then 10
  else if ciEqStr m "nov" then 11 else if ciEqStr m "dec" then 12
  else 0

/-- Howard Hinnant days-from-civil (proleptic Gregorian, epoch 1970-01-01). -/
def daysFromCivil (y0 m d : Int) : Int :=
  let y := if m ≤ 2 then y0 - 1 else y0
  let era := (if y ≥ 0 then y else y - 399) / 400
  let yoe := y - era * 400
  let mp := if m > 2 then m - 3 else m + 9
  let doy := (153 * mp + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

/-- Parse an RFC 7231 IMF-fixdate (`Wdy, DD Mon YYYY HH:MM:SS GMT`) to a unix
epoch second, clamped at 0. Returns `none` if it does not look like one. -/
def httpDateToEpoch (v : List UInt8) : Option Nat :=
  let toks := (splitOnByte 32 (trimWS v)).map trimWS |>.filter (· ≠ [])
  match toks with
  | _wday :: dd :: mon :: yyyy :: time :: _ =>
    let d := (dvalNat 0 dd : Int)
    let mo := (monthNum mon : Int)
    let y := (dvalNat 0 yyyy : Int)
    match (splitOnByte 58 time).map (dvalNat 0) with
    | hh :: mm :: ss :: _ =>
      if mo == 0 then none else
      let days := daysFromCivil y mo d
      let secs := days * 86400 + (hh : Int) * 3600 + (mm : Int) * 60 + (ss : Int)
      some (if secs < 0 then 0 else secs.toNat)
    | _ => none
  | _ => none

/-- The wire `Set-Cookie` attributes we lex out before handing to the proven model. -/
structure RawAttrs where
  maxAge  : Option Int := none
  expires : Option Nat := none
  domain  : Option (List UInt8) := none
  path    : Option (List UInt8) := none
  secure  : Bool := false

/-- Fold one `attr[=val]` token (already `;`-split and trimmed) into the accumulator. -/
def stepAttr (a : RawAttrs) (part : List UInt8) : RawAttrs :=
  let (nm, vopt) := splitFirst 61 part          -- 61 = '='
  let nm := trimWS nm
  let v := trimWS (vopt.getD [])
  if ciEqStr nm "max-age" then { a with maxAge := some (parseIntDec v) }
  else if ciEqStr nm "expires" then { a with expires := httpDateToEpoch v }
  else if ciEqStr nm "domain" then
    { a with domain := some (if v.headD 0 == 46 then v.tail else v) }  -- strip leading '.'
  else if ciEqStr nm "path" then { a with path := some v }
  else if ciEqStr nm "secure" then { a with secure := true }
  else a

/-- A parsed cookie: the PROVEN `StoredCookie` (fed to the proven decisions) plus
the raw `name=value` bytes to re-emit on the wire. -/
structure ParsedCookie where
  sc    : StoredCookie
  name  : List UInt8
  value : List UInt8

/-- The `Cookie: name=value` wire text for re-emission. -/
def ParsedCookie.raw (p : ParsedCookie) : List UInt8 := p.name ++ [61] ++ p.value

/-- Byte string → the model's `Nat`-token list (per-byte), the same bridge the
proven `Client.Fetch.reqOfTarget` uses (host/path bytes become label/segment
tokens). -/
def toTokens (l : List UInt8) : List Nat := l.map (·.toNat)

/-- **Parse one `Set-Cookie` header value into the PROVEN `StoredCookie`.** The
byte-lexing is here; the expiry INSTANT is `Client.CookieExpiry.resolveExpiry`
(the proven §5.2.1/§5.2.2 resolver) applied to the lexed attribute. `Max-Age`
takes precedence over `Expires` (RFC 6265 §5.3); absent both, it is a session
cookie. Absent `Domain`, the cookie is host-only to `originHost`; absent `Path`,
it defaults to `/`. -/
def parseSetCookie (now : Nat) (originHost : List UInt8) (v : List UInt8) : ParsedCookie :=
  let parts := (splitOnByte 59 v).map trimWS       -- 59 = ';'
  let nv := parts.headD []
  let attrs := parts.tail
  let (nm, vopt) := splitFirst 61 nv
  let cname := trimWS nm
  let cval := trimWS (vopt.getD [])
  let ra : RawAttrs := attrs.foldl stepAttr {}
  -- Compose the proven §5.2 resolver over the lexed lifetime attribute.
  let eattr : ExpiryAttr :=
    match ra.maxAge, ra.expires with
    | some d, _      => .maxAge d
    | none,   some t => .expiresAt t
    | none,   none   => .session
  let expiry : Option Nat := resolveExpiry now eattr
  let hostOnly := ra.domain.isNone
  let dom := toTokens (ra.domain.getD originHost)
  let cpath := toTokens (ra.path.getD (s2b "/"))
  let c : Cookie :=
    { name := tok cname, value := tok cval, domain := dom, path := cpath,
      secure := ra.secure, hostOnly := hostOnly }
  { sc := { cookie := c, expiry := expiry, created := now }, name := cname, value := cval }

/-- Build the outgoing `Req` (the proven matcher's request context) for a target. -/
def reqOfArgs (scheme host path : String) : Req :=
  { host := toTokens (s2b host), path := toTokens (s2b path),
    https := scheme == "https", hostIsIp := false }

/-- **The proven send-decision, applied.** The `Cookie:` header value for a
request at clock `now`: exactly the jar entries the proven
`Client.CookieExpiry.sendableNow` admits (`!expired && cookieMatches`), joined by
`"; "`. Expired cookies and domain/path/Secure mismatches are dropped by the
proven predicate, not by the exe. -/
def cookieHeaderFor (now : Nat) (req : Req) (jar : List ParsedCookie) : List UInt8 :=
  let sendable := jar.filter (fun p => sendableNow now req p.sc)
  match sendable with
  | [] => []
  | p :: ps => ps.foldl (fun acc q => acc ++ s2b "; " ++ q.raw) p.raw

/-- The scheme token from a CLI arg. -/
def schemeOf (s : String) : Scheme := if s == "https" then Scheme.https else Scheme.http

/-- Build the outbound `Proto.Request` for a GET on `path`, with `Host` and an
optional `Cookie` header, plus `Connection: close`. -/
def buildReq (host path : String) (cookie : Option String) : Proto.Request :=
  let base : List (List UInt8 × List UInt8) :=
    [(s2b "Host", s2b host)] ++
    (match cookie with | some c => [(s2b "Cookie", s2b c)] | none => []) ++
    [(s2b "Connection", s2b "close")]
  { method := s2b "GET", target := s2b path, version := s2b "HTTP/1.1", headers := base }

/-- Reconstruct the byte string from a per-byte `Nat`-token list (dual of `toTokens`). -/
def tokensToStr (l : List Nat) : String := b2s (l.map (fun n => UInt8.ofNat n))

/-- A one-line dump of a parsed cookie's attributes (all off the PROVEN `StoredCookie`). -/
def showParsed (p : ParsedCookie) : String :=
  let dom := tokensToStr p.sc.cookie.domain
  let pth := tokensToStr p.sc.cookie.path
  let exp := match p.sc.expiry with | none => "session" | some e => s!"@{e}"
  s!"name={b2s p.name} value={b2s p.value} domain={dom} path={pth} " ++
    s!"secure={p.sc.cookie.secure} hostOnly={p.sc.cookie.hostOnly} expiry={exp}"

/-- Drive parse→store→next-request over concrete `Set-Cookie` headers, printing the
attribute parse and the PROVEN send-decision (`sendableNow` = `!expired && cookieMatches`)
for each cookie against a follow-up request. -/
def runCookieSelftest : IO Unit := do
  let originHost := "example.com"
  -- A unix-epoch-scale clock, so Max-Age (resolved to now+Δ) and an absolute
  -- Expires epoch share units. now ≈ 2023-11-14; later is a few seconds on.
  let now : Nat := 1700000000
  let later : Nat := 1700000005
  IO.println s!"=== cookie-selftest: origin=https://{originHost}/  store@now={now} ==="
  -- Concrete Set-Cookie header VALUES exactly as they arrive on the wire.
  let headers : List (String × String) :=
    [ ("expired-maxage",  "sess=old; Max-Age=0; Domain=example.com; Path=/"),
      ("expired-expires", "e2=x; Expires=Wed, 09 Jun 2021 10:18:14 GMT; Domain=example.com; Path=/"),
      ("valid",           "sid=abc123; Max-Age=3600; Domain=example.com; Path=/"),
      ("cross-domain",    "track=1; Max-Age=3600; Domain=evil.com; Path=/"),
      ("secure-only",     "s=1; Max-Age=3600; Domain=example.com; Path=/; Secure") ]
  let jar : List ParsedCookie :=
    headers.map (fun (_, h) => parseSetCookie now (s2b originHost) (s2b h))
  IO.println "--- PARSED (byte-lex → proven StoredCookie via resolveExpiry) ---"
  for ((tag, _), p) in headers.zip jar do
    IO.println s!"[{tag}] {showParsed p}"
  -- Follow-up request 1: GET https://example.com/next
  let reqHttps := reqOfArgs "https" originHost "/next"
  IO.println s!"--- DECISION @ later={later}, next req = GET https://{originHost}/next ---"
  for ((tag, _), p) in headers.zip jar do
    let expired := p.sc.expiredAt later
    let matched := cookieMatches p.sc.cookie reqHttps
    let send := sendableNow later reqHttps p.sc
    let reason :=
      if send then "SENT"
      else if expired then "DROP(expired)"
      else if !matched then "DROP(no-match: domain/path/secure)"
      else "DROP"
    IO.println s!"[{tag}] expired={expired} cookieMatches={matched} sendableNow={send} => {reason}"
  IO.println s!"Cookie header emitted (https): {b2s (cookieHeaderFor later reqHttps jar)}"
  -- Follow-up request 2 over plain HTTP: the Secure cookie must now be withheld.
  let reqHttp := reqOfArgs "http" originHost "/next"
  IO.println s!"Cookie header emitted (http, Secure withheld): {b2s (cookieHeaderFor later reqHttp jar)}"

def main (args : List String) : IO Unit := do
  match args with
  | ["--demo"] =>
    -- The composed fetch, executed in-process on the proven witness upstream.
    let tr := fetchLoop exUpstream exSetC reqOfTarget 3 [] exOrigin mGET
    IO.println s!"fetch-client demo: composed verified fetch over {tr.emitted.length} request(s)"
    for e in tr.emitted do
      let host := b2s e.target.host
      let path := b2s e.target.path
      let cookieNames := e.sent.map (fun c => c.name)
      IO.println s!"  → {repr e.target.scheme} host={host} path={path} method={b2s e.method} cookies={cookieNames}"
    IO.println s!"  final status={tr.final.status}, jar now holds {tr.jar.length} cookie(s)"
  | ["--emit", _scheme, host, path] =>
    let bytes : ByteArray := ⟨(Proto.RequestSerialize.serialize (buildReq host path none)).toArray⟩
    (← IO.getStdout).write bytes
  | ["--emit", _scheme, host, path, cookie] =>
    let bytes : ByteArray := ⟨(Proto.RequestSerialize.serialize (buildReq host path (some cookie))).toArray⟩
    (← IO.getStdout).write bytes
  | ["--recv", scheme, host, path, method] =>
    let data ← readAll (← IO.getStdin) ByteArray.empty
    match Proto.ResponseParse.parse data.toList with
    | none => IO.println "fetch-client: VERIFIED-PARSE fail"
    | some resp =>
      IO.println s!"STATUS={resp.status}"
      IO.println s!"BODYLEN={resp.body.length}"
      for v in findSetCookies resp.headers do
        IO.println s!"SETCOOKIE={b2s v}"
        -- Parse the wire attributes into the PROVEN StoredCookie (Max-Age/Expires
        -- resolved by CookieExpiry.resolveExpiry) and surface them, so the live
        -- socket path stores attributes rather than a raw value.
        IO.println s!"PARSED {showParsed (parseSetCookie 0 (s2b host) v)}"
      let cur : Target := ⟨schemeOf scheme, s2b host, s2b path⟩
      -- the verified redirect decision, live, against the parsed response
      match followStep cur (s2b method) resp.status resp.headers 10 with
      | .followed fr _ =>
        IO.println s!"FOLLOW {reprStr fr.target.scheme} {b2s fr.target.host} {b2s fr.target.path} {b2s fr.method}"
      | .tooManyRedirects => IO.println "DECISION=too-many-redirects"
      | .blockedDowngrade => IO.println "DECISION=blocked-downgrade"
      | .noRedirect => IO.println "DELIVER"
  | ["--cookie-selftest"] => runCookieSelftest
  | _ =>
    IO.println "usage: fetch-client [--demo | --cookie-selftest | --emit SCHEME HOST PATH [COOKIE] | --recv SCHEME HOST PATH METHOD]"
