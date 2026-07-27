import Reactor.Serialize

/-
# Cgi — the CGI/1.1 gateway (RFC 3875)

A total model of the two halves of a CGI gateway:

  * **Request → meta-variable environment** (RFC 3875 §4.1): the server maps
    an HTTP request onto the fixed set of CGI meta-variables (AUTH_TYPE,
    CONTENT_LENGTH, CONTENT_TYPE, GATEWAY_INTERFACE, PATH_INFO,
    PATH_TRANSLATED, QUERY_STRING, REMOTE_ADDR, REMOTE_HOST, REMOTE_IDENT,
    REMOTE_USER, REQUEST_METHOD, SCRIPT_NAME, SERVER_NAME, SERVER_PORT,
    SERVER_PROTOCOL, SERVER_SOFTWARE). The mapping is TOTAL: every
    meta-variable receives a value (possibly the empty string for the
    optional ones, per the §4.1 `"" | ...` productions).
  * **Response framing** (RFC 3875 §6.2): the script's header fields are
    classified into one of the four CGI response types — document response
    (§6.2.1), local redirect (§6.2.2), client redirect (§6.2.3), client
    redirect with document (§6.2.4) — and the server-visible HTTP status is
    derived (document defaults to 200; a bare client redirect becomes 302).

Everything the script computes enters as opaque strings/bytes; the gateway
models only the meta-variable mapping and the response classification, not
process execution. This is the boundary: theorems are about the shape of the
environment and the response classification, not about running a program.

Theorems:
  * `cgi_env_total`            — the environment is total: every meta-variable
                                 appears in the constructed environment list
                                 with its value (full domain coverage).
  * `name_injective`           — distinct meta-variables have distinct names
                                 (no two env entries collide on a key).
  * `env_requestMethod` etc.   — the mapping is faithful to the request fields.
  * `cgi_document_default_200`  — a document response with no Status defaults
                                 to 200 (§6.2.1).
  * `cgi_client_redirect_302`   — a bare client redirect yields HTTP 302
                                 (§6.2.3).
  * `cgi_framing_total`        — at least one CGI field ⇒ the response is
                                 classified (§6.3 "at least one CGI field MUST
                                 be supplied"); with none it is malformed.

Left as a boundary / UNCLOSED:
  * NPH (non-parsed-header) responses (RFC 3875 §5.2) are out of scope.
  * The `protocol-specific` / `extension` header fields (§6.3.4/§6.3.5) are
    not carried through; only the three CGI fields (Content-Type, Location,
    Status) drive classification.
  * PATH_TRANSLATED derivation (§4.1.6, from PATH_INFO + a document-root map)
    is modeled as a supplied request field, not computed here.
-/

namespace Cgi

/-- Raw bytes, modeled as a list. -/
abbrev Bytes := List UInt8

/-! ## Meta-variables (RFC 3875 §4.1) -/

/-- The CGI/1.1 request meta-variables (RFC 3875 §4.1, the
`meta-variable-name` production). -/
inductive Meta where
  | authType | contentLength | contentType | gatewayInterface
  | pathInfo | pathTranslated | queryString | remoteAddr | remoteHost
  | remoteIdent | remoteUser | requestMethod | scriptName
  | serverName | serverPort | serverProtocol | serverSoftware
deriving DecidableEq, Repr

/-- The environment-variable name of a meta-variable (RFC 3875 §4.1). -/
def Meta.name : Meta → String
  | .authType => "AUTH_TYPE"
  | .contentLength => "CONTENT_LENGTH"
  | .contentType => "CONTENT_TYPE"
  | .gatewayInterface => "GATEWAY_INTERFACE"
  | .pathInfo => "PATH_INFO"
  | .pathTranslated => "PATH_TRANSLATED"
  | .queryString => "QUERY_STRING"
  | .remoteAddr => "REMOTE_ADDR"
  | .remoteHost => "REMOTE_HOST"
  | .remoteIdent => "REMOTE_IDENT"
  | .remoteUser => "REMOTE_USER"
  | .requestMethod => "REQUEST_METHOD"
  | .scriptName => "SCRIPT_NAME"
  | .serverName => "SERVER_NAME"
  | .serverPort => "SERVER_PORT"
  | .serverProtocol => "SERVER_PROTOCOL"
  | .serverSoftware => "SERVER_SOFTWARE"

/-- The complete list of meta-variables (RFC 3875 §4.1). -/
def allMetas : List Meta :=
  [.authType, .contentLength, .contentType, .gatewayInterface,
   .pathInfo, .pathTranslated, .queryString, .remoteAddr, .remoteHost,
   .remoteIdent, .remoteUser, .requestMethod, .scriptName,
   .serverName, .serverPort, .serverProtocol, .serverSoftware]

/-- Every meta-variable is in `allMetas` (the list is complete). -/
theorem mem_allMetas (m : Meta) : m ∈ allMetas := by
  cases m <;> decide

/-- **Names are injective**: distinct meta-variables have distinct
environment names, so the constructed environment has no key collisions. -/
theorem name_injective (a b : Meta) (h : a.name = b.name) : a = b := by
  cases a <;> cases b <;> first | rfl | (exact absurd h (by decide))

/-! ## The request the server maps to the environment -/

/-- The request fields the CGI meta-variable mapping reads. Optional
meta-variables default to the empty string, matching the RFC 3875 §4.1
`"" | ...` productions; `gatewayInterface` defaults to the required
`"CGI/1.1"` (§4.1.4). -/
structure Req where
  requestMethod : String
  scriptName : String
  pathInfo : String := ""
  pathTranslated : String := ""
  queryString : String := ""
  serverName : String
  serverPort : String
  serverProtocol : String
  serverSoftware : String
  gatewayInterface : String := "CGI/1.1"
  contentType : String := ""
  contentLength : String := ""
  authType : String := ""
  remoteAddr : String
  remoteHost : String := ""
  remoteIdent : String := ""
  remoteUser : String := ""

/-! ## Request-target splitting (RFC 3875 §4.1.7 / §4.1.13) -/

/-- Split a request-target into its path portion and query component at the
**first** `?` (RFC 3875 §4.1.7 / §4.1.13). The path portion (everything before
the first `?`) identifies the CGI script and is what `SCRIPT_NAME` carries; the
query component is the substring **after** the first `?` (without the `?`
delimiter, and without splitting on any later `?`), and is empty when the target
carries no `?`. Total: defined for every input string. -/
def splitTarget (target : String) : String × String :=
  let cs := target.toList
  let path := cs.takeWhile (· ≠ '?')
  match cs.dropWhile (· ≠ '?') with
  | []      => (String.mk path, "")          -- no `?`: whole target is the path
  | _ :: q  => (String.mk path, String.mk q) -- drop the leading `?`; keep the rest verbatim

/-- The path portion of a request-target (before the first `?`) — what
`SCRIPT_NAME`/`PATH_INFO` are drawn from (RFC 3875 §4.1.13). -/
def targetPath (target : String) : String := (splitTarget target).1

/-- The query component of a request-target — the substring after the first `?`,
without the `?`, empty when absent (RFC 3875 §4.1.7). -/
def targetQuery (target : String) : String := (splitTarget target).2

/-! ## The meta-variable mapping (RFC 3875 §4.1) -/

/-- Map a request onto a meta-variable's value (RFC 3875 §4.1). Total: every
meta-variable has a defined value. -/
def env (req : Req) : Meta → String
  | .authType => req.authType
  | .contentLength => req.contentLength
  | .contentType => req.contentType
  | .gatewayInterface => req.gatewayInterface
  | .pathInfo => req.pathInfo
  | .pathTranslated => req.pathTranslated
  | .queryString => req.queryString
  | .remoteAddr => req.remoteAddr
  | .remoteHost => req.remoteHost
  | .remoteIdent => req.remoteIdent
  | .remoteUser => req.remoteUser
  | .requestMethod => req.requestMethod
  | .scriptName => req.scriptName
  | .serverName => req.serverName
  | .serverPort => req.serverPort
  | .serverProtocol => req.serverProtocol
  | .serverSoftware => req.serverSoftware

/-- The constructed environment: every meta-variable paired with its value
for this request (`(NAME, value)` entries). -/
def envList (req : Req) : List (String × String) :=
  allMetas.map (fun m => (m.name, env req m))

/-- **`cgi_env_total`.** The environment is TOTAL over the meta-variable
domain: for every meta-variable `m`, the pair `(m.name, env req m)` occurs
in the constructed environment. No meta-variable is left unmapped. -/
theorem cgi_env_total (req : Req) (m : Meta) :
    (m.name, env req m) ∈ envList req := by
  unfold envList
  exact List.mem_map.mpr ⟨m, mem_allMetas m, rfl⟩

/-- The environment carries exactly one entry per meta-variable — its length
is the number of meta-variables (17), with no duplicates introduced. -/
theorem envList_length (req : Req) : (envList req).length = 17 := by
  unfold envList allMetas
  simp

/-! ### The mapping is faithful (a sampling of the §4.1 sub-sections) -/

theorem env_requestMethod (req : Req) :
    env req .requestMethod = req.requestMethod := rfl
theorem env_scriptName (req : Req) :
    env req .scriptName = req.scriptName := rfl
theorem env_pathInfo (req : Req) :
    env req .pathInfo = req.pathInfo := rfl
theorem env_queryString (req : Req) :
    env req .queryString = req.queryString := rfl
theorem env_serverProtocol (req : Req) :
    env req .serverProtocol = req.serverProtocol := rfl

/-! ## Response framing (RFC 3875 §6.2) -/

/-- The four CGI response types (RFC 3875 §6.2). -/
inductive CgiResp where
  /-- §6.2.1 Document Response: a Content-Type, a status, and a body. -/
  | document (contentType : String) (status : Nat) (body : Bytes)
  /-- §6.2.2 Local Redirect Response: a local `path?query` the server
  reprocesses (no other fields, no body). -/
  | localRedirect (pathQuery : String)
  /-- §6.2.3 Client Redirect Response: an absolute URI; the server emits a
  302 to the client. -/
  | clientRedirect (location : String)
  /-- §6.2.4 Client Redirect Response with Document. -/
  | clientRedirectDoc (location : String) (status : Nat) (contentType : String)
      (body : Bytes)
deriving Repr

/-- The script's parsed header block: the three CGI header fields (§6.3),
each optional in the raw output, plus the response body. -/
structure ScriptOut where
  contentType : Option String := none
  location : Option String := none
  status : Option Nat := none
  body : Bytes := []

/-- A `Location` value is *local* (§6.2.2) when it is a path — modeled as
beginning with `/` — as opposed to an absolute client URI (§6.2.3). -/
def isLocal (loc : String) : Bool := loc.startsWith "/"

/-- **Classify** the script output into a CGI response type (RFC 3875 §6.2),
or `none` when malformed (no CGI field at all — §6.3 requires at least one).

  * `Location` present and local → local redirect (§6.2.2).
  * `Location` present, absolute, with Status **and** Content-Type → client
    redirect with document (§6.2.4).
  * `Location` present, absolute, otherwise → client redirect (§6.2.3).
  * no `Location`, Content-Type present → document response (§6.2.1), with
    Status defaulting to 200 when omitted.
  * neither → malformed.
-/
def classify (o : ScriptOut) : Option CgiResp :=
  match o.location with
  | some loc =>
    if isLocal loc then
      some (.localRedirect loc)
    else
      match o.status, o.contentType with
      | some st, some ct => some (.clientRedirectDoc loc st ct o.body)
      | _, _ => some (.clientRedirect loc)
  | none =>
    match o.contentType with
    | some ct => some (.document ct (o.status.getD 200) o.body)
    | none => none

/-- The HTTP status a CGI response yields to the client. A document uses its
own status; a local redirect is reprocessed internally (modeled as 200 once
served); a bare client redirect becomes 302 (§6.2.3); a client redirect with
document uses its supplied status (§6.2.4). -/
def CgiResp.httpStatus : CgiResp → Nat
  | .document _ st _ => st
  | .localRedirect _ => 200
  | .clientRedirect _ => 302
  | .clientRedirectDoc _ st _ _ => st

/-- **`cgi_document_default_200`.** A document response (no Location,
Content-Type present) with no Status header defaults to status 200
(RFC 3875 §6.2.1). -/
theorem cgi_document_default_200 (ct : String) (body : Bytes) :
    classify { contentType := some ct, location := none, status := none,
               body := body }
      = some (.document ct 200 body) := by
  simp [classify]

/-- **`cgi_client_redirect_302`.** A bare client redirect (absolute Location,
no Status/Content-Type) yields HTTP 302 to the client (RFC 3875 §6.2.3). -/
theorem cgi_client_redirect_302 (loc : String) (body : Bytes)
    (habs : isLocal loc = false) :
    ∃ r, classify { location := some loc, contentType := none, status := none,
                    body := body } = some r ∧ r.httpStatus = 302 := by
  refine ⟨.clientRedirect loc, ?_, rfl⟩
  simp [classify, habs]

/-- **`cgi_framing_total`.** If the script supplies at least one CGI header
field (a Content-Type or a Location), the response is classified — `classify`
is defined (RFC 3875 §6.3: "at least one CGI field MUST be supplied"). -/
theorem cgi_framing_total (o : ScriptOut)
    (h : o.contentType.isSome ∨ o.location.isSome) :
    (classify o).isSome := by
  unfold classify
  cases hloc : o.location with
  | some loc =>
    by_cases hl : isLocal loc
    · simp [hl]
    · simp only [hl, if_false]
      cases o.status <;> cases o.contentType <;> rfl
  | none =>
    cases hct : o.contentType with
    | some ct => simp
    | none => rw [hloc, hct] at h; simp at h

/-- A response with no CGI field at all is malformed (`none`) — the
contrapositive boundary of `cgi_framing_total`. -/
theorem cgi_malformed (body : Bytes) :
    classify { contentType := none, location := none, status := none,
               body := body } = none := rfl

/-! ## Concrete witnesses (RFC 3875 §6.2) -/

/-- A local `Location` (a path) classifies as a §6.2.2 local redirect the
server reprocesses internally. -/
theorem local_redirect_classifies (loc : String) (h : isLocal loc = true) :
    classify { location := some loc } = some (.localRedirect loc) := by
  simp only [classify, h, if_true]

/-- A client redirect with document supplies its own 302 status (§6.2.4). -/
theorem client_redirectdoc_example :
    (CgiResp.clientRedirectDoc "https://example/x" 302 "text/html" []).httpStatus
      = 302 := by decide

/-! ## The gateway RUNS the script (RFC 3875 §7)

Everything above models the *shape* of the CGI boundary — the meta-variable
environment (§4.1) and the response classification (§6.2). This section is the
gateway itself: it renders the environment onto a real child process, executes
the script, and frames the child's stdout into an HTTP response. The one thing
Lean cannot do purely — `fork`/`execve` — is the single `@[extern]` primitive
`execBytes`, bound to `ffi/cgi_exec.c`; every other step (env rendering, header
parsing, response classification) is total Lean code proved out above. -/

/-- **The process-spawn primitive (RFC 3875 §7).** Run `script` as a child
process with `envBlock` (a newline-separated `NAME=VALUE` environment, one line
per entry) installed as the child's environment and `stdin` fed on its standard
input; return the child's standard output. Opaque, bound to the POSIX
`fork`/`execve` shim `ffi/cgi_exec.c` (`drorb_cgi_exec`). This is the ONLY
impure step; it carries no proof obligation beyond totality of its Lean type. -/
@[extern "drorb_cgi_exec"]
opaque execBytes (script : @&String) (envBlock : @&String)
    (stdin : @&ByteArray) : ByteArray

/-- Render the meta-variable environment (`Cgi.envList`) as the newline-separated
`NAME=VALUE` block the shim installs. The value keeps every byte after the first
`=`, so a `QUERY_STRING=a=1&b=2` round-trips intact. -/
def envBlockOf (env : List (String × String)) : String :=
  String.intercalate "\n" (env.map (fun p => p.1 ++ "=" ++ p.2))

/-- The `Req` the deployed CGI route runs a script under: a complete RFC 3875
§4.1 environment (all 17 meta-variables receive a value). The server identity is
fixed by the gateway; the script path fills `SCRIPT_NAME`; request-optional
variables take the empty string per the §4.1 `"" | ...` productions. -/
def deployReq (script : String) : Req :=
  { requestMethod  := "GET"
    scriptName     := script
    serverName     := "drorb"
    serverPort     := "80"
    serverProtocol := "HTTP/1.1"
    serverSoftware := "drorb/0.1"
    gatewayInterface := "CGI/1.1"
    remoteAddr     := "127.0.0.1" }

/-! ### Parsing the script's response (RFC 3875 §6) -/

/-- ASCII-lowercase a header name for case-insensitive comparison (§6.3 field
names are case-insensitive). -/
def lowerAscii (s : String) : String :=
  String.mk (s.toList.map Char.toLower)

/-- The leading status code of a `Status:` value (`"302 Found" ↦ some 302`). -/
def firstNat (v : String) : Option Nat :=
  match v.trim.splitOn " " with
  | s :: _ => s.toNat?
  | []     => none

/-- Split the script's raw output into its header block and body at the first
blank line (RFC 3875 §6: the CGI header fields are terminated by an empty line;
the remainder is the response body). Handles `LF LF`, `CRLF CRLF`, and the mixed
`LF CRLF` boundary; a body-less output yields an empty body. Total. -/
def splitHead (rem : List UInt8) (pre : List UInt8) : List UInt8 × List UInt8 :=
  match rem with
  | 10 :: 10 :: rest             => (pre.reverse, rest)
  | 13 :: 10 :: 13 :: 10 :: rest => (pre.reverse, rest)
  | 10 :: 13 :: 10 :: rest       => (pre.reverse, rest)
  | b :: rest                    => splitHead rest (b :: pre)
  | []                           => (pre.reverse, [])

/-- Parse the header block bytes into the three CGI header fields (§6.3.1–§6.3.3:
Content-Type, Location, Status). Each line is `Name: Value`; the value keeps
every byte after the first `:` (so a `Location: http://h/p` URL survives), then
is OWS-trimmed. Unknown fields are ignored per the documented boundary. -/
def parseHeaders (head : List UInt8) : ScriptOut :=
  let text := String.mk (head.map (fun x => Char.ofNat x.toNat))
  let rawLines := text.splitOn "\n"
  let lines := rawLines.map (fun l => if l.endsWith "\r" then l.dropRight 1 else l)
  lines.foldl (fun acc line =>
    match line.splitOn ":" with
    | name :: rest =>
      let v := (String.intercalate ":" rest).trim
      let nl := lowerAscii name.trim
      if nl == "content-type" then { acc with contentType := some v }
      else if nl == "location" then { acc with location := some v }
      else if nl == "status" then { acc with status := firstNat v }
      else acc
    | [] => acc) ({} : ScriptOut)

/-- Reason-phrase bytes for the CGI-derived HTTP statuses. -/
def reasonPhrase (st : Nat) : Bytes :=
  (if st == 200 then "OK"
   else if st == 302 then "Found"
   else if st == 500 then "Internal Server Error"
   else if st == 502 then "Bad Gateway"
   else "").toUTF8.toList

/-- Header name/value as wire bytes. -/
private def hdr (name value : String) : Bytes × Bytes :=
  (name.toUTF8.toList, value.toUTF8.toList)

/-- Frame a classified CGI response (RFC 3875 §6.2) into the deployed HTTP
`Reactor.Response`: document → its status + Content-Type + body; client redirect
→ 302 + Location; client redirect with document → its status + Content-Type +
Location + body; local redirect → 200 (reprocessed internally, modeled empty);
malformed (`none`) → 502. -/
def respOf : Option CgiResp → Reactor.Response
  | some (.document ct st body) =>
    { status := st, reason := reasonPhrase st,
      headers := [hdr "Content-Type" ct], body := body }
  | some (.clientRedirect loc) =>
    { status := 302, reason := reasonPhrase 302,
      headers := [hdr "Location" loc], body := [] }
  | some (.clientRedirectDoc loc st ct body) =>
    { status := st, reason := reasonPhrase st,
      headers := [hdr "Content-Type" ct, hdr "Location" loc], body := body }
  | some (.localRedirect _) =>
    { status := 200, reason := reasonPhrase 200, headers := [], body := [] }
  | none =>
    { status := 502, reason := reasonPhrase 502, headers := [],
      body := "cgi: no CGI header field in script output".toUTF8.toList }

/-- **`serveCgi` — the deployed CGI handler (RFC 3875 §7 + §6.2).** Build the
§4.1 meta-variable environment for `script`, run the script as a real child
process under that environment (the `execBytes` shim), split its output into the
CGI header block and body (§6), classify the header block (§6.2), and frame the
result as the HTTP response. This is the function the deployed route dispatches;
it genuinely spawns a process and returns the script's stdout. -/
def serveCgi (script : String) : Reactor.Response :=
  let out := (execBytes script (envBlockOf (envList (deployReq script)))
                ByteArray.empty).toList
  let (head, body) := splitHead out []
  respOf (classify { parseHeaders head with body := body })

/-! ### Facts about the deployed handler (pure parts; the spawn is opaque) -/

/-- The environment the deployed handler installs is the complete RFC 3875 §4.1
environment: 17 meta-variables, every one mapped (`envList_length`). -/
theorem deploy_env_complete (script : String) :
    (envList (deployReq script)).length = 17 := envList_length _

/-- The deployed handler installs `SCRIPT_NAME` = the script path and
`GATEWAY_INTERFACE` = `CGI/1.1` (§4.1.4/§4.1.13). -/
theorem deploy_env_scriptName (script : String) :
    env (deployReq script) .scriptName = script
    ∧ env (deployReq script) .gatewayInterface = "CGI/1.1" := ⟨rfl, rfl⟩

/-- An empty header block followed by a blank line splits to an empty header and
the whole remainder as body (RFC 3875 §6). -/
theorem splitHead_blank_first (body : List UInt8) :
    splitHead (10 :: 10 :: body) [] = ([], body) := rfl

end Cgi
