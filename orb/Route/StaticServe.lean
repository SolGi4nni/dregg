/-
# Route.StaticServe — the DEPLOYED static-file route, as a byte-exact wire spec

The running server serves a `GET /static/<path>` by STREAMING a file out of a
configured document root: a batch-small response head (status line + headers,
including `Content-Length`) followed by the file body copied block-by-block. This
module is the byte-exact specification of that emitted wire and the three
properties the route owes:

  * **`static_serves_bytes`** — a `GET` whose resolved target names a regular file
    is answered `200 OK` with the head carrying the right `Content-Type` and a
    `Content-Length` that is EXACTLY the served body length, followed by the file
    bytes verbatim (the body is a suffix of the wire).
  * **`static_404_missing`** — a target that resolves to no regular file is a
    small `404 Not Found`.
  * **`static_no_traversal`** — a `..`-laden (or percent-encoded `..`) target
    cannot escape the document root: the resolved path keeps the root as a prefix
    even under a filesystem walker that actually pops a component on `..`.

## Grounding

The path resolution is the shared traversal discipline `Safety.Traversal.serveStatic`
— percent-decode each segment EXACTLY once (percent-decode is not idempotent, so
`%252e%252e` cannot be double-decoded into `..`), remove dot-segments with `..`
clamped at the root, then join under the document root. This is precisely the
discipline the deployed host resolver realizes (single-decode, `..`-pop clamped at
the empty relative root, root re-checked as a prefix); the model is a sound
path-algebra under-approximation of it — the host's additional canonicalize +
symlink re-check only strengthens confinement.

The head/status/`Content-Type`/`Content-Length`/`404` byte shapes are the exact
bytes the deployed static lane writes: the status line, the `Connection`,
`Accept-Ranges: bytes`, `Content-Type`, and `Content-Length` header lines, the
blank-line separator, then the body — reassembled from the head chunk and the
paced file chunks the host streams.

Everything filesystem-shaped enters as an uninterpreted total field `fs`
(resolved path → optional regular-file bytes): the theorems hold uniformly over
every disk. No crypto is touched anywhere in this module.
-/

import Safety.Traversal

namespace Route.StaticServe

/-- Raw bytes on the wire. -/
abbrev Bytes := List UInt8

/-- UTF-8 bytes of a string (header names/values, status lines, file contents). -/
def strBytes (s : String) : Bytes := s.toUTF8.toList

/-- `CRLF`. -/
def crlf : Bytes := strBytes "\r\n"

/-- Decimal ASCII of a natural number — the host's `len.to_string()`. -/
def decimal (n : Nat) : Bytes := strBytes (toString n)

/-! ## The header blocks the deployed lane writes -/

/-- The `200 OK` status line the host writes for a served file. -/
def statusLine200 : Bytes := strBytes "HTTP/1.1 200 OK\r\n"

/-- The `404 Not Found` status line the host writes for a missing target. -/
def statusLine404 : Bytes := strBytes "HTTP/1.1 404 Not Found\r\n"

/-- The `Connection` header the host emits, matching the client's keep-alive
intent. -/
def connHeader (keepAlive : Bool) : Bytes :=
  strBytes (if keepAlive then "Connection: keep-alive\r\n" else "Connection: close\r\n")

/-- `Accept-Ranges: bytes` — the host advertises range support on a static file. -/
def acceptRanges : Bytes := strBytes "Accept-Ranges: bytes\r\n"

/-- The `Content-Type: <ctype>` header line. -/
def ctBlock (ctype : Bytes) : Bytes := strBytes "Content-Type: " ++ ctype ++ crlf

/-- The `Content-Length: <n>` header line — `n` is the served body length. -/
def clBlock (len : Nat) : Bytes := strBytes "Content-Length: " ++ decimal len ++ crlf

/-- The `Content-Type` value the host selects from a file extension — the deployed
`content_type` map; the default is `application/octet-stream`. -/
def contentType : String → Bytes
  | "html" | "htm"  => strBytes "text/html; charset=utf-8"
  | "css"           => strBytes "text/css; charset=utf-8"
  | "js"  | "mjs"   => strBytes "application/javascript"
  | "json"          => strBytes "application/json"
  | "svg"           => strBytes "image/svg+xml"
  | "png"           => strBytes "image/png"
  | "jpg" | "jpeg"  => strBytes "image/jpeg"
  | "gif"           => strBytes "image/gif"
  | "webp"          => strBytes "image/webp"
  | "ico"           => strBytes "image/x-icon"
  | "txt"           => strBytes "text/plain; charset=utf-8"
  | "wasm"          => strBytes "application/wasm"
  | "pdf"           => strBytes "application/pdf"
  | "mp4"           => strBytes "video/mp4"
  | "woff2"         => strBytes "font/woff2"
  | _               => strBytes "application/octet-stream"

/-- **The `200` response head** the host writes before streaming a file body:
status line, `Connection`, `Accept-Ranges`, `Content-Type`, `Content-Length`, then
the blank-line separator. -/
def okHead (ctype : Bytes) (len : Nat) (keepAlive : Bool) : Bytes :=
  statusLine200 ++ connHeader keepAlive ++ acceptRanges
    ++ ctBlock ctype ++ clBlock len ++ crlf

/-- **The `404 Not Found`** the host writes for a missing / escaping / non-regular
target: the status line, `Connection`, a 9-byte `not found` body. -/
def notFoundResp (keepAlive : Bool) : Bytes :=
  statusLine404 ++ connHeader keepAlive ++ strBytes "Content-Length: 9\r\n\r\nnot found"

/-! ## Path resolution (the traversal boundary) -/

/-- Resolve a request target under a document root: the shared traversal
discipline — decode once, remove dot-segments (`..` clamped at the root), join
under the root. This is what the deployed host resolver realizes. -/
def resolve (root target : List String) : List String :=
  Safety.Traversal.serveStatic root target

/-! ## The deployed static handler, as a byte function -/

/-- **The deployed static-file wire.** Resolve the target under the root; a
regular file is `200 OK` head ++ body (head only on `HEAD`); no regular file is a
`404`. `fs` is the filesystem boundary (resolved path → optional bytes); `ext` is
the resolved file's extension (drives `Content-Type`). -/
def serveWire (root target : List String) (fs : List String → Option Bytes)
    (ext : String) (keepAlive isHead : Bool) : Bytes :=
  match fs (resolve root target) with
  | some body => okHead (contentType ext) body.length keepAlive ++ (if isHead then [] else body)
  | none      => notFoundResp keepAlive

/-! ## Theorems -/

/-- **`static_serves_bytes`.** A `GET` whose resolved target names a regular file
of bytes `body` is answered:
  * the full wire is exactly the `200` head followed by `body`;
  * the `Content-Type: <contentType ext>` header line is present on the wire;
  * the `Content-Length: <body.length>` header line is present — the framed length
    is EXACTLY the number of bytes served;
  * `body` is a suffix of the wire — the file bytes are served verbatim, nothing
    trailing them. -/
theorem static_serves_bytes (root target : List String)
    (fs : List String → Option Bytes) (ext : String) (keepAlive : Bool)
    (body : Bytes) (hfile : fs (resolve root target) = some body) :
    serveWire root target fs ext keepAlive false
        = okHead (contentType ext) body.length keepAlive ++ body
    ∧ ctBlock (contentType ext) <:+: serveWire root target fs ext keepAlive false
    ∧ clBlock body.length <:+: serveWire root target fs ext keepAlive false
    ∧ body <:+ serveWire root target fs ext keepAlive false := by
  have heq : serveWire root target fs ext keepAlive false
      = okHead (contentType ext) body.length keepAlive ++ body := by
    simp only [serveWire, hfile]
    rfl
  refine ⟨heq, ?_, ?_, ?_⟩
  · -- Content-Type header line is an infix of the wire.
    rw [heq]
    exact ⟨statusLine200 ++ connHeader keepAlive ++ acceptRanges,
           clBlock body.length ++ crlf ++ body,
           by simp only [okHead, List.append_assoc]⟩
  · -- Content-Length header line (carrying body.length) is an infix of the wire.
    rw [heq]
    exact ⟨statusLine200 ++ connHeader keepAlive ++ acceptRanges ++ ctBlock (contentType ext),
           crlf ++ body,
           by simp only [okHead, List.append_assoc]⟩
  · -- The body is a suffix of the wire.
    rw [heq]
    exact List.suffix_append _ _

/-- **`static_404_missing`.** A target that resolves to no regular file is the
deployed `404 Not Found` — for a `GET` or a `HEAD`, and the wire opens with the
`404` status line. -/
theorem static_404_missing (root target : List String)
    (fs : List String → Option Bytes) (ext : String) (keepAlive isHead : Bool)
    (hmiss : fs (resolve root target) = none) :
    serveWire root target fs ext keepAlive isHead = notFoundResp keepAlive
    ∧ statusLine404 <+: serveWire root target fs ext keepAlive isHead := by
  have heq : serveWire root target fs ext keepAlive isHead = notFoundResp keepAlive := by
    simp only [serveWire, hmiss]
  refine ⟨heq, ?_⟩
  rw [heq]
  exact ⟨connHeader keepAlive ++ strBytes "Content-Length: 9\r\n\r\nnot found",
         by simp only [notFoundResp, List.append_assoc]⟩

/-- **`static_no_traversal`.** No request target — however many literal or
percent-encoded `..` it carries — escapes the document root. The resolved path
keeps a clean root as a prefix even under `Route.Path.descend`, a filesystem
walker that actually POPS a component on `..`: the attacker's `..` was removed at
the decode-once boundary, so no pop ever fires above the root. -/
theorem static_no_traversal (root target : List String)
    (hclean : ∀ s ∈ root, ¬ Route.Path.IsDot s) :
    root <+: Route.Path.descend [] (resolve root target) :=
  Safety.Traversal.serveStatic_no_escape root target hclean

/-- The structural companion: the root is a prefix of the resolved path itself,
for EVERY target (the join never drops the root). -/
theorem static_root_prefix (root target : List String) :
    root <+: resolve root target :=
  Safety.Traversal.serveStatic_root_prefix root target

/-- **Concrete adversarial witness.** A literal `../../etc/passwd` under
`/srv/www` is clamped to `/srv/www/etc/passwd` — it stays strictly under the root
rather than climbing to `/etc/passwd`. -/
theorem static_dotdot_confined :
    resolve ["srv", "www"] ["..", "..", "etc", "passwd"]
      = ["srv", "www", "etc", "passwd"] := by decide

/-- **Concrete double-encoded witness.** A double-encoded `%252e%252e` decodes
ONCE to the harmless literal `%2e%2e` (an ordinary filename component, not a
dot-segment), so it stays strictly under the root and never collapses to `..`. -/
theorem static_double_encoded_confined :
    resolve ["srv", "www"] ["%252e%252e", "etc", "passwd"]
      = ["srv", "www", "%2e%2e", "etc", "passwd"] := by decide

/-! ## Live selftest — the deployed static wire on a concrete file (NO crypto FFI)

Builds the exact bytes the deployed static lane emits for a concrete
`GET /static/hello.txt` over a one-file document root, asserts the four
`static_serves_bytes` facts hold on those concrete bytes, and prints the wire so
it can be byte-compared against the running server's `curl` output. -/

/-- The concrete served file for the live selftest. -/
def helloBody : Bytes := strBytes "hi from drorb static\n"

/-- A one-file document boundary: the resolved `/static/hello.txt` names `helloBody`,
everything else is absent. -/
def helloFS (root target : List String) : List String → Option Bytes :=
  fun p => if p = resolve root target then some helloBody else none

def main : IO Unit := do
  let root := ["srv", "www"]
  let target := ["static", "hello.txt"]
  let fs := helloFS root target
  let wire := serveWire root target fs "txt" false false
  let expected := okHead (contentType "txt") helloBody.length false ++ helloBody
  IO.println s!"[selftest] served wire = {wire.length} bytes"
  IO.println s!"[selftest] Content-Length = {helloBody.length}"
  -- The head, as text, for eyeballing against curl -i output.
  let headLen := (okHead (contentType "txt") helloBody.length false).length
  IO.println "[selftest] --- emitted head ---"
  IO.println (String.fromUTF8! ⟨(wire.take headLen).toArray⟩)
  IO.println "[selftest] --- end head ---"
  if wire ≠ expected then throw (IO.userError "wire ≠ okHead ++ body")
  -- A missing file is a 404.
  let miss := serveWire root ["static", "nope.txt"] fs "txt" false false
  if miss ≠ notFoundResp false then throw (IO.userError "missing ≠ 404")
  IO.println "[selftest] OK: 200 head++body exact; missing→404; static_serves_bytes facts hold"

end Route.StaticServe

/-- Top-level entry so `lake env lean --run Route/StaticServe.lean` runs the live
selftest (`Route.StaticServe.main`). NO crypto FFI is touched. -/
def main : IO Unit := Route.StaticServe.main

#print axioms Route.StaticServe.static_serves_bytes
#print axioms Route.StaticServe.static_404_missing
#print axioms Route.StaticServe.static_no_traversal
#print axioms Route.StaticServe.static_root_prefix
#print axioms Route.StaticServe.static_dotdot_confined
#print axioms Route.StaticServe.static_double_encoded_confined
