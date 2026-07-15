import Reactor.ServeStep

/-!
# Reactor.ProxyForwardHead — hop-by-hop header stripping on the proxy REQUEST path (RFC 9110 §7.6.1)

Before this file, the reverse proxy forwarded the client's request head to the chosen
upstream VERBATIM (`proxy_dial::forward` / `dial_and_read_head` wrote `req` unchanged). That
violates RFC 9110 §7.6.1: an intermediary MUST NOT forward the connection-scoped
("hop-by-hop") header fields — `Connection`, `Keep-Alive`, `Proxy-Authenticate`,
`Proxy-Authorization`, `TE`, `Trailer`, `Transfer-Encoding`, `Upgrade` — nor any field NAMED
in the `Connection` header, to the next hop. Leaking them corrupts framing (a stale
`Transfer-Encoding` / `Keep-Alive`), leaks proxy credentials, and is the request-side arm of
the proxy conformance differential.

This module is the proven SPEC for the transform the host applies on the forward path. It is
a byte-level `Bytes → Bytes` (`stripHopByHop`), so the Rust host computes byte-identical
output (parity by construction): it splits the request at the first CRLFCRLF, keeps the
request line unchanged, drops every header line whose (case-insensitive) name is a fixed
hop-by-hop field OR a token listed in a `Connection` header, and re-emits the surviving
headers followed by the body verbatim.

## What is proven (REAL, non-vacuous)

* `stripped_survivor_not_dropped` — **the RFC guarantee**: every header line that SURVIVES
  the strip has a non-dropped name (not a fixed hop field, not a `Connection` token). The
  forwarded head carries no hop-by-hop field.
* `hop_named_line_removed` — any header line whose name is one of the eight fixed hop-by-hop
  fields is removed (never in the survivor set), for ANY request.
* `endToEnd_line_preserved` — an end-to-end header (name not in the drop set) survives
  VERBATIM (same bytes, no rewrite).
* `reqLine_isPrefix` / `body_isSuffix` — the request line (method/target/version) is a prefix
  and the body is a suffix of the forwarded bytes: the proxy alters neither the request
  target nor the payload, only the header block between them.
* `demo_strip` — a concrete request with `Connection: keep-alive, X-Trace`, an `X-Trace`
  header (a `Connection`-named token), and a `Keep-Alive` header: the forwarded bytes are
  exactly the request with all three removed and `Host` / `Accept` / body kept — the full
  pipeline including `Connection`-token expansion, computed to the byte.

Axiom footprint of the general theorems ⊆ `{propext, Quot.sound}`; the concrete `demo_strip`
depends on none (`decide`).
-/

namespace Reactor.ProxyForward

open Proto (Bytes)
open Reactor.ServeStep (splitHeadBody splitCRLFLines beforeColon afterColon lowerByte
  trimLeadingSpace)

/-! ## Header-name normalisation -/

/-- The lowercased header NAME of a header line: the bytes before the first colon, ASCII
lowercased. `"Connection: keep-alive"` ↦ `"connection"`. -/
def headerNameLower (line : Bytes) : Bytes := (beforeColon line).map lowerByte

/-! ## The fixed hop-by-hop field names (RFC 9110 §7.6.1), lowercase -/

/-- The connection-scoped header names an intermediary MUST NOT forward, lowercase
(the eight RFC 9110 §7.6.1 fields plus the legacy `Proxy-Connection`).
Written as raw bytes so every proof reduces without touching `String.toUTF8`. -/
def hopByHopNames : List Bytes :=
  [ [99, 111, 110, 110, 101, 99, 116, 105, 111, 110]                       -- connection
  , [107, 101, 101, 112, 45, 97, 108, 105, 118, 101]                       -- keep-alive
  , [112, 114, 111, 120, 121, 45, 97, 117, 116, 104, 101, 110, 116, 105, 99, 97, 116, 101]      -- proxy-authenticate
  , [112, 114, 111, 120, 121, 45, 97, 117, 116, 104, 111, 114, 105, 122, 97, 116, 105, 111, 110]-- proxy-authorization
  , [116, 101]                                                             -- te
  , [116, 114, 97, 105, 108, 101, 114]                                     -- trailer
  , [116, 114, 97, 110, 115, 102, 101, 114, 45, 101, 110, 99, 111, 100, 105, 110, 103]           -- transfer-encoding
  , [117, 112, 103, 114, 97, 100, 101]
  , [112, 114, 111, 120, 121, 45, 99, 111, 110, 110, 101, 99, 116, 105, 111, 110] ]                                   -- upgrade

/-! ## `Connection`-token expansion -/

/-- Split bytes on commas (`44`). Never empty (base case `[[]]`), the shape of
`splitCRLFLines`. -/
def splitCommas : Bytes → List Bytes
  | [] => [[]]
  | 44 :: rest => [] :: splitCommas rest
  | b :: rest =>
    match splitCommas rest with
    | [] => [[b]]
    | t :: ts => (b :: t) :: ts

/-- Drop leading ASCII SP (`32`) / HTAB (`9`). -/
def trimLeadingOWS : Bytes → Bytes
  | 32 :: rest => trimLeadingOWS rest
  | 9 :: rest => trimLeadingOWS rest
  | bs => bs

/-- Trim ASCII OWS (SP/HTAB) from both ends. -/
def trimOWS (b : Bytes) : Bytes := (trimLeadingOWS (trimLeadingOWS b).reverse).reverse

/-- Normalise one `Connection` token: trim OWS, lowercase. -/
def normToken (b : Bytes) : Bytes := (trimOWS b).map lowerByte

/-- The header name `"connection"` (lowercase), as raw bytes. -/
def connectionName : Bytes := [99, 111, 110, 110, 101, 99, 116, 105, 111, 110]

/-- The set of field names listed across all `Connection` header lines of a header block:
each `Connection` value split on commas, each token OWS-trimmed and lowercased, empties
dropped. These names are ALSO hop-by-hop for this hop (RFC 9110 §7.6.1). -/
def connectionTokens (hlines : List Bytes) : List Bytes :=
  hlines.foldr
    (fun line acc =>
      if headerNameLower line == connectionName then
        ((splitCommas (afterColon line)).map normToken).filter (· ≠ []) ++ acc
      else acc)
    []

/-! ## The strip -/

/-- The full set of header names to drop from the forwarded request: the eight fixed
hop-by-hop fields plus every token named in a `Connection` header. -/
def dropSet (hlines : List Bytes) : List Bytes := hopByHopNames ++ connectionTokens hlines

/-- Is this header line's name in the drop set? Decided over `Bytes` membership (so
`dropName drop line = false ↔ headerNameLower line ∉ drop`). -/
def dropName (drop : List Bytes) (line : Bytes) : Bool := decide (headerNameLower line ∈ drop)

/-- Keep a header line iff its name is NOT dropped. -/
def keepLine (drop : List Bytes) (line : Bytes) : Bool := ! dropName drop line

/-- CRLF-join header lines (inverse of `splitCRLFLines` on a well-formed head). -/
def joinCRLF : List Bytes → Bytes
  | [] => []
  | [l] => l
  | l :: ls => l ++ [13, 10] ++ joinCRLF ls

/-- The surviving header lines after the strip: the request head split into lines, the
request line kept, the header lines with a dropped name removed. -/
def survivors (head : Bytes) : List Bytes :=
  match splitCRLFLines head with
  | [] => []
  | _ :: hlines => hlines.filter (keepLine (dropSet hlines))

/-- **The forwarded request HEAD** with hop-by-hop headers stripped: keep the request line,
drop every hop-by-hop / `Connection`-named header, rejoin with CRLF. -/
def stripHopByHopHead (head : Bytes) : Bytes :=
  match splitCRLFLines head with
  | [] => head
  | reqLine :: hlines => joinCRLF (reqLine :: hlines.filter (keepLine (dropSet hlines)))

/-- **The forwarded request** with hop-by-hop headers stripped: strip the head, restore the
CRLFCRLF separator, and append the body VERBATIM. This is the exact `Bytes → Bytes` the host
applies before writing the request to the upstream socket. -/
def stripHopByHop (req : Bytes) : Bytes :=
  let (head, body) := splitHeadBody req
  stripHopByHopHead head ++ [13, 10, 13, 10] ++ body

/-! ## The RFC 9110 §7.6.1 guarantees -/

/-- **The RFC guarantee (survivor direction).** Every header line that survives the strip
has a name that is NOT in the drop set — so the forwarded head carries no fixed hop-by-hop
field and no `Connection`-named field. -/
theorem stripped_survivor_not_dropped (head line : Bytes)
    (hmem : line ∈ survivors head) :
    ∀ (reqLine : Bytes) (hlines : List Bytes),
      splitCRLFLines head = reqLine :: hlines → headerNameLower line ∉ dropSet hlines := by
  intro reqLine hlines hsplit
  rw [survivors, hsplit] at hmem
  have hkeep : keepLine (dropSet hlines) line = true := (List.mem_filter.mp hmem).2
  have hdrop : dropName (dropSet hlines) line = false := by
    simpa [keepLine] using hkeep
  simpa [dropName, decide_eq_false_iff_not] using hdrop

/-- **Hop-by-hop fields are removed.** A header line whose name is one of the eight fixed
hop-by-hop fields is never in the survivor set — it is dropped for ANY request. -/
theorem hop_named_line_removed (line : Bytes) (hlines : List Bytes)
    (hname : headerNameLower line ∈ hopByHopNames) :
    line ∉ hlines.filter (keepLine (dropSet hlines)) := by
  intro hmem
  have hkeep : keepLine (dropSet hlines) line = true := (List.mem_filter.mp hmem).2
  have hin : headerNameLower line ∈ dropSet hlines :=
    List.mem_append.mpr (Or.inl hname)
  have hdrop : dropName (dropSet hlines) line = true := by
    simpa [dropName, decide_eq_true_iff] using hin
  simp [keepLine, hdrop] at hkeep

/-- **End-to-end headers are preserved verbatim.** A header line present in the request
whose name is NOT in the drop set survives the strip unchanged (same bytes). -/
theorem endToEnd_line_preserved (line : Bytes) (hlines : List Bytes)
    (hin : line ∈ hlines)
    (hkeep : headerNameLower line ∉ dropSet hlines) :
    line ∈ hlines.filter (keepLine (dropSet hlines)) := by
  rw [List.mem_filter]
  refine ⟨hin, ?_⟩
  have : dropName (dropSet hlines) line = false := by
    simpa [dropName, decide_eq_false_iff_not] using hkeep
  simp [keepLine, this]

/-! ## The request line and body are untouched -/

/-- `joinCRLF (a :: as)` begins with `a`. -/
theorem joinCRLF_prefix (a : Bytes) (as : List Bytes) : a <+: joinCRLF (a :: as) := by
  cases as with
  | nil => simp [joinCRLF]
  | cons b bs => exact ⟨[13, 10] ++ joinCRLF (b :: bs), by simp [joinCRLF, List.append_assoc]⟩

/-- **The request line is a prefix of the forwarded head.** The proxy never rewrites the
method / target / version — only the header block after it. -/
theorem reqLine_isPrefix (head reqLine : Bytes) (hlines : List Bytes)
    (hsplit : splitCRLFLines head = reqLine :: hlines) :
    reqLine <+: stripHopByHopHead head := by
  rw [stripHopByHopHead, hsplit]
  exact joinCRLF_prefix reqLine _

/-- **The body is a suffix of the forwarded request.** The proxy forwards the payload
verbatim; the strip touches only the header block. -/
theorem body_isSuffix (req : Bytes) : (splitHeadBody req).2 <:+ stripHopByHop req := by
  rw [stripHopByHop]
  exact List.suffix_append _ _

/-! ## Concrete end-to-end witness -/

/-- A request with a `Connection: keep-alive, X-Trace` header (naming the token `X-Trace`),
an `X-Trace` header, and a `Keep-Alive` header, plus end-to-end `Host` / `Accept` and a body. -/
def demoReq : Bytes :=
  [71, 69, 84, 32, 47, 97, 112, 105, 32, 72, 84, 84, 80, 47, 49, 46, 49, 13, 10, 72, 111, 115,
   116, 58, 32, 101, 46, 120, 13, 10, 67, 111, 110, 110, 101, 99, 116, 105, 111, 110, 58, 32,
   107, 101, 101, 112, 45, 97, 108, 105, 118, 101, 44, 32, 88, 45, 84, 114, 97, 99, 101, 13,
   10, 88, 45, 84, 114, 97, 99, 101, 58, 32, 97, 98, 99, 13, 10, 75, 101, 101, 112, 45, 65,
   108, 105, 118, 101, 58, 32, 116, 105, 109, 101, 111, 117, 116, 61, 53, 13, 10, 65, 99, 99,
   101, 112, 116, 58, 32, 42, 47, 42, 13, 10, 13, 10, 66, 79, 68, 89]

/-- The forwarded request: `Connection` (fixed hop), `Keep-Alive` (fixed hop), and `X-Trace`
(a `Connection`-named token) removed; `Host`, `Accept`, and the body kept verbatim. -/
def demoForwarded : Bytes :=
  [71, 69, 84, 32, 47, 97, 112, 105, 32, 72, 84, 84, 80, 47, 49, 46, 49, 13, 10, 72, 111, 115,
   116, 58, 32, 101, 46, 120, 13, 10, 65, 99, 99, 101, 112, 116, 58, 32, 42, 47, 42, 13, 10,
   13, 10, 66, 79, 68, 89]

/-- **The strip, computed to the byte.** `Connection`, `Keep-Alive`, and the
`Connection`-named `X-Trace` are all gone; `Host`, `Accept`, and the body survive. -/
theorem demo_strip : stripHopByHop demoReq = demoForwarded := by decide

/-! ## Proxy identity headers: `Via` and `X-Forwarded-For` (RFC 9110 §7.6.3 / §7.6.2)

An intermediary announces itself with a `Via` field on BOTH the forwarded request
and the returned response (RFC 9110 §7.6.3), and records the client's address in
`X-Forwarded-For` on the forwarded request (RFC 9110 §7.6.2, de-facto). These are
proven `Bytes`-level insertions layered on top of the hop-by-hop strip, so the host
computes byte-identical output. -/

/-- The proxy's protocol-and-pseudonym token for `Via`: `1.1 drorb` (HTTP version
`1.1`, received-by pseudonym `drorb`). Raw bytes. -/
def viaToken : Bytes :=
  [49, 46, 49, 32, 100, 114, 111, 114, 98]                                   -- "1.1 drorb"

/-- A `Via: 1.1 drorb` header line (RFC 9110 §7.6.3). Raw bytes. -/
def viaLine : Bytes :=
  [86, 105, 97, 58, 32] ++ viaToken                                          -- "Via: " ++ token

/-- The `X-Forwarded-For: ` field-name-and-separator prefix. Raw bytes. -/
def xffPrefix : Bytes :=
  [88, 45, 70, 111, 114, 119, 97, 114, 100, 101, 100, 45, 70, 111, 114, 58, 32] -- "X-Forwarded-For: "

/-- An `X-Forwarded-For: <ip>` header line for a client address `ip`. -/
def xffLine (ip : Bytes) : Bytes := xffPrefix ++ ip

/-- The `X-Forwarded-For` line to prepend, or nothing when the host supplied no
client address (`ip = []`): a header with an empty value is never emitted. -/
def xffLines (ip : Bytes) : List Bytes := if ip = [] then [] else [xffLine ip]

/-- The forwarded request header LINES: the request line, the proxy `Via`, the
`X-Forwarded-For` (when a client address is known), then the client's surviving
end-to-end headers (hop-by-hop stripped, exactly the `stripHopByHop` survivors). -/
def forwardReqLines (ip reqLine : Bytes) (hlines : List Bytes) : List Bytes :=
  reqLine :: viaLine :: (xffLines ip ++ hlines.filter (keepLine (dropSet hlines)))

/-- **The forwarded request HEAD**: hop-by-hop stripped, `Via` and
`X-Forwarded-For` added, rejoined with CRLF. -/
def forwardReqHead (ip head : Bytes) : Bytes :=
  match splitCRLFLines head with
  | [] => head
  | reqLine :: hlines => joinCRLF (forwardReqLines ip reqLine hlines)

/-- **The forwarded request**: strip + annotate the head, restore the CRLFCRLF
separator, append the body VERBATIM. The exact `Bytes → Bytes` the host writes to
the upstream socket. -/
def forwardReq (ip req : Bytes) : Bytes :=
  let (head, body) := splitHeadBody req
  forwardReqHead ip head ++ [13, 10, 13, 10] ++ body

/-- Structural unfold of `forwardReqHead` on a well-formed head. -/
theorem forwardReqHead_cons (ip head reqLine : Bytes) (hlines : List Bytes)
    (hsplit : splitCRLFLines head = reqLine :: hlines) :
    forwardReqHead ip head = joinCRLF (forwardReqLines ip reqLine hlines) := by
  rw [forwardReqHead, hsplit]

/-- **`Via` is on the forwarded request.** The proxy always announces itself. -/
theorem forward_via_line (ip reqLine : Bytes) (hlines : List Bytes) :
    viaLine ∈ forwardReqLines ip reqLine hlines := by
  simp [forwardReqLines]

/-- **`X-Forwarded-For` is on the forwarded request** whenever the host knows the
client address. -/
theorem forward_xff_line (ip reqLine : Bytes) (hlines : List Bytes) (hip : ip ≠ []) :
    xffLine ip ∈ forwardReqLines ip reqLine hlines := by
  simp [forwardReqLines, xffLines, hip]

/-- **Hop-by-hop is still stripped after annotation.** Every SURVIVING client
header line (the filtered tail, past the added `Via`/`X-Forwarded-For`) has a name
NOT in the drop set — adding the identity headers does not reintroduce a
connection-scoped field. -/
theorem forward_survivor_not_dropped (ip reqLine line : Bytes) (hlines : List Bytes)
    (hmem : line ∈ hlines.filter (keepLine (dropSet hlines))) :
    headerNameLower line ∉ dropSet hlines := by
  have hkeep : keepLine (dropSet hlines) line = true := (List.mem_filter.mp hmem).2
  have hdrop : dropName (dropSet hlines) line = false := by simpa [keepLine] using hkeep
  simpa [dropName, decide_eq_false_iff_not] using hdrop

/-- **The request line is a prefix of the forwarded head** — method/target/version
untouched. -/
theorem forward_reqLine_isPrefix (ip head reqLine : Bytes) (hlines : List Bytes)
    (hsplit : splitCRLFLines head = reqLine :: hlines) :
    reqLine <+: forwardReqHead ip head := by
  rw [forwardReqHead_cons ip head reqLine hlines hsplit, forwardReqLines]
  exact joinCRLF_prefix reqLine _

/-- **The body is a suffix of the forwarded request** — payload untouched. -/
theorem forward_body_isSuffix (ip req : Bytes) : (splitHeadBody req).2 <:+ forwardReq ip req := by
  rw [forwardReq]
  exact List.suffix_append _ _

/-! ## Response-side hop-by-hop stripping + `Via` (RFC 9110 §7.6.1 / §7.6.3)

An upstream reply carries connection-scoped headers meant for the upstream↔proxy
hop (`Connection`, `Keep-Alive`, …). The intermediary MUST strip them and manage
the client connection itself, and announces itself with `Via` on the response too.
`Transfer-Encoding` is DELIBERATELY preserved: the proxy forwards a chunked
response body with its framing intact, so removing `Transfer-Encoding` without
de-chunking would unframe the body — it is kept, not stripped. -/

/-- The connection-scoped names to strip from an UPSTREAM RESPONSE: the fixed
hop-by-hop fields EXCEPT `transfer-encoding` (preserved for pass-through framing). -/
def respHopByHopNames : List Bytes :=
  [ [99, 111, 110, 110, 101, 99, 116, 105, 111, 110]                        -- connection
  , [107, 101, 101, 112, 45, 97, 108, 105, 118, 101]                        -- keep-alive
  , [112, 114, 111, 120, 121, 45, 97, 117, 116, 104, 101, 110, 116, 105, 99, 97, 116, 101]      -- proxy-authenticate
  , [112, 114, 111, 120, 121, 45, 97, 117, 116, 104, 111, 114, 105, 122, 97, 116, 105, 111, 110]-- proxy-authorization
  , [116, 101]                                                              -- te
  , [116, 114, 97, 105, 108, 101, 114]                                      -- trailer
  , [117, 112, 103, 114, 97, 100, 101]
  , [112, 114, 111, 120, 121, 45, 99, 111, 110, 110, 101, 99, 116, 105, 111, 110] ]                                    -- upgrade

/-- The full response drop set: the response hop-by-hop names plus every token
named in a `Connection` header of the reply. -/
def respDropSet (hlines : List Bytes) : List Bytes := respHopByHopNames ++ connectionTokens hlines

/-- The `transfer-encoding` header name, lowercase, raw bytes. -/
def transferEncodingName : Bytes :=
  [116, 114, 97, 110, 115, 102, 101, 114, 45, 101, 110, 99, 111, 100, 105, 110, 103]

/-- The forwarded RESPONSE header LINES: status line, the proxy `Via`, then the
upstream's surviving end-to-end headers (response hop-by-hop stripped, framing kept). -/
def forwardRespLines (statusLine : Bytes) (hlines : List Bytes) : List Bytes :=
  statusLine :: viaLine :: hlines.filter (keepLine (respDropSet hlines))

/-- **The forwarded response HEAD** (header block, no trailing CRLFCRLF): strip
response hop-by-hop, add `Via`, rejoin with CRLF. The host splices this in place of
the upstream header block, then re-appends CRLFCRLF and streams the body verbatim. -/
def forwardRespHead (head : Bytes) : Bytes :=
  match splitCRLFLines head with
  | [] => head
  | statusLine :: hlines => joinCRLF (forwardRespLines statusLine hlines)

/-- Structural unfold of `forwardRespHead` on a well-formed head. -/
theorem forwardRespHead_cons (head statusLine : Bytes) (hlines : List Bytes)
    (hsplit : splitCRLFLines head = statusLine :: hlines) :
    forwardRespHead head = joinCRLF (forwardRespLines statusLine hlines) := by
  rw [forwardRespHead, hsplit]

/-- **`Via` is on the response.** The proxy announces itself to the client too. -/
theorem resp_via_line (statusLine : Bytes) (hlines : List Bytes) :
    viaLine ∈ forwardRespLines statusLine hlines := by
  simp [forwardRespLines]

/-- **Response hop-by-hop is stripped.** Every surviving response header has a name
not in the response drop set. -/
theorem resp_survivor_not_dropped (statusLine line : Bytes) (hlines : List Bytes)
    (hmem : line ∈ hlines.filter (keepLine (respDropSet hlines))) :
    headerNameLower line ∉ respDropSet hlines := by
  have hkeep : keepLine (respDropSet hlines) line = true := (List.mem_filter.mp hmem).2
  have hdrop : dropName (respDropSet hlines) line = false := by simpa [keepLine] using hkeep
  simpa [dropName, decide_eq_false_iff_not] using hdrop

/-- **`Connection` is stripped from the response.** A `Connection` header of the
reply is never in the survivor set — the intermediary manages the client
disposition itself. -/
theorem resp_connection_removed (line : Bytes) (hlines : List Bytes)
    (hname : headerNameLower line = connectionName) :
    line ∉ hlines.filter (keepLine (respDropSet hlines)) := by
  intro hmem
  have hkeep : keepLine (respDropSet hlines) line = true := (List.mem_filter.mp hmem).2
  have hin : headerNameLower line ∈ respDropSet hlines := by
    rw [hname]; exact List.mem_append.mpr (Or.inl (by decide))
  have hdrop : dropName (respDropSet hlines) line = true := by
    simpa [dropName, decide_eq_true_iff] using hin
  simp [keepLine, hdrop] at hkeep

/-- **`Transfer-Encoding` is PRESERVED on the response.** A `Transfer-Encoding`
header of the reply — as long as it is not also named in a `Connection` token —
survives the strip VERBATIM: the chunked framing the proxy forwards intact is kept. -/
theorem resp_transfer_encoding_preserved (line : Bytes) (hlines : List Bytes)
    (hin : line ∈ hlines)
    (hname : headerNameLower line = transferEncodingName)
    (hnotoken : headerNameLower line ∉ connectionTokens hlines) :
    line ∈ hlines.filter (keepLine (respDropSet hlines)) := by
  rw [List.mem_filter]
  refine ⟨hin, ?_⟩
  have hnotdrop : headerNameLower line ∉ respDropSet hlines := by
    rw [respDropSet]
    intro hmem
    rcases List.mem_append.mp hmem with hfix | htok
    · rw [hname] at hfix; exact absurd hfix (by decide)
    · exact hnotoken htok
  have : dropName (respDropSet hlines) line = false := by
    simpa [dropName, decide_eq_false_iff_not] using hnotdrop
  simp [keepLine, this]

/-- **The status line is a prefix of the forwarded response head** — status
untouched. -/
theorem resp_statusLine_isPrefix (head statusLine : Bytes) (hlines : List Bytes)
    (hsplit : splitCRLFLines head = statusLine :: hlines) :
    statusLine <+: forwardRespHead head := by
  rw [forwardRespHead_cons head statusLine hlines hsplit, forwardRespLines]
  exact joinCRLF_prefix statusLine _

/-! ## Gateway error status (RFC 9110 §15.6.3 / §15.6.5) -/

/-- The gateway error response the host returns when the upstream forward failed:
`504 Gateway Timeout` when the upstream accepted but did not answer in time,
`502 Bad Gateway` when it could not be reached / gave no valid response. Raw bytes,
the exact wire response the host writes. -/
def gatewayError (timedOut : Bool) : Bytes :=
  if timedOut then
    [72, 84, 84, 80, 47, 49, 46, 49, 32, 53, 48, 52, 32, 71, 97, 116, 101, 119, 97, 121, 32,
     84, 105, 109, 101, 111, 117, 116, 13, 10, 67, 111, 110, 116, 101, 110, 116, 45, 76, 101,
     110, 103, 116, 104, 58, 32, 49, 53, 13, 10, 67, 111, 110, 110, 101, 99, 116, 105, 111,
     110, 58, 32, 99, 108, 111, 115, 101, 13, 10, 13, 10, 103, 97, 116, 101, 119, 97, 121, 32,
     116, 105, 109, 101, 111, 117, 116]
  else
    [72, 84, 84, 80, 47, 49, 46, 49, 32, 53, 48, 50, 32, 66, 97, 100, 32, 71, 97, 116, 101,
     119, 97, 121, 13, 10, 67, 111, 110, 116, 101, 110, 116, 45, 76, 101, 110, 103, 116, 104,
     58, 32, 49, 49, 13, 10, 67, 111, 110, 110, 101, 99, 116, 105, 111, 110, 58, 32, 99, 108,
     111, 115, 101, 13, 10, 13, 10, 98, 97, 100, 32, 103, 97, 116, 101, 119, 97, 121]

/-- The two gateway responses are distinct — a timeout is never reported as a plain
bad-gateway and vice versa. -/
theorem gatewayError_distinguishes : gatewayError true ≠ gatewayError false := by decide

/-! ## Concrete end-to-end witnesses -/

/-- A request with `Connection: keep-alive` (a fixed hop-by-hop field), a `Host`,
and a body, plus a known client address `1.2.3.4`. -/
def demoFwdReqIn : Bytes :=
  [71, 69, 84, 32, 47, 32, 72, 84, 84, 80, 47, 49, 46, 49, 13, 10, 67, 111, 110, 110, 101, 99,
   116, 105, 111, 110, 58, 32, 107, 101, 101, 112, 45, 97, 108, 105, 118, 101, 13, 10, 72, 111,
   115, 116, 58, 32, 120, 13, 10, 13, 10, 66, 79, 68, 89]

def demoFwdIp : Bytes := [49, 46, 50, 46, 51, 46, 52]                        -- "1.2.3.4"

/-- The forwarded request: `Connection` stripped, `Via` and `X-Forwarded-For:
1.2.3.4` inserted after the request line, `Host` and body kept verbatim. -/
def demoFwdReqOut : Bytes :=
  [71, 69, 84, 32, 47, 32, 72, 84, 84, 80, 47, 49, 46, 49, 13, 10, 86, 105, 97, 58, 32, 49, 46,
   49, 32, 100, 114, 111, 114, 98, 13, 10, 88, 45, 70, 111, 114, 119, 97, 114, 100, 101, 100,
   45, 70, 111, 114, 58, 32, 49, 46, 50, 46, 51, 46, 52, 13, 10, 72, 111, 115, 116, 58, 32,
   120, 13, 10, 13, 10, 66, 79, 68, 89]

/-- **The request forward, computed to the byte** — strip + `Via` + `X-Forwarded-For`. -/
theorem demo_forward_req : forwardReq demoFwdIp demoFwdReqIn = demoFwdReqOut := by decide

/-- An upstream response header block (no trailing CRLFCRLF) with `Connection`,
`Keep-Alive` (fixed hop-by-hop), a `Transfer-Encoding` (framing), and an `ETag`. -/
def demoRespIn : Bytes :=
  [72, 84, 84, 80, 47, 49, 46, 49, 32, 50, 48, 48, 32, 79, 75, 13, 10, 67, 111, 110, 110, 101,
   99, 116, 105, 111, 110, 58, 32, 99, 108, 111, 115, 101, 13, 10, 75, 101, 101, 112, 45, 65,
   108, 105, 118, 101, 58, 32, 116, 105, 109, 101, 111, 117, 116, 61, 53, 13, 10, 84, 114, 97,
   110, 115, 102, 101, 114, 45, 69, 110, 99, 111, 100, 105, 110, 103, 58, 32, 99, 104, 117,
   110, 107, 101, 100, 13, 10, 69, 84, 97, 103, 58, 32, 34, 122, 34]

/-- The forwarded response head: `Connection` and `Keep-Alive` stripped, `Via`
inserted after the status line, `Transfer-Encoding` (framing) and `ETag` kept. -/
def demoRespOut : Bytes :=
  [72, 84, 84, 80, 47, 49, 46, 49, 32, 50, 48, 48, 32, 79, 75, 13, 10, 86, 105, 97, 58, 32, 49,
   46, 49, 32, 100, 114, 111, 114, 98, 13, 10, 84, 114, 97, 110, 115, 102, 101, 114, 45, 69,
   110, 99, 111, 100, 105, 110, 103, 58, 32, 99, 104, 117, 110, 107, 101, 100, 13, 10, 69, 84,
   97, 103, 58, 32, 34, 122, 34]

/-- **The response forward, computed to the byte** — hop-by-hop stripped, framing
preserved, `Via` added. -/
theorem demo_forward_resp : forwardRespHead demoRespIn = demoRespOut := by decide

#print axioms forwardReqHead_cons
#print axioms forward_via_line
#print axioms forward_xff_line
#print axioms forward_survivor_not_dropped
#print axioms forward_reqLine_isPrefix
#print axioms forward_body_isSuffix
#print axioms forwardRespHead_cons
#print axioms resp_via_line
#print axioms resp_survivor_not_dropped
#print axioms resp_connection_removed
#print axioms resp_transfer_encoding_preserved
#print axioms resp_statusLine_isPrefix
#print axioms gatewayError_distinguishes
#print axioms demo_forward_req
#print axioms demo_forward_resp

#print axioms stripped_survivor_not_dropped
#print axioms hop_named_line_removed
#print axioms endToEnd_line_preserved
#print axioms reqLine_isPrefix
#print axioms body_isSuffix
#print axioms demo_strip

end Reactor.ProxyForward
