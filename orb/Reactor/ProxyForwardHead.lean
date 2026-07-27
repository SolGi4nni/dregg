import Reactor.ServeStep
import Body.FrameRaw

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
the exact wire response the host writes.

**The definition moved to `Reactor.ServeStep`** when the effect seam got its own bare-LF
upstream-response gate: both proxy paths now refuse onto the SAME `502` object rather than
two byte literals that could drift apart. This is a reducible alias, so every `decide` over
it still reduces to the literal. -/
abbrev gatewayError : Bool → Bytes := Reactor.ServeStep.gatewayError

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

/-! ## ★ Bare-LF UPSTREAM RESPONSE heads: the two-parse hazard, refused (RFC 9112 §2.2)

The response-direction mirror of the request-side gate in `Body.FrameRaw` §(1b).

RFC 9112 §2.2: *"Although the line terminator for the start-line and fields is the
sequence CRLF, a recipient MAY recognize a single LF as a line terminator and
ignore any preceding CR."* Every line scan in this core takes the CRLF-only
reading — `splitCRLFLines` here, `Body.FrameRaw.takeLine` there. So an UPSTREAM
RESPONSE head carrying a **bare LF** has *two* admissible parses, and the
downstream client is free to take the other one: a field sitting after a bare LF
is part of the previous field's VALUE to this proxy but a field-line of its own to
an LF-tolerant client — and after a bare LF LF, an entire second message.

Measured against the deployed proxy on the SHIPPED io_uring reactor
(`conformance/proxy/respsplit_probe.py`, 2026-07-25), the upstream head

    HTTP/1.1 200 OK CRLF Content-Type: text/plain CRLF
    X-Tag: a LF Set-Cookie: sess=EVIL; Path=/ CRLF Content-Length: 3

was forwarded VERBATIM (plus `Via`), and `curl -D -` — a real client — reported
`Set-Cookie: sess=EVIL; Path=/` as a header field of the response. This proxy
never saw that field: to `splitCRLFLines` it sits inside `X-Tag`'s value, so no
hop-by-hop strip and no header decision ever applied to it. A second vector put a
whole `HTTP/1.1 200 OK … OWNED!` message behind a bare LF LF and the client saw
two responses to one request. That is RFC 9112 §11.2 response splitting, and it is
the intermediary's fault: RFC 9110 §7.6.1 makes this hop responsible for the head
it hands its client.

The gate therefore **fails closed**, exactly as the request side does: it refuses
the upstream head rather than making `splitCRLFLines` LF-tolerant. A proxy must not
forward a head it parsed differently from its client, and tolerance would only move
the disagreement to whatever hop *is* CRLF-only. A refused head surfaces as
`502 Bad Gateway` (`gatewayError false`, RFC 9110 §15.6.3) — the upstream produced
a response this intermediary cannot forward unambiguously, which is exactly an
invalid response from the upstream server. It is never a silent pass-through:
`respGate_reject_is_not_forward` says the reject outcome is no forwarded head at
all, and `respGate_seam_reject_not_a_head` says the same about the bytes crossing
the C ABI. -/

open Body.FrameRaw (noBareLF)

/-! ### The OTHER admissible parse, written down -/

/-- The **LF-tolerant** line split RFC 9112 §2.2 permits a recipient to take: a bare
`LF` terminates a line just as `CRLF` does (a `CR` immediately before an `LF` is
ignored). This is *not* what this core does — `splitCRLFLines` is CRLF-only — it is
what the NEXT HOP is allowed to do, written down so the two-hop disagreement is a
statement in Lean rather than a paragraph of prose. -/
def splitLFLines : Bytes → List Bytes
  | [] => [[]]
  | 13 :: 10 :: rest => [] :: splitLFLines rest
  | 10 :: rest => [] :: splitLFLines rest
  | b :: rest =>
    match splitLFLines rest with
    | [] => [[b]]
    | l :: ls => (b :: l) :: ls

/-- The ordinary-octet step of `splitLFLines`: an octet that is neither a bare `LF`
nor the `CR` of a `CRLF` pair extends the current line. -/
theorem splitLFLines_cons (b : UInt8) (rest : Bytes) (h2 : b = 10 → False)
    (h1 : ∀ r, b = 13 → rest = 10 :: r → False) :
    splitLFLines (b :: rest)
      = match splitLFLines rest with
        | [] => [[b]]
        | l :: ls => (b :: l) :: ls := by
  rw [splitLFLines.eq_def]
  split <;> simp_all

/-- The ordinary-octet step of `splitCRLFLines` is its own third equation lemma
(same case split, one arm fewer — it has no bare-`LF` arm), so it is used directly
rather than restated. -/
theorem splitCRLFLines_cons (b : UInt8) (rest : Bytes)
    (h1 : ∀ r, b = 13 → rest = 10 :: r → False) :
    splitCRLFLines (b :: rest)
      = match splitCRLFLines rest with
        | [] => [[b]]
        | l :: ls => (b :: l) :: ls :=
  Reactor.ServeStep.splitCRLFLines.eq_3 b rest h1

/-- **★ The two admissible parses coincide on unambiguously-terminated blocks.** On
a block with no bare LF, the LF-tolerant parse the next hop may take is *equal* to
the CRLF-only parse this core takes: the block has exactly one reading, so no two
hops can disagree about where its fields begin. This is the payoff both bare-LF
gates buy — the request side's `Body.FrameRaw.frameRaw_complete_noBareLF` hands an
admitted head to `stripHopByHop`, this turns that into "the upstream cannot see a
field the strip could not"; the response gate below hands an admitted head to
`forwardRespHead`, and this turns that into "the client cannot see a field this
proxy did not". -/
theorem splitLFLines_eq_splitCRLFLines (bs : Bytes) (h : noBareLF bs = true) :
    splitLFLines bs = splitCRLFLines bs := by
  induction bs using Body.FrameRaw.noBareLF.induct with
  | case1 => rfl
  | case2 rest ih =>
    have hr : noBareLF rest = true := by simpa [Body.FrameRaw.noBareLF] using h
    simp [splitLFLines, splitCRLFLines, ih hr]
  | case3 x => simp [Body.FrameRaw.noBareLF] at h
  | case4 b rest h1 h2 ih =>
    have hr : noBareLF rest = true := by
      rwa [Body.FrameRaw.noBareLF_cons_step b rest h2 h1] at h
    rw [splitLFLines_cons b rest h2 h1, splitCRLFLines_cons b rest h1, ih hr]

/-! ### The gate -/

/-- The verdict on an upstream response head block: either the transformed head to
forward, or a refusal. There is no third outcome and no "forward anyway" — the
refusal carries no bytes, which is what makes the failure closed. -/
inductive RespHeadOutcome where
  /-- The upstream head is not unambiguously terminated (RFC 9112 §2.2): refuse it.
  The host answers the client `502 Bad Gateway` (`gatewayError false`). -/
  | reject : RespHeadOutcome
  /-- The transformed head to forward (hop-by-hop stripped, `Via` added). -/
  | forward : Bytes → RespHeadOutcome
  deriving DecidableEq, Repr

/-- **The gated response forward.** Refuse an upstream response head whose line
terminators are ambiguous (`noBareLF`, RFC 9112 §2.2 — see above); otherwise take
the proven transform `forwardRespHead` unchanged. This is the decision the host
crosses instead of `forwardRespHead` directly. -/
def forwardRespHeadGated (head : Bytes) : RespHeadOutcome :=
  if noBareLF head then .forward (forwardRespHead head) else .reject

/-- **The gate fails closed on a bare LF.** An upstream head carrying a bare LF is
refused — the gate never yields a head to forward, so no bytes of it reach the
client. -/
theorem respGate_bareLF_rejected (head : Bytes) (hbare : noBareLF head = false) :
    forwardRespHeadGated head = .reject
    ∧ (∀ out, forwardRespHeadGated head ≠ .forward out) := by
  have hr : forwardRespHeadGated head = .reject := by
    simp [forwardRespHeadGated, hbare]
  exact ⟨hr, by intro out h; rw [hr] at h; exact RespHeadOutcome.noConfusion h⟩

/-- **★ The gate forwards only unambiguously-terminated upstream heads.** Whenever
the gate hands the host a head to forward, that upstream head contained no bare LF
— so this core's CRLF-only parse is the only parse RFC 9112 §2.2 permits of it. The
completeness direction, mirroring `Body.FrameRaw.frameRaw_complete_noBareLF`. -/
theorem respGate_forward_noBareLF (head out : Bytes)
    (h : forwardRespHeadGated head = .forward out) : noBareLF head = true := by
  cases hclean : noBareLF head with
  | false => exact absurd h ((respGate_bareLF_rejected head hclean).2 out)
  | true => rfl

/-- On a head with unambiguous terminators the gate is **exactly** the proven
transform — the refusal adds a refusal and changes nothing else. -/
theorem respGate_clean (head : Bytes) (hclean : noBareLF head = true) :
    forwardRespHeadGated head = .forward (forwardRespHead head) := by
  simp [forwardRespHeadGated, hclean]

/-- **★ What the gate forwards, this hop and its client parse the same way.** For a
forwarded upstream head, the LF-tolerant parse an RFC 9112 §2.2 recipient may take
of that head equals the CRLF-only parse this proxy took of it. The disagreement the
demonstration exploited cannot arise on a head the gate admitted. -/
theorem respGate_forward_parses_agree (head out : Bytes)
    (h : forwardRespHeadGated head = .forward out) :
    splitLFLines head = splitCRLFLines head :=
  splitLFLines_eq_splitCRLFLines head (respGate_forward_noBareLF head out h)

/-- **A reject is not a forward.** Stated on its own because "fail closed" is the
whole point: there is no head — not even an empty one — that a refused upstream
head yields. -/
theorem respGate_reject_is_not_forward (head : Bytes)
    (h : forwardRespHeadGated head = .reject) (out : Bytes) :
    forwardRespHeadGated head ≠ .forward out := by
  rw [h]; intro hc; exact RespHeadOutcome.noConfusion hc

/-! ### ★ …and the head the gate EMITS has one parse too

`respGate_forward_parses_agree` is about the head that came IN. The client is handed
what goes OUT — the same lines with `Via` spliced in and the block rejoined — so the
guarantee has to survive the transform. It does: the emitted block is `joinCRLF` of
lines each of which is a line of an unambiguous block (plus the constant `viaLine`),
and neither the split nor the CRLF join can manufacture a bare LF. -/

/-- **Append closure.** Concatenating two blocks with no bare LF makes none: the only
way to create one at the join is an `LF` opening the second block, which the second
block's own cleanliness forbids. (A `CR` ending the first block is harmless — it either
pairs with a following `LF` or is an ordinary octet.) -/
theorem noBareLF_append (a b : Bytes) (ha : noBareLF a = true) (hb : noBareLF b = true) :
    noBareLF (a ++ b) = true := by
  induction a using Body.FrameRaw.noBareLF.induct with
  | case1 => simpa using hb
  | case2 rest ih =>
    have hr : noBareLF rest = true := by simpa [Body.FrameRaw.noBareLF] using ha
    simpa [Body.FrameRaw.noBareLF] using ih hr
  | case3 x => simp [Body.FrameRaw.noBareLF] at ha
  | case4 x rest h1 h2 ih =>
    have hr : noBareLF rest = true := by
      rwa [Body.FrameRaw.noBareLF_cons_step x rest h2 h1] at ha
    have hstep : noBareLF (x :: (rest ++ b)) = noBareLF (rest ++ b) := by
      refine Body.FrameRaw.noBareLF_cons_step x (rest ++ b) h2 ?_
      intro r hx hr2
      cases rest with
      | nil =>
        rw [List.nil_append] at hr2
        rw [hr2] at hb
        simp [Body.FrameRaw.noBareLF] at hb
      | cons y ys =>
        rw [List.cons_append] at hr2
        injection hr2 with e1 _
        exact h1 ys hx (by rw [e1])
    show noBareLF (x :: (rest ++ b)) = true
    rw [hstep]
    exact ih hr

/-- **CRLF-join closure.** Joining lines that each carry no bare LF, with CRLF between
them, yields a block with no bare LF. -/
theorem noBareLF_joinCRLF : ∀ (ls : List Bytes), (∀ l ∈ ls, noBareLF l = true) →
    noBareLF (joinCRLF ls) = true
  | [], _ => rfl
  | [l], h => h l (by simp)
  | l :: m :: ms, h => by
    have hl : noBareLF l = true := h l (by simp)
    have hrest : noBareLF (joinCRLF (m :: ms)) = true :=
      noBareLF_joinCRLF (m :: ms) (fun x hx => h x (List.mem_cons_of_mem l hx))
    show noBareLF (l ++ [13, 10] ++ joinCRLF (m :: ms)) = true
    rw [List.append_assoc]
    refine noBareLF_append l _ hl ?_
    simpa [Body.FrameRaw.noBareLF] using hrest

/-- **Split closure.** Every line of an unambiguously-terminated block is itself
unambiguously terminated. (The delicate case is the octet joining a line: a line that
started with `LF` would already have been refused by the induction hypothesis, which is
exactly why no separate first-octet lemma is needed.) -/
theorem splitCRLFLines_lines_noBareLF (bs : Bytes) (h : noBareLF bs = true) :
    ∀ l ∈ splitCRLFLines bs, noBareLF l = true := by
  induction bs using Body.FrameRaw.noBareLF.induct with
  | case1 =>
    intro l hl
    rw [Reactor.ServeStep.splitCRLFLines.eq_1] at hl
    simp at hl
    subst hl; rfl
  | case2 rest ih =>
    intro l hl
    have hr : noBareLF rest = true := by simpa [Body.FrameRaw.noBareLF] using h
    rw [Reactor.ServeStep.splitCRLFLines.eq_2] at hl
    rcases List.mem_cons.mp hl with rfl | hm
    · rfl
    · exact ih hr l hm
  | case3 x => simp [Body.FrameRaw.noBareLF] at h
  | case4 b rest h1 h2 ih =>
    intro l hl
    have hr : noBareLF rest = true := by
      rwa [Body.FrameRaw.noBareLF_cons_step b rest h2 h1] at h
    have ihr := ih hr
    rw [Reactor.ServeStep.splitCRLFLines.eq_3 b rest h1] at hl
    cases hs : splitCRLFLines rest with
    | nil =>
      rw [hs] at hl
      simp at hl
      subst hl
      rw [Body.FrameRaw.noBareLF_cons_step b [] h2 (by intro r _ hc; exact absurd hc (by simp))]
      rfl
    | cons l0 ls0 =>
      rw [hs] at hl
      rcases List.mem_cons.mp hl with rfl | hm
      · have hl0 : noBareLF l0 = true := ihr l0 (by rw [hs]; exact List.mem_cons_self ..)
        rw [Body.FrameRaw.noBareLF_cons_step b l0 h2 ?_]
        · exact hl0
        · intro r hb hc
          rw [hc] at hl0
          simp [Body.FrameRaw.noBareLF] at hl0
      · exact ihr l (by rw [hs]; exact List.mem_cons_of_mem l0 hm)

/-- **★ The head the gate emits carries no bare LF.** Not just the upstream head that
came in — the transformed block that goes out. Its lines are lines of an unambiguous
block plus the constant `Via`, and the CRLF join adds none.

Scope, stated honestly: this is the block the proven transform emits. The host still
appends the `CRLFCRLF` separator it stripped and stamps its own `Connection:`
disposition (`http::annotate_connection`) onto the result; both are host marshalling
outside this theorem. -/
theorem respGate_out_clean (head out : Bytes)
    (h : forwardRespHeadGated head = .forward out) : noBareLF out = true := by
  have hclean : noBareLF head = true := respGate_forward_noBareLF head out h
  have hout : out = forwardRespHead head := by
    rw [respGate_clean head hclean] at h
    injection h with e
    exact e.symm
  have hlines := splitCRLFLines_lines_noBareLF head hclean
  subst hout
  rw [forwardRespHead]
  split
  · exact hclean
  · rename_i statusLine hlines' hsplit
    rw [forwardRespLines]
    refine noBareLF_joinCRLF _ ?_
    intro l hl
    rcases List.mem_cons.mp hl with rfl | hl1
    · exact hlines l (by rw [hsplit]; exact List.mem_cons_self ..)
    · rcases List.mem_cons.mp hl1 with rfl | hl2
      · decide
      · exact hlines l (by
          rw [hsplit]
          exact List.mem_cons_of_mem statusLine (List.mem_filter.mp hl2).1)

/-- **★ The client cannot read a field out of our head that we did not put there.** For
a head the gate forwarded, the LF-tolerant parse an RFC 9112 §2.2 client may take of the
EMITTED block equals the CRLF-only parse this proxy took of it. The exact disagreement
`respBareLF_gate_not_vacuous` exhibits on the pre-fix bytes is impossible on any head
the gate admits. -/
theorem respGate_client_parses_agree (head out : Bytes)
    (h : forwardRespHeadGated head = .forward out) :
    splitLFLines out = splitCRLFLines out :=
  splitLFLines_eq_splitCRLFLines out (respGate_out_clean head out h)

/-! ### The 502 the client sees

RFC 9110 §15.6.3: `502 Bad Gateway` is "the server, while acting as a gateway or
proxy, received an invalid response from an inbound server". A head this hop cannot
parse the same way its client will IS an invalid response, so 502 is the natural
status — and it is the one the host already emits for a dial failure
(`gatewayError false`), so the refusal reuses a wire response that already exists
rather than inventing one. -/

/-- The response the host writes to the client when the gate refuses an upstream
head: `502 Bad Gateway` (RFC 9110 §15.6.3).

The host writes these bytes from its own `proxy_dial::bad_gateway()` literal, which
is byte-identical to `gatewayError false` but is a HAND-WRITTEN twin, not this object
crossed — named as residual in `DEPLOYED-WEAKNESSES.md` rather than papered over. -/
def respGateReject : Bytes := gatewayError false

/-- The refusal surfaces as a `502` status line — not a `504`, not a pass-through. -/
theorem respGateReject_is_502 :
    respGateReject.take 12 = [72, 84, 84, 80, 47, 49, 46, 49, 32, 53, 48, 50] := by decide

/-- The refusal response is not the timeout response: a bare-LF upstream head is
reported as a bad gateway, never as a gateway timeout. -/
theorem respGateReject_not_timeout : respGateReject ≠ gatewayError true := by decide

/-! ### ★ Non-vacuity: the crafted upstream head the deployed proxy leaked

The exact vector `conformance/proxy/respsplit_probe.py` serves at `/api/cookie`.
Before the refusal the response path ADMITTED it, forwarded it verbatim (plus
`Via`), and `curl` read a `Set-Cookie` field out of it that this proxy never saw. -/

/-- The crafted upstream response head BLOCK (no trailing CRLFCRLF — that is what
the host hands the transform):

    HTTP/1.1 200 OK CRLF
    Content-Type: text/plain CRLF
    X-Tag: a LF Set-Cookie: sess=EVIL; Path=/ CRLF
    Content-Length: 3

— the injected field hides behind the bare LF, inside `X-Tag`'s value. -/
def bareLFRespHead : Bytes :=
  [72, 84, 84, 80, 47, 49, 46, 49, 32, 50, 48, 48, 32, 79, 75, 13, 10, 67, 111, 110, 116, 101,
   110, 116, 45, 84, 121, 112, 101, 58, 32, 116, 101, 120, 116, 47, 112, 108, 97, 105, 110,
   13, 10, 88, 45, 84, 97, 103, 58, 32, 97, 10, 83, 101, 116, 45, 67, 111, 111, 107, 105, 101,
   58, 32, 115, 101, 115, 115, 61, 69, 86, 73, 76, 59, 32, 80, 97, 116, 104, 61, 47, 13, 10,
   67, 111, 110, 116, 101, 110, 116, 45, 76, 101, 110, 103, 116, 104, 58, 32, 51]

/-- What the response path forwarded to the client before the gate: the crafted head
with `Via` inserted after the status line and NOTHING else changed — the bare LF and
the field behind it ride through untouched. -/
def bareLFRespForwarded : Bytes :=
  [72, 84, 84, 80, 47, 49, 46, 49, 32, 50, 48, 48, 32, 79, 75, 13, 10, 86, 105, 97, 58, 32,
   49, 46, 49, 32, 100, 114, 111, 114, 98, 13, 10, 67, 111, 110, 116, 101, 110, 116, 45, 84,
   121, 112, 101, 58, 32, 116, 101, 120, 116, 47, 112, 108, 97, 105, 110, 13, 10, 88, 45, 84,
   97, 103, 58, 32, 97, 10, 83, 101, 116, 45, 67, 111, 111, 107, 105, 101, 58, 32, 115, 101,
   115, 115, 61, 69, 86, 73, 76, 59, 32, 80, 97, 116, 104, 61, 47, 13, 10, 67, 111, 110, 116,
   101, 110, 116, 45, 76, 101, 110, 103, 116, 104, 58, 32, 51]

/-- `Set-Cookie: sess=EVIL; Path=/` — the field-line `curl` reported and this proxy
never saw. -/
def setCookieLine : Bytes :=
  [83, 101, 116, 45, 67, 111, 111, 107, 105, 101, 58, 32, 115, 101, 115, 115, 61, 69, 86, 73,
   76, 59, 32, 80, 97, 116, 104, 61, 47]

/-- **The pre-fix response path forwarded the crafted head, computed to the byte.**
`forwardRespHead` IS the transform that shipped, so this is the leak itself, not a
reconstruction of it: `Via` added, bare LF and hidden field intact. -/
theorem bareLF_resp_forwarded : forwardRespHead bareLFRespHead = bareLFRespForwarded := by decide

/-- **★ The bug, witnessed in Lean.** On the bytes the pre-fix path forwarded, the
two admissible parses DISAGREE, and the disagreement is a whole field-line: the
LF-tolerant parse (what `curl` took) carries `Set-Cookie: sess=EVIL; Path=/` as a
field of its own, and the CRLF-only parse (what this proxy took, and therefore what
the hop-by-hop strip and every header decision ran on) does not contain it at all.
The gate refuses that head. So the refusal changes a real verdict on a real vector —
it is not vacuous, and the pre-fix behaviour is machine-checked to be the leak. -/
theorem respBareLF_gate_not_vacuous :
    splitLFLines bareLFRespForwarded ≠ splitCRLFLines bareLFRespForwarded
    ∧ setCookieLine ∈ splitLFLines bareLFRespForwarded
    ∧ setCookieLine ∉ splitCRLFLines bareLFRespForwarded
    ∧ forwardRespHeadGated bareLFRespHead = .reject := by decide

/-- On a head with unambiguous terminators the gate changes nothing: the clean
upstream head of `demo_forward_resp` still forwards, to the same bytes. -/
theorem clean_resp_gate_agrees :
    forwardRespHeadGated demoRespIn = .forward demoRespOut := by decide

/-! ### The seam encoding -/

/-- Encode the gate's verdict for the host: `1` = reject (one byte, no head),
`0 :: out` = forward this head. The tag is the FIRST byte so a host that reads a
short buffer cannot mistake a reject for a head. -/
def encodeRespHead : RespHeadOutcome → Bytes
  | .reject => [1]
  | .forward out => 0 :: out

/-- **A rejected upstream head crosses the seam as a refusal, never as a head.** The
payload for a reject is the single byte `1`; no forwarded head can encode to it (a
forward always begins with `0`). The host cannot accidentally splice a refused head
into the client's response. -/
theorem respGate_seam_reject_not_a_head (out : Bytes) :
    encodeRespHead .reject ≠ encodeRespHead (.forward out) := by
  simp [encodeRespHead]

/-- **ABI check for the refusal.** The seam's payload for the crafted upstream head
is `[1]` — a reject. -/
theorem bareLF_resp_encoded : encodeRespHead (forwardRespHeadGated bareLFRespHead) = [1] := by
  decide

/-- **Regression guard on the seam.** The ungated transform and the gate do not
merely differ as verdicts — they differ in the *bytes crossing the C ABI*. Anyone
who re-points the host at the ungated `drorb_proxy_forward_resp` changes the
verdict for the crafted head from "reject, 502" back to "forward this head", and
this inequality is what says so. -/
theorem ungated_resp_seam_differs :
    encodeRespHead (.forward (forwardRespHead bareLFRespHead))
      ≠ encodeRespHead (forwardRespHeadGated bareLFRespHead) := by decide

/-! ## Host C-ABI exports — the proven forward transforms the reverse proxy crosses

Each is `ByteArray → ByteArray` (the single-argument request/response transforms fit
the host serve-thread Seam dispatch `fn(*mut LeanObject) → *mut LeanObject` directly):
the connection thread submits its bytes across the seam and the PROVEN transform runs
on the single runtime-owner thread — proven code, not a hand-written byte-mirror. -/

/-- `drorb_proxy_strip_req` — strip request-side hop-by-hop headers (RFC 9110 §7.6.1)
over the raw request bytes (`stripHopByHop`). -/
@[export drorb_proxy_strip_req]
def drorbProxyStripReq (req : ByteArray) : ByteArray :=
  ByteArray.mk (stripHopByHop req.toList).toArray

/-- The UNGATED upstream-RESPONSE head transform at the `ByteArray` level: strip
response hop-by-hop headers (`Transfer-Encoding` PRESERVED) and add the `Via` line
(RFC 9110 §7.6.1/§7.6.3) (`forwardRespHead`).

**RETIRED as a host crossing.** It carried `@[export drorb_proxy_forward_resp]`, and
its own contract was "the host must not call it" — `ungated_resp_seam_differs`
machine-checks that crossing it instead of `drorb_proxy_forward_resp_gated` turns the
crafted head's verdict from "reject, 502" back into "forward this head", i.e. restores
the response-splitting leak. An exported C symbol whose documented contract is *never
call this* is a footgun rather than an affordance, so the export is gone and the gated
seam is the only response-head transform the host can reach. Nothing about the proof
changed: this def and every theorem stated over `forwardRespHead` (including
`ungated_resp_seam_differs` itself, which is what makes the retirement legible) stand
unchanged — only the C symbol that let a host bypass the gate is withdrawn. -/
def drorbProxyForwardResp (head : ByteArray) : ByteArray :=
  ByteArray.mk (forwardRespHead head.toList).toArray

/-- `drorb_proxy_forward_resp_gated` — the **gated** upstream-RESPONSE head transform,
and the seam the host crosses on the response path. Same transform as
`drorb_proxy_forward_resp`, with the RFC 9112 §2.2 bare-LF refusal in front of it
(`forwardRespHeadGated`). Output is `encodeRespHead`: `1` = refuse this upstream head
(the host answers the client `502 Bad Gateway`), `0 :: head` = forward this head.

This is the ONLY response-head transform the host can cross: the ungated
`drorbProxyForwardResp` above no longer carries an `@[export]`, precisely because
`ungated_resp_seam_differs` machine-checks that crossing it restores the leak. -/
@[export drorb_proxy_forward_resp_gated]
def drorbProxyForwardRespGated (head : ByteArray) : ByteArray :=
  ByteArray.mk (encodeRespHead (forwardRespHeadGated head.toList)).toArray

/-- `drorb_proxy_forward_req` — the FULL forwarded request: strip hop-by-hop headers
AND inject the `Via` (and, for a non-empty client ip, `X-Forwarded-For`) proxy-identity
lines (`forwardReq`). The first argument is the client ip bytes (empty ⇒ no XFF). -/
@[export drorb_proxy_forward_req]
def drorbProxyForwardReq (ip req : ByteArray) : ByteArray :=
  ByteArray.mk (forwardReq ip.toList req.toList).toArray

#print axioms drorbProxyStripReq
#print axioms drorbProxyForwardResp
#print axioms drorbProxyForwardReq
#print axioms drorbProxyForwardRespGated

#print axioms splitLFLines_eq_splitCRLFLines
#print axioms respGate_bareLF_rejected
#print axioms respGate_forward_noBareLF
#print axioms respGate_clean
#print axioms respGate_forward_parses_agree
#print axioms respGate_reject_is_not_forward
#print axioms respGate_seam_reject_not_a_head
#print axioms respGateReject_is_502
#print axioms bareLF_resp_forwarded
#print axioms respBareLF_gate_not_vacuous
#print axioms clean_resp_gate_agrees
#print axioms ungated_resp_seam_differs
#print axioms noBareLF_append
#print axioms noBareLF_joinCRLF
#print axioms splitCRLFLines_lines_noBareLF
#print axioms respGate_out_clean
#print axioms respGate_client_parses_agree

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
