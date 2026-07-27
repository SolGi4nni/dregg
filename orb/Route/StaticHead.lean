/-
Route.StaticHead — the DEPLOYED static response HEAD decision, in the core.

`Route.StaticServe` specifies the static lane's wire byte-exactly (`okHead`,
`notFoundResp`, `contentType`) and proves `static_serves_bytes` /
`static_404_missing` over it — but the RUNNING head was still built by the
host: the status line, `Connection`, `Accept-Ranges`, `Content-Type`, and
`Content-Length` bytes were assembled host-side, and the extension → MIME
decision (extract the extension from the real file name, lowercase it, map
it) was a host mirror of the model's `contentType`. Model and deployment
could drift silently — exactly the gap `Route.StaticResolve` closed for the
PATH decision. This module closes it for the HEAD decision: the exported
`drorb_static_head` below IS the head builder the running host calls per
static response, and it calls the MODEL's own `okHead` / `notFoundResp` —
deployed = model definitionally, so `static_serves_bytes` /
`static_404_missing` speak about the running bytes verbatim. What runs is
what is proven.

The decision, moved across the boundary:

  1. extension extraction from the real file name (the bytes after the LAST
     `.`; no `.`, or a `.` only in leading position — a dotfile — means NO
     extension), the host filesystem rule it replaces;
  2. ASCII-lowercase of the extension (so `pic.SVG` is `image/svg+xml`);
  3. the extension → MIME map (`ctypeFor`, each row byte-equal to the
     model's `contentType` row — `mime_row_witnesses`);
  4. the head bytes themselves: the model's `okHead` (which renders the
     Content-Length via `decimal` = `Nat.repr`), and the model's
     `notFoundResp` for the `404`.

The host contributes only its boundary facts: the real file's length (from
the filesystem), the real file's NAME (post-canonicalize, so a symlink's
MIME follows its target exactly as before), the client's keep-alive intent,
and found-vs-missing. It assembles no header bytes and owns no MIME row.

Grounding reused from `Proto.Dec` (the response-parser decimal theory, which
proved the kernel-opaque `String.toUTF8`/`ByteArray.toList` bridge once):
  * `dval_natToDec`   — ∀ n, the rendered digits parse back to exactly `n`:
                        the framed Content-Length is EXACTLY the body length,
                        for every length, on the DEPLOYED rendering.
  * `natToDec_isDigit`— ∀ n, every rendered byte is an ASCII digit (so the
                        header line carries no delimiter bytes).
  * `baMkList`        — the `ByteArray.toList` loop bridge, used here to
                        prove `ascii_eq_strBytes`.

Theorems here:
  * `ascii_eq_strBytes`     — kernel-computable ASCII byte literals equal the
                              model's UTF-8 `strBytes`, ∀ ASCII strings (real
                              induction over the UTF-8 encoder).
  * `okHeadFor_eq_model` / `staticHeadC_notFound` — deployed = model, by
                              `rfl` / directly.
  * `contentLength_roundtrip` / `contentLength_digits` — the ∀-length
                              Content-Length facts, restated on the model's
                              `decimal` (definitionally `Proto.Dec.natToDec`).
  * structure theorems on the deployed head: status-line prefix, CRLF·CRLF
    termination, Connection / Content-Type / Content-Length lines present.
  * `staticHeadC_found` / `staticHeadC_notFound` — the exported seam returns
    exactly the deployed head / the model's `404`.
  * extension/MIME witnesses: every map row = the model row; uppercase
    folding, dotfiles (NO extension → octet-stream, including `.html`),
    trailing dot, multi-dot names, no-dot names.

Residual (named, host-side): the request-line split, the serving-prefix
strip, filesystem open/metadata/canonicalize + root re-check (unchanged,
covered by the `StaticResolve` wave), and the streamed body pump. The body's
byte-exactness on the wire is `static_serves_bytes` + the host pump, as
before. The `HEAD`-method body suppression stays a host decision (write the
head only), as does writing order.
-/

import Route.StaticServe
import Proto.Decimal

namespace Route.StaticHead

open Route.StaticServe (strBytes crlf statusLine200 statusLine404 connHeader
  acceptRanges ctBlock clBlock decimal okHead notFoundResp contentType)

/-- Raw bytes. -/
abbrev Bytes := List UInt8

/-! ## ASCII byte literals, bridged to the model's UTF-8 `strBytes` -/

/-- ASCII bytes of a string — kernel-computable (unlike `String.toUTF8`,
which the kernel will not reduce), so `decide` can evaluate the concrete
witnesses below. Bridged to the model's `strBytes` by `ascii_eq_strBytes`. -/
def ascii (s : String) : Bytes := s.data.map (fun c => UInt8.ofNat c.toNat)

/-- A char under `0x80` UTF-8-encodes to exactly its own code byte. -/
theorem utf8EncodeChar_ascii {c : Char} (h : c.val ≤ 0x7f) :
    String.utf8EncodeChar c = [UInt8.ofNat c.toNat] := by
  have hv : c.toNat ≤ 127 := by
    simpa using (UInt32.le_iff_toNat_le).mp h
  simp only [String.utf8EncodeChar, Char.toNat_val, if_pos hv]

/-- The UTF-8 encoding of an all-ASCII char list is the per-char code map. -/
theorem flatMap_utf8_ascii (cs : List Char) (h : ∀ c ∈ cs, c.val ≤ 0x7f) :
    cs.flatMap String.utf8EncodeChar = cs.map (fun c => UInt8.ofNat c.toNat) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.flatMap_cons, List.map_cons,
        utf8EncodeChar_ascii (h c (List.mem_cons_self ..)),
        ih (fun c hc => h c (List.mem_cons_of_mem _ hc))]
    rfl

/-- `strBytes` as the flat UTF-8 encoding of the char list (the
`ByteArray.toList` loop discharged by `Proto.Dec.baMkList`). -/
theorem strBytes_eq_flatMap (s : String) :
    strBytes s = s.data.flatMap String.utf8EncodeChar := by
  show s.toByteArray.toList = s.toList.flatMap String.utf8EncodeChar
  rw [← String.utf8Encode_toList]
  show (List.toByteArray (s.toList.flatMap String.utf8EncodeChar)).toList = _
  rw [Proto.Dec.toList_eq_data_toList, List.toList_data_toByteArray]

/-- **`ascii` = the model's `strBytes`** for every ASCII string. -/
theorem ascii_eq_strBytes (s : String) (h : ∀ c ∈ s.data, c.val ≤ 0x7f) :
    ascii s = strBytes s := by
  rw [strBytes_eq_flatMap, flatMap_utf8_ascii s.data h]
  rfl

/-- `ascii` distributes over string concatenation: the code-byte map of a
concatenation is the concatenation of the code-byte maps. Lets the concrete
head witnesses below be discharged STRUCTURALLY (append-associativity on
already-`ascii`-split literals) instead of by kernel-evaluating a whole
hundred-byte head through the UTF-8 char decode. -/
theorem ascii_append (a b : String) : ascii (a ++ b) = ascii a ++ ascii b := by
  show ((a ++ b).toList).map _ = _
  rw [String.toList_append, List.map_append]
  rfl

/-! ## Extension extraction and the MIME decision -/

/-- ASCII-lowercase one byte. -/
def lowerB (b : UInt8) : UInt8 :=
  if 0x41 ≤ b ∧ b ≤ 0x5a then b + 0x20 else b

/-- The extension of a real FILE NAME (no `/` inside — the host passes the
final path component of the canonicalized real path): the bytes after the
LAST `.`. `none` when there is no `.`, or when the only `.` is leading (a
dotfile like `.gitignore` has NO extension) — the host filesystem rule this
replaces. -/
def extOf (name : Bytes) : Option Bytes :=
  let extRev := name.reverse.takeWhile (fun b => b != 0x2e)
  if extRev.length = name.length then none          -- no dot at all
  else if extRev.length + 1 = name.length then none -- the one dot is leading
  else some extRev.reverse

/-- The deployed MIME map, over the (lowercased) extension bytes. Each row
is byte-for-byte the model's `contentType` row (`mime_row_witnesses`); the
default is `application/octet-stream`. -/
def ctypeFor (ext : Option Bytes) : Bytes :=
  match ext with
  | none => ascii "application/octet-stream"
  | some e =>
    let l := e.map lowerB
    if l = ascii "html" ∨ l = ascii "htm" then ascii "text/html; charset=utf-8"
    else if l = ascii "css" then ascii "text/css; charset=utf-8"
    else if l = ascii "js" ∨ l = ascii "mjs" then ascii "application/javascript"
    else if l = ascii "json" then ascii "application/json"
    else if l = ascii "svg" then ascii "image/svg+xml"
    else if l = ascii "png" then ascii "image/png"
    else if l = ascii "jpg" ∨ l = ascii "jpeg" then ascii "image/jpeg"
    else if l = ascii "gif" then ascii "image/gif"
    else if l = ascii "webp" then ascii "image/webp"
    else if l = ascii "ico" then ascii "image/x-icon"
    else if l = ascii "txt" then ascii "text/plain; charset=utf-8"
    else if l = ascii "wasm" then ascii "application/wasm"
    else if l = ascii "pdf" then ascii "application/pdf"
    else if l = ascii "mp4" then ascii "video/mp4"
    else if l = ascii "woff2" then ascii "font/woff2"
    else ascii "application/octet-stream"

/-! ## The deployed head builder — the model's own -/

/-- **The deployed `200` head** for a real file: `name` is the real file's
name (post-canonicalize), `len` its byte length, `ka` the client's
keep-alive intent. This IS the model's `okHead` — deployed = specified,
definitionally. -/
def okHeadFor (name : Bytes) (len : Nat) (ka : Bool) : Bytes :=
  okHead (ctypeFor (extOf name)) len ka

/-- Deployed = model, by definition (recorded as a theorem so drift would be
a build break, not a silent divergence). -/
theorem okHeadFor_eq_model (name : Bytes) (len : Nat) (ka : Bool) :
    okHeadFor name len ka = okHead (ctypeFor (extOf name)) len ka := rfl

/-! ## Content-Length semantics, ∀ length (reused from `Proto.Dec`) -/

/-- **∀ len**: the digits `okHead` frames parse back to EXACTLY the body
length the host will stream (`decimal` is definitionally
`Proto.Dec.natToDec`). -/
theorem contentLength_roundtrip (len : Nat) :
    Proto.Dec.dval 0 (decimal len) = len :=
  Proto.Dec.dval_natToDec len

/-- **∀ len**: every framed byte is an ASCII digit — the header line carries
no stray delimiter. -/
theorem contentLength_digits (len : Nat) :
    ∀ b ∈ decimal len, 48 ≤ b.toNat ∧ b.toNat ≤ 57 :=
  Proto.Dec.natToDec_isDigit len

/-! ## Structure theorems on the deployed head -/

/-- The deployed head opens with the `200` status line. -/
theorem okHeadFor_status (name : Bytes) (len : Nat) (ka : Bool) :
    statusLine200 <+: okHeadFor name len ka :=
  ⟨connHeader ka ++ acceptRanges ++ ctBlock (ctypeFor (extOf name))
     ++ clBlock len ++ crlf,
   by simp [okHeadFor, Route.StaticServe.okHead, List.append_assoc]⟩

/-- The deployed head is terminated by the blank line (`CRLF CRLF`): the
last header line's CRLF followed by the separator. -/
theorem okHeadFor_terminated (name : Bytes) (len : Nat) (ka : Bool) :
    crlf ++ crlf <:+ okHeadFor name len ka :=
  ⟨statusLine200 ++ connHeader ka ++ acceptRanges
     ++ ctBlock (ctypeFor (extOf name)) ++ (strBytes "Content-Length: " ++ decimal len),
   by simp [okHeadFor, Route.StaticServe.okHead, Route.StaticServe.clBlock,
        List.append_assoc]⟩

/-- The `Connection` header the client's intent selected is on the wire. -/
theorem okHeadFor_conn (name : Bytes) (len : Nat) (ka : Bool) :
    connHeader ka <:+: okHeadFor name len ka :=
  ⟨statusLine200,
   acceptRanges ++ ctBlock (ctypeFor (extOf name)) ++ clBlock len ++ crlf,
   by simp [okHeadFor, Route.StaticServe.okHead, List.append_assoc]⟩

/-- The `Content-Type` header line (the proven MIME decision) is on the
wire. -/
theorem okHeadFor_ctype (name : Bytes) (len : Nat) (ka : Bool) :
    ctBlock (ctypeFor (extOf name)) <:+: okHeadFor name len ka :=
  ⟨statusLine200 ++ connHeader ka ++ acceptRanges,
   clBlock len ++ crlf,
   by simp [okHeadFor, Route.StaticServe.okHead, List.append_assoc]⟩

/-- The `Content-Length` header line is on the wire — and by
`contentLength_roundtrip` its digits parse to EXACTLY the length the host
will stream. -/
theorem okHeadFor_clen (name : Bytes) (len : Nat) (ka : Bool) :
    clBlock len <:+: okHeadFor name len ka
    ∧ Proto.Dec.dval 0 (decimal len) = len :=
  ⟨⟨statusLine200 ++ connHeader ka ++ acceptRanges ++ ctBlock (ctypeFor (extOf name)),
    crlf,
    by simp [okHeadFor, Route.StaticServe.okHead, List.append_assoc]⟩,
   contentLength_roundtrip len⟩

/-! ## The exported seam -/

/-- Big-endian read of the 8 length bytes. -/
def beNat (bs : Bytes) : Nat := bs.foldl (fun a b => a * 256 + b.toNat) 0

/-- **`drorb_static_head` — the static HEAD decision as `ByteArray →
ByteArray`.** Input framing: `flags(1) :: len(8 BE) :: fileName` where flags
bit 0 = the client's keep-alive intent and bit 1 = found (a regular file
will be streamed). `found` ⇒ the exact `200` head bytes out (the host
streams the body after them); not-found ⇒ the model's full `404` response
bytes out. A malformed frame (empty, or found with fewer than 8 length
bytes) returns EMPTY — the host fails safe (drops the connection), never
builds header bytes itself. -/
-- RETIRED EXPORT (`drorb_static_head`). Superseded by `drorb_static_decide`
-- (Route.StaticDecide, which imports this module): the static lane's FULL response
-- decision — method gate, 404, conditional GET, range/multipart AND the 200 head —
-- crossed once per request by the running host (`call_static_decide`). This
-- head-only seam had no call site left. Definition and theorems unchanged; the
-- head bytes it builds are still the model's own, now reached through StaticDecide.
def staticHeadC (input : ByteArray) : ByteArray :=
  match input.toList with
  | [] => ⟨#[]⟩
  | flags :: rest =>
    let ka := (flags &&& 0x01) == 0x01
    if (flags &&& 0x02) == 0x02 then
      if rest.length < 8 then ⟨#[]⟩
      else ⟨(okHeadFor (rest.drop 8) (beNat (rest.take 8)) ka).toArray⟩
    else ⟨(notFoundResp ka).toArray⟩

/-- The seam on a found file returns exactly the deployed head. -/
theorem staticHeadC_found (input : ByteArray) (flags : UInt8) (rest : List UInt8)
    (hin : input.toList = flags :: rest)
    (hf : ((flags &&& 0x02) == 0x02) = true) (h8 : ¬ rest.length < 8) :
    staticHeadC input
      = ⟨(okHeadFor (rest.drop 8) (beNat (rest.take 8))
            ((flags &&& 0x01) == 0x01)).toArray⟩ := by
  unfold staticHeadC
  rw [hin]
  simp [hf, h8]

/-- The seam on a missing file returns EXACTLY the model's `notFoundResp` —
the deployed `404` is the model's bytes. -/
theorem staticHeadC_notFound (input : ByteArray) (flags : UInt8) (rest : List UInt8)
    (hin : input.toList = flags :: rest)
    (hf : ((flags &&& 0x02) == 0x02) = false) :
    staticHeadC input
      = ⟨(notFoundResp ((flags &&& 0x01) == 0x01)).toArray⟩ := by
  unfold staticHeadC
  rw [hin]
  simp [hf]

/-! ## Concrete witnesses (the live-captured shapes) -/

/-- Every MIME row of the deployed map equals the model's `contentType`
row, through real file names (extraction + lowercase + map). -/
theorem mime_row_witnesses :
    ctypeFor (extOf (ascii "index.html")) = contentType "html"
    ∧ ctypeFor (extOf (ascii "a.htm"))    = contentType "htm"
    ∧ ctypeFor (extOf (ascii "s.css"))    = contentType "css"
    ∧ ctypeFor (extOf (ascii "app.js"))   = contentType "js"
    ∧ ctypeFor (extOf (ascii "m.mjs"))    = contentType "mjs"
    ∧ ctypeFor (extOf (ascii "d.json"))   = contentType "json"
    ∧ ctypeFor (extOf (ascii "pic.svg"))  = contentType "svg"
    ∧ ctypeFor (extOf (ascii "p.png"))    = contentType "png"
    ∧ ctypeFor (extOf (ascii "p.jpg"))    = contentType "jpg"
    ∧ ctypeFor (extOf (ascii "p.jpeg"))   = contentType "jpeg"
    ∧ ctypeFor (extOf (ascii "p.gif"))    = contentType "gif"
    ∧ ctypeFor (extOf (ascii "p.webp"))   = contentType "webp"
    ∧ ctypeFor (extOf (ascii "f.ico"))    = contentType "ico"
    ∧ ctypeFor (extOf (ascii "t.txt"))    = contentType "txt"
    ∧ ctypeFor (extOf (ascii "w.wasm"))   = contentType "wasm"
    ∧ ctypeFor (extOf (ascii "d.pdf"))    = contentType "pdf"
    ∧ ctypeFor (extOf (ascii "v.mp4"))    = contentType "mp4"
    ∧ ctypeFor (extOf (ascii "f.woff2"))  = contentType "woff2" := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact (by decide : ctypeFor _ = ascii _).trans (ascii_eq_strBytes _ (by decide))

/-- Extension-rule witnesses: uppercase folds (`pic.SVG` → svg), a dotfile
has NO extension (octet-stream — including `.html`, which is NOT
text/html), a trailing dot is an empty extension (octet-stream), multi-dot
names take the last extension, no dot is octet-stream. -/
theorem ext_rule_witnesses :
    ctypeFor (extOf (ascii "pic.SVG")) = ascii "image/svg+xml"
    ∧ ctypeFor (extOf (ascii "INDEX.HTML")) = ascii "text/html; charset=utf-8"
    ∧ ctypeFor (extOf (ascii ".gitignore")) = ascii "application/octet-stream"
    ∧ ctypeFor (extOf (ascii ".html")) = ascii "application/octet-stream"
    ∧ ctypeFor (extOf (ascii "noext")) = ascii "application/octet-stream"
    ∧ ctypeFor (extOf (ascii "odd.")) = ascii "application/octet-stream"
    ∧ ctypeFor (extOf (ascii "a.tar.gz")) = ascii "application/octet-stream"
    ∧ ctypeFor (extOf (ascii "min.old.js")) = ascii "application/javascript"
    ∧ ctypeFor (extOf (ascii ".config.json")) = ascii "application/json" := by
  decide

/-- A full deployed head, byte-for-byte (the live-captured
`GET /static/index.html` keep-alive shape). -/
theorem head_witness_index_html :
    okHeadFor (ascii "index.html") 11 true
      = ascii ("HTTP/1.1 200 OK\r\n" ++ "Connection: keep-alive\r\n"
          ++ "Accept-Ranges: bytes\r\n"
          ++ ("Content-Type: " ++ "text/html; charset=utf-8" ++ "\r\n")
          ++ ("Content-Length: " ++ "11" ++ "\r\n") ++ "\r\n") := by
  have hct : ctypeFor (extOf (ascii "index.html")) = ascii "text/html; charset=utf-8" := by
    decide
  have hdec : decimal 11 = ascii "11" :=
    (congrArg strBytes (show Nat.repr 11 = "11" by decide)).trans
      (ascii_eq_strBytes "11" (by decide)).symm
  simp only [okHeadFor, Route.StaticServe.okHead, Route.StaticServe.statusLine200,
    Route.StaticServe.connHeader, Route.StaticServe.acceptRanges,
    Route.StaticServe.ctBlock, Route.StaticServe.clBlock, Route.StaticServe.crlf,
    if_true, hct, hdec]
  rw [← ascii_eq_strBytes "HTTP/1.1 200 OK\r\n" (by decide),
      ← ascii_eq_strBytes "Connection: keep-alive\r\n" (by decide),
      ← ascii_eq_strBytes "Accept-Ranges: bytes\r\n" (by decide),
      ← ascii_eq_strBytes "Content-Type: " (by decide),
      ← ascii_eq_strBytes "Content-Length: " (by decide),
      ← ascii_eq_strBytes "\r\n" (by decide)]
  simp only [ascii_append, List.append_assoc]

/-- The full deployed `404`, byte-for-byte (the model's `notFoundResp`,
which the seam returns verbatim). -/
theorem notfound_witness :
    notFoundResp true
      = ascii ("HTTP/1.1 404 Not Found\r\n" ++ "Connection: keep-alive\r\n"
          ++ "Content-Length: 9\r\n\r\nnot found") := by
  simp only [Route.StaticServe.notFoundResp, Route.StaticServe.statusLine404,
    Route.StaticServe.connHeader, if_true]
  rw [← ascii_eq_strBytes "HTTP/1.1 404 Not Found\r\n" (by decide),
      ← ascii_eq_strBytes "Connection: keep-alive\r\n" (by decide),
      ← ascii_eq_strBytes "Content-Length: 9\r\n\r\nnot found" (by decide)]
  decide

/-! ## Live selftest — exercises the exported seam function on the captured
case frames and writes each output for byte-comparison (`cmp`) against the
running server's capture. -/

/-- 8-byte big-endian frame of a length. -/
def beBytes8 (n : Nat) : Bytes :=
  (List.range 8).map (fun i => UInt8.ofNat ((n >>> ((7 - i) * 8)) % 256))

/-- Build a seam input frame. -/
def mkFrame (found ka : Bool) (len : Nat) (name : Bytes) : ByteArray :=
  let flags : UInt8 := (if ka then 0x01 else 0x00) ||| (if found then 0x02 else 0x00)
  ⟨(flags :: (if found then beBytes8 len ++ name else [])).toArray⟩

def selftestCases : List (String × ByteArray) :=
  [ ("index_html_ka",  mkFrame true  true  11    (ascii "index.html"))
  , ("app_js_close",   mkFrame true  false 14    (ascii "app.js"))
  , ("blob_bin_ka",    mkFrame true  true  70000 (ascii "blob.bin"))
  , ("style_css_ka",   mkFrame true  true  6     (ascii "style.css"))
  , ("noext_ka",       mkFrame true  true  1     (ascii "noext"))
  , ("pic_svg_upper",  mkFrame true  true  4     (ascii "pic.SVG"))
  , ("head_index",     mkFrame true  true  11    (ascii "index.html"))
  , ("missing_404_ka", mkFrame false true  0     [])
  ]

/-- Write each case's seam output for the byte-identity `cmp` gate. -/
def selftestMain (args : List String) : IO Unit := do
  let outDir := args.headD "/tmp/dp-statichead/lean-out"
  IO.FS.createDirAll outDir
  for (nm, frame) in selftestCases do
    let out := staticHeadC frame
    IO.FS.writeBinFile s!"{outDir}/{nm}.bin" out
    IO.println s!"[selftest] {nm}: {out.size} bytes"
  IO.println "[selftest] wrote all case outputs"

end Route.StaticHead

#print axioms Route.StaticHead.ascii_eq_strBytes
#print axioms Route.StaticHead.strBytes_eq_flatMap
#print axioms Route.StaticHead.okHeadFor_eq_model
#print axioms Route.StaticHead.contentLength_roundtrip
#print axioms Route.StaticHead.contentLength_digits
#print axioms Route.StaticHead.okHeadFor_status
#print axioms Route.StaticHead.okHeadFor_terminated
#print axioms Route.StaticHead.okHeadFor_conn
#print axioms Route.StaticHead.okHeadFor_ctype
#print axioms Route.StaticHead.okHeadFor_clen
#print axioms Route.StaticHead.staticHeadC_found
#print axioms Route.StaticHead.staticHeadC_notFound
#print axioms Route.StaticHead.mime_row_witnesses
#print axioms Route.StaticHead.ext_rule_witnesses
#print axioms Route.StaticHead.head_witness_index_html
#print axioms Route.StaticHead.notfound_witness
