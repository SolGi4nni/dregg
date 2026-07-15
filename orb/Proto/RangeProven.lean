/-
# Proto.RangeProven — Range / `206 Partial Content` on the DEPLOYED static handler

PROVE-WHAT-RUNS for the ledger row `h1.range` (RFC 7233 byte-range serving).

The deployed default app (`Reactor.App.demoApp`) carries a `/static` prefix route to
the `staticFile` handler, and `Reactor.App.responseOfReq req .staticFile` is
DEFINITIONALLY `StaticFile.serveDeployed (targetSegments req.target) req.headers`
(`Proto.EtagProven.deployed_staticFile_route`, `rfl`). `serveDeployed` parses the raw
request headers (`reqOfHeaders`) — INCLUDING the `Range:` header — and renders
`StaticFile.serveConditional StaticFile.deployedConfig` onto the wire. So the theorems
below describe the EXACT `206` the running dataplane emits for
`GET /static/app.js` with `Range: bytes=0-9`.

The CURL that anchors this file (lane `ran` field):

    $ curl -s -i -H 'Range: bytes=0-9' http://127.0.0.1:8080/static/app.js
    HTTP/1.1 206 Partial Content
    ETag: "9e983f35"
    Accept-Ranges: bytes
    Content-Range: bytes 0-9/35
    Content-Length: 10

    console.lo

Theorems:
  * `range_header_parses` — the deployed header parser (`reqOfHeaders`) turns the raw
    `Range: bytes=0-9` wire header into the model range-set `[.fromTo 0 9]` (and a
    matching `range`). This is the parse the running serve performs — no pre-baked Req.
  * `deployed_range_206` — the deployed handler answers that request with `206`, a body
    of exactly `slice appJs 0 9` (the first ten bytes), a `Content-Range: bytes 0-9/35`
    header, and `Accept-Ranges: bytes`.
  * `range_body_bytes` — those ten body bytes ARE `"console.lo"` — octet-for-octet the
    curl body, so nothing is vacuous.

## `Lean.ofReduceBool` EVICTED (2026-07-11)

This file previously discharged `range_header_parses` by `native_decide`: `reqOfHeaders`
routes through `String.toLower` / `splitOn` / `trim` / `toNat?` / `isPrefixOf`, whose
well-founded worker loops do not reduce in the kernel, and every theorem downstream of
the parse (`range_selects`, `deployed_range_206`, `deployed_range_route`) inherited
`Lean.ofReduceBool` — the native compiler in the TCB.

The parse is now evaluated in the PURE KERNEL through the WF step kit of
`Proto.Kernel.Shortcuts` (`mapAux`/`splitOnAux`/`foldlAux`/`anyAux`/`takeWhileAux`/
`takeRightWhileAux`/`substrEq.loop` step lemmas + the ASCII `bytesToStr∘strBytes`
round-trip): every theorem below is `{propext, Quot.sound}` — no `native_decide`, no
`Lean.ofReduceBool`, no `sorryAx`.
-/

import StaticFile
import Reactor.App
import Proto.EtagProven
import Proto.Kernel.Shortcuts

namespace Proto.RangeProven

open StaticFile
open Proto.Kernel

/-- The served path segments for `/static/app.js`. -/
def assetSegs : List String := ["static", "app.js"]

/-- The raw `Range: bytes=0-9` request header, exactly as it arrives on the wire
(header name + value bytes). -/
def rangeHeader : Bytes × Bytes := (strBytes "Range", strBytes "bytes=0-9")

/-! ## The pure-kernel evaluation ladder for the deployed parse

Each rung evaluates one concrete String-function call through the
`Proto.Kernel.Shortcuts` WF step kit — kernel `decide` discharges every loop guard;
the compiler is nowhere. -/

/-- The parser's Latin-1 decode inverts the wire encoding of the ASCII name. -/
theorem bytesToStr_Range : bytesToStr (strBytes "Range") = "Range" :=
  Shortcuts.bytesToStr_strBytes (by decide)

/-- … and of the ASCII value. -/
theorem bytesToStr_val : bytesToStr (strBytes "bytes=0-9") = "bytes=0-9" :=
  Shortcuts.bytesToStr_strBytes (by decide)

theorem toLower_Range : "Range".toLower = "range" := by
  rw [show "Range".toLower = String.mapAux Char.toLower 0 "Range" from rfl]
  simp (config := { decide := true }) only [Shortcuts.mapAux_step, Shortcuts.mapAux_stop]

theorem toLower_range : "range".toLower = "range" := by
  rw [show "range".toLower = String.mapAux Char.toLower 0 "range" from rfl]
  simp (config := { decide := true }) only [Shortcuts.mapAux_step, Shortcuts.mapAux_stop]

theorem toLower_inm : "if-none-match".toLower = "if-none-match" := by
  rw [show "if-none-match".toLower = String.mapAux Char.toLower 0 "if-none-match" from rfl]
  simp (config := { decide := true }) only [Shortcuts.mapAux_step, Shortcuts.mapAux_stop]

/-- The request carries no `If-None-Match` — the deployed `findHeader` really returns
`none` on the single `Range` header. -/
theorem findHeader_inm : findHeader "if-none-match" [rangeHeader] = none := by
  have hpred : ((bytesToStr (strBytes "Range")).toLower == "if-none-match".toLower)
      = false := by
    rw [bytesToStr_Range, toLower_Range, toLower_inm]
    decide
  simp only [StaticFile.findHeader, rangeHeader, List.find?, hpred, Option.map]

/-- The deployed `findHeader` recovers the raw `Range` value string. -/
theorem findHeader_range : findHeader "range" [rangeHeader] = some "bytes=0-9" := by
  have hpred : ((bytesToStr (strBytes "Range")).toLower == "range".toLower) = true := by
    rw [bytesToStr_Range, toLower_Range, toLower_range]
    decide
  simp only [StaticFile.findHeader, rangeHeader, List.find?, hpred, Option.map]
  rw [bytesToStr_val]

theorem splitOn_bytes09 : "bytes=0-9".splitOn "=" = ["bytes", "0-9"] := by
  rw [show "bytes=0-9".splitOn "="
        = String.splitOnAux "bytes=0-9" "=" 0 0 0 [] from rfl]
  simp (config := { decide := true }) only [Shortcuts.splitOnAux_miss,
    Shortcuts.splitOnAux_matchend, Shortcuts.splitOnAux_matchcont, Shortcuts.splitOnAux_stop]

theorem splitOn_09_comma : "0-9".splitOn "," = ["0-9"] := by
  rw [show "0-9".splitOn "," = String.splitOnAux "0-9" "," 0 0 0 [] from rfl]
  simp (config := { decide := true }) only [Shortcuts.splitOnAux_miss,
    Shortcuts.splitOnAux_matchend, Shortcuts.splitOnAux_matchcont, Shortcuts.splitOnAux_stop]

theorem splitOn_09_dash : "0-9".splitOn "-" = ["0", "9"] := by
  rw [show "0-9".splitOn "-" = String.splitOnAux "0-9" "-" 0 0 0 [] from rfl]
  simp (config := { decide := true }) only [Shortcuts.splitOnAux_miss,
    Shortcuts.splitOnAux_matchend, Shortcuts.splitOnAux_matchcont, Shortcuts.splitOnAux_stop]

theorem trim_bytes : "bytes".trim = "bytes" := by
  rw [show "bytes".trim
        = ("bytes".extract
            (Substring.takeWhileAux "bytes" "bytes".endPos Char.isWhitespace 0)
            (Substring.takeRightWhileAux "bytes"
              (Substring.takeWhileAux "bytes" "bytes".endPos Char.isWhitespace 0)
              Char.isWhitespace "bytes".endPos)) from rfl]
  rw [Shortcuts.takeWhileAux_stop_false _ _ _ _ (by decide) (by decide)]
  rw [Shortcuts.takeRightWhileAux_stop_false _ _ _ _ (by decide) (by decide)]
  decide

theorem trim_09 : "0-9".trim = "0-9" := by
  rw [show "0-9".trim
        = ("0-9".extract
            (Substring.takeWhileAux "0-9" "0-9".endPos Char.isWhitespace 0)
            (Substring.takeRightWhileAux "0-9"
              (Substring.takeWhileAux "0-9" "0-9".endPos Char.isWhitespace 0)
              Char.isWhitespace "0-9".endPos)) from rfl]
  rw [Shortcuts.takeWhileAux_stop_false _ _ _ _ (by decide) (by decide)]
  rw [Shortcuts.takeRightWhileAux_stop_false _ _ _ _ (by decide) (by decide)]
  decide

theorem dash_not_prefix_09 : "-".isPrefixOf "0-9" = false := by
  rw [show "-".isPrefixOf "0-9"
        = ((0 + 1 ≤ "-".endPos.byteIdx) && (0 + 1 ≤ "0-9".endPos.byteIdx)
            && String.substrEq.loop "-" "0-9" 0 0 ⟨0 + 1⟩) from rfl]
  rw [Shortcuts.substrEq_loop_step _ _ _ _ _ (by decide)]
  rw [show ("-".get 0 == "0-9".get 0) = false from rfl, Bool.false_and]
  decide

theorem isNat_0 : "0".isNat = true := by
  rw [show "0".isNat
        = (!"0".isEmpty && !String.anyAux "0" "0".endPos (fun c => !c.isDigit) 0) from rfl]
  rw [Shortcuts.anyAux_step _ _ _ _ (by decide) (by decide),
      Shortcuts.anyAux_stop _ _ _ _ (by decide)]
  decide

theorem toNatQ_0 : "0".toNat? = some 0 := by
  rw [show "0".toNat?
        = (if "0".isNat then some ("0".foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0)
           else none) from rfl]
  rw [if_pos (by rw [isNat_0])]
  rw [show "0".foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0
        = String.foldlAux (fun n c => n * 10 + (c.toNat - '0'.toNat)) "0" "0".endPos 0 0
        from rfl]
  rw [Shortcuts.foldlAux_step _ _ _ _ _ (by decide),
      Shortcuts.foldlAux_stop _ _ _ _ _ (by decide)]
  decide

theorem isNat_9 : "9".isNat = true := by
  rw [show "9".isNat
        = (!"9".isEmpty && !String.anyAux "9" "9".endPos (fun c => !c.isDigit) 0) from rfl]
  rw [Shortcuts.anyAux_step _ _ _ _ (by decide) (by decide),
      Shortcuts.anyAux_stop _ _ _ _ (by decide)]
  decide

theorem toNatQ_9 : "9".toNat? = some 9 := by
  rw [show "9".toNat?
        = (if "9".isNat then some ("9".foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0)
           else none) from rfl]
  rw [if_pos (by rw [isNat_9])]
  rw [show "9".foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0
        = String.foldlAux (fun n c => n * 10 + (c.toNat - '0'.toNat)) "9" "9".endPos 0 0
        from rfl]
  rw [Shortcuts.foldlAux_step _ _ _ _ _ (by decide),
      Shortcuts.foldlAux_stop _ _ _ _ _ (by decide)]
  decide

/-- The deployed one-spec parse: `0-9` is `fromTo 0 9` (RFC 7233 §2.1). -/
theorem parseOneSpec_09 : parseOneSpec "0-9" = some (RangeSpec.fromTo 0 9) := by
  simp only [StaticFile.parseOneSpec, trim_09, dash_not_prefix_09, splitOn_09_dash,
    toNatQ_0, toNatQ_9]
  rfl

/-- The deployed range-set parse of the raw value: `bytes=0-9` ⇒ `[fromTo 0 9]`. -/
theorem parseRangeSet_bytes09 : parseRangeSet "bytes=0-9" = [RangeSpec.fromTo 0 9] := by
  simp only [StaticFile.parseRangeSet, splitOn_bytes09, trim_bytes, splitOn_09_comma,
    List.filterMap, parseOneSpec_09]
  rfl

/-- The whole deployed `Req` build over the raw wire header, in the pure kernel. -/
theorem reqOfHeaders_range :
    reqOfHeaders [rangeHeader]
      = { target := [], ifNoneMatch := [],
          range := some (RangeSpec.fromTo 0 9),
          rangeSet := [RangeSpec.fromTo 0 9],
          ifModifiedSince := none, ifRange := none } := by
  simp only [StaticFile.reqOfHeaders, findHeader_inm, findHeader_range, Option.map,
    Option.getD, parseRangeSet_bytes09, List.head?]

/-! ## The deployed header parser turns the raw `Range:` bytes into a range-set -/

/-- **`range_header_parses`.** `reqOfHeaders`, the parser the deployed `serveDeployed`
runs over the raw request headers, maps the wire header `Range: bytes=0-9` to the model
range-set `[.fromTo 0 9]` and a matching single `range`. This is the running parse, not
a hand-supplied Req — and it is now evaluated in the PURE KERNEL (formerly
`native_decide`/`Lean.ofReduceBool`). -/
theorem range_header_parses :
    (reqOfHeaders [rangeHeader]).rangeSet = [RangeSpec.fromTo 0 9]
  ∧ (reqOfHeaders [rangeHeader]).range = some (RangeSpec.fromTo 0 9)
  ∧ (reqOfHeaders [rangeHeader]).ifNoneMatch = []
  ∧ (reqOfHeaders [rangeHeader]).ifRange = none := by
  rw [reqOfHeaders_range]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## The deployed `206` -/

/-- `appJs` is 35 bytes long (the embedded `/static/app.js` content), so the range
`0-9` is satisfiable and the `Content-Range` completes to `/35`. -/
theorem appJs_len : appJs.length = 35 := by
  simp only [appJs, strBytes, Shortcuts.ba_toList_eq]; decide

/-- The `bytes=0-9` spec resolves to the inclusive offsets `(0, 9)` on a 35-byte
representation (RFC 7233 §2.1). -/
theorem range_resolves : resolveAll appJs.length [RangeSpec.fromTo 0 9] = [(0, 9)] := by
  rw [appJs_len]; decide

/-- The `serveConditional` selection for the parsed range request over the deployed
config: a single-range `206`, body `slice appJs 0 9`, complete length `appJs.length`. -/
theorem range_selects :
    serveConditional deployedConfig (reqOfHeaders [rangeHeader]) assetSegs
      = .partialContent (slice appJs 0 9) 0 9 appJs.length (contentETag appJs) := by
  have hnm : ifNoneMatchHit (reqOfHeaders [rangeHeader]).ifNoneMatch
      (deployedConfig.etag assetSegs) = false := by
    rw [range_header_parses.2.2.1]; rfl
  refine serveConditional_single deployedConfig (reqOfHeaders [rangeHeader]) assetSegs
    appJs (RangeSpec.fromTo 0 9) [] 0 9 rfl hnm ?_ ?_ range_header_parses.1 range_resolves
  · rfl
  · rw [range_header_parses.2.2.2]; rfl

/-- **`deployed_range_206`.** The DEPLOYED handler answers `GET /static/app.js` with
`Range: bytes=0-9` by a `206 (Partial Content)` whose body is exactly the first ten
bytes `slice appJs 0 9`, carrying `Content-Range: bytes 0-9/35` and `Accept-Ranges:
bytes` — the exact `206` the curl above observes. Pure kernel end to end (the two
header memberships formerly closed by `native_decide`). -/
theorem deployed_range_206 :
    (serveDeployed assetSegs [rangeHeader]).status = 206
  ∧ (serveDeployed assetSegs [rangeHeader]).body = slice appJs 0 9
  ∧ (strBytes "Content-Range", strBytes "bytes 0-9/35")
        ∈ (serveDeployed assetSegs [rangeHeader]).headers
  ∧ (strBytes "Accept-Ranges", strBytes "bytes")
        ∈ (serveDeployed assetSegs [rangeHeader]).headers := by
  have hsel : serveDeployed assetSegs [rangeHeader]
      = toResponse (.partialContent (slice appJs 0 9) 0 9 appJs.length (contentETag appJs)) := by
    unfold serveDeployed; rw [range_selects]
  rw [hsel, appJs_len]
  refine ⟨rfl, rfl, ?_, ?_⟩ <;>
    (simp only [StaticFile.toResponse, StaticFile.strBytes, StaticFile.renderETag,
       StaticFile.appJs, Shortcuts.ba_toList_eq];
     decide)

/-- The deployed handler ties `serveDeployed` to the running staticFile route: for any
request whose normalized target is `/static/app.js` and whose headers are the single
`Range` header, the app's `staticFile` response IS this `206`. -/
theorem deployed_range_route (req : Proto.Request)
    (htarget : Reactor.App.targetSegments req.target = assetSegs)
    (hhdr : req.headers = [rangeHeader]) :
    (Reactor.App.responseOfReq req .staticFile).status = 206
  ∧ (Reactor.App.responseOfReq req .staticFile).body = slice appJs 0 9 := by
  rw [Proto.EtagProven.deployed_staticFile_route, htarget, hhdr]
  exact ⟨deployed_range_206.1, deployed_range_206.2.1⟩

/-! ## The exact deployed-wire bytes the curl carries -/

/-- **`range_body_bytes`.** The ten `206` body bytes are exactly `"console.lo"` — the
first ten octets of `console.log('drorb static asset');\n`. This is the curl body,
octet-for-octet, so the `206` proof is grounded on the real wire (non-vacuous). -/
theorem range_body_bytes :
    slice appJs 0 9 = [0x63, 0x6f, 0x6e, 0x73, 0x6f, 0x6c, 0x65, 0x2e, 0x6c, 0x6f] := by
  simp only [appJs, strBytes, slice, Shortcuts.ba_toList_eq]; decide

end Proto.RangeProven

#print axioms Proto.RangeProven.range_header_parses
#print axioms Proto.RangeProven.range_selects
#print axioms Proto.RangeProven.deployed_range_206
#print axioms Proto.RangeProven.deployed_range_route
#print axioms Proto.RangeProven.range_body_bytes
