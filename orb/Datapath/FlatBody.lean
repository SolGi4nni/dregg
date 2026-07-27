import Datapath.FlatWire
import Reactor.Stage.Compress

/-!
# Datapath.FlatBody — the response BODY carried as a genuine `ByteArray` on the flat
egress path (kills K2's body cons + R3's `body.toArray`)

The header fan-out (`Datapath.FlatHeaders`, `Datapath.FlatWire`) removed the response
*header* cons-spine, but the flat egress serializer `Datapath.FlatWire.serializeFlat`
STILL takes `body : Proto.Bytes = List UInt8` and, at its very last step, `body.toArray`s
it (`FlatWire.lean:90-93`). That is residual **R3** in `CONS-LIST-KILLLIST.md`, and it is
the flat-egress face of **K2**: the deployed response body is a genuine runtime
`List UInt8` — built `.toUTF8.toList` in `Reactor.App` (App.lean:153-172, the SOURCE
cons), transformed `codecTag enc :: body` by the compress stage
(`Reactor.Stage.Compress.encode`, Compress.lean:130, a `List` prepend), and appended
once at egress. On an 8 KB body that per-byte cons-spine is the measured body-cliff
(`DATAPATH-SPEED-STORY.md`).

This module builds the FLAT-BODY egress path: the body is a `ByteArray` end to end, NEVER
a runtime `List UInt8`.

* `serializeFlatB` — the flat egress serializer over a `ByteArray` body. Identical to
  `FlatWire.serializeFlat` except the body arg is a `ByteArray` and the final wire append
  is `... ++ fbody.data` (an `Array UInt8` append), and the derived `Content-Length` is
  computed from `fbody.size` (`O(1)`, no `List.length` walk). **No `body.toArray`, no
  `List UInt8` body — R3 killed.**

* `prependTag` — the compress container `codecTag enc :: body`, done FLAT: prepend the
  codec-tag byte to the `ByteArray` body as `#[tag] ++ fbody.data` (an `Array` op).
  `prependTag_encode` proves it denotes to the REAL `Reactor.Stage.Compress.encode enc`
  of the body — the SPEC's `List` prepend is only on the RHS.

* `serializeFlatB_refines` — **byte-identical** to the DEPLOYED `List`-body serializer:
  `serializeFlatB status reason hb fbody` refines
  `Reactor.serialize (FlatWire.respOf status reason hb fbody.data.toList)`. The `List`
  body (`fbody.data.toList`) is ONLY on the spec (RHS) side — the flat computation carries
  the `ByteArray` and never materializes a body `List`. Proven by an equality transfer to
  `FlatWire.serializeFlat_refines`, not a re-spec.

* `flatBodyServe_refines` — the exemplar COMPOSE: the flat security-header stage
  (`FlatStage.flatSecurityStage`, an `Array.push` fold on `HdrBlock`) supplies the flat
  header block AND the body is carried as a `ByteArray` (codec-tag-prepended flat),
  egressed by `serializeFlatB` — byte-identical to `Reactor.serialize` of the DEPLOYED
  secured, compressed `List`-body response. NO `Reactor.Response` record and NO runtime
  `List UInt8` body is ever built on this path.

## Honest scope

`Proto.Bytes := List UInt8` (`Proto/Basic.lean:28`) and `Reactor.Response.body : Bytes`
are UNCHANGED — the `Reactor.Response` with a `List` body appears ONLY as the spec object
on the RHS of every refinement here (it is the abstract thing the flat path is proven
byte-identical to; it is never constructed on the flat computation path). This is the same
equality-transfer discipline `HdrBlock`/`serializeFlat` used for the header block: the
flat runtime object (here a `ByteArray` body) is proven equal to the deployed `List`-typed
spec, with the 15k proofs and the `Bytes` root untouched. Migrating `Response.body`'s TYPE
to `ByteArray` (so the *deployed* serve also carries no body `List`) is a separate root
change (see the report); the flat-body serve is achieved additively without it.

The one residual `Array.toList` still present is `flatRenderBlock`'s HEADER-fragment
enumeration inside the un-modifiable `FlatHeaders` (residual R1) — a distinct,
`O(#headers)` header item, NOT the body. The body is a genuine `ByteArray` throughout.
-/

namespace Datapath.FlatBody

open Proto (Bytes)
open Reactor (Response)
open Datapath.FlatHeaders (HdrBlock flatRenderBlock)
open Datapath.FlatStage (flatSecurityStage securedResp flatSecurityStage_refines)
open Datapath.FlatWire (respOf serializeFlat serializeFlat_refines clHeader)
open Reactor.Stage.SecurityHeaders (wireHeaders policy)
open Reactor.Stage.Compress (Encoding encode codecTag)

/-! ## The flat egress serializer over a `ByteArray` body — R3 killed -/

/-- The `Content-Length` header derived from the body's SIZE — the SAME
`(clName, natToDec body.length)` pair the deployed `Reactor.allHeaders` appends, but the
length is read from the `ByteArray`'s `size` field (`O(1)`) instead of walking a `List`.
`fbody.size = fbody.data.toList.length`, so the emitted value is identical. -/
def clHeaderB (fbody : ByteArray) : Bytes × Bytes := (Reactor.clName, Reactor.natToDec fbody.size)

/-- **The flat response serializer with the body as a genuine `ByteArray`.** Renders the
response bytes from the flat header block and the `ByteArray` body: push the derived
`Content-Length` onto the flat block (`HdrBlock.addHeader`, an `Array.push`), render the
block flat (`FlatHeaders.flatRenderBlock`), frame it with the status line and blank-line
separator, and append the body as `fbody.data` — an `Array UInt8` append, NOT `body.toArray`
of a `List`. The body is never a runtime `List UInt8`; R3 is killed. -/
def serializeFlatB (status : Nat) (reason : Bytes) (hb : HdrBlock) (fbody : ByteArray) : ByteArray :=
  let statusBytes : Array UInt8 :=
    (Reactor.http11 ++ [32] ++ Reactor.natToDec status ++ [32] ++ reason).toArray
  ByteArray.mk (
    statusBytes
      ++ Reactor.crlf.toArray
      ++ flatRenderBlock (hb.addHeader (clHeaderB fbody))
      ++ Reactor.crlf.toArray
      ++ Reactor.crlf.toArray
      ++ fbody.data)

/-- `serializeFlatB` on a `ByteArray` body computes exactly `FlatWire.serializeFlat` on
that body's denotation — the two agree because `fbody.data.toList.toArray = fbody.data`
(the final append) and `fbody.size = fbody.data.toList.length` (the `Content-Length`). The
`.toList` appears ONLY on the RHS here (it is the bridge to the `List`-body serializer);
the LHS `serializeFlatB` never touches a body `List`. -/
theorem serializeFlatB_eq (status : Nat) (reason : Bytes) (hb : HdrBlock) (fbody : ByteArray) :
    serializeFlatB status reason hb fbody = serializeFlat status reason hb fbody.data.toList := by
  have hlen : fbody.size = fbody.data.toList.length := (Array.length_toList).symm
  have hdata : fbody.data.toList.toArray = fbody.data := Array.toArray_toList
  unfold serializeFlatB serializeFlat clHeaderB clHeader
  rw [hlen, hdata]

/-- **THE FLAT-BODY EGRESS BYTE-IDENTITY.** `serializeFlatB status reason hb fbody` is
byte-identical to the DEPLOYED `Reactor.serialize` on the response with header block
`hb.denote` and body `fbody.data.toList`. The body `List` (`fbody.data.toList`) is ONLY on
the spec (RHS) side — the flat computation carries the `ByteArray` and never materializes a
body `List` (R3 killed). Equality transfer to `FlatWire.serializeFlat_refines`, no re-spec. -/
theorem serializeFlatB_refines (status : Nat) (reason : Bytes) (hb : HdrBlock) (fbody : ByteArray) :
    Datapath.Refinement.Refines (Reactor.serialize (respOf status reason hb fbody.data.toList))
      (serializeFlatB status reason hb fbody) := by
  rw [serializeFlatB_eq]
  exact serializeFlat_refines status reason hb fbody.data.toList

/-! ## The compress container, done FLAT — a `ByteArray` codec-tag prepend -/

/-- **The compress container `codecTag enc :: body`, done FLAT.** Prepend the codec-tag
byte to the `ByteArray` body as `#[tag] ++ fbody.data` — an `Array UInt8` op, no `List`
cons. This is the flat sibling of `Reactor.Stage.Compress.encode`'s `codecTag enc :: body`. -/
def prependTag (tag : UInt8) (fbody : ByteArray) : ByteArray := ByteArray.mk (#[tag] ++ fbody.data)

/-- The flat prepend denotes to the `List` prepend `tag :: fbody.data.toList` — the
abstraction relation for the codec container (RHS `List` only). -/
theorem prependTag_denote (tag : UInt8) (fbody : ByteArray) :
    (prependTag tag fbody).data.toList = tag :: fbody.data.toList := by
  show (#[tag] ++ fbody.data).toList = tag :: fbody.data.toList
  rw [Array.toList_append]
  rfl

/-- **The flat prepend IS the real compress container.** `prependTag (codecTag enc) fbody`
denotes to `Reactor.Stage.Compress.encode enc fbody.data.toList` — the DEPLOYED compress
transform. The `List` container is only the RHS spec; the flat path keeps the body a
`ByteArray`. -/
theorem prependTag_encode (enc : Encoding) (fbody : ByteArray) :
    (prependTag (codecTag enc) fbody).data.toList = encode enc fbody.data.toList := by
  rw [prependTag_denote]
  rfl

/-! ## The flat-body serves — passthrough and compressed, byte-identical to deployed -/

/-- **Passthrough flat-body serve, byte-identical to the deployed `List`-body serve.** The
body comes from `payload.toUTF8` (a `ByteArray`, the App source WITHOUT the `.toList` cons)
and is egressed by `serializeFlatB`; it is byte-identical to `Reactor.serialize` of the
deployed response whose body is `payload.toUTF8.toList` (the App `List` body — RHS spec
only). -/
theorem flatBody_passthrough_refines (status : Nat) (reason : Bytes) (hb : HdrBlock)
    (payload : String) :
    Datapath.Refinement.Refines (Reactor.serialize (respOf status reason hb payload.toUTF8.data.toList))
      (serializeFlatB status reason hb payload.toUTF8) :=
  serializeFlatB_refines status reason hb payload.toUTF8

/-- **Compressed flat-body serve, byte-identical to the deployed `List`-body serve.** The
body is codec-tag-prepended FLAT (`prependTag (codecTag enc)`, a `ByteArray` op) and
egressed by `serializeFlatB`; it is byte-identical to `Reactor.serialize` of the deployed
response whose body is the real `Reactor.Stage.Compress.encode enc payload.toUTF8.toList`
(the compress `List` prepend — RHS spec only). -/
theorem flatBody_compressed_refines (status : Nat) (reason : Bytes) (hb : HdrBlock)
    (enc : Encoding) (payload : String) :
    Datapath.Refinement.Refines (Reactor.serialize (respOf status reason hb (encode enc payload.toUTF8.data.toList)))
      (serializeFlatB status reason hb (prependTag (codecTag enc) payload.toUTF8)) := by
  have h := serializeFlatB_refines status reason hb (prependTag (codecTag enc) payload.toUTF8)
  rw [prependTag_encode] at h
  exact h

/-! ## The exemplar COMPOSE — flat header stage ⟶ flat body ⟶ flat egress, NO body `List` -/

/-- **THE FULL FLAT-BODY SERVE (exemplar).** The flat security-header stage
(`flatSecurityStage`, an `Array.push` fold on the flat `HdrBlock`) supplies the header
block; the body is carried as a `ByteArray` end to end (`fbody`, codec-tag-prepended flat
by `prependTag`); the egress is `serializeFlatB`. The result is byte-identical to
`Reactor.serialize` of the DEPLOYED secured (`securedResp`), compressed (`encode enc`)
`List`-body response. NO `Reactor.Response` record and NO runtime `List UInt8` body is ever
constructed on the flat path — K2 + R3 killed for the exemplar, with the deployed `List`
body only as the spec. Chains the flat-header effect (`flatSecurityStage_refines`) and the
flat-body container (`prependTag_encode`) into `serializeFlatB_refines`. -/
theorem flatBodyServe_refines (status : Nat) (reason : Bytes) (baseHeaders : List (Bytes × Bytes))
    (enc : Encoding) (fbody : ByteArray) :
    Datapath.Refinement.Refines
      (Reactor.serialize
        (securedResp { status := status, reason := reason, headers := baseHeaders,
                       body := encode enc fbody.data.toList }))
      (serializeFlatB status reason (flatSecurityStage (HdrBlock.ofList baseHeaders))
        (prependTag (codecTag enc) fbody)) := by
  have hbody : (prependTag (codecTag enc) fbody).data.toList = encode enc fbody.data.toList :=
    prependTag_encode enc fbody
  have hhdr : (flatSecurityStage (HdrBlock.ofList baseHeaders)).denote
      = baseHeaders ++ wireHeaders policy := by
    rw [flatSecurityStage_refines (HdrBlock.ofList baseHeaders), HdrBlock.denote_ofList]
  have key : respOf status reason (flatSecurityStage (HdrBlock.ofList baseHeaders))
        (prependTag (codecTag enc) fbody).data.toList
      = securedResp { status := status, reason := reason, headers := baseHeaders,
                      body := encode enc fbody.data.toList } := by
    unfold respOf securedResp
    rw [hbody, hhdr]
  rw [← key]
  exact serializeFlatB_refines status reason (flatSecurityStage (HdrBlock.ofList baseHeaders))
    (prependTag (codecTag enc) fbody)

/-! ## Non-vacuity — concrete bodies to the exact wire bytes (evaluated by the kernel) -/

/-- A concrete 2-header flat block: `X-A: 1` and `X-B: 22`. -/
def demoBlock : HdrBlock :=
  HdrBlock.ofList [("X-A".toUTF8.toList, "1".toUTF8.toList), ("X-B".toUTF8.toList, "22".toUTF8.toList)]

-- Passthrough: the `ByteArray`-body flat serializer produces the exact HTTP/1.1 wire
-- response (status line + headers + derived Content-Length + blank line + body) — the
-- concrete wire witness, body from `.toUTF8` (a ByteArray), never a `List`.
#guard (serializeFlatB 200 Reactor.reasonOK demoBlock "hello".toUTF8).data.toList
        == "HTTP/1.1 200 OK\r\nX-A: 1\r\nX-B: 22\r\nContent-Length: 5\r\n\r\nhello".toUTF8.toList

-- Passthrough agrees with the deployed `List`-body serializer, evaluated by the kernel.
#guard (serializeFlatB 200 Reactor.reasonOK demoBlock "hello".toUTF8).data.toList
        == Reactor.serialize (respOf 200 Reactor.reasonOK demoBlock "hello".toUTF8.toList)

-- Compressed: gzip container (tag 0x1F) prepended FLAT; the exact wire bytes are the head
-- with Content-Length 3 then the 3 body bytes `[0x1F, 'h', 'i']` — the concrete compressed
-- wire witness.
#guard (serializeFlatB 200 Reactor.reasonOK demoBlock (prependTag (codecTag .gzip) "hi".toUTF8)).data.toList
        == ("HTTP/1.1 200 OK\r\nX-A: 1\r\nX-B: 22\r\nContent-Length: 3\r\n\r\n".toUTF8.toList
             ++ [(0x1F : UInt8), 104, 105])

-- Compressed agrees with the deployed serialize of the REAL compress-encoded `List` body.
#guard (serializeFlatB 200 Reactor.reasonOK demoBlock (prependTag (codecTag .gzip) "hi".toUTF8)).data.toList
        == Reactor.serialize (respOf 200 Reactor.reasonOK demoBlock (encode .gzip "hi".toUTF8.toList))

-- Genuine dependence on the body: different bodies give different flat wire bytes.
#guard (serializeFlatB 200 Reactor.reasonOK demoBlock "a".toUTF8).data.toList
        != (serializeFlatB 200 Reactor.reasonOK demoBlock "bb".toUTF8).data.toList

-- The flat prepend equals the real compress container, evaluated.
#guard (prependTag (codecTag .gzip) "hi".toUTF8).data.toList == encode .gzip "hi".toUTF8.toList

/-! ## Axiom audit -/

#print axioms serializeFlatB_refines
#print axioms prependTag_encode
#print axioms flatBody_passthrough_refines
#print axioms flatBody_compressed_refines
#print axioms flatBodyServe_refines

end Datapath.FlatBody
