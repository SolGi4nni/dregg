import Cgi

-- Lean 4.30: the record round-trip's `omega` goals over nested div/mod of
-- `c.length` reach past the default 512 recursion limit during elaboration.
set_option maxRecDepth 4000

/-!
# FastCGI record framing (the gateway upstream wire, FastCGI/1.0)

`Cgi.lean` models the CGI/1.1 gateway (RFC 3875): the meta-variable environment
and the response classification. That model speaks in *strings* — it is the
process-execution boundary. A production gateway does not fork a CGI process per
request; it multiplexes requests to a long-lived application server over the
**FastCGI** binary record protocol. This module is that missing wire: the
byte-exact record framing that carries the same CGI meta-variables (as a PARAMS
name-value stream) and the request body (as STDIN) to the upstream, and reads
its records back.

Everything here is a *total, pure* codec — no I/O, no process model. The wire is
a stream of **records**, each an 8-octet header followed by content and 8-byte
alignment padding:

```text
version(1) type(1) requestId(2, BE) contentLength(2, BE) paddingLength(1) reserved(1)
<content: contentLength octets> <padding: paddingLength zero octets>
```

The application-request direction is a fixed sequence of record kinds
(FastCGI/1.0 §3.3, §5):

```text
BEGIN_REQUEST(role, flags)  PARAMS*  PARAMS(empty)  STDIN*  STDIN(empty)
```

`PARAMS` content is a self-delimiting stream of name-value pairs; each side is a
length-prefix (one octet if `< 128`, else four octets with the top bit of the
first set) followed by the raw name and value octets.

## Headline theorems

* `fcgi_record_roundtrip` — a record (type + requestId + content) `frame`s and
  `deframe`s losslessly: `deframe (frame ty id c ++ rest) = some (⟨ty,id,c⟩, rest)`
  for any following bytes, recovering the type, request id, and content exactly.
* `fcgi_params_encode` — the PARAMS name-value encoding round-trips:
  `decodeParams ps.length (encodeParams ps) = ps`, for well-formed pairs (each
  side length `< 2^31`). The round-trip witnesses that the encoding is injective
  on well-formed input, so distinct names/values are never conflated.
* `fcgi_request_wellformed` — a serialized application request deframes to the
  exact five-record sequence `BEGIN_REQUEST · PARAMS · PARAMS(∅) · STDIN ·
  STDIN(∅)`, with the BEGIN_REQUEST body carrying the RESPONDER role and both
  terminators empty (FastCGI/1.0 §3.3).

Grounded on concrete wire octets (`example … := by decide`) so no theorem is
vacuous; a length-mutant (`deframe_length_mutant`) shows a corrupted content
length recovers a *different* record, so the length field is load-bearing.
-/

namespace Cgi.FastCgi

open Cgi (Bytes)

/-! ## Protocol constants (FastCGI/1.0 §8) -/

/-- Protocol version (always 1). -/
def version : Nat := 1
/-- `FCGI_BEGIN_REQUEST` record type. -/
def beginType : Nat := 1
/-- `FCGI_END_REQUEST` record type. -/
def endType : Nat := 3
/-- `FCGI_PARAMS` record type (the meta-variable name-value stream). -/
def paramsType : Nat := 4
/-- `FCGI_STDIN` record type (the request body). -/
def stdinType : Nat := 5
/-- `FCGI_STDOUT` record type (the response body from upstream). -/
def stdoutType : Nat := 6
/-- The `FCGI_RESPONDER` role. -/
def responderRole : Nat := 1
/-- The `FCGI_KEEP_CONN` flag. -/
def keepConn : Nat := 1

/-! ## Big-endian 16-bit field -/

/-- Big-endian 16-bit encoder (request id, content length). -/
def be16 (n : Nat) : Bytes := [UInt8.ofNat (n / 256), UInt8.ofNat (n % 256)]

theorem be16_length (n : Nat) : (be16 n).length = 2 := rfl

/-! ## Record header + record -/

/-- A deframed FastCGI record: its type octet, request id, and content octets.
The version octet is fixed at 1 and the padding is alignment-only, so neither is
surfaced. -/
structure Record where
  recordType : Nat
  requestId : Nat
  content : Bytes
deriving DecidableEq, Repr

/-- Padding octets needed to 8-byte-align a record of `n` content octets
(FastCGI/1.0 §3.3). Always `< 8`. -/
def paddingFor (n : Nat) : Nat := (8 - n % 8) % 8

theorem paddingFor_lt (n : Nat) : paddingFor n < 8 :=
  Nat.mod_lt _ (by decide)

/-- The 8-octet record header. -/
def header (ty reqId clen pad : Nat) : Bytes :=
  [UInt8.ofNat version, UInt8.ofNat ty,
   UInt8.ofNat (reqId / 256), UInt8.ofNat (reqId % 256),
   UInt8.ofNat (clen / 256), UInt8.ofNat (clen % 256),
   UInt8.ofNat pad, UInt8.ofNat 0]

/-- Frame one record: header, then content, then alignment padding. -/
def frame (ty reqId : Nat) (c : Bytes) : Bytes :=
  header ty reqId c.length (paddingFor c.length)
    ++ c ++ List.replicate (paddingFor c.length) (0 : UInt8)

/-- Try to deframe one record from the front of a buffer, returning the record
and the *remaining* bytes, or `none` if the buffer is short. -/
def deframe : Bytes → Option (Record × Bytes)
  | _v :: ty :: r0 :: r1 :: c0 :: c1 :: pad :: _rsv :: rest =>
    if c0.toNat * 256 + c1.toNat + pad.toNat ≤ rest.length then
      some ({ recordType := ty.toNat,
              requestId := r0.toNat * 256 + r1.toNat,
              content := rest.take (c0.toNat * 256 + c1.toNat) },
            (rest.drop (c0.toNat * 256 + c1.toNat)).drop pad.toNat)
    else none
  | _ => none

/-- **Record round-trip.** For a type octet `< 256`, request id `< 2^16`, and
content shorter than `2^16` octets, `deframe` inverts `frame` exactly — for any
trailing bytes `rest`, recovering the type, request id, and content, and leaving
`rest` as the remainder. -/
theorem fcgi_record_roundtrip (ty reqId : Nat) (c rest : Bytes)
    (hty : ty < 256) (hid : reqId < 65536) (hc : c.length < 65536) :
    deframe (frame ty reqId c ++ rest)
      = some ({ recordType := ty, requestId := reqId, content := c }, rest) := by
  have hpad : paddingFor c.length < 8 := paddingFor_lt _
  simp only [frame, header, List.cons_append, List.nil_append, List.append_assoc,
    deframe, UInt8.toNat_ofNat']
  have hLc : c.length / 256 % 256 * 256 + c.length % 256 % 256 = c.length := by omega
  have hRid : reqId / 256 % 256 * 256 + reqId % 256 % 256 = reqId := by omega
  have hTy : ty % 256 = ty := by omega
  have hPad : paddingFor c.length % 256 = paddingFor c.length := by omega
  have hlen : (c ++ (List.replicate (paddingFor c.length) (0 : UInt8) ++ rest)).length
      = c.length + (paddingFor c.length + rest.length) := by
    simp [List.length_append, List.length_replicate]
  rw [hLc, hRid, hTy, hPad, if_pos (by rw [hlen]; omega),
      List.take_left' (l₁ := c) rfl,
      List.drop_left' (l₁ := c) rfl,
      List.drop_left' (l₁ := List.replicate (paddingFor c.length) (0 : UInt8)) (by simp)]

/-- Round-trip specialized to an empty tail (a record laid alone on the wire). -/
theorem fcgi_record_roundtrip_nil (ty reqId : Nat) (c : Bytes)
    (hty : ty < 256) (hid : reqId < 65536) (hc : c.length < 65536) :
    deframe (frame ty reqId c)
      = some ({ recordType := ty, requestId := reqId, content := c }, []) := by
  have h := fcgi_record_roundtrip ty reqId c [] hty hid hc
  simpa using h

/-! ## PARAMS name-value encoding (FastCGI/1.0 §3.4) -/

/-- Encode a length prefix: one octet if `< 128`, else four octets with the top
bit of the first set (the value occupies the low 31 bits). -/
def encodeLen (n : Nat) : Bytes :=
  if n < 128 then [UInt8.ofNat n]
  else [UInt8.ofNat (n / 16777216 % 256 + 128),
        UInt8.ofNat (n / 65536 % 256),
        UInt8.ofNat (n / 256 % 256),
        UInt8.ofNat (n % 256)]

/-- Decode a length prefix, returning the length and remaining bytes. -/
def decodeLen : Bytes → Option (Nat × Bytes)
  | b :: rest =>
    if b.toNat < 128 then some (b.toNat, rest)
    else match rest with
      | b1 :: b2 :: b3 :: rest' =>
        some ((b.toNat - 128) * 16777216 + b1.toNat * 65536
                + b2.toNat * 256 + b3.toNat, rest')
      | _ => none
  | [] => none

/-- The length codec round-trips for lengths `< 2^31`. -/
theorem decodeLen_encodeLen (n : Nat) (rest : Bytes) (h : n < 2147483648) :
    decodeLen (encodeLen n ++ rest) = some (n, rest) := by
  by_cases hn : n < 128
  · simp only [encodeLen, hn, if_true, List.cons_append, List.nil_append,
      decodeLen, UInt8.toNat_ofNat']
    rw [if_pos (show n % 256 < 128 by omega)]
    congr 1
    refine Prod.ext ?_ rfl
    simp only []
    omega
  · simp only [encodeLen, hn, if_false, List.cons_append, List.nil_append,
      decodeLen, UInt8.toNat_ofNat']
    rw [if_neg (show ¬ (n / 16777216 % 256 + 128) % 256 < 128 by omega)]
    refine congrArg some (Prod.ext ?_ rfl)
    simp only []
    omega

/-- Encode a list of name-value pairs to the PARAMS wire stream. -/
def encodeParams : List (Bytes × Bytes) → Bytes
  | [] => []
  | (nm, v) :: rest =>
    encodeLen nm.length ++ encodeLen v.length ++ nm ++ v ++ encodeParams rest

/-- Decode one name-value pair, returning the pair and remaining bytes. -/
def decodePair (buf : Bytes) : Option ((Bytes × Bytes) × Bytes) :=
  match decodeLen buf with
  | none => none
  | some (nlen, r1) =>
    match decodeLen r1 with
    | none => none
    | some (vlen, r2) =>
      if nlen + vlen ≤ r2.length then
        some ((r2.take nlen, (r2.drop nlen).take vlen), (r2.drop nlen).drop vlen)
      else none

/-- Decode a PARAMS stream, peeling `fuel` pairs. -/
def decodeParams : Nat → Bytes → List (Bytes × Bytes)
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, buf =>
    match decodePair buf with
    | some (p, rest) => p :: decodeParams fuel rest
    | none => []

/-- Well-formed pair: each side is shorter than the 31-bit length limit. -/
def PairWF (p : Bytes × Bytes) : Prop := p.1.length < 2147483648 ∧ p.2.length < 2147483648

/-- One pair peels off cleanly from an encoded stream. -/
theorem decodePair_encode (nm v rest : Bytes)
    (hn : nm.length < 2147483648) (hv : v.length < 2147483648) :
    decodePair (encodeLen nm.length ++ encodeLen v.length ++ nm ++ v ++ rest)
      = some ((nm, v), rest) := by
  have hb : encodeLen nm.length ++ encodeLen v.length ++ nm ++ v ++ rest
      = encodeLen nm.length ++ (encodeLen v.length ++ (nm ++ (v ++ rest))) := by
    simp [List.append_assoc]
  rw [hb, decodePair, decodeLen_encodeLen nm.length _ hn]
  dsimp only
  rw [decodeLen_encodeLen v.length _ hv]
  dsimp only
  rw [if_pos (by simp only [List.length_append]; omega),
      List.take_left' (l₁ := nm) rfl, List.drop_left' (l₁ := nm) rfl,
      List.take_left' (l₁ := v) rfl, List.drop_left' (l₁ := v) rfl]

/-- One pair peels off `decodeParams` given a successful `decodePair`. -/
theorem decodeParams_succ (fuel : Nat) (buf : Bytes) (p : Bytes × Bytes) (rest : Bytes)
    (h : decodePair buf = some (p, rest)) :
    decodeParams (fuel + 1) buf = p :: decodeParams fuel rest := by
  cases buf with
  | nil => simp [decodePair, decodeLen] at h
  | cons b bs => simp only [decodeParams, h]

/-- **PARAMS round-trip.** For a list of well-formed name-value pairs, decoding
the encoded stream (with fuel = the pair count) recovers the pairs exactly. -/
theorem fcgi_params_encode (ps : List (Bytes × Bytes)) (h : ∀ p ∈ ps, PairWF p) :
    decodeParams ps.length (encodeParams ps) = ps := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨nm, v⟩ := p
    have hp : PairWF (nm, v) := h (nm, v) (by simp)
    have hrest : ∀ q ∈ rest, PairWF q := fun q hq => h q (by simp [hq])
    simp only [List.length_cons, encodeParams]
    rw [decodeParams_succ rest.length _ (nm, v) (encodeParams rest)
          (decodePair_encode nm v (encodeParams rest) hp.1 hp.2)]
    rw [ih hrest]

/-! ## Application request framing (FastCGI/1.0 §3.3) -/

/-- The 8-octet BEGIN_REQUEST body: role (BE16), flags octet, five reserved. -/
def beginBody (role flags : Nat) : Bytes :=
  be16 role ++ [UInt8.ofNat flags, 0, 0, 0, 0, 0]

theorem beginBody_length (role flags : Nat) : (beginBody role flags).length = 8 := rfl

/-- Serialize a complete application request: BEGIN_REQUEST (RESPONDER role,
keep-conn), the PARAMS stream, the empty-PARAMS terminator, STDIN (body), and the
empty-STDIN terminator (FastCGI/1.0 §3.3, §5). -/
def serializeRequest (reqId : Nat) (params : List (Bytes × Bytes)) (body : Bytes) : Bytes :=
  frame beginType reqId (beginBody responderRole keepConn)
    ++ (frame paramsType reqId (encodeParams params)
    ++ (frame paramsType reqId []
    ++ (frame stdinType reqId body
    ++ frame stdinType reqId [])))

/-- **Request well-formedness.** A serialized application request deframes to the
exact five-record sequence `BEGIN_REQUEST · PARAMS · PARAMS(∅) · STDIN ·
STDIN(∅)`: the BEGIN_REQUEST body carries the RESPONDER role, the PARAMS record
carries the encoded meta-variable stream, and both terminators are empty. The
existential tails are the byte offsets between records; each `deframe` recovers
one record and hands the next its start. -/
theorem fcgi_request_wellformed (reqId : Nat) (params : List (Bytes × Bytes)) (body : Bytes)
    (hid : reqId < 65536)
    (hp : (encodeParams params).length < 65536)
    (hb : body.length < 65536) :
    ∃ t1 t2 t3 t4,
      deframe (serializeRequest reqId params body)
        = some (⟨beginType, reqId, beginBody responderRole keepConn⟩, t1) ∧
      deframe t1 = some (⟨paramsType, reqId, encodeParams params⟩, t2) ∧
      deframe t2 = some (⟨paramsType, reqId, []⟩, t3) ∧
      deframe t3 = some (⟨stdinType, reqId, body⟩, t4) ∧
      deframe t4 = some (⟨stdinType, reqId, []⟩, []) := by
  have hbb : (beginBody responderRole keepConn).length < 65536 := by
    rw [beginBody_length]; decide
  refine ⟨ frame paramsType reqId (encodeParams params)
             ++ (frame paramsType reqId []
             ++ (frame stdinType reqId body ++ frame stdinType reqId [])),
           frame paramsType reqId []
             ++ (frame stdinType reqId body ++ frame stdinType reqId []),
           frame stdinType reqId body ++ frame stdinType reqId [],
           frame stdinType reqId [],
           ?_, ?_, ?_, ?_, ?_ ⟩
  · exact fcgi_record_roundtrip beginType reqId _ _ (by decide) hid hbb
  · exact fcgi_record_roundtrip paramsType reqId _ _ (by decide) hid hp
  · exact fcgi_record_roundtrip paramsType reqId _ _ (by decide) hid (by decide)
  · exact fcgi_record_roundtrip stdinType reqId _ _ (by decide) hid hb
  · exact fcgi_record_roundtrip_nil stdinType reqId _ (by decide) hid (by decide)

/-! ## Non-vacuity: concrete wire, and a load-bearing length field -/

/-- A concrete STDOUT record ("Hi", request id 1) frames and deframes back. -/
example :
    deframe (frame stdoutType 1 [72, 105]) = some (⟨6, 1, [72, 105]⟩, []) := by
  decide

/-- A three-pair PARAMS block (a real CGI meta-variable slice) round-trips. -/
example :
    let ps : List (Bytes × Bytes) :=
      [([82, 77], [71, 69, 84]), ([81, 83], [102, 111, 111]), ([72, 72], [104])]
    decodeParams ps.length (encodeParams ps) = ps := by decide

/-- **Length field is load-bearing.** If the encoded content-length octet is
mutated (here understating the length by one), `deframe` recovers a *different*,
shorter record — so the framing genuinely depends on the length, not just the
payload bytes. -/
theorem deframe_length_mutant :
    deframe (header stdoutType 1 1 (paddingFor 2) ++ [72, 105]
              ++ List.replicate (paddingFor 2) 0)
      ≠ some (⟨6, 1, [72, 105]⟩, []) := by
  decide

end Cgi.FastCgi
