import Reactor.Proxy.Grpc
import Reactor.ProxyDial

/-!
# Proxy.GrpcHealth — the verified `grpc.health.v1.Health/Check` probe

An active health checker can speak the standard gRPC health protocol
(`grpc.health.v1`, the canonical `Health/Check` unary RPC) to decide whether an
upstream is fit to receive traffic. This module is the *proven codec + verdict*
for that probe:

* build a `HealthCheckRequest` for a service name (protobuf field 1 = the name),
  gRPC-framed, ready to POST to `/grpc.health.v1.Health/Check`;
* parse the framed `HealthCheckResponse` (protobuf field 1 = the `ServingStatus`
  enum) together with the `grpc-status` trailer into a single up/down verdict;
* map that verdict onto the load balancer's health mask so the **proven pick**
  (`Reactor.ProxyDial.pickWith`) ejects a `NOT_SERVING` (or otherwise
  non-`SERVING`) backend for *any* configured LB policy chain.

The gRPC message framing is the already-proven length-prefixed codec
(`Reactor.Proxy.Grpc.encodeFrame` / `decodeFrame`, inverse by
`decodeFrame_encodeFrame`); the `ServingStatus` enum is
`Reactor.Proxy.Grpc.ServingStatus`. What this module adds is the two protobuf
bodies (a hand-rolled LEB128 varint + the two one-field messages) and the
composition with selection.

## Protobuf on the wire

`HealthCheckRequest` is one length-delimited field: tag `0x0A` (field 1, wire
type 2), a LEB128 length, then the UTF-8 service-name bytes. An empty service
name is the empty payload (queries the whole-server status). `HealthCheckResponse`
is one varint field: tag `0x08` (field 1, wire type 0), a LEB128
`ServingStatus`; `UNKNOWN` is the default and encodes to the empty payload.

## Key theorems

* `decVarint_encVarint` — the LEB128 varint round-trips (`decode ∘ encode = id`),
  leaving any tail untouched, for **every** `Nat`.
* `grpc_health_request_roundtrip` — a built `HealthCheckRequest` parses back to
  the exact service name (the request/response framing is faithful).
* `grpc_health_response_roundtrip` — a built `HealthCheckResponse` parses back to
  the exact `ServingStatus`.
* `check_maps_serving` — an `OK`-trailer Check response maps **exactly** onto the
  serving status's healthy bit: `checkResponseHealthy .ok (build s) = s.isHealthy`.
* `grpc_health_check_maps` — the composed statement: a non-`SERVING` Check verdict,
  taken as backend `i`'s health-mask bit, is never returned by the proven pick,
  for any config LB policy chain (through `pickWith_health_ejects`).

## Boundaries

The probe *transport* (issuing the HTTP/2 POST on the interval, collecting the
response body + trailers) is the host's; this module consumes the bytes it
returns. The mask-bit contract (bit `i` reflects backend `i`'s verdict) is the
`drorb_proxy_pick` ABI the host discharges when it builds the mask.
-/

namespace Proxy.GrpcHealth

open Reactor.Proxy

/-! ## LEB128 varint (base-128 little-endian, over the `List Nat` byte model) -/

/-- Unsigned LEB128 varint: each byte carries 7 bits of magnitude, the high bit
(`+128`) is the continuation flag, clear on the last byte. -/
def encVarint (n : Nat) : List Nat :=
  if n < 128 then [n]
  else (n % 128 + 128) :: encVarint (n / 128)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- Read one LEB128 varint off the front, returning the value and the rest. -/
def decVarint : List Nat → Option (Nat × List Nat)
  | [] => none
  | b :: rest =>
    if b < 128 then some (b, rest)
    else match decVarint rest with
      | some (m, rest') => some ((b - 128) + 128 * m, rest')
      | none => none

/-- **Varint round-trip.** Encoding a `Nat` and reading it back recovers the
value exactly and leaves any trailing bytes untouched, for every `Nat`. -/
theorem decVarint_encVarint (n : Nat) (tail : List Nat) :
    decVarint (encVarint n ++ tail) = some (n, tail) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [encVarint]
    by_cases h : n < 128
    · rw [if_pos h]
      simp only [List.cons_append, List.nil_append, decVarint]
      rw [if_pos h]
    · rw [if_neg h]
      simp only [List.cons_append, decVarint]
      rw [if_neg (by omega)]
      have hdiv : n / 128 < n := Nat.div_lt_self (by omega) (by omega)
      rw [ih (n / 128) hdiv]
      dsimp only
      have hrec : (n % 128 + 128) - 128 + 128 * (n / 128) = n := by
        have := Nat.div_add_mod n 128; omega
      rw [hrec]

/-! ## `HealthCheckRequest` — one length-delimited service-name field -/

/-- Encode a `HealthCheckRequest` protobuf payload for a service name (bytes).
Field 1 (string, wire type 2): tag `0x0A`, LEB128 length, name bytes. An empty
name is the empty payload — the health spec's "whole server" query. -/
def encodeHealthRequest (service : List Nat) : List Nat :=
  match service with
  | [] => []
  | svc => 10 :: (encVarint svc.length ++ svc)

/-- Parse a `HealthCheckRequest` protobuf payload back to the service name. -/
def parseServiceName (payload : List Nat) : Option (List Nat) :=
  match payload with
  | [] => some []
  | tag :: rest =>
    if tag == 10 then
      match decVarint rest with
      | some (len, rest') => if len ≤ rest'.length then some (rest'.take len) else none
      | none => none
    else none

/-- The canonical health-check HTTP path. -/
def healthCheckPath : String := "/grpc.health.v1.Health/Check"

/-- Build a complete gRPC-framed `HealthCheckRequest`: the protobuf payload
wrapped in the length-prefixed gRPC frame (uncompressed). -/
def buildHealthCheckRequest (service : List Nat) : List Nat :=
  Grpc.encodeFrame { compressed := false, payload := encodeHealthRequest service }

/-- Parse a gRPC-framed `HealthCheckRequest` back to the service name.
Structured as `Option.bind` over `decodeFrame` rather than a nested `match`:
the compiled nested matcher, reduced by the *kernel* on a `some (…)` discriminant
carrying an `encodeFrame`/`be32` argument, overflows the kernel recursion guard
(the `Derp.derp_frame_bounds` / `GrpcWeb.splitWeb` failure class). `bind` reduces
through the `Option` recursor instead, so the kernel never normalizes the whole
nested-match term. Definitionally the same function. -/
def parseHealthRequest (bytes : List Nat) : Option (List Nat) :=
  (Grpc.decodeFrame bytes).bind fun p => parseServiceName p.1.payload

/-- The protobuf payload round-trips: parse recovers the exact service name. -/
theorem parseServiceName_encode (service : List Nat) :
    parseServiceName (encodeHealthRequest service) = some service := by
  cases service with
  | nil => rfl
  | cons a rest =>
    have hle : (a :: rest).length ≤ (a :: rest).length := Nat.le_refl _
    simp only [encodeHealthRequest, parseServiceName, decVarint_encVarint,
      beq_self_eq_true, if_true, if_pos hle, List.take_length]

/-- **Request framing round-trip.** A built `HealthCheckRequest` parses back to
the exact service name — the Check request framing is faithful. The only side
condition is that the protobuf payload fits a gRPC frame's 32-bit length. -/
theorem grpc_health_request_roundtrip (service : List Nat)
    (hlen : (encodeHealthRequest service).length < 4294967296) :
    parseHealthRequest (buildHealthCheckRequest service) = some service := by
  unfold parseHealthRequest buildHealthCheckRequest
  rw [show Grpc.encodeFrame { compressed := false, payload := encodeHealthRequest service }
        = Grpc.encodeFrame { compressed := false, payload := encodeHealthRequest service } ++ []
        from (List.append_nil _).symm,
      Grpc.decodeFrame_encodeFrame _ [] hlen, Option.bind_some]
  exact parseServiceName_encode service

/-! ## `HealthCheckResponse` — one varint `ServingStatus` field -/

/-- Encode a `HealthCheckResponse` protobuf payload for a serving status.
Field 1 (enum, wire type 0): tag `0x08`, LEB128 status code. `UNKNOWN` is the
proto default and encodes to the empty payload. -/
def encodeHealthResponse : Grpc.ServingStatus → List Nat
  | .unknown => []
  | .serving => [8, 1]
  | .notServing => [8, 2]
  | .serviceUnknown => [8, 3]

/-- Parse a `HealthCheckResponse` protobuf payload to a `ServingStatus`.
An empty payload (or a missing field 1) is `UNKNOWN`, the proto default. -/
def parseServingStatus (payload : List Nat) : Grpc.ServingStatus :=
  match payload with
  | [] => .unknown
  | tag :: rest =>
    if tag == 8 then
      match decVarint rest with
      | some (v, _) => Grpc.ServingStatus.ofCode v
      | none => .unknown
    else .unknown

/-- Build a complete gRPC-framed `HealthCheckResponse`. -/
def buildHealthCheckResponse (status : Grpc.ServingStatus) : List Nat :=
  Grpc.encodeFrame { compressed := false, payload := encodeHealthResponse status }

/-- Parse a gRPC-framed `HealthCheckResponse` back to its `ServingStatus`. -/
def parseHealthResponse (bytes : List Nat) : Option Grpc.ServingStatus :=
  match Grpc.decodeFrame bytes with
  | some (f, _) => some (parseServingStatus f.payload)
  | none => none

/-- **Response framing round-trip.** A built `HealthCheckResponse` parses back to
the exact `ServingStatus`. -/
theorem grpc_health_response_roundtrip (status : Grpc.ServingStatus) :
    parseHealthResponse (buildHealthCheckResponse status) = some status := by
  cases status <;> rfl

/-! ## The health verdict, and its composition with the proven pick -/

/-- The single up/down health verdict from a Check response: `true` iff the
`grpc-status` trailer is `OK` **and** the framed body decodes to `SERVING`. This
mirrors the reference probe evaluation exactly. -/
def checkResponseHealthy (grpcStatus : Grpc.GrpcStatus) (body : List Nat) : Bool :=
  match Grpc.decodeFrame body with
  | some (f, _) => grpcStatus.isOk && (parseServingStatus f.payload).isHealthy
  | none => false

/-- **The verdict maps exactly onto the serving status.** An `OK`-trailer Check
response's health verdict is precisely the serving status's healthy bit — so
`SERVING ⇒ up`, and `NOT_SERVING` / `UNKNOWN` / `SERVICE_UNKNOWN ⇒ down`. -/
theorem check_maps_serving (status : Grpc.ServingStatus) :
    checkResponseHealthy .ok (buildHealthCheckResponse status) = status.isHealthy := by
  cases status <;> rfl

/-- **The composed statement (px.17).** A gRPC health Check that did not report
`SERVING` (`status.isHealthy = false`: `NOT_SERVING`, `UNKNOWN`, or
`SERVICE_UNKNOWN`), taken as backend `i`'s live health-mask bit, is never
returned by the proven pick — for **any** config LB policy chain. Eligibility is
`Proxy.selectChain`'s, so the LB policy cannot override the health verdict.

This threads the gRPC health codec of this module through
`Reactor.ProxyDial.pickWith_health_ejects`: the Check response decides the mask
bit, and a down bit ejects the backend from selection. -/
theorem grpc_health_check_maps
    {policies : List Proxy.Policy} {mask key i : Nat} (status : Grpc.ServingStatus)
    (hbit : mask.testBit i = checkResponseHealthy .ok (buildHealthCheckResponse status))
    (hdown : status.isHealthy = false) :
    Reactor.ProxyDial.pickWith policies mask key ≠ some i := by
  apply Reactor.ProxyDial.pickWith_health_ejects
  rw [hbit, check_maps_serving, hdown]

/-! ## Non-vacuity: real probes, real ejection, a mutant -/

/-- A `SERVING` upstream on an `OK` trailer is healthy. -/
example : checkResponseHealthy .ok (buildHealthCheckResponse .serving) = true := by decide

/-- A `NOT_SERVING` upstream is unhealthy (down) — the mapping is real, not vacuous. -/
example : checkResponseHealthy .ok (buildHealthCheckResponse .notServing) = false := by decide

/-- **Mutant:** a `SERVING` verdict does NOT eject. If the composed theorem held
for `SERVING` too it would be vacuous; the verdict genuinely gates ejection —
`SERVING` keeps the mask bit set (`true`), so `grpc_health_check_maps`'s
`hdown : status.isHealthy = false` hypothesis is unsatisfiable there. -/
example : Grpc.ServingStatus.serving.isHealthy = true := rfl

/-- A concrete built request for service `"a"` (byte `0x61`) parses back to `"a"`.
The frame is `[0x00, 0,0,0,3, 0x0A, 0x01, 0x61]` (flag, len 3, tag, len 1, 'a'). -/
example : parseHealthRequest (buildHealthCheckRequest [0x61]) = some [0x61] := by
  have he : encVarint 1 = [1] := by rw [encVarint]; simp
  apply grpc_health_request_roundtrip
  simp only [encodeHealthRequest, List.length_cons, List.length_nil, he,
    List.cons_append, List.nil_append]
  omega

/-- The empty-service ("whole server") request round-trips: empty payload. -/
example : parseHealthRequest (buildHealthCheckRequest []) = some [] := by decide

/-- End-to-end ejection on the default dial chain: a backend whose Check reported
`NOT_SERVING` — mask bit `0` reflecting that down verdict (`mask = 6 = 0b110`) —
is out of the pick set for any affinity key. -/
example {key : Nat} (hbit : (6 : Nat).testBit 0
    = checkResponseHealthy .ok (buildHealthCheckResponse .notServing)) :
    Reactor.ProxyDial.pickWith Reactor.ProxyDial.dialPolicies 6 key ≠ some 0 :=
  grpc_health_check_maps .notServing hbit (by decide)

end Proxy.GrpcHealth
