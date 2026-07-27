/-
# AcmeOrderLive — driving the PROVEN ACME order-lifecycle FSM over the byte level

`Acme.Order` models the RFC 8555 §7.1.6 order state machine as sans-IO, proven
Lean: the total/deterministic transition `orderStep`
(`pending → ready → processing → valid`, with `invalid` an absorbing failure),
its fold `orderRun`, the well-formedness invariant `Order.wf` (an order in
`ready`/`processing`/`valid` has every authorization valid), and the headline
safety theorem `valid_requires_all_authz_valid` — **no certificate is issued
past a pending or failed authorization.**

None of that logic was wired into a running binary. This executable is that
wiring: a `selftest` that drives the ORDER FSM over the byte level in one
process — it encodes a sequence of order events (the CA's per-authorization
verdicts, the client's `finalize`, the CA's `issued`) to a compact wire, decodes
them back with the proven-below `decodeEvents`, folds `orderStep` over the
recovered events, and cross-checks the reached order against the model.

This lane is deliberately **crypto-free**: it drives ONLY the order FSM. There
is no SHA-256, no DNS-01 digest, no HTTP-01 provisioning — nothing that would
require a native crypto backend to be linked. It therefore runs end-to-end under
`lake env lean --run` (the interpreter), unlike the SHA-256-carrying `acme-live`.

## Faithfulness / realization boundary (the ControlLive / DnsResolveLive discipline)

The `selftest` is **drorb-native**: the CA verdicts and client control events are
our own spec-conformant peers, encoded to bytes and decoded byte-to-byte in one
process (no sockets, no external ACME directory). Everything structural is the
proven Lean. The gap the selftest discharges by construction (not by proof) is
that this exe faithfully CALLS the proven `orderStep`/`orderRun` on the recovered
events. The faithfulness of the decode→fold chain ITSELF is proven below as
`acme_order_live_faithful` (the wire-driven run equals the model `orderRun`), and
the byte-driven safety guarantee as `acme_order_live_safe`. Real interop against
a public CA — the JWS-signed HTTPS transport, nonce handling, account
registration — is the named residual.

Usage:
  acme-order-live selftest
-/
import Acme.Order

namespace AcmeOrderLive

open Acme

/-! ## A compact byte wire for order events

Each event serializes to a self-delimiting byte record:
  * `authzResult i ok` → `0x00, byte i, (1 if ok else 0)`
  * `finalize`         → `0x01`
  * `issued`           → `0x02`
  * `issuanceFailed`   → `0x03`
A message is the concatenation of the per-event records. -/

def encEvent : OrderEvent → List UInt8
  | .authzResult i ok => [0, UInt8.ofNat i, if ok then 1 else 0]
  | .finalize => [1]
  | .issued => [2]
  | .issuanceFailed => [3]

def encEvents (es : List OrderEvent) : List UInt8 := (es.map encEvent).flatten

/-- Decode a byte message back to an event list. Malformed input (an unknown
control byte, or a truncated `authzResult` record) fails as `none`. -/
def decodeEvents : List UInt8 → Option (List OrderEvent)
  | [] => some []
  | b :: rest =>
    if b == 1 then (decodeEvents rest).map (OrderEvent.finalize :: ·)
    else if b == 2 then (decodeEvents rest).map (OrderEvent.issued :: ·)
    else if b == 3 then (decodeEvents rest).map (OrderEvent.issuanceFailed :: ·)
    else if b == 0 then
      match rest with
      | i :: v :: rest' =>
          (decodeEvents rest').map (OrderEvent.authzResult i.toNat (v == 1) :: ·)
      | _ => none
    else none

/-- The wire-driven order run: decode the byte message, then fold the proven
`orderStep` over the recovered events. `none` iff the message is malformed. -/
def runWire (o : Order) (wire : List UInt8) : Option Order :=
  match decodeEvents wire with
  | some es => some (orderRun o es)
  | none => none

/-! ## The faithfulness theorem

The wire-driven run applies EXACTLY the proven fold to the decoded events. Not a
`P → P`: the hypothesis `hdec` is the (satisfiable — the selftest exhibits it)
well-formed decode of the byte message, and the conclusion is a real equation
tying `runWire` over arbitrary bytes to the model `orderRun` over the recovered
events. It is the direct analogue of DnsResolveLive's `dns_resolve_faithful`:
byte-driven driver = proven model. -/
theorem acme_order_live_faithful
    (ids : List Bytes) (wire : List UInt8) (es : List OrderEvent)
    (hdec : decodeEvents wire = some es) :
    runWire (Order.fresh ids) wire = some (orderRun (Order.fresh ids) es) := by
  simp only [runWire, hdec]

/-! ## The byte-driven safety guarantee

Composing faithfulness with the proven `valid_requires_all_authz_valid`: if a
byte message drives a fresh order to `valid` — the status at which a certificate
issues — then EVERY authorization is `valid`. Both hypotheses are load-bearing:
`hrun` recovers the model run from the wire, `hvalid` feeds the safety theorem.
The conclusion is a distinct fact about the reached order, not a hypothesis. -/
theorem acme_order_live_safe
    (ids : List Bytes) (wire : List UInt8) (o' : Order)
    (hrun : runWire (Order.fresh ids) wire = some o')
    (hvalid : o'.status = .valid) :
    allValid o'.authzs = true := by
  unfold runWire at hrun
  cases hd : decodeEvents wire with
  | none => rw [hd] at hrun; simp at hrun
  | some es =>
    rw [hd] at hrun
    simp only [Option.some.injEq] at hrun
    subst hrun
    exact valid_requires_all_authz_valid ids es hvalid

/-! ## A fully closed instance: the ENCODE→decode→run chain, discharged

The canonical single-authorization happy path: validate the one authorization,
`finalize`, `issued`. Its wire round-trips (`happyWire_decodes`, by kernel
`decide` — the REAL `encEvents`/`decodeEvents` run), so the faithfulness
hypothesis is closed; and it reaches `valid` (`happy_reaches_valid`), inhabiting
the safety hypothesis so the guarantee is non-vacuous. -/

def happyEvents : List OrderEvent := [.authzResult 0 true, .finalize, .issued]

def happyWire : List UInt8 := encEvents happyEvents

theorem happyWire_decodes : decodeEvents happyWire = some happyEvents := by decide

/-- **Faithful, closed over all identifier sets.** For every `ids`, driving the
fresh order over the `encEvents`-encoded happy wire equals the model `orderRun`
over the happy events — the wire realizes the model, mediated only by the proven
decode round-trip. Analogue of `dns_resolve_faithful_up`. -/
theorem acme_order_live_faithful_happy (ids : List Bytes) :
    runWire (Order.fresh ids) happyWire = some (orderRun (Order.fresh ids) happyEvents) :=
  acme_order_live_faithful ids happyWire happyEvents happyWire_decodes

/-- The happy path reaches `valid` (kernel `decide`, not `native_decide`). -/
theorem happy_reaches_valid :
    (orderRun (Order.fresh ["acme.example".toList]) happyEvents).status
      = OrderStatus.valid := by decide

/-- **The byte-driven safety guarantee, discharged for the happy path.** The
order the happy wire drives to `valid` has every authorization valid — a closed
corollary, no open hypotheses. -/
theorem acme_order_live_safe_happy :
    allValid (orderRun (Order.fresh ["acme.example".toList]) happyEvents).authzs = true :=
  valid_requires_all_authz_valid _ _ happy_reaches_valid

/-! ## Rendering helpers -/

def idText (b : Acme.Bytes) : String := String.mk b

def toHex (b : List UInt8) : String :=
  let d := "0123456789abcdef".toList.toArray
  b.foldl (fun s x => s ++ s!"{d[(x.toNat / 16)]!}{d[(x.toNat % 16)]!}") ""

/-! ## The selftest — the order FSM over the byte level, one process -/

def selftest : IO UInt32 := do
  IO.println "== acme-order-live selftest : RFC 8555 order FSM, byte-level, encode + decode + run =="

  let domain : Acme.Bytes := "www.example.com".toList
  let ids : List Acme.Bytes := [domain]
  IO.println s!"identifier (domain) : {idText domain}"

  -- 1. build + ENCODE the happy event sequence to the byte wire
  let events := happyEvents
  let wire := encEvents events
  IO.println s!"\n-- events --"
  IO.println s!"order events        : authzResult 0 true; finalize; issued"
  IO.println s!"encEvents wire      : {wire.length}B  {toHex wire}"

  -- 2. DECODE the wire back with the proven decoder; the round-trip is realized
  let decoded := decodeEvents wire
  let roundtrips := decoded == some events
  IO.println s!"decodeEvents∘encEvents == events (wire round-trip realized) : {roundtrips}"

  -- 3. drive the ORDER FSM over the decoded events via runWire (decode∘fold)
  let driven := runWire (Order.fresh ids) wire
  let model := orderRun (Order.fresh ids) events
  IO.println s!"\n-- run (runWire = decode then fold orderStep over the wire bytes) --"
  match driven with
  | none => do IO.eprintln "wire failed to decode"; return 1
  | some o => do
    IO.println s!"driven order status : {repr o.status}"
    IO.println s!"driven authzs       : {repr o.authzs}"
    -- 4. faithfulness cross-check: wire-driven run == model orderRun
    let faithful := driven == some model
    IO.println s!"\n-- cross-check (realizes acme_order_live_faithful) --"
    IO.println s!"runWire == model orderRun (decode∘fold = proven fold) : {faithful}"
    -- 5. the safety guarantee, realized on the reached order
    let reachedValid := o.status == OrderStatus.valid
    let allAuthzValid := allValid o.authzs
    IO.println s!"order reached valid                                    : {reachedValid}"
    IO.println s!"all authorizations valid (valid_requires_all_authz_valid) : {allAuthzValid}"

    -- 6. negative discipline: finalize-before-validate cannot reach valid
    let skipWire := encEvents [.finalize, .issued]
    let skipDriven := runWire (Order.fresh ids) skipWire
    let skipStatus := (skipDriven.map (·.status))
    let skipNotValid := skipStatus != some OrderStatus.valid
    IO.println s!"\n-- negative: finalize-before-validate (no skip) --"
    IO.println s!"runWire on [finalize,issued] status : {repr skipStatus}  (must NOT be valid)"

    -- 7. negative discipline: a failed authorization verdict never reaches valid
    let failWire := encEvents [.authzResult 0 false, .finalize, .issued]
    let failDriven := runWire (Order.fresh ids) failWire
    let failStatus := (failDriven.map (·.status))
    let failNotValid := failStatus != some OrderStatus.valid
    IO.println s!"runWire on authzResult 0 false      : {repr failStatus}  (must NOT be valid)"

    -- 8. negative discipline: a malformed (truncated authzResult) wire fails to decode
    let badWire : List UInt8 := [0, 0]  -- authzResult opcode with a missing verdict byte
    let badDecode := decodeEvents badWire
    let badRefused := badDecode == none
    IO.println s!"decodeEvents on truncated record    : {repr badDecode}  (must be none)"

    if roundtrips && faithful && reachedValid && allAuthzValid
        && skipNotValid && failNotValid && badRefused then do
      IO.println "\nPASS — events encoded, wire decoded, the order FSM driven byte-to-byte;"
      IO.println "       the decode→fold chain equals the proven model, and the order reaches"
      IO.println "       valid ONLY with every authorization valid (skip/fail/malformed refused)."
      IO.println "FULL ORDER-FSM EXCHANGE COMPLETE (drorb-native, byte-level, verified FSM, no crypto)."
      return 0
    else do
      IO.eprintln "\nFAIL — a stage of the order-FSM pipeline did not cross-check."
      return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["selftest"] => selftest
  | _ => do
    IO.eprintln "usage: acme-order-live selftest"
    return 1

end AcmeOrderLive

def main (args : List String) : IO UInt32 := AcmeOrderLive.main args
