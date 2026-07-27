/-
Reactor.ParseFaithful — discharging the parse-faithfulness assumption AT THE SEAM.

`Reactor/Config.lean` wires the arena parser into the connection FSM through
`protoReqOf`, and `h1Parse_complete_content` proves the `Proto.Request` the FSM
dispatches carries fields *equal to the resolved arena entries*
(`resolveBytes req.store req.method`, …). What that theorem left open — the gap
the serve then *assumed* — is whether those resolved entries are the RIGHT bytes:
that `resolveBytes … req.method` is actually the method the wire spells, not just
"some in-bounds range the parser happened to register".

`Arena.Parse.parse_faithful` closes that gap at the arena level (the resolved
method/target/version ARE the wire slices, and round-trip the request line
verbatim). This file composes the two: `deployed_request_faithful` states the
`Proto.Request` the deployed serve dispatches on has method / target / version
equal to the *exact wire bytes* of `buf`, and that the three rejoin — with the
single `SP` separators RFC 7230 §3.1.1 mandates — into the request line
`buf.take (m+t+v+2)` verbatim.

Scope note. This discharges the *parse-faithfulness* assumption (resolved fields
= wire bytes) that sat under `h1Parse_complete_content`. It is ORTHOGONAL to the
serve's `hsub` DISPATCH hypothesis (`deploySubs input = .dispatch req :: rest`),
which asserts the reactor FSM produced a dispatch for a given `req` and concerns
routing, not parse faithfulness; that hypothesis is unaffected here.
-/
import Reactor.Config
import Arena.ParseFaithful

open Arena.Parse (SP startsWithHttpSlash)

namespace Reactor
namespace Config

/-- The adapter's `resolveBytes` is exactly the arena-level `viewBytes` the
faithfulness theorems are stated over (same `Store.resolve` read-back). -/
theorem viewBytes_eq_resolveBytes (s : Arena.Store) (e : Arena.Entry) :
    Arena.Parse.viewBytes s e = resolveBytes s e := rfl

/-- **`deployed_request_faithful` — the dispatched request IS the wire.** On a
`complete` arena parse, the `Proto.Request` the deployed serve dispatches on
(`protoReqOf req`, the head `h1Parse_complete_content` feeds the FSM) has method,
target, and version equal to the *literal wire slices* of `buf`, and those three
fields rejoin — with the single `SP` separators — into the request line
`buf.take (m+t+v+2)` verbatim (a lossless decode); the version begins `HTTP/`.
Composition of `Arena.Parse.parse_faithful` with the adapter, discharging the
parse-faithfulness assumption the serve previously carried. -/
theorem deployed_request_faithful (buf : Proto.Bytes) (req : Arena.Parse.Request)
    (h : Arena.Parse.parse buf = .complete req) :
    ∃ m t v : Nat,
      (protoReqOf req).method  = buf.take m
      ∧ (protoReqOf req).target  = (buf.drop (m + 1)).take t
      ∧ (protoReqOf req).version = (buf.drop (m + t + 2)).take v
      ∧ (protoReqOf req).method
          ++ SP :: ((protoReqOf req).target ++ SP :: (protoReqOf req).version)
            = buf.take (m + t + v + 2)
      ∧ startsWithHttpSlash (protoReqOf req).version := by
  obtain ⟨m, t, v, hm, ht, hv, hround, hhttp, _⟩ := Arena.Parse.parse_faithful h
  simp only [protoReqOf]
  exact ⟨m, t, v, hm, ht, hv, hround, hhttp⟩

/-- The same, stated against the deployed `h1Parse` field the FSM actually calls:
when the arena parser reports `complete req`, the FSM ingests
`ParseOutcome.request _ (protoReqOf req) _`, and that request's head fields are the
exact wire bytes (via `deployed_request_faithful`). -/
theorem h1Parse_dispatch_faithful (buf : Proto.Bytes) (req : Arena.Parse.Request)
    (h : Arena.Parse.parse buf = .complete req) :
    demoConfig.h1Parse buf
        = .request req.consumed (protoReqOf req) (deriveKeepAlive (protoReqOf req).headers)
      ∧ ∃ m t v : Nat,
          (protoReqOf req).method  = buf.take m
          ∧ (protoReqOf req).target  = (buf.drop (m + 1)).take t
          ∧ (protoReqOf req).version = (buf.drop (m + t + 2)).take v :=
  ⟨demoConfig_complete_content buf req h,
   let ⟨m, t, v, hm, ht, hv, _, _⟩ := deployed_request_faithful buf req h
   ⟨m, t, v, hm, ht, hv⟩⟩

end Config
end Reactor
