import Reactor.ServeStep

/-!
# Proxy.ForwardProven — the DEPLOYED reverse-proxy forward, proven end-to-end

This is the PROVE-WHAT-RUNS seam for the reverse-proxy forward the running
dataplane executes on the `--io uring` path. Two facts, both over the code the
engine actually runs:

* **`proxy_backend_pick`** — the fleet backend pick is *governed by the live
  mask*. The deployed step (`Reactor.ServeStep.serveStep`) chooses the upstream
  with the proven `Reactor.ProxyDial.pick`, a pure function of the health/breaker
  `mask` and the sticky affinity `key`. A backend is picked ONLY when its mask bit
  is set — so a probe-down / breaker-open backend is never dialled — and the pick
  is single-valued (deterministic) in `(mask, key)`.

* **`proxy_forwards_faithful`** — a proxied request reaches EXACTLY that picked
  backend, and the reply is relayed through the proven response transform. The
  deployed step `.yield`s a `proxyDial` to the id the pick chose (never a
  host-side re-pick), and resuming with the upstream reply produces
  `Reactor.ServeStep.proxyRespTransform input upstream` — the reply parsed and run
  through the cors / gzip / security-headers / header fold and re-serialized. The
  relayed response therefore carries the added transform headers (proven here for
  HSTS); the upstream's own headers (e.g. `X-Backend`) and body ride through the
  relay, confirmed on the wire by the deployed curl.

Nothing here is a new model: `serveStep` / `resumeStep` / `proxyRespTransform` are
the exact defs the leanc-compiled core runs behind `drorb_serve_step`, and the
backend id is the exact `Reactor.ProxyDial.pick` the io_uring shard crosses. The
host owns only the socket (dial the id → its configured address, move bytes); the
WHICH-backend decision and the reply transform are the proven core's.
-/

namespace Proxy.ForwardProven

open Proto (Bytes)
open Reactor.ServeStep (serveStep resumeStep proxyRespTransform proxyRespTransformGated proxyRespStages
  parseUpstream isApiPath stickyKey BackendId)

/-! ## The backend pick is governed by the live mask -/

/-- **The deployed pick is governed by the mask.** The reverse proxy dials
`Reactor.ProxyDial.pick mask key`; whenever it returns a backend `id`, that
backend's bit is set in the live health/breaker `mask`. Equivalently: a backend
whose probe is down or whose breaker is open (bit clear) is NEVER the dialled
backend. This is the contrapositive of the proven `pick_health_ejects`, so it is
the running-path meaning of "eject an unhealthy upstream". -/
theorem proxy_backend_pick {mask key id : Nat}
    (h : Reactor.ProxyDial.pick mask key = some id) :
    mask.testBit id = true := by
  cases hc : mask.testBit id with
  | true  => rfl
  | false => exact absurd h (Reactor.ProxyDial.pick_health_ejects hc)

/-- **The pick is deterministic (single-valued) in `(mask, key)`.** Two picks over
the same live mask and the same affinity key agree — so a fixed session key pins
to one backend across requests (sticky affinity), given a stable health verdict. -/
theorem proxy_backend_pick_deterministic {mask key id id' : Nat}
    (h : Reactor.ProxyDial.pick mask key = some id)
    (h' : Reactor.ProxyDial.pick mask key = some id') : id = id' := by
  rw [h] at h'; exact Option.some.inj h'

/-! ## The forward reaches the picked backend and relays the reply faithfully -/

/-- **The deployed reverse-proxy forward is faithful.** For an api-path request
whose proven pick selects backend `id` over the live `mask`:

1. the deployed step forwards to EXACTLY that backend — it `.yield`s
   `proxyDial id input`, the id the proven pick chose, with the response-transform
   fold as its continuation (no host-side re-selection);
2. resuming the step with the upstream reply relays it through the proven
   `proxyRespTransform` — the reply parsed, run through the cors / gzip /
   security-headers / header fold, and re-serialized;
3. the dialled backend is genuinely up in the live mask (health honoured); and
4. the relayed response carries the transform's added header block — proven here
   for HSTS, so the relay demonstrably annotates the reply, not merely echoes it.

The upstream's own headers (`X-Backend`, `Content-Type`) and body pass through the
transform (only `Content-Length` is dropped and re-derived); that passthrough is
confirmed on the wire by the deployed `--io uring` curl. -/
theorem proxy_forwards_faithful (mask : Nat) (input upstream : Bytes) (id : BackendId)
    (hapi : isApiPath input = true)
    (hpick : Reactor.ProxyDial.pick mask (stickyKey input) = some id) :
    serveStep mask input
        = .yield (.proxyDial id input) (fun up => .done (proxyRespTransformGated input up))
    ∧ resumeStep mask input [upstream] = .done (proxyRespTransformGated input upstream)
    ∧ mask.testBit id = true
    ∧ (Reactor.Stage.SecurityHeaders.hstsHeaderName,
       Reactor.Stage.SecurityHeaders.hstsHeaderVal)
        ∈ ((Reactor.Pipeline.runPipeline proxyRespStages
              (fun _ => parseUpstream upstream) (Reactor.Deploy.ctxOf input)).build).headers := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Reactor.ServeStep.serveStep_proxy_yields mask input id hapi hpick
  · exact Reactor.ServeStep.serveStep_proxy_resume mask input upstream id hapi hpick
  · exact proxy_backend_pick hpick
  · exact Reactor.ServeStep.proxyRespTransform_hsts input upstream

/-- **★ …and the relay REFUSES a bare-LF upstream head (RFC 9112 §2.2).** The proxy
relay proven above now crosses `proxyRespTransformGated`, so an upstream reply whose head
block carries a bare LF is answered `502 Bad Gateway` and none of its bytes are relayed —
the response-splitting mirror of the request-side `Body.FrameRaw` gate, at the effect seam.
On a clean upstream head the relay is byte-identical to the pre-gate transform. -/
theorem proxy_forwards_refuses_bareLF (mask : Nat) (input upstream : Bytes) (id : BackendId)
    (hapi : isApiPath input = true)
    (hpick : Reactor.ProxyDial.pick mask (stickyKey input) = some id) :
    (Body.FrameRaw.noBareLF (Reactor.ServeStep.upstreamHeadBlock upstream) = false →
      resumeStep mask input [upstream] = .done (Reactor.ServeStep.gatewayError false))
    ∧ (Body.FrameRaw.noBareLF (Reactor.ServeStep.upstreamHeadBlock upstream) = true →
      resumeStep mask input [upstream] = .done (proxyRespTransform input upstream)) :=
  ⟨fun hb => Reactor.ServeStep.serveStep_proxy_resume_rejected mask input upstream id hapi hpick hb,
   fun hc => Reactor.ServeStep.serveStep_proxy_resume_clean mask input upstream id hapi hpick hc⟩

/-- **No eligible backend ⇒ the core's 503, never a dial.** When the whole pool is
down / breaker-open (every mask bit clear ⇒ `pick = none`), the deployed step
`.done`s the 503 without yielding a `proxyDial`: the host serves 503 and opens no
upstream socket. -/
theorem proxy_no_backend_no_dial (mask : Nat) (input : Bytes)
    (hapi : isApiPath input = true)
    (hpick : Reactor.ProxyDial.pick mask (stickyKey input) = none) :
    serveStep mask input = .done (Reactor.serialize Reactor.ServeStep.serviceUnavailable503) :=
  Reactor.ServeStep.serveStep_proxy_no_backend mask input hapi hpick

/-! ## Runnable, concrete checks — the pick actually chooses and honours health

These reuse the deployed `Reactor.ProxyDial.pick` over the demo tier-0 fleet: the
same pure decision the io_uring shard crosses per request. They witness that the
hypotheses of `proxy_forwards_faithful` are genuinely satisfiable (the pick is not
vacuously `none`) and that the mask actually steers the dial. -/

-- All three backends up: affinity key 4 homes to backend 0 (a real LB choice).
example : Reactor.ProxyDial.pick 0b111 4 = some 0 := by decide
-- Eject backend 0 (probe down / breaker open ⇒ its bit clears): the proven pick
-- moves key 4 to another eligible backend — the mask steering the running dial.
example : Reactor.ProxyDial.pick 0b110 4 = some 1 := by decide
-- Whole pool down ⇒ no pick ⇒ the 503 branch (never a dial).
example : Reactor.ProxyDial.pick 0b000 4 = none := by decide
-- The mask-governance theorem, concretely: the chosen backend's bit is set.
example : (0b111 : Nat).testBit 0 = true := proxy_backend_pick (by decide : Reactor.ProxyDial.pick 0b111 4 = some 0)
-- Determinism: the same (mask, key) yields the same backend (sticky affinity).
example : (0 : Nat) = 0 :=
  proxy_backend_pick_deterministic
    (by decide : Reactor.ProxyDial.pick 0b111 4 = some 0)
    (by decide : Reactor.ProxyDial.pick 0b111 4 = some 0)

#print axioms proxy_backend_pick
#print axioms proxy_backend_pick_deterministic
#print axioms proxy_forwards_faithful
#print axioms proxy_no_backend_no_dial

end Proxy.ForwardProven
