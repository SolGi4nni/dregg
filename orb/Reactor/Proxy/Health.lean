import Proxy.Health
import Reactor.ProxyDial

/-!
# Reactor.Proxy.Health — active health checks composed with the proven backend pick

Active health checking runs a probe against each backend on an interval; each
probe passes or fails. The verdict machine `Proxy.Health` (rise/fall hysteresis)
turns a *history* of probes into an up/down verdict per backend: `fall`
consecutive failures take a settled-Up backend Down; `rise` consecutive passes
bring a Down backend back Up. That machine is already fully proven
(`Proxy.down_at_fall`, `Proxy.up_at_rise`, the anti-flap and threshold lemmas).

What this module adds is the **composition with selection**: the health verdict
is the `healthy` bit each `Proxy.Backend` carries, packed into the `mask` the
proven pick (`Reactor.ProxyDial.pickWith`) consumes (bit `i` ⇒ backend `i` is
probe-healthy). The load balancer already refuses an ineligible backend for ANY
policy chain (`pickWith_health_ejects`). Chaining the two closes the end-to-end
statement the operator cares about:

> a backend that fails `fall` consecutive health probes is removed from the pick
> set and is never dialled again until it passes `rise` consecutive probes.

## Key theorems

* `probes_eject` — `fall` consecutive failed probes drive a settled-Up backend's
  verdict to Down (`= false`).
* `probes_recover` — `rise` consecutive passed probes drive a Down backend's
  verdict back to Up (`= true`).
* `ejected_not_picked` — given the mask-bit contract (bit `i` = backend `i`'s
  live verdict), a backend whose verdict is Down is never returned by the pick,
  under any config LB chain. This is `probes_eject` composed through
  `Reactor.ProxyDial.pickWith_health_ejects`.
* `probed_out_not_picked` — the fully-composed statement: `fall` failed probes ⇒
  not in the pick set. Non-vacuous concrete instances are the `example`s below
  (an ejected backend `0` under `mask = 6`, and its recovery).

## Boundaries

* The probe *transport* (the HTTP GET / gRPC `Check` the host issues on the
  interval) is the host's; the machine consumes the pass/fail verdicts it
  produces. The mask-bit contract (bit `i` reflects backend `i`) is the
  `drorb_proxy_pick` ABI, discharged by the host that builds the mask; the
  theorems below are stated relative to it.
-/

namespace Reactor.Proxy.Health

open Proxy

/-! ## Probe histories drive the verdict -/

/-- **Ejection.** A settled-Up backend that fails `fall` consecutive probes has
verdict Down. -/
theorem probes_eject {g : Proxy.HealthGate} (h1 : 1 ≤ g.fall) :
    (Proxy.hrun g Proxy.HealthState.initUp (List.replicate g.fall Proxy.Probe.fail)).up = false := by
  rw [Proxy.down_at_fall h1]
  rfl

/-- **Recovery.** A Down backend that passes `rise` consecutive probes has
verdict Up again. -/
theorem probes_recover {g : Proxy.HealthGate} (h1 : 1 ≤ g.rise) :
    (Proxy.hrun g Proxy.HealthState.initDown (List.replicate g.rise Proxy.Probe.pass)).up = true := by
  rw [Proxy.up_at_rise h1]
  rfl

/-! ## Composition with the proven pick -/

/-- **A Down backend is never dialled.** Given the mask-bit contract (bit `i` of
`mask` equals backend `i`'s live health verdict `v.up`), a backend whose verdict
is Down (`v.up = false`) is never returned by the pick — for ANY config LB
policy chain. Eligibility is the selector's, so the LB policy cannot override it. -/
theorem ejected_not_picked {policies : List Proxy.Policy} {mask key i : Nat}
    {v : Proxy.HealthState}
    (hbit : mask.testBit i = v.up)
    (hdown : v.up = false) :
    Reactor.ProxyDial.pickWith policies mask key ≠ some i := by
  apply Reactor.ProxyDial.pickWith_health_ejects
  rw [hbit, hdown]

/-- **The fully-composed statement.** If backend `i` failed `fall` consecutive
health probes (from settled-Up) and the mask bit reflects that verdict, the pick
never returns `i`, for any LB policy chain. -/
theorem probed_out_not_picked {g : Proxy.HealthGate} (h1 : 1 ≤ g.fall)
    {policies : List Proxy.Policy} {mask key i : Nat}
    (hbit : mask.testBit i
      = (Proxy.hrun g Proxy.HealthState.initUp (List.replicate g.fall Proxy.Probe.fail)).up) :
    Reactor.ProxyDial.pickWith policies mask key ≠ some i :=
  ejected_not_picked hbit (probes_eject h1)

/-! ## Non-vacuity: concrete eject / recover / not-picked -/

/-- Three consecutive failures eject (fall = 3). -/
example : (Proxy.hrun ⟨2, 3⟩ Proxy.HealthState.initUp
    (List.replicate 3 Proxy.Probe.fail)).up = false := by decide

/-- Two consecutive passes recover (rise = 2). -/
example : (Proxy.hrun ⟨2, 3⟩ Proxy.HealthState.initDown
    (List.replicate 2 Proxy.Probe.pass)).up = true := by decide

/-- With backend `0`'s bit clear (`mask = 6 = 0b110`), the proven pick never
returns backend `0`, whatever the affinity key. -/
example (key : Nat) : Reactor.ProxyDial.pick 6 key ≠ some 0 :=
  Reactor.ProxyDial.pick_health_ejects (by decide)

/-- End-to-end on the default chain: a backend probed Down (bit reflects the
verdict) is out of the pick set. -/
example {key : Nat} (hbit : (6 : Nat).testBit 0
    = (Proxy.hrun ⟨2, 3⟩ Proxy.HealthState.initUp (List.replicate 3 Proxy.Probe.fail)).up) :
    Reactor.ProxyDial.pickWith Reactor.ProxyDial.dialPolicies 6 key ≠ some 0 :=
  probed_out_not_picked (by decide) hbit

end Reactor.Proxy.Health
