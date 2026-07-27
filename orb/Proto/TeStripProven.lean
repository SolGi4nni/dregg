/-
# Proto.TeStripProven — the DEPLOYED response rewrite STRIPS the hop-by-hop `TE` header

PROVE-WHAT-RUNS for RFC 9110 §7.6.1 connection-management. `TE` is a hop-by-hop request
header (RFC 9110 §10.1.4) that MUST NOT be forwarded end-to-end. The deployed response
rewrite is `Reactor.Deploy.deployProg` — `Lifecycle.stdRewrite` (dynamic hop-strip `hopDyn`,
then install `Server`) followed by the `x-upstream` and `x-corr` stamps. Because `TE` is in
the fixed hop set `Header.hopStd`, it is in `Header.dynHopSet` of ANY message, so the
deployed strip removes it and none of the three later `set`s (`Server` / `x-upstream` /
`x-corr`, all distinct names) reinstates it. This is a real PRESENT behaviour (a strip that
runs), not a not-deployed finding.

Companion to `Proto.ServerHeaderProven` (which proves the `Server` install survives the same
three sets); this file proves the dual: a hop name goes to `none` through them.

## Ground truth — curl against the running dataplane (io_uring)

The deployed `200` response carries NO `TE` header (curl output has `ETag`, `Accept-Ranges`,
`Content-Type`, the security headers, `Server: drorb`, `x-upstream`, `Content-Length` — no
`TE`). The case where a `TE` is present on the response header list and is removed is the
kernel content below (`te_present_before` → `deploy_strips_te` instance).

## What is proven here (pure-kernel; `#print axioms` ⊆ {propext, Quot.sound})

  * `te_is_hop` — `TE` is in the fixed RFC 9110 §7.6.1 hop set (`decide`).
  * `deploy_strips_te` — for ANY plan/input/base-headers, `Header.get TE` on the deployed
    rewrite's output is `none`: the hop-by-hop `TE` never survives to the wire.
  * `te_present_before` / `te_stripped_after` — a concrete response header list that
    contains `TE: trailers` has it BEFORE the rewrite and NOT after (non-vacuous witness).
  * `te_wire_bytes` — the `TE` name is exactly the 2 bytes `[84, 69]`, and the case-folded
    lower form `[116, 101]` is also a hop name (case-insensitive match), pinned via
    `Shortcuts.ba_toList_eq` (pure-kernel `decide`, no `native_decide`).
-/

import Reactor.Deploy
import Reactor.Lifecycle
import Header.Hop
import Proto.Kernel.Shortcuts

namespace Proto.TeStripProven

open Proto (Bytes)
open Reactor (RingSubmission)
open Proto.Kernel

/-- The `TE` header name as it appears on the wire (ASCII `T E`). A literal so the kernel
reduces it directly (no `toUTF8`). -/
def teName : Header.Name := [84, 69]

/-! ## `TE` is a hop-by-hop header -/

/-- **`te_is_hop`.** `TE` is in the fixed RFC 9110 §7.6.1 hop set `Header.hopStd` (matched
case-insensitively against the stored lower-case `"te"`). Pure-kernel `decide`. -/
theorem te_is_hop : Header.isHop Header.hopStd teName = true := by decide

/-- The lower-cased form `"te"` is likewise a hop name — the case-insensitive match. -/
theorem te_lower_is_hop : Header.isHop Header.hopStd [116, 101] = true := by decide

/-! ## The deployed rewrite strips `TE` -/

/-- **`deploy_strips_te`.** On the deployed header rewrite (`deployProg` = `stdRewrite ++
[set upstream, set corr]`), a `Header.get TE` on the emitted headers is `none` for ANY
DNS/proxy plan, any input bytes, any base headers: `TE` is a hop-by-hop name, so the leading
`hopDyn` strips it, and the three later `set`s (`Server` / `x-upstream` / `x-corr`, all
distinct from `TE`) never reinstate it. The hop-by-hop `TE` never reaches the wire. -/
theorem deploy_strips_te (plan : List RingSubmission) (input : Bytes) (h : Header.Headers) :
    Header.get teName (Header.run (Reactor.Deploy.deployProg plan input) h) = none := by
  unfold Reactor.Deploy.deployProg
  rw [Header.run_append, Header.run_cons, Header.run_cons, Header.run_nil]
  simp only [Header.applyOp]
  rw [Header.get_set,
      if_neg (Header.name_neq (by decide : Header.nameEqb Reactor.Deploy.corrName teName = false)),
      Header.get_set,
      if_neg (Header.name_neq (by decide :
        Header.nameEqb Reactor.Deploy.upstreamName teName = false))]
  show Header.get teName
      (Header.set Reactor.Lifecycle.serverName Reactor.Lifecycle.serverVal
        (Header.strip (Header.dynHopSet h) h)) = none
  rw [Header.get_set,
      if_neg (Header.name_neq (by decide :
        Header.nameEqb Reactor.Lifecycle.serverName teName = false))]
  exact Header.get_strip_hop h (Header.isHop_hopStd_dynHopSet te_is_hop)

/-! ## A concrete non-vacuous witness -/

/-- A response header list that includes a `TE: trailers` field. -/
def teField : Header.Field := ⟨teName, [116, 114, 97, 105, 108, 101, 114, 115]⟩

/-- The base header list carrying `TE: trailers`. -/
def baseWithTe : Header.Headers := [teField]

/-- **`te_present_before`.** Before the deployed rewrite, `TE` is present with its value —
so the strip below is not vacuous. -/
theorem te_present_before :
    Header.get teName baseWithTe = some [116, 114, 97, 105, 108, 101, 114, 115] := by decide

/-- **`te_stripped_after`.** After the deployed rewrite over that same list, `TE` is gone
(an instance of `deploy_strips_te`). -/
theorem te_stripped_after (plan : List RingSubmission) (input : Bytes) :
    Header.get teName (Header.run (Reactor.Deploy.deployProg plan input) baseWithTe) = none :=
  deploy_strips_te plan input baseWithTe

/-! ## The exact wire bytes -/

/-- **`te_wire_bytes`.** The `TE` name is exactly the 2 bytes `[84, 69]`, and its
case-folded form `"te"` (`toUTF8`) is `[116, 101]` — pinned through `Shortcuts.ba_toList_eq`
(pure-kernel `decide`, no `native_decide`). -/
theorem te_wire_bytes : teName = [84, 69] ∧ "te".toUTF8.toList = [116, 101] := by
  refine ⟨rfl, ?_⟩
  simp only [Shortcuts.ba_toList_eq]; decide

end Proto.TeStripProven

#print axioms Proto.TeStripProven.te_is_hop
#print axioms Proto.TeStripProven.te_lower_is_hop
#print axioms Proto.TeStripProven.deploy_strips_te
#print axioms Proto.TeStripProven.te_present_before
#print axioms Proto.TeStripProven.te_stripped_after
#print axioms Proto.TeStripProven.te_wire_bytes
