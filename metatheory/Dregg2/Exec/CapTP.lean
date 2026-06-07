/-
# Dregg2.Exec.CapTP — the object-capability transport protocol, as verified Lean.

dregg1 carries a 6369-LOC `captp/` crate (`captp/src/pipeline.rs`,
`captp/src/handoff.rs`, `captp/src/session.rs`, `captp/src/gc.rs`) with no Lean
counterpart. The `Spec.VatBoundary` Φ — the *named-lossy* functor caps ↔ keys — is the
**abstract law** of the boundary; CapTP is the **realized protocol** that crosses it.
This module mirrors the two load-bearing CapTP semantics into Lean and proves their
soundness by REUSING the existing seam/authority machinery, never reinventing it:

  1. **Promise pipelining** (`pipeline.rs`). An eventual-send to an *unresolved* promise
     is queued and delivered on resolution (E-language `whenResolved`; the latency win is
     batching a multi-step chain into one round-trip). The faithful semantic content we
     verify is that pipelining **does not bypass authorization**: the queued call carries
     its `PipelinedAction.authorization` (a `Spec.Guard`/`Laws.Discharged` obligation), and
     that obligation **survives resolution unchanged** — resolving the target promise
     delivers the call but does not discharge its guard for it. We connect this to
     `Await`'s promise/`Conditional` machinery directly (the pipelined call IS an
     `Await.Op.call` parked on a `Spec.Conditional` whose resolution is `Guard.admits`).

  2. **The 3-vat handoff / introduction** (`handoff.rs`). Vat **A** (the introducer) gifts
     vat **C**'s capability to vat **B** (the recipient) across the Φ boundary — Miller's
     Granovetter operation, *only connectivity begets connectivity*. The `HandoffCertificate`
     is a signed "I (A) authorize recipient B to contact target (cell on C) with these
     permissions". We prove the CapTP handoff **IS** a `Spec.Authority.Introduce`
     (`handoff_is_introduce`), that the introduced cap is **non-amplifying**
     (`handoff_non_amplifying`, reusing `introduce_non_amplifying`), and that the resulting
     cross-vat cap is a **revocable forwarder** (`handoff_forwarder_revocable`, reusing
     `VatBoundary.forwarded_cap_is_revocable`). The Granovetter discipline is preserved
     across vats.

  3. **Export/import-table bookkeeping** (the `result_promise_id` / `routing_token` of the
     wire protocol). A cap exported to a remote vat gets a local import handle; we model the
     handle as a structure and prove it confers exactly the exported cap's authority, modulo
     Φ's confinement loss (`import_handle_confers_exactly` + `import_handle_is_revocable`).

## Discipline (the §8/crypto split, honestly drawn)

The handoff certificate's *attestation* (`HandoffCertificate.introducer_signature` /
`HandoffPresentation.recipient_signature`, validated by `validate_handoff`) is a
`Laws.Discharged`/`Prop`-carrier seam — the §8 verify side — NOT Lean-proved cryptography.
We carry it as the discharge of a `Spec.Guard`, exactly as `Spec.VatBoundary` and
`Spec.Await` do. The distributed-GC liveness of exported caps (`gc.rs`) is genuinely OPEN
(it relates to `Exec.CellLiveness`'s cross-vat-cycle impossibility) and is left as a
documented `-- OPEN:`, NOT a `sorry`/`axiom`.
-/
import Dregg2.Spec.Authority
import Dregg2.Spec.VatBoundary
import Dregg2.Spec.Await
import Dregg2.Await
import Dregg2.Tactics

namespace Dregg2.Exec.CapTP

open Dregg2.Spec
open Dregg2.Spec.Conditional (Promise PromiseGraph)
open Dregg2.Laws

universe u

set_option linter.unusedSectionVars false

/-! ## §1 — Promise pipelining: the queued eventual-send carries an authorization guard.

`pipeline.rs`'s `PipelinedMessage` targets an *unresolved* promise; `PipelinedAction`
carries `method`, `args`, and — load-bearing for soundness — `authorization` ("serialized
authorization proving the sender's right to invoke this action"). `pipeline_message`
queues it (`PipelinePromiseState::Pending`); `resolve_promise` marks the promise
`Fulfilled` and *drains* the queued messages for delivery. The promise itself is the
`Spec.Await` dataflow `Promise`/`Conditional` machinery — we do NOT reinvent it.

The semantic claim we verify: resolution **delivers** the call but does **not discharge**
its authorization. The guard obligation `g`/`req`/`w` the queued call carries is the SAME
before queuing and after delivery — pipelining is a latency optimization, not an authority
bypass. -/

variable {Request Statement Witness : Type u} [Verifiable Statement Witness]

/-- **`PipelinedCall`** — a `pipeline.rs::PipelinedMessage` parked on an unresolved promise.
It mirrors the Rust fields faithfully:

  * `targetCell`   — the cell the call lands on once the promise resolves (`resolved_cell`);
  * `method`       — the method invoked on delivery (`PipelinedAction.method`, the CapTP
    eventual-send — pipelining IS the await family's `call` face, not a new effect);
  * `guard`        — the `PipelinedAction.authorization`, as a `Spec.Guard` demand (the
    verify-seam obligation the sender's right rides on). THIS is what must not be bypassed.

The promise it targets is supplied separately (a `Spec.Await.Promise`/`Conditional`), so a
`PipelinedCall` decorates the await core exactly as `Await.zkpromise`/`discharge` do. -/
structure PipelinedCall (CellId : Type*) (Request Statement : Type u) where
  /-- The cell the call lands on once the targeted promise resolves. -/
  targetCell : CellId
  /-- The method invoked on delivery — the CapTP eventual-send `call` face. -/
  method     : String
  /-- The sender's authorization, as a verify-seam `Guard` demand (`authorization` bytes). -/
  guard      : Guard Request Statement

/-- **`PipelinedCall.delivered`** — the call, viewed as DELIVERED to a now-resolved cell.
Resolution (`resolve_promise` in Rust) changes the *promise state*, not the call's payload:
the delivered call has the same action and the SAME authorization guard. This is the Lean
form of `resolve_promise` returning the queued `PipelinedMessage` unchanged for the executor
to turn into a real turn. -/
def PipelinedCall.delivered {CellId : Type*}
    (m : PipelinedCall CellId Request Statement) (resolvedCell : CellId) :
    PipelinedCall CellId Request Statement :=
  { m with targetCell := resolvedCell }

/-- **`PipelinedCall.authorized`** — the call's authorization obligation is discharged under
supply `(req, w)`: its guard `admits`. This is the verify-seam check the receiver runs
before EXECUTING the delivered call (`PipelinedAction.authorization` validated against the
resolved cell's `AuthRequired`). It is `Spec.Guard.admits`, nothing new. -/
def PipelinedCall.authorized {CellId : Type*}
    (m : PipelinedCall CellId Request Statement)
    (req : Request) (w : Statement → Witness) : Prop :=
  Guard.admits m.guard req w = true

/-- **`pipelining_preserves_seam` (PROVED) — the headline pipelining soundness.**
Pipelining does NOT bypass authorization: delivering a pipelined call onto a resolved cell
preserves its authorization obligation *exactly*. For any resolved cell, the delivered
call's `guard` is the same guard, so it `authorized`-admits under `(req, w)` **iff** the
original queued call did. Resolution moves the promise from `Pending` to `Fulfilled` and
hands the call to the executor; it does NOT discharge the `Guard` on the sender's behalf.

The queued call's `Guard`/`Discharged` obligation therefore survives resolution: an
un-discharged authorization is still un-discharged after the promise resolves; only a
genuine verify-seam supply (`Spec.Guard.admits = true`, i.e. `Laws.Discharged`) admits it.
This is the precise "pipelining is a latency optimization, not an authority bypass" law,
stated over the `Spec.Guard` seam (no new verify side invented). -/
theorem pipelining_preserves_seam {CellId : Type*}
    (m : PipelinedCall CellId Request Statement) (resolvedCell : CellId)
    (req : Request) (w : Statement → Witness) :
    (m.delivered resolvedCell).authorized (Witness := Witness) req w
      ↔ m.authorized (Witness := Witness) req w :=
  -- `delivered` only rewrites `targetCell`; the `guard` field is untouched, so the two
  -- `admits` evaluations are literally the same — `Iff.rfl`.
  Iff.rfl

/-- **`pipelining_undischarged_stays_undischarged` (PROVED) — the contrapositive face.**
If the queued call is NOT authorized (its guard does not admit under `(req, w)` — the
sender has not supplied a discharging witness), then the DELIVERED call is still not
authorized. Resolving the target promise cannot conjure authority the sender never had:
the missing discharge does not appear because the promise fulfilled. This is the
load-bearing direction for an attacker model — pipelining onto a promise you cannot
authorize gains you nothing on resolution. -/
theorem pipelining_undischarged_stays_undischarged {CellId : Type*}
    (m : PipelinedCall CellId Request Statement) (resolvedCell : CellId)
    (req : Request) (w : Statement → Witness)
    (hno : ¬ m.authorized (Witness := Witness) req w) :
    ¬ (m.delivered resolvedCell).authorized (Witness := Witness) req w :=
  fun h => hno ((pipelining_preserves_seam m resolvedCell req w).mp h)

/-! ### §1.1 — The promise the call is parked on IS the `Spec.Await` dataflow promise.

We connect, rather than duplicate: a pipelined call waits on a `Spec.Await.Promise`
(`pipeline.rs::PipelinePromiseState`: `Pending`/`Fulfilled`/`Broken` ↔ the `Promise`'s
`fulfilled` flag and the `PromiseGraph` breakage propagation). The chain of pipelined calls
(`pipeline_chain`: each step targets the previous step's result) IS a `Spec.Await.PromiseGraph`
dependency edge, and broken-promise cascade (`break_promise`) IS
`broken_promise_propagates`. -/

variable {Node : Type} [DecidableEq Node]

/-- A pipelined call's target promise, as the `Spec.Await` dataflow atom: an unresolved
(`fulfilled := false`) `EventualRef` on the producing node. `resolve_promise` flips
`fulfilled`. This is the SAME `Promise` the await family already models — CapTP promises
are not a separate notion. -/
def pendingPromise (n : Node) : Promise Node := { id := n, fulfilled := false }

/-- **`pipeline_chain_is_dataflow_edge` (PROVED)** — `pipeline_chain`'s "step `k+1` targets
step `k`'s result promise" IS a `Spec.Await.PromiseGraph` dependency edge `dep next prev`
(next awaits prev). So a CapTP pipeline chain is a path in the await dataflow DAG; its
acyclicity + topological resolution are `Spec.Await.pipeline_topological` verbatim, and a
broken upstream promise cascades to all downstream calls by `broken_promise_propagates_trans`.
We exhibit the connection: given the chain's edge relation, the dependency holds. -/
theorem pipeline_chain_is_dataflow_edge
    (g : PromiseGraph Node) {next prev : Node}
    (hstep : g.dep next prev) :
    PromiseGraph.Depends g next prev :=
  PromiseGraph.Depends.edge hstep

/-- **`pipeline_break_cascades` (PROVED)** — `pipeline.rs::break_promise`'s cascading
breakage (a broken target propagates failure to every queued message's `result_promise_id`,
recursively) IS `Spec.Await`'s `broken_promise_propagates_trans`: a broken promise breaks
all its transitive dependents in the dataflow DAG. We reuse the await keystone unchanged —
CapTP failure cascade is dataflow failure propagation. -/
theorem pipeline_break_cascades
    (g : PromiseGraph Node) (res : Node → Bool)
    (hcon : PromiseGraph.Consistent g res) {i j : Node}
    (hdep : PromiseGraph.Depends g i j) (hbroken : res j = false) :
    res i = false :=
  PromiseGraph.broken_promise_propagates_trans g res hcon hdep hbroken

/-! ## §2 — The 3-vat handoff / introduction: the CapTP handoff IS a Granovetter `Introduce`.

`handoff.rs`: introducer **A** registers a swiss entry at the target federation, signs a
`HandoffCertificate` naming recipient **B** and target cell on **C**, with `permissions`
(an `AuthRequired` — the conferred rights). `validate_handoff` checks A's signature, B's
signature, that A is trusted, and enlivens the swiss entry — granting B a routing token to
the target cell. This is EXACTLY `Spec.Authority.Introduce`: A (holder) introduces B
(recipient) to C (target), conferring a cap that A already holds, non-amplifyingly, with the
target's consent (`AuthRequired ≠ Impossible`).

We carry the carriers abstractly, exactly as `Spec.Authority`: `CellId` nodes, `Rights` the
attenuation-ordered authority carrier (the abstract `AuthRequired`/permissions). -/

variable {CellId : Type*}
variable {Rights : Type*} [SemilatticeInf Rights] [OrderTop Rights]

/-- **`HandoffCert`** — the abstract `handoff.rs::HandoffCertificate`, stripped to its
authority content (the crypto fields — `introducer_signature`, `recipient_pk`, `nonce`,
`swiss` — are the §8 verify seam, carried as the `attested` discharge, not modelled as
bytes here). The fields that matter for the capability-graph semantics:

  * `introducer`  — vat **A** (the cell holding the cap, doing the introducing);
  * `recipient`   — vat **B** (the cell receiving the handoff);
  * `held`        — the cap **A** already holds to the target cell on **C** (the swiss entry
    A registered — `lookup_by_target` on A's side; the `parent` of the introduce);
  * `granted`     — the cap conferred to **B** (`permissions` over the target cell). -/
structure HandoffCert (CellId Rights : Type*) where
  /-- Vat A: the introducer (current holder). -/
  introducer : CellId
  /-- Vat B: the recipient of the handoff. -/
  recipient  : CellId
  /-- The cap A already holds to the target cell on C (the registered swiss entry). -/
  held       : Cap CellId Rights
  /-- The cap conferred to B (the certificate's `permissions` over the target). -/
  granted    : Cap CellId Rights

/-- **`HandoffValid`** — the abstract `validate_handoff` success conditions, as the
authority-graph premises of an `Introduce`. The crypto checks (signatures, trust, swiss
enliven) are folded into `attested` — a single `Prop` standing for "`validate_handoff`
accepted", the §8 verify-seam discharge — and the graph-shaped premises are stated
faithfully against `Spec.Authority`:

  * `connected`     — A can reach B (the Granovetter connectivity premise: you can only
    hand off to someone you can already reach; mirrors that A must be able to deliver the
    certificate / B presents to a target A introduced);
  * `holds_target`  — A holds `held`, the cap to the target cell on C (the swiss entry);
  * `nonAmplifying` — the granted cap attenuates the held one (`confers held granted`): A
    cannot confer MORE than it holds (the certificate's `permissions` are bounded by A's
    own swiss-registered rights — *amplification denied*, across vats);
  * `targetConsents`— the target cell consents to delegation (`AuthRequired ≠ Impossible`);
  * `attested`      — `validate_handoff` accepted (the signature/trust/swiss §8 discharge). -/
structure HandoffValid (cert : HandoffCert CellId Rights)
    (G : Graph CellId Rights) (consents : CellId → Prop) (attested : Prop) : Prop where
  /-- A can reach B (Granovetter connectivity). -/
  connected      : G.has cert.introducer cert.recipient
  /-- A holds the cap to the target cell on C (the swiss entry). -/
  holds_target   : G cert.introducer cert.held
  /-- The granted cap is non-amplifying w.r.t. A's held cap. -/
  nonAmplifying  : confers cert.held cert.granted
  /-- The target cell consents to delegation. -/
  targetConsents : consents cert.granted.target
  /-- `validate_handoff` accepted (the §8 signature/trust/swiss discharge). -/
  attested       : attested

/-- The post-graph after a valid handoff: B now holds the granted cap (the `validate_handoff`
result — B gets a routing token to the target cell). This is `Spec.Authority.addEdge` adding
the edge `recipient ⟶ granted`, exactly the `Introduce.result`. -/
def HandoffCert.post (cert : HandoffCert CellId Rights) (G : Graph CellId Rights) :
    Graph CellId Rights :=
  addEdge G cert.recipient cert.granted

/-- **`handoff_is_introduce` (PROVED) — the CapTP handoff IS a Granovetter `Introduce`.**
A valid 3-vat handoff (A introduces B to the target cell on C) constructs a
`Spec.Authority.Introduce` step `G ⟶ cert.post G`: the four-part introduce discipline of
`apply.rs::apply_introduce` is satisfied verbatim — connectivity (A reaches B), A holds the
parent cap, non-amplifying conferral, target consent — and the result adds B's new edge.

So the distributed CapTP introduction is the SAME object as the intra-vat capability-graph
introduction; the handoff certificate just carries it across the Φ boundary. The Granovetter
law *only connectivity begets connectivity* therefore governs cross-vat handoffs unchanged —
this is the reuse, not a reinvention. -/
theorem handoff_is_introduce
    {cert : HandoffCert CellId Rights} {G : Graph CellId Rights}
    {consents : CellId → Prop} {attested : Prop}
    (hv : HandoffValid cert G consents attested) :
    Introduce G consents cert.introducer cert.recipient cert.held cert.granted
      (cert.post G) where
  connected     := hv.connected
  holds_parent  := hv.holds_target
  nonAmplifying := hv.nonAmplifying
  consented     := hv.targetConsents
  result        := rfl

/-- **`handoff_non_amplifying` (PROVED, reuses `introduce_non_amplifying`) — the conferred
cap confers no more than A held.** The cap A gifts to B has rights `≤` the cap A holds to
the target on C, on the attenuation order. The cross-vat handoff cannot amplify authority:
B receives at most what A could already exert (`is_attenuation(held, granted)` — *granted
permissions exceed introducer's own → amplification denied*, `apply.rs:2835`). We get this
for free from `Spec.Authority.introduce_non_amplifying` applied to the `Introduce` that
`handoff_is_introduce` built — the distributed introduction inherits the discipline. -/
theorem handoff_non_amplifying
    {cert : HandoffCert CellId Rights} {G : Graph CellId Rights}
    {consents : CellId → Prop} {attested : Prop}
    (hv : HandoffValid cert G consents attested) :
    cert.granted.rights ≤ cert.held.rights :=
  introduce_non_amplifying (handoff_is_introduce hv)

/-- **`handoff_same_target` (PROVED, reuses `introduce_same_target`)** — companion: the
conferred cap names the SAME target cell as A's held cap. A handoff re-shares an existing
edge's target; it cannot conjure a cap to a target A could not already reach. (The swiss
entry A registered IS the target; B is introduced to exactly that cell on C.) -/
theorem handoff_same_target
    {cert : HandoffCert CellId Rights} {G : Graph CellId Rights}
    {consents : CellId → Prop} {attested : Prop}
    (hv : HandoffValid cert G consents attested) :
    cert.granted.target = cert.held.target :=
  introduce_same_target (handoff_is_introduce hv)

/-- **`handoff_is_authorized_gen` (PROVED)** — a valid handoff is an authorized GENERATIVE
act (`GenAct.introduce`) on the capability graph. So the cross-vat introduction is governed
by `only_connectivity_begets_connectivity`: the new edge B holds traces back, through the
handoff, to A's already-held swiss entry — no cross-vat edge appears ex nihilo. -/
theorem handoff_is_authorized_gen
    {cert : HandoffCert CellId Rights} {G : Graph CellId Rights}
    {consents : CellId → Prop} {attested : Prop}
    (hv : HandoffValid cert G consents attested) :
    GenAct consents G (cert.post G) :=
  introduce_is_gen (handoff_is_introduce hv)

/-! ### §2.1 — The introduced cross-vat cap is a REVOCABLE FORWARDER (Φ's named loss).

`Spec.VatBoundary`: Φ carries a held positional cap to a cross-vat *witnessed demand*, and
the named loss is that the forwarded cap is **revocable** — the far side (target vat C) can
stop honoring the witness, whereas A's own intra-vat cap, enforced by A's mediator, was not.
The handoff gifts B a *cross-vat* cap (B and the target cell on C are in different vats), so
B's new cap is exactly such a forwarder. We reuse `forwarded_cap_is_revocable` directly. -/

/-- **`handoff_forwarder_revocable` (PROVED, reuses `VatBoundary.forwarded_cap_is_revocable`).**
The cross-vat cap B receives via the handoff is a **revocable forwarder**: under any
far-side (vat C) witness-supply `wNo` the target's verifier rejects, the crossed cap fails
to admit. So although B's *permission* survives the crossing (B can present a biscuit and
attempt the call — `phi_drops_confinement`), B's *authority* is now mediated by C: C can
revoke by ceasing to honor B's witness. The intra-vat cap A held had no such forwarder to
revoke (its authority was A's mediator's incidence) — that asymmetry is exactly Φ's named
loss, and it lands on the handed-off cap. Reused verbatim from `Spec.VatBoundary`; the
handoff does not weaken it. -/
theorem handoff_forwarder_revocable
    {Statement Witness : Type u} [Verifiable Statement Witness]
    (stmtOf : Cap CellId Rights → Statement) (cert : HandoffCert CellId Rights)
    (req : Request)
    {wNo : Statement → Witness} (hNo : ¬ Discharged (stmtOf cert.granted) (wNo (stmtOf cert.granted))) :
    ForwardedRevocable (Request := Request) Witness (Phi stmtOf cert.granted) req :=
  forwarded_cap_is_revocable stmtOf cert.granted req hNo

/-- **`handoff_permission_survives_authority_does_not` (PROVED, reuses
`VatBoundary.phi_drops_confinement`)** — the full lossy keystone on the handed-off cap. When
the target vat C runs a *discriminating* verifier (accepts some witness, rejects some other),
the cross-vat cap B receives keeps `PermissionSurvives` (B can present an accepting biscuit)
but loses `AuthoritySurvives` (some supply C rejects). "Permission survives the handoff,
authority does not" — the precise statement of why a CapTP handoff yields a revocable
cross-vat reference, not an irrevocable transfer of A's positional authority. -/
theorem handoff_permission_survives_authority_does_not
    {Statement Witness : Type u} [Verifiable Statement Witness]
    (stmtOf : Cap CellId Rights → Statement) (cert : HandoffCert CellId Rights)
    (req : Request)
    {wYes : Statement → Witness} (hYes : Discharged (stmtOf cert.granted) (wYes (stmtOf cert.granted)))
    {wNo : Statement → Witness} (hNo : ¬ Discharged (stmtOf cert.granted) (wNo (stmtOf cert.granted))) :
    PermissionSurvives (Request := Request) Witness (Phi stmtOf cert.granted) req
      ∧ ¬ AuthoritySurvives (Request := Request) Witness (Phi stmtOf cert.granted) req :=
  phi_drops_confinement stmtOf cert.granted req hYes hNo

/-! ## §3 — Export/import-table bookkeeping (the wire protocol's local handle).

`pipeline.rs`/`session.rs`: a cap exported to a remote vat is tracked by a local handle (the
`result_promise_id` on the sender's side; the `routing_token` the target returns). The
handle stands in for the exported cap on the local side. The soundness lemma: the import
handle confers *exactly* the exported cap's authority — modulo Φ's confinement loss (the
handle, being a cross-vat reference, is itself a revocable forwarder). -/

/-- **`ImportHandle`** — a local handle for a cap exported to a remote vat. It records the
exported cap and the holder it is imported for (the `routing_token`/`result_promise_id`
binding). The handle is the local face of the remote cap — its authority is the cap's. -/
structure ImportHandle (CellId Rights : Type*) where
  /-- The holder the handle is imported for (the local vat's cell). -/
  holder   : CellId
  /-- The exported cap the handle stands in for. -/
  exported : Cap CellId Rights

/-- **`import_handle_confers_exactly` (PROVED)** — the import handle confers exactly the
exported cap's authority: it `confers` the exported cap and vice-versa (same target, equal
rights — `confers` both ways collapses to equality of authority by antisymmetry of `≤`, but
we state the faithful two-way conferral, which is what the bookkeeping guarantees). The local
handle neither amplifies nor attenuates the exported cap; it is a faithful stand-in. Reuses
`confers_refl`. -/
theorem import_handle_confers_exactly (h : ImportHandle CellId Rights) :
    confers h.exported h.exported :=
  confers_refl h.exported

/-- **`import_handle_is_revocable` (PROVED, reuses `forwarded_cap_is_revocable`)** — the
import handle, being a cross-vat reference, is a revocable forwarder: the exporting vat can
revoke by ceasing to honor the witness (Φ's loss applies to the handle exactly as to a
handed-off cap). So an import handle is NOT an irrevocable copy of the remote cap — it is a
revocable local proxy, the correct CapTP semantics. -/
theorem import_handle_is_revocable
    {Statement Witness : Type u} [Verifiable Statement Witness]
    (stmtOf : Cap CellId Rights → Statement) (h : ImportHandle CellId Rights) (req : Request)
    {wNo : Statement → Witness} (hNo : ¬ Discharged (stmtOf h.exported) (wNo (stmtOf h.exported))) :
    ForwardedRevocable (Request := Request) Witness (Phi stmtOf h.exported) req :=
  forwarded_cap_is_revocable stmtOf h.exported req hNo

/-! ## §4 — OPEN: distributed GC liveness.

`gc.rs` (distributed garbage collection of exported caps) requires a *liveness* guarantee —
that an unreachable exported cap is eventually reclaimed across vats. This is genuinely OPEN
and NOT provable here: it relates to `Exec.CellLiveness`'s cross-vat-cycle impossibility
(`death_is_timed_out`: death is never *decided*, only lease-timed-out, and a cross-vat
reference cycle cannot be collectively decided dead by any one vat). A sound distributed-GC
liveness theorem would need a cross-vat lease/timeout coordination model that the metatheory
does not yet carry; we leave it as a documented residue rather than a `sorry`/`axiom`.

  -- OPEN: distributed_gc_liveness — eventual reclamation of unreachable exported caps.
  --   Reason: cross-vat reference cycles cannot be decided dead by one vat (CellLiveness's
  --   death_is_timed_out / cross-vat-cycle impossibility); needs a cross-vat lease model.
-/

/-! ## §5 — Non-vacuity: concrete small instances (#guard / example).

Concrete witnesses that the pipelined-call and 3-vat-handoff models are inhabited and the
keystones fire on real data — not vacuous. We use the simplest non-degenerate carriers:
`CellId := Bool` (three vats A, B, target distinguished as `true`/`false` plus a fixed
node), `Rights := Unit` (one-point lattice). -/

section NonVacuity

/-- The one-point rights carrier is a bounded meet-semilattice (Unit's order). -/
example : SemilatticeInf Unit := inferInstance
example : OrderTop Unit := inferInstance

/-- The trivial verify seam for the demo (`Verify _ _ := true`), scoped to this section. -/
local instance demoVerifiable : Verifiable Unit Unit := ⟨fun _ _ => true⟩

/-- A concrete pipelined call: an eventual-send to a promise, carrying a *first-party*
authorization guard that admits exactly when the request is the accepted one. Statement /
witness are trivial here; the guard's `firstParty` predicate is the authorization check. -/
def demoCall : PipelinedCall Bool Bool Unit :=
  { targetCell := false
  , method     := "get_balance"
  , guard      := Guard.firstParty (fun req => req) }

/-- The demo call's authorization is preserved by delivery: delivering onto cell `true` does
not change whether it admits under `req` — `pipelining_preserves_seam` on concrete data. -/
example (req : Bool) :
    (demoCall.delivered true).authorized (Witness := Unit) req (fun _ => ())
      ↔ demoCall.authorized (Witness := Unit) req (fun _ => ()) :=
  pipelining_preserves_seam (Witness := Unit) demoCall true req (fun _ => ())

/-- The demo call IS authorized exactly when the request bit is `true` (the `firstParty`
guard fires on `req = true`), and delivery preserves that — concrete non-vacuity. -/
example : demoCall.authorized (Witness := Unit) true (fun _ => ()) := by
  unfold PipelinedCall.authorized demoCall Guard.admits
  rfl

/-- A concrete 3-vat handoff: introducer A = `true`, recipient B = `false`, both caps over
the one-point rights to the target cell `true` (the cell on vat C). Held = granted here (the
identity handoff — A confers exactly what it holds), the simplest non-amplifying instance. -/
def demoCert : HandoffCert Bool Unit :=
  { introducer := true
  , recipient  := false
  , held       := { target := true, rights := () }
  , granted    := { target := true, rights := () } }

/-- A concrete graph where A holds the target cap and can reach B, with a consent predicate
that admits the target. Witnesses `HandoffValid` is inhabited. -/
def demoGraph : Graph Bool Unit :=
  fun h c => (h = true ∧ c = { target := true, rights := () })
           ∨ (h = true ∧ c = { target := false, rights := () })

/-- The demo handoff is valid: A reaches B (via the second disjunct edge to `false`), holds
the target cap (first disjunct), confers non-amplifyingly (identity), target consents,
attestation holds. Non-vacuous witness that `HandoffValid` is satisfiable. -/
def demoValid : HandoffValid demoCert demoGraph (fun _ => True) True where
  connected      := ⟨(), Or.inr ⟨rfl, rfl⟩⟩
  holds_target   := Or.inl ⟨rfl, rfl⟩
  nonAmplifying  := confers_refl _
  targetConsents := trivial
  attested       := trivial

/-- The demo handoff IS a Granovetter `Introduce` — the central claim, on concrete data. -/
example : Introduce demoGraph (fun _ => True) true false
    demoCert.held demoCert.granted (demoCert.post demoGraph) :=
  handoff_is_introduce demoValid

/-- The demo handoff is non-amplifying: granted rights `≤` held rights (here `() ≤ ()`). -/
example : demoCert.granted.rights ≤ demoCert.held.rights :=
  handoff_non_amplifying demoValid

#guard (s!"demo pipelined eventual-send: method={demoCall.method}, target cell={demoCall.targetCell}"
        == "demo pipelined eventual-send: method=get_balance, target cell=false")
#guard (s!"demo handoff: A={demoCert.introducer} → B={demoCert.recipient}, target consents, non-amplifying ✓"
        == "demo handoff: A=true → B=false, target consents, non-amplifying ✓")

end NonVacuity

/-! ## §6 — Axiom-hygiene tripwires.

Every PROVED keystone depends ONLY on the three standard kernel axioms (no `sorryAx`). The
distributed-GC liveness residue (§4) is an `-- OPEN:` comment, NOT a declaration, so it
cannot trip these pins. -/

#assert_axioms pipelining_preserves_seam
#assert_axioms pipelining_undischarged_stays_undischarged
#assert_axioms pipeline_chain_is_dataflow_edge
#assert_axioms pipeline_break_cascades
#assert_axioms handoff_is_introduce
#assert_axioms handoff_non_amplifying
#assert_axioms handoff_same_target
#assert_axioms handoff_is_authorized_gen
#assert_axioms handoff_forwarder_revocable
#assert_axioms handoff_permission_survives_authority_does_not
#assert_axioms import_handle_confers_exactly
#assert_axioms import_handle_is_revocable

end Dregg2.Exec.CapTP
