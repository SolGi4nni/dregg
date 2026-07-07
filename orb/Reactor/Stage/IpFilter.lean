import Reactor.Pipeline
import IpFilter

/-!
# Reactor.Stage.IpFilter — the CIDR admission GATE as a byte-driving pipeline stage

`IpFilter` (the base library) proved the access-control core: `permits`, an ordered
allow/deny CIDR decision with deny-precedence and a default toggle. This file
promotes that decision from a *proof-attachment* to a **byte-driver** in the deployed
serve fold: a `Stage` whose request phase runs the REAL `IpFilter.permits` decision on
the client address carried in the context and, on a rejected address, short-circuits
the whole pipeline with a serializer-built **403 Forbidden** — the handler and every
later stage are skipped, and the emitted bytes are the 403's, not the handler's. A
permitted address passes straight through, so the handler's own response is emitted
unchanged. The effect is visible in `runPipeline (…).build`.

## The deployed ruleset — production-safe over a real listener

`deployRuleset` is `defaultDeny := false` (admit by default) with ONE real deny block,
`10.0.0.0/8`. That is the production-safe shape for a listener whose accepted peers are
mostly untrusted-but-allowed: an unlisted address (a normal client, loopback,
`127.0.0.0/8`, …) is ADMITTED, while any address inside the denied `/8` is 403'd by the
REAL deny-precedence path. This is deliberately NOT a fail-closed `defaultDeny := true`
policy: a fail-closed default would 403 every real peer (e.g. the loopback the dataplane
accepts on), which is not a deployable gate — it is an outage. The gate only fires on a
client address that actually lands in the configured deny CIDR.

The client address is threaded through the context's extensible `attrs` bag under
`clientIpKey` (a simple family-tagged byte encoding; `decodeAddr ∘ encodeAddr` is the
identity on the concrete clients). No `Ctx`/`Stage` field is widened — the disjoint
one-file discipline the pipeline is built for. The accept path (the dataplane host)
writes the peer address it read off the socket under `clientIpKey`; this stage reads it
in the request phase.
-/

namespace Reactor.Stage.IpFilter

open Reactor.Pipeline
open Proto (Request Bytes)
open _root_.IpFilter (Addr Family Cidr Action Ruleset)

/-! ## Carrying the client address in the context attribute bag -/

/-- The `attrs` key the client IP is stashed under (written by the accept path that
reads the peer address off the socket; read here in the request phase). -/
def clientIpKey : String := "client.ip"

/-- Encode a client address into the attribute bytes: a family tag byte (`4`/`6`)
followed by one `0`/`1` byte per address bit. -/
def encodeAddr (a : Addr) : Bytes :=
  (match a.family with | .v4 => (4 : UInt8) | .v6 => (6 : UInt8))
    :: a.bits.map (fun b => if b then (1 : UInt8) else (0 : UInt8))

/-- Decode the attribute bytes back to an address; the inverse of `encodeAddr` on
well-formed input (`decode_encode` below on the concrete clients). -/
def decodeAddr : Bytes → Addr
  | []          => ⟨.v4, []⟩
  | fam :: rest => ⟨if fam == 6 then .v6 else .v4, rest.map (fun b => b != 0)⟩

/-- The client address the stage decides on: the one stashed under `clientIpKey`,
or an empty v4 address (which the default-admit policy passes) when none is present. -/
def ctxAddr (c : Ctx) : Addr :=
  match c.attrs.find? (fun kv => kv.1 == clientIpKey) with
  | some kv => decodeAddr kv.2
  | none    => ⟨.v4, []⟩

/-! ## The deployed admission ruleset -/

/-- `10.0.0.0/8` as a CIDR — network prefix `00001010` (MSB-first), length `8`. The one
deny block of the deployed listener. -/
def denyCidr : Cidr :=
  { family := .v4, net := [false, false, false, false, true, false, true, false], len := 8 }

/-- **The deployed admission ruleset.** One deny rule (`10.0.0.0/8`) with default-admit
(`defaultDeny := false`): an unlisted client (loopback, any public peer) is ADMITTED; a
client inside `10.0.0.0/8` is 403'd via the REAL deny-precedence path. Production-safe —
it never fails closed on a real accepted peer. -/
def deployRuleset : Ruleset :=
  { rules := [(denyCidr, Action.deny)], defaultDeny := false }

/-- The REAL admission decision: `IpFilter.permits` over the deployed ruleset. `true` =
admit, `false` = reject. Not a stub — the base-library access-control transition. -/
def deployAdmits (a : Addr) : Bool := _root_.IpFilter.permits deployRuleset a

/-! ## Concrete witnesses (non-vacuity) -/

/-- A blocked client: `10.0.0.0` — inside the denied `/8`, so deny-precedence fires. -/
def blockedClient : Addr :=
  ⟨.v4, [false, false, false, false, true, false, true, false] ++ List.replicate 24 false⟩

/-- A clean client: `127.0.0.0` (loopback) — outside the deny CIDR, so it is admitted by
the default-admit policy. This is the kind of peer the dataplane actually accepts. -/
def cleanClient : Addr :=
  ⟨.v4, [false, true, true, true, true, true, true, true] ++ List.replicate 24 false⟩

/-- The blocked client is rejected — the REAL deny path fires. -/
theorem deployAdmits_blocked : deployAdmits blockedClient = false := by decide

/-- The clean (loopback) client is admitted — default-admit passes it. -/
theorem deployAdmits_clean : deployAdmits cleanClient = true := by decide

/-- Round-trip: decoding an encoded address recovers it (concrete-witness form). -/
theorem decode_encode_blocked :
    decodeAddr (encodeAddr blockedClient) = blockedClient := rfl

theorem decode_encode_clean :
    decodeAddr (encodeAddr cleanClient) = cleanClient := rfl

/-! ## The 403 the gate serves -/

/-- `403` reason phrase and body — the bytes the gate emits in place of the handler. -/
def forbiddenReason : Bytes := "Forbidden".toUTF8.toList
def forbiddenBody : Bytes := "forbidden: ip not admitted".toUTF8.toList

/-- The serializer-built 403 response a rejected client receives. -/
def forbidden403 : Response :=
  { status := 403, reason := forbiddenReason, headers := [], body := forbiddenBody }

/-! ## The stage -/

/-- **The IP-filter gate.** The request phase runs the REAL deployed admission decision
(`deployAdmits`, i.e. `IpFilter.permits` over the deploy allow/deny CIDR policy) on the
context's client address. A rejected address `.respond`s the 403 — short-circuiting the
handler and every later stage. A permitted address `.continue`s unchanged. The response
phase is the identity on the affine builder: this stage acts entirely in the request
phase (a pure gate), so a passed-through response is threaded outward untouched. -/
def ipfilterStage : Stage where
  name := "ipfilter"
  onRequest := fun c =>
    match deployAdmits (ctxAddr c) with
    | true  => .continue c
    | false => .respond forbidden403
  onResponse := fun _ b => b

/-! ## Concrete contexts -/

/-- A context whose client is in the blocked CIDR (deny-precedence fires). -/
def blockedCtx : Ctx :=
  { input := [], req := {}, attrs := [(clientIpKey, encodeAddr blockedClient)] }

/-- A context whose client is a clean trusted host (admitted). -/
def cleanCtx : Ctx :=
  { input := [], req := {}, attrs := [(clientIpKey, encodeAddr cleanClient)] }

/-! ## Byte-effect theorems -/

/-- The gate fires on the blocked client: its request phase `.respond`s the 403. -/
theorem ipfilterStage_gates_blocked :
    ipfilterStage.onRequest blockedCtx = .respond forbidden403 := by
  have h : deployAdmits (ctxAddr blockedCtx) = false := by
    rw [show ctxAddr blockedCtx = blockedClient from rfl]; exact deployAdmits_blocked
  simp only [ipfilterStage, h]

/-- The gate passes the clean client: its request phase `.continue`s unchanged. -/
theorem ipfilterStage_passes_clean :
    ipfilterStage.onRequest cleanCtx = .continue cleanCtx := by
  have h : deployAdmits (ctxAddr cleanCtx) = true := by
    rw [show ctxAddr cleanCtx = cleanClient from rfl]; exact deployAdmits_clean
  simp only [ipfilterStage, h]

/-- **Byte-effect (gate).** A blocked client's emitted response IS the 403 — for ANY
tail and ANY handler. Because the built output is `forbidden403` regardless of the
handler, the handler's body never reaches the wire: the gate genuinely changes the
emitted bytes. -/
theorem ipfilterStage_blocked_emits_403 (rest : List Stage) (h : Ctx → Response) :
    runPipeline (ipfilterStage :: rest) h blockedCtx
      = runResp rest blockedCtx (ResponseBuilder.ofResponse forbidden403) :=
  pipeline_gate_short_circuits ipfilterStage rest h blockedCtx forbidden403
    ipfilterStage_gates_blocked

/-- The emitted status on a blocked client is exactly `403` — preserved through a
status-stable inner onion (the refusal now carries the response transforms). -/
theorem ipfilterStage_blocked_status_403 (rest : List Stage) (h : Ctx → Response)
    (hst : ∀ t ∈ rest, Stage.statusStable t) :
    ((runPipeline (ipfilterStage :: rest) h blockedCtx).build).status = 403 :=
  pipeline_gate_status ipfilterStage rest h blockedCtx forbidden403
    ipfilterStage_gates_blocked hst

/-- **The skip is real.** A blocked client's output is unchanged by swapping the
HANDLER: the handler contributes nothing to the bytes. (The tail's response
transforms now enrich the refusal — the short-circuit-carries-transforms semantics.) -/
theorem ipfilterStage_blocked_ignores_handler
    (rest : List Stage) (h h' : Ctx → Response) :
    runPipeline (ipfilterStage :: rest) h blockedCtx
      = runPipeline (ipfilterStage :: rest) h' blockedCtx :=
  pipeline_gate_ignores_handler ipfilterStage rest h h' blockedCtx forbidden403
    ipfilterStage_gates_blocked

/-- **Byte-effect (pass-through).** A clean client passes the gate: the emitted
response is exactly the handler's — the gate does not perturb an admitted request's
bytes. (With no tail, `build` yields the handler's own response.) -/
theorem ipfilterStage_clean_emits_handler (h : Ctx → Response) :
    (runPipeline [ipfilterStage] h cleanCtx).build = h cleanCtx := by
  rw [pipeline_stage_effect ipfilterStage [] h cleanCtx cleanCtx
        ipfilterStage_passes_clean]
  show (runPipeline [] h cleanCtx).build = h cleanCtx
  rw [pipeline_empty, build_ofResponse]

/-- **Contrast — the gate is not a no-op.** On the SAME handler, a blocked client and
a clean client emit different responses whenever the handler is not itself a 403.
Concretely: blocked emits `forbidden403` (status 403) while clean emits `h cleanCtx`;
for a `200` handler the emitted statuses differ. -/
theorem ipfilterStage_changes_bytes (body : Bytes) :
    ((runPipeline [ipfilterStage] (fun _ => Reactor.ok200 body) blockedCtx).build).status = 403
    ∧ ((runPipeline [ipfilterStage] (fun _ => Reactor.ok200 body) cleanCtx).build).status = 200 := by
  refine ⟨ipfilterStage_blocked_status_403 [] _ (by intro t ht; exact absurd ht (List.not_mem_nil t)), ?_⟩
  rw [ipfilterStage_clean_emits_handler]
  rfl

/-! ## Axiom audit -/

#print axioms deployAdmits_blocked
#print axioms deployAdmits_clean
#print axioms ipfilterStage_gates_blocked
#print axioms ipfilterStage_passes_clean
#print axioms ipfilterStage_blocked_emits_403
#print axioms ipfilterStage_blocked_status_403
#print axioms ipfilterStage_blocked_ignores_handler
#print axioms ipfilterStage_clean_emits_handler
#print axioms ipfilterStage_changes_bytes

end Reactor.Stage.IpFilter
