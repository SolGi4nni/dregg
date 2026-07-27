import Reactor.Pipeline

/-!
# Reactor.Stage.ConnLimit — the per-source concurrent-connection cap GATE

A byte-driving `Stage` for the extensible serve fold: on the request phase it
consults the number of connections currently active from this request's source
(its client IP) and, when that count has reached the configured per-source cap,
short-circuits the whole pipeline with a `503 Service Unavailable` — the handler
and every later stage are skipped. Under the cap the request passes through
untouched.

## The decision core — a real bounded admission test

`admits cap active` is the exact admission rule of a per-source concurrent cap: a
new connection is admitted iff the cap is disabled (`cap = 0`, unlimited) OR the
source's active-connection count is strictly below the cap. This is the total,
saturation-free form of the reference accept test (reject once `active ≥ cap`;
always accept when the cap is `0`).

Because the sans-IO serve is one stateless call per request, the source's standing
active-connection count rides in the extensible attribute bag under `activeKey`:
the accept path (which owns the per-IP counter) stashes that many bytes, and the
gate reads its length. A source at or over the cap therefore reconstructs an
over-limit `active`, and the REAL `admits` decision rejects it with a `503`.

The effect is a genuine change to the emitted bytes:

* `connStage_gate_build` — at/over the cap, the built pipeline response IS the `503`;
* `connStage_pass` — under the cap, the stage is transparent (the handler's bytes);
* `connStage_changes_bytes` — same handler, an over-cap and an under-cap source emit
  *different* status bytes: the gate really drives the wire.

`admits` truth-table lemmas (`admits_unlimited`, `admits_under`, `admits_at_cap`,
`admits_over`) and the concrete over/under contexts (`overCtx_over`,
`underCtx_under`, closed by `decide`) keep all of the above non-vacuous.

## The cap is CONFIG, not a constant

`admits` always took the cap as a PARAMETER; what used to be hardcoded was the value
fed to it (`connCap := 4`, a module constant no operator directive could move — a
default deployment answered `503` to any source at five concurrent connections, below
what a browser opens). The cap now rides the context alongside the count, under
`capKey`, written by the host from the operator's `max-connections`; `capOf` reads it
and `defaultConnCap` (512, the config layer's own default) applies when none was
threaded. `knob_moves_the_gate` is the statement that the configured value decides:
the same five connections are refused at a configured `4` and admitted at a
configured `16`.
-/

namespace Reactor.Stage.ConnLimit

open Reactor.Pipeline
open Proto (Bytes)

/-! ## The 503 rejection response -/

/-- Reason phrase for the rejection. -/
def reason503 : Bytes := "Service Unavailable".toUTF8.toList

/-- Body prose for the rejection. -/
def busyBody : Bytes := "per-source connection limit reached\n".toUTF8.toList

/-- The `503 Service Unavailable` response the gate answers with when the source is
at or over its concurrent-connection cap — a real `Response` whose status is `503`. -/
def resp503 : Response := error4xx 503 reason503 busyBody

/-! ## The decision core -/

/-- **The DEFAULT per-source concurrent-connection cap** — the cap in force when a
context carries no configured one (`capOf`, below). `512`: the SAME number the
operator config layer defaults `max-connections` to, so one source is bounded by ONE
per-source number rather than two disagreeing ones.

Deliberately NOT the process-wide bound. The process-wide ceiling (how many
connections the whole reactor may hold at once) and this per-source policy bound (how
many ONE source may hold) are different quantities over different state and must not
be conflated: the first is a resource bound on the process, the second is a fairness
bound on a peer. This one only has to sit above what a legitimate SINGLE client
opens — a browser opens ~6 parallel connections per origin, an aggressive one a few
dozen, a NAT/CDN egress hundreds — while still bounding a single-source flood well
under the process ceiling.

The previous value (`4`) sat BELOW a browser: a default deployment answered `503` to
any source at five concurrent connections, and no config value could move it. `0`
(explicitly configured) still disables the cap entirely. -/
def defaultConnCap : Nat := 512

/-- **The admission decision.** A new connection from a source with `active`
currently-open connections is admitted iff the cap is disabled (`cap = 0`) or the
source is strictly below the cap. This is the reference accept rule, total. -/
def admits (cap active : Nat) : Bool := cap == 0 || active < cap

/-! ### Truth table (non-vacuity of the decision) -/

/-- A disabled cap (`0`) admits any load — the unlimited path. -/
theorem admits_unlimited (active : Nat) : admits 0 active = true := by
  simp [admits]

/-- Strictly under the cap ⇒ admitted. -/
theorem admits_under {cap active : Nat} (hpos : 0 < cap) (h : active < cap) :
    admits cap active = true := by
  simp only [admits, Bool.or_eq_true, decide_eq_true_eq]
  exact Or.inr h

/-- Exactly at the cap ⇒ rejected (the boundary is closed against admission). -/
theorem admits_at_cap {cap : Nat} (hpos : 0 < cap) : admits cap cap = false := by
  simp only [admits, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true']
  simp [Nat.ne_of_gt hpos, Nat.lt_irrefl]

/-- At or over the cap (with a live cap) ⇒ rejected. -/
theorem admits_over {cap active : Nat} (hpos : 0 < cap) (h : cap ≤ active) :
    admits cap active = false := by
  have h0 : (cap == 0) = false := by simp [Nat.ne_of_gt hpos]
  have h1 : decide (active < cap) = false := by simp [Nat.not_lt.mpr h]
  simp only [admits, h0, h1, Bool.or_false]

/-! ### The default cap admits a browser (non-vacuity of the DEFAULT choice) -/

/-- **A browser-shaped burst is admitted by default.** Eight concurrent connections
from one source — more than the ~6 a browser opens per origin — pass the default
cap. -/
theorem defaultConnCap_admits_browserBurst : admits defaultConnCap 8 = true := by decide

/-- …and the retired module constant genuinely did NOT admit it: the two caps
DISAGREE on the browser burst, so raising the default is a real change of decision,
not a rename. This is the regression, stated. -/
theorem retiredCap4_refused_browserBurst : admits 4 8 = false := by decide

/-! ## Reading the source's active-connection count off the context -/

/-- Attribute key holding the source's standing active-connection count (its
byte-length = the number of connections currently open from this source). Written
by the accept path that owns the per-source counter. -/
def activeKey : String := "conn-active"

/-- Look the value bytes up for a key in the attribute bag (`[]` if absent). -/
def lookupBytes (c : Ctx) (k : String) : Bytes :=
  match c.attrs.find? (fun p => p.1 == k) with
  | some p => p.2
  | none   => []

/-- The source's active-connection count = the length of the `activeKey` attr
(`0` when absent — a fresh source with no standing connections). -/
def activeOf (c : Ctx) : Nat := (lookupBytes c activeKey).length

/-! ## Reading the CONFIGURED cap off the context

The per-source cap is OPERATOR CONFIG (`max-connections`), not a module constant. It
rides the SAME extensible attribute bag the accept-path readings do — that bag exists
precisely so a new input does not widen the shared `Ctx` — under `capKey`, as a
little-endian base-256 word of exactly eight bytes (the host crosses a `UInt64`). A
context carrying no such attr (every model context, and the plain sans-IO
`ctxOfMetered`) denotes the DEFAULT cap, so nothing that predates the knob changes.

The active COUNT is unary (`activeOf` is a length) because that is the accept-path
encoding already in place; the CAP is positional, so a cap of `512` costs eight bytes
rather than five hundred and twelve. -/

/-- Attribute key holding the CONFIGURED per-source cap (little-endian base-256,
exactly eight bytes). Written by the host from the operator's `max-connections`. -/
def capKey : String := "conn-cap"

/-- **The attribute-bag WORD codec, with a caller-chosen unconfigured value.**
Little-endian base-256 decode of an exact eight-byte word; any OTHER shape — the key
absent (`[]`) or a malformed width — reads as `d`, the value that denotes
"unconfigured" for this particular knob. That default is a PARAMETER because
different knobs disagree about it and must not be forced to share one: an absent
connection cap means `defaultConnCap` (512, the config layer's own default), while an
absent rate limit means `0` (the gate is OFF — the only reading under which a context
that predates the knob keeps its behaviour).

This is the ONE positional encoding in the attribute bag. Every host-threaded scalar
— the connection cap, the rate limit, the in-window arrival count — rides `encodeCap`
and comes back through `decodeWordD`, so there is a single round-trip theorem
(`decodeWordD_encodeCap`) rather than one per knob. -/
def decodeWordD (d : Nat) : Bytes → Nat
  | [b0, b1, b2, b3, b4, b5, b6, b7] =>
      b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * (b3.toNat +
        256 * (b4.toNat + 256 * (b5.toNat + 256 * (b6.toNat + 256 * b7.toNat))))))
  | _ => d

/-- Little-endian base-256 decode of an exact eight-byte cap word. Any OTHER shape —
the key absent (`[]`) or a malformed width — denotes "unconfigured" and reads as
`defaultConnCap`, which is what makes the knob additive: every existing context keeps
the default. -/
def decodeCap : Bytes → Nat := decodeWordD defaultConnCap

/-- Little-endian base-256 encode of a cap into an exact eight-byte word. -/
def encodeCap (n : Nat) : Bytes :=
  [ UInt8.ofNat n
  , UInt8.ofNat (n / 256)
  , UInt8.ofNat (n / 256 / 256)
  , UInt8.ofNat (n / 256 / 256 / 256)
  , UInt8.ofNat (n / 256 / 256 / 256 / 256)
  , UInt8.ofNat (n / 256 / 256 / 256 / 256 / 256)
  , UInt8.ofNat (n / 256 / 256 / 256 / 256 / 256 / 256)
  , UInt8.ofNat (n / 256 / 256 / 256 / 256 / 256 / 256 / 256) ]

/-- **The word round-trips, for EVERY unconfigured default.** Every scalar the host
can cross (it crosses a `UInt64`) is recovered EXACTLY by the decode — so the number
the proven gate decides on IS the number the operator configured, with no silent
truncation. Stated over `d` because the codec is shared: the connection cap, the rate
limit and the in-window arrival count all inherit this one proof. -/
theorem decodeWordD_encodeCap (d : Nat) {n : Nat} (h : n < 2 ^ 64) :
    decodeWordD d (encodeCap n) = n := by
  have hb : ∀ m : Nat, (UInt8.ofNat m).toNat = m % 256 := by
    intro m; simp [UInt8.toNat_ofNat]
  simp only [encodeCap, decodeWordD, hb]
  omega

/-- **The cap word round-trips** — the connection-cap instance of the shared codec
round trip. -/
theorem decodeCap_encodeCap {n : Nat} (h : n < 2 ^ 64) : decodeCap (encodeCap n) = n :=
  decodeWordD_encodeCap defaultConnCap h

/-- **The configured per-source cap carried by the context** — the operator's value
where the host threaded one, `defaultConnCap` otherwise. -/
def capOf (c : Ctx) : Nat := decodeCap (lookupBytes c capKey)

/-- A context with no `conn-cap` attr reads as the DEFAULT cap (the no-regression
fact every pre-knob context relies on). -/
theorem capOf_absent {c : Ctx} (h : lookupBytes c capKey = []) : capOf c = defaultConnCap := by
  simp [capOf, h, decodeCap, decodeWordD]

/-! ## The gate decision -/

/-- **The real gate decision on the context.** Admit iff the source's reconstructed
active count is under the cap the CONTEXT CARRIES — the operator's `max-connections`
where the host threaded one, `defaultConnCap` otherwise. The cap is an INPUT to the
decision here, never a constant baked into it. -/
def ctxAdmits (c : Ctx) : Bool := admits (capOf c) (activeOf c)

/-! ## The stage -/

/-- **The connection-limit gate stage.** Request phase: consult the real admission
rule on the source's active-connection count — admit → `.continue`, reject →
`.respond resp503` (short-circuit with the `503`, skipping the handler and every
later stage). Response phase: transparent — a pure gate. -/
def connStage : Stage where
  name := "conn-limit"
  onRequest  := fun c => cond (ctxAdmits c) (.continue c) (.respond resp503)
  onResponse := fun _ b => b

/-! ## The gate's request-phase decision -/

/-- At/over the cap, the gate short-circuits with the `503`. -/
theorem connStage_onReq_respond (c : Ctx) (hover : ctxAdmits c = false) :
    connStage.onRequest c = .respond resp503 := by
  simp only [connStage, hover, cond]

/-- Under the cap, the gate passes the context through. -/
theorem connStage_onReq_continue (c : Ctx) (hunder : ctxAdmits c = true) :
    connStage.onRequest c = .continue c := by
  simp only [connStage, hunder, cond]

/-! ## The byte effect -/

/-- **Gate byte-effect.** At/over the cap, the BUILT pipeline response — for ANY
tail and handler — is the `503`: the handler and every later stage are skipped. -/
theorem connStage_gate_build (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (hover : ctxAdmits c = false) :
    runPipeline (connStage :: rest) h c = runResp rest c (ResponseBuilder.ofResponse resp503) :=
  pipeline_gate_short_circuits connStage rest h c resp503 (connStage_onReq_respond c hover)

/-- The `503`'s status field is `503`. -/
theorem resp503_status : resp503.status = 503 := rfl

/-- The over-cap response's status byte is `503` — preserved through a
status-stable inner onion. -/
theorem connStage_over_status (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (hover : ctxAdmits c = false) (hst : ∀ t ∈ rest, Stage.statusStable t) :
    ((runPipeline (connStage :: rest) h c).build).status = 503 :=
  pipeline_gate_status connStage rest h c resp503 (connStage_onReq_respond c hover) hst

/-- **Pass-through byte-effect.** Under the cap, the stage is transparent: the
pipeline output is exactly the tail's. -/
theorem connStage_pass (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (hunder : ctxAdmits c = true) :
    runPipeline (connStage :: rest) h c = runPipeline rest h c := by
  rw [pipeline_stage_effect connStage rest h c c (connStage_onReq_continue c hunder)]
  rfl

/-! ## Concrete over- and under-cap contexts (non-vacuity) -/

/-- A context carrying an explicit CONFIGURED cap and an explicit standing
active-connection count — the shape the host builds per request. -/
def cfgCtx (cap active : Nat) : Ctx :=
  { input := [], req := {},
    attrs := [(capKey, encodeCap cap), (activeKey, List.replicate active (0 : UInt8))] }

/-- The configured cap is read back off `cfgCtx` exactly (for any cap the host can
cross). -/
theorem cfgCtx_cap {cap : Nat} (active : Nat) (h : cap < 2 ^ 64) :
    capOf (cfgCtx cap active) = cap := by
  have hl : lookupBytes (cfgCtx cap active) capKey = encodeCap cap := by
    simp [lookupBytes, cfgCtx, capKey, activeKey]
  rw [capOf, hl, decodeCap_encodeCap h]

/-- The standing count is read back off `cfgCtx` exactly. -/
theorem cfgCtx_active (cap active : Nat) : activeOf (cfgCtx cap active) = active := by
  simp [activeOf, lookupBytes, cfgCtx, capKey, activeKey]

/-- **THE KNOB MOVES THE GATE.** At the SAME five concurrent connections, a source
under a configured cap of `4` is REFUSED and a source under a configured cap of `16`
is ADMITTED. The decision follows the configured value; nothing here is a constant.
(Under the retired hardcoded cap both were refused — that was the bug.) -/
theorem knob_moves_the_gate :
    ctxAdmits (cfgCtx 4 5) = false ∧ ctxAdmits (cfgCtx 16 5) = true := by decide

/-- A context carrying ONLY the standing count — no configured cap, so the DEFAULT
cap applies. This is the shape every pre-knob context has. -/
def unconfiguredCtx (active : Nat) : Ctx :=
  { input := [], req := {}, attrs := [(activeKey, List.replicate active (0 : UInt8))] }

/-- An unconfigured context reads the DEFAULT cap. -/
theorem unconfiguredCtx_cap (active : Nat) : capOf (unconfiguredCtx active) = defaultConnCap := by
  simp [capOf, lookupBytes, unconfiguredCtx, capKey, activeKey, decodeCap, decodeWordD]

/-- **The default admits the browser burst on the real context shape.** With no
configured cap the gate admits a source holding eight concurrent connections — the
case a default deployment used to answer `503` to. -/
theorem default_admits_browserBurst : ctxAdmits (unconfiguredCtx 8) = true := by decide

/-- A source whose standing active-connection count has reached ITS CONFIGURED cap —
over the limit, so this connection is rejected. The witness now carries an explicit
configured cap, so it exercises the CONFIGURED path rather than a module constant. -/
def overCtx : Ctx := cfgCtx 4 4

/-- A fresh source (no standing connections, no configured cap) — under the default
limit, admitted. -/
def underCtx : Ctx := { input := [], req := {}, attrs := [] }

/-- `overCtx` is over the cap — the real rule rejects it. -/
theorem overCtx_over : ctxAdmits overCtx = false := by decide

/-- `underCtx` is under the cap — the real rule admits it. -/
theorem underCtx_under : ctxAdmits underCtx = true := by decide

/-- An over-cap connection emits a `503` (through a status-stable inner onion). -/
theorem overCtx_emits_503 (rest : List Stage) (h : Ctx → Response)
    (hst : ∀ t ∈ rest, Stage.statusStable t) :
    ((runPipeline (connStage :: rest) h overCtx).build).status = 503 :=
  connStage_over_status rest h overCtx overCtx_over hst

/-- An under-cap connection passes through to the tail unchanged. -/
theorem underCtx_passes (rest : List Stage) (h : Ctx → Response) :
    runPipeline (connStage :: rest) h underCtx = runPipeline rest h underCtx :=
  connStage_pass rest h underCtx underCtx_under

/-- **The gate genuinely drives the wire.** With the SAME handler and tail, an
over-cap source and an under-cap source emit different status bytes: the over-cap
one is forced to `503`, the under-cap one keeps the handler's status. So the stage
really changes the bytes the serve emits — a byte-driver, not a proof attachment. -/
theorem connStage_changes_bytes (h : Ctx → Response)
    (hstatus : (h underCtx).status ≠ 503) :
    ((runPipeline [connStage] h overCtx).build).status
      ≠ ((runPipeline [connStage] h underCtx).build).status := by
  rw [overCtx_emits_503 [] h (by intro t ht; exact absurd ht (List.not_mem_nil)),
      underCtx_passes [] h, pipeline_empty, build_ofResponse]
  exact fun heq => hstatus heq.symm

/-! ## Axiom audit -/

#print axioms admits_unlimited
#print axioms admits_at_cap
#print axioms defaultConnCap_admits_browserBurst
#print axioms retiredCap4_refused_browserBurst
#print axioms decodeWordD_encodeCap
#print axioms decodeCap_encodeCap
#print axioms cfgCtx_cap
#print axioms knob_moves_the_gate
#print axioms default_admits_browserBurst
#print axioms overCtx_over
#print axioms underCtx_under
#print axioms connStage_gate_build
#print axioms connStage_over_status
#print axioms connStage_pass
#print axioms connStage_changes_bytes

end Reactor.Stage.ConnLimit
