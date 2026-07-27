import Reactor.Pipeline
import Reactor.Stage.FramingValidation

/-!
# Reactor.Stage.MaxForwards — RFC 9110 §7.6.2 `Max-Forwards` (hop-limited
`OPTIONS`/`TRACE`: terminate at zero, decrement when forwarding)

RFC 9110 §7.6.2: `Max-Forwards` bounds how many hops an `OPTIONS` or `TRACE`
request may be forwarded. A recipient of `Max-Forwards: 0` **MUST NOT forward
the request; instead, the recipient MUST respond as the final recipient**. A
forwarding recipient of a greater value **MUST** send the decremented value
onward. §9.3.7 (`OPTIONS`): the final recipient answers about its own
communication options — a successful `2xx` whose `Allow` header (§10.2.1) lists
the methods the target surface supports.

## Ground truth — the deployed serve ignores Max-Forwards entirely

The deployed fold routes method-blind on the target path: `OPTIONS /health` with
`Max-Forwards: 0` is answered with the `/health` GET representation, and the
hop-count header is neither honored (no final-recipient answer) nor decremented
for any forwarding arm. Both §7.6.2 MUSTs are unimplemented. This stage supplies
them as a request-phase `Stage`.

## Behaviour

* `OPTIONS` with `Max-Forwards: 0` → **terminate here**: `204 No Content` +
  `Allow: GET, HEAD, POST, OPTIONS` (the deployed surface's method set). The
  request never reaches the routing fold.
* `OPTIONS`/`TRACE` with `Max-Forwards: n` (n > 0, decimal) → pass through with
  the FIRST `Max-Forwards` value rewritten to `n − 1` in the request context, so
  any downstream forwarding consumer sends the decremented hop count.
* Any other request (no `Max-Forwards`, unparsable value, or another method —
  §7.6.2 scopes the field to `OPTIONS`/`TRACE`) → pass through with the context
  UNTOUCHED.

## What is proved (pure-kernel; `#print axioms` ⊆ {propext, Quot.sound})

* `mfStage_gates` — `OPTIONS` + `Max-Forwards: 0` `.respond`s the `Allow`-carrying
  `204` (the §7.6.2 final-recipient MUST), and `mfStage_gate_status` carries that
  `204` through any status-stable inner onion.
* `mfStage_passthrough` — a non-`OPTIONS`/`TRACE` request `.continue`s with the
  context UNCHANGED (byte-transparent off the scoped methods).
* `mfStage_forwards_decremented` — a non-zero-`Max-Forwards` request `.continue`s
  via `mfContinueCtx`; `decMFHeaders_decrements` pins the rewrite: the first
  `Max-Forwards: n+1` becomes exactly `renderMF n`, the rest of the head untouched.
* `decMFHeaders_no_mf_id` — no `Max-Forwards` field ⇒ the rewrite is the identity.
* `parseMF_renderMF_le255` — parse/render round-trip over the full deployed hop
  range (`∀ n < 256`, kernel-decided), grounding the decrement arithmetic.
* `mfStage_statusStable` — the response phase is transparent (safe to braid).
* Concrete witnesses: `witness_gates` (`OPTIONS * Max-Forwards: 0` ⇒ the `204`),
  `witness_decrements` (`Max-Forwards: 3` rewritten to `2`), `witness_get_passes`
  (a plain GET unchanged) — all `by decide` on explicit ASCII bytes.

Deployment: wired into the deployed default fold by `Reactor.DeployPlus4`
(`deployStagesPlus4`). Residuals (named): the deployed route table has no
forwarding arm that CONSUMES the decremented value today (the rewrite is proven
and wired, its consumer is the proxy fold's future hop); `TRACE` termination
(the §9.3.8 `message/http` echo of the received request) is NOT implemented —
`TRACE` passes through method-blind exactly as before this stage.
-/

namespace Reactor.Stage.MaxForwards

open Reactor.Pipeline
open Proto (Bytes Request)
open Reactor.Stage.FramingValidation (lowerBytes trimOWS)

/-! ## Tokens (explicit ASCII so every decision reduces in the kernel) -/

/-- `max-forwards` (lowercase). -/
def mfNameLower : Bytes :=
  [109, 97, 120, 45, 102, 111, 114, 119, 97, 114, 100, 115]

/-- `OPTIONS`. -/
def mOPTIONS : Bytes := [79, 80, 84, 73, 79, 78, 83]

/-- `TRACE`. -/
def mTRACE : Bytes := [84, 82, 65, 67, 69]

/-- Is the request method `OPTIONS`? -/
def isOPTIONS (req : Request) : Bool := req.method == mOPTIONS

/-- Is the request method `TRACE`? -/
def isTRACE (req : Request) : Bool := req.method == mTRACE

/-! ## Decimal hop-count parse / render -/

/-- One ASCII digit's value. -/
def digitVal (b : UInt8) : Option Nat :=
  if 48 ≤ b && b ≤ 57 then some (b.toNat - 48) else none

/-- Accumulate a decimal number; any non-digit fails the parse. -/
def parseNatAux : Bytes → Nat → Option Nat
  | [], acc => some acc
  | b :: bs, acc =>
    match digitVal b with
    | some d => parseNatAux bs (acc * 10 + d)
    | none => none

/-- Parse a (non-empty, all-digit) decimal hop count. -/
def parseMF : Bytes → Option Nat
  | [] => none
  | bs => parseNatAux bs 0

/-- One decimal digit's ASCII byte (of `n`'s low digit). -/
def renderDigit (n : Nat) : UInt8 := UInt8.ofNat (48 + n % 10)

/-- Render a positive number's digits, MSD-first (accumulator carries the
already-rendered lower digits). STRUCTURAL on a fuel bound (`fuel ≥ n` suffices —
`n/10 < n` strictly shrinks), so the kernel reduces it — no well-founded fix. -/
def renderAux : Nat → Nat → Bytes → Bytes
  | _, 0, acc => acc
  | 0, _, acc => acc
  | fuel + 1, n + 1, acc => renderAux fuel ((n + 1) / 10) (renderDigit (n + 1) :: acc)

/-- Render a decimal hop count (`0` ⇒ `"0"`). -/
def renderMF (n : Nat) : Bytes := if n = 0 then [48] else renderAux n n []

set_option maxRecDepth 4096 in
/-- **Round-trip over the deployed hop range.** For every hop count below 256 the
render parses back exactly (kernel-decided — 256 closed evaluations; `Max-Forwards`
hop chains beyond 255 do not occur on any deployed path). -/
theorem parseMF_renderMF_le255 :
    (List.range 256).all (fun n => parseMF (renderMF n) == some n) = true := by
  decide

/-! ## The Max-Forwards field of a request -/

/-- The FIRST `Max-Forwards` header (case-insensitive), if any. -/
def mfEntry? (req : Request) : Option (Bytes × Bytes) :=
  req.headers.find? (fun kv => lowerBytes kv.1 == mfNameLower)

/-- Its `OWS`-trimmed value. -/
def mfValue? (req : Request) : Option Bytes := (mfEntry? req).map (fun kv => trimOWS kv.2)

/-- **The termination test.** `Max-Forwards` present and parsing to exactly `0`. -/
def mfZero (req : Request) : Bool :=
  match mfValue? req with
  | some v => parseMF v == some 0
  | none => false

/-- **The decrement rewrite.** The FIRST `Max-Forwards: n+1` becomes `n`; a zero,
absent, or unparsable value leaves the head untouched; later fields untouched. -/
def decMFHeaders : List (Bytes × Bytes) → List (Bytes × Bytes)
  | [] => []
  | (nm, v) :: rest =>
    if lowerBytes nm == mfNameLower then
      match parseMF (trimOWS v) with
      | some (k + 1) => (nm, renderMF k) :: rest
      | _ => (nm, v) :: rest
    else (nm, v) :: decMFHeaders rest

/-- **Identity off the field.** A head with no `Max-Forwards` is returned UNCHANGED. -/
theorem decMFHeaders_no_mf_id (hs : List (Bytes × Bytes))
    (h : hs.all (fun kv => !(lowerBytes kv.1 == mfNameLower)) = true) :
    decMFHeaders hs = hs := by
  induction hs with
  | nil => rfl
  | cons kv rest ih =>
    rw [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨hkv, hrest⟩ := h
    have hne : (lowerBytes kv.1 == mfNameLower) = false := by
      cases hb : lowerBytes kv.1 == mfNameLower
      · rfl
      · rw [hb] at hkv; exact absurd hkv (by decide)
    show decMFHeaders ((kv.1, kv.2) :: rest) = _
    unfold decMFHeaders
    rw [hne]
    simp only [Bool.false_eq_true, if_false]
    rw [ih hrest]

/-- **The decrement, pinned.** When the head's first field IS `Max-Forwards` and its
value parses to `n+1`, the rewrite yields exactly `renderMF n` there and touches
nothing else. -/
theorem decMFHeaders_decrements (nm v : Bytes) (rest : List (Bytes × Bytes)) (k : Nat)
    (hn : (lowerBytes nm == mfNameLower) = true)
    (hp : parseMF (trimOWS v) = some (k + 1)) :
    decMFHeaders ((nm, v) :: rest) = (nm, renderMF k) :: rest := by
  unfold decMFHeaders
  rw [hn, hp]
  rfl

/-! ## The final-recipient answer (RFC 9110 §7.6.2 + §9.3.7 + §10.2.1) -/

/-- The `Allow` field name. -/
def allowName : Bytes := [65, 108, 108, 111, 119]

/-- The deployed surface's method set: `GET, HEAD, POST, OPTIONS`. -/
def allowVal : Bytes :=
  [71, 69, 84, 44, 32, 72, 69, 65, 68, 44, 32, 80, 79, 83, 84, 44, 32,
   79, 80, 84, 73, 79, 78, 83]

/-- `204 No Content` + `Allow` — this hop's own communication options (§9.3.7),
the §10.2.1 method advertisement carried. -/
def optionsResp : Reactor.Response :=
  { status := 204
    reason := [78, 111, 32, 67, 111, 110, 116, 101, 110, 116]
    headers := [(allowName, allowVal)]
    body := [] }

theorem optionsResp_status : optionsResp.status = 204 := rfl

theorem optionsResp_has_allow : (allowName, allowVal) ∈ optionsResp.headers := by
  exact List.mem_singleton.mpr rfl

/-! ## The stage -/

/-- The `.continue` context: `OPTIONS`/`TRACE` get the decremented hop count
(§7.6.2 scopes the field to those methods); everything else passes untouched. -/
def mfContinueCtx (c : Ctx) : Ctx :=
  if isOPTIONS c.req || isTRACE c.req then
    { c with req := { c.req with headers := decMFHeaders c.req.headers } }
  else c

/-- **The `Max-Forwards` stage.** Request phase: `OPTIONS` at hop-limit zero is
answered HERE (`204` + `Allow`); a forwardable `OPTIONS`/`TRACE` continues with
the decremented hop count; everything else continues untouched. Response phase
transparent. -/
def mfStage : Stage where
  name := "max-forwards"
  onRequest := fun c =>
    if isOPTIONS c.req && mfZero c.req then .respond optionsResp
    else .continue (mfContinueCtx c)
  onResponse := fun _ b => b

/-- The response phase is transparent — safe under any status-stable onion. -/
theorem mfStage_statusStable : mfStage.statusStable := fun _ _ => rfl

/-! ## Gate theorems -/

/-- **§7.6.2 MUST (terminate).** `OPTIONS` + `Max-Forwards: 0` `.respond`s the
`Allow`-carrying `204` — the request is answered by THIS recipient. -/
theorem mfStage_gates (c : Ctx) (hopt : isOPTIONS c.req = true)
    (hz : mfZero c.req = true) :
    mfStage.onRequest c = .respond optionsResp := by
  show (if isOPTIONS c.req && mfZero c.req then StageStep.respond optionsResp
        else StageStep.continue (mfContinueCtx c)) = _
  rw [hopt, hz]
  rfl

/-- **Byte-transparent off the scoped methods.** A non-`OPTIONS`/`TRACE` request
`.continue`s with the context UNCHANGED. -/
theorem mfStage_passthrough (c : Ctx)
    (hmeth : (isOPTIONS c.req || isTRACE c.req) = false) :
    mfStage.onRequest c = .continue c := by
  have hopt : isOPTIONS c.req = false := by
    cases hb : isOPTIONS c.req
    · rfl
    · rw [hb, Bool.true_or] at hmeth; exact absurd hmeth (by decide)
  show (if isOPTIONS c.req && mfZero c.req then StageStep.respond optionsResp
        else StageStep.continue (mfContinueCtx c)) = _
  rw [hopt, Bool.false_and, if_neg (by decide)]
  unfold mfContinueCtx
  rw [hmeth, if_neg (by decide)]

/-- **§7.6.2 MUST (decrement).** A request whose `Max-Forwards` is NOT zero
`.continue`s via `mfContinueCtx` — on the scoped methods, the decremented head
(`decMFHeaders_decrements` pins the value). -/
theorem mfStage_forwards_decremented (c : Ctx) (hz : mfZero c.req = false) :
    mfStage.onRequest c = .continue (mfContinueCtx c) := by
  show (if isOPTIONS c.req && mfZero c.req then StageStep.respond optionsResp
        else StageStep.continue (mfContinueCtx c)) = _
  rw [hz, Bool.and_false, if_neg (by decide)]

/-- The `204` survives any status-stable inner onion — the gate composition. -/
theorem mfStage_gate_status (c : Ctx) (rest : List Stage) (handler : Ctx → Response)
    (hopt : isOPTIONS c.req = true) (hz : mfZero c.req = true)
    (hst : ∀ t ∈ rest, Stage.statusStable t) :
    ((runPipeline (mfStage :: rest) handler c).build).status = 204 := by
  have := pipeline_gate_status mfStage rest handler c optionsResp
    (mfStage_gates c hopt hz) hst
  rw [this]
  rfl

/-- A terminated request never reaches the handler. -/
theorem mfStage_gate_skips_handler (c : Ctx) (rest : List Stage)
    (handler handler' : Ctx → Response)
    (hopt : isOPTIONS c.req = true) (hz : mfZero c.req = true) :
    runPipeline (mfStage :: rest) handler c
      = runPipeline (mfStage :: rest) handler' c :=
  pipeline_gate_ignores_handler mfStage rest handler handler' c optionsResp
    (mfStage_gates c hopt hz)

/-! ## Concrete non-vacuity witnesses (evaluate on real bytes) -/

/-- `Host` field name. -/
def hostName : Bytes := [72, 111, 115, 116]
/-- `Max-Forwards` as sent on the wire (mixed case). -/
def mfNameWire : Bytes := [77, 97, 120, 45, 70, 111, 114, 119, 97, 114, 100, 115]
/-- `GET`. -/
def mGET : Bytes := [71, 69, 84]
/-- `/health`. -/
def hpath : Bytes := [47, 104, 101, 97, 108, 116, 104]
/-- `HTTP/1.1`. -/
def v11 : Bytes := [72, 84, 84, 80, 47, 49, 46, 49]

/-- **Terminate witness.** `OPTIONS /health` with `Max-Forwards: 0`. -/
def optionsMf0Ctx : Ctx :=
  { input := [], req :=
      { method := mOPTIONS, target := hpath, version := v11
        headers := [(hostName, [120]), (mfNameWire, [48])] }
    attrs := [] }

theorem witness_gates : mfStage.onRequest optionsMf0Ctx = .respond optionsResp :=
  mfStage_gates _ (by decide) (by decide)

/-- **Decrement witness.** `OPTIONS /health` with `Max-Forwards: 3`. -/
def optionsMf3Ctx : Ctx :=
  { input := [], req :=
      { method := mOPTIONS, target := hpath, version := v11
        headers := [(hostName, [120]), (mfNameWire, [51])] }
    attrs := [] }

theorem witness_decrements :
    (mfContinueCtx optionsMf3Ctx).req.headers
      = [(hostName, [120]), (mfNameWire, [50])] := by decide

/-- **Pass witness.** A plain `GET` (even carrying `Max-Forwards: 0`) is
untouched — §7.6.2 scopes the field to `OPTIONS`/`TRACE`. -/
def getMf0Ctx : Ctx :=
  { input := [], req :=
      { method := mGET, target := hpath, version := v11
        headers := [(hostName, [120]), (mfNameWire, [48])] }
    attrs := [] }

theorem witness_get_passes : mfStage.onRequest getMf0Ctx = .continue getMf0Ctx :=
  mfStage_passthrough _ (by decide)

#print axioms Reactor.Stage.MaxForwards.parseMF_renderMF_le255
#print axioms Reactor.Stage.MaxForwards.decMFHeaders_no_mf_id
#print axioms Reactor.Stage.MaxForwards.decMFHeaders_decrements
#print axioms Reactor.Stage.MaxForwards.mfStage_gates
#print axioms Reactor.Stage.MaxForwards.mfStage_passthrough
#print axioms Reactor.Stage.MaxForwards.mfStage_forwards_decremented
#print axioms Reactor.Stage.MaxForwards.mfStage_gate_status
#print axioms Reactor.Stage.MaxForwards.mfStage_gate_skips_handler
#print axioms Reactor.Stage.MaxForwards.mfStage_statusStable
#print axioms Reactor.Stage.MaxForwards.witness_gates
#print axioms Reactor.Stage.MaxForwards.witness_decrements
#print axioms Reactor.Stage.MaxForwards.witness_get_passes

end Reactor.Stage.MaxForwards
