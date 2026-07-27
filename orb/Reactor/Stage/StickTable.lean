import Reactor.Pipeline
import StickTable
import Reactor.Stage.ConnLimit

/-!
# Reactor.Stage.StickTable — the keyed cross-request counter, as a pipeline stage

The `StickTable` base library proved the shared accounting substrate: a keyed
counter table (`bump`/`track`, `lookup`, `evict`) with the per-step correctness
lemmas — `bump_getCount_self` (a track raises exactly the tracked key's counter by
one), `lookup_expired` / `evict_removes_expired` (an entry past its TTL reads back
absent and is evicted), and `bump_Wf` / `evict_Wf` (the table stays a finite,
key-unique map). This is the counter behind per-source request aggregation and the
threshold limits (rate / connection caps) that read it.

This file promotes that substrate from a *proof-attachment* to a **byte-driver** in
the deployed serve fold. It is the SUBSTRATE stage the threshold gates compose on:
on the request phase it reconstructs the source's standing request count from the
attribute bag, and when that aggregated count has reached the configured threshold
it short-circuits with a `429 Too Many Requests` — the handler and every later stage
are skipped.

## The counting bound is the base library's, lifted

`countAfter n` is the table produced by `n` successive `track`s of one source key
from empty. `getCount_countAfter` proves its counter is EXACTLY `n` — a direct
induction on the base `StickTable.bump_getCount_self`, so the aggregated count the
gate decides on is the real stick-table counter, not a stub. Because the sans-IO
serve is one stateless call per request, `n` (the source's standing count) rides in
the attribute bag under `countKey`, and `ctxAdmits_substrate` is the statement that
deciding on that threaded number IS deciding on the substrate's counter.

## Both the COUNT and the LIMIT are threaded — neither is a constant

The gate used to decide `count < threshold` against a module constant `threshold = 16`,
on a `countOf` that read an attribute NOTHING wrote — so it was inert on every seam,
and would have been a 16-request-per-source cliff if it had ever bound. Both halves are
now inputs:

* `countOf c` — the source's in-window ARRIVAL COUNT, threaded by the host from the
  process-wide rate table (`SharedStanding::req_note_count`);
* `limitOf c` — the operator's `rate-limit`, threaded by the host from the same config
  the accept path reads.

Both ride the SINGLE positional attribute-bag codec (`ConnLimit.encodeCap` /
`ConnLimit.decodeWordD`), proven to round-trip for every `UInt64`
(`decodeWordD_encodeCap`) — one representation, one proof, shared with the connection
cap. The count is positional and not unary (which is how the connection count rides)
because an in-window arrival count is unbounded by the flood, and a unary reading would
allocate one cons per arrival on the request path.

The unconfigured reading of BOTH is `0`, and `admitsAt 0 _ = true`: a context that
predates the knob — every model context, the plain `ctxOfMetered` — has the gate OFF,
so nothing that predates the threading changes (`unlimited_by_default`).

The TTL bound is likewise the base library's: `stick_lookup_expired` and
`stick_evict_removes_expired` re-export `StickTable.lookup_expired` /
`evict_removes_expired` on a concrete over-TTL table — an idle entry reads back
absent and is evicted, so the table is bounded, not monotonically growing.

The byte effect is genuine:

* `stickStage_gate_build` — at/over the threshold, the built response IS the `429`;
* `stickStage_pass` — under the threshold, the stage is transparent;
* `stickStage_changes_bytes` — same handler, an over- and an under-threshold source
  emit different status bytes.
-/

namespace Reactor.Stage.StickTable

open Reactor.Pipeline
open Proto (Bytes)

/-! ## The keyed counter, driven from the base substrate -/

/-- The single source key the deployed stick stage aggregates on (one shard's view;
the cross-shard merge is the base library's named CR-2 obligation). -/
def srcKey : Nat := 0

/-- `countAfter n` — the stick table after `n` successive `track`s of `srcKey` from
empty, each at clock `0`. This is the source's live table reconstructed from its
standing request count. -/
def countAfter : Nat → _root_.StickTable.Table
  | 0     => []
  | n + 1 => _root_.StickTable.bump srcKey 0 (countAfter n)

/-- **The counting bound (lifted from the base substrate).** The aggregated counter
for `srcKey` after `n` tracks is EXACTLY `n` — a direct induction on the base
`bump_getCount_self`, so the gate decides on the real stick-table counter. -/
theorem getCount_countAfter (n : Nat) :
    _root_.StickTable.getCount srcKey (countAfter n) = n := by
  induction n with
  | zero => rfl
  | succ m ih =>
    show _root_.StickTable.getCount srcKey
      (_root_.StickTable.bump srcKey 0 (countAfter m)) = m + 1
    rw [_root_.StickTable.bump_getCount_self, ih]

/-- The reconstructed table stays a finite key-unique map (base `bump_Wf`). -/
theorem countAfter_Wf (n : Nat) : _root_.StickTable.Wf (countAfter n) := by
  induction n with
  | zero => exact _root_.StickTable.Wf_nil
  | succ m ih => exact _root_.StickTable.bump_Wf srcKey 0 ih

/-! ## The 429 rejection response -/

/-- Reason phrase for the rejection. -/
def reason429 : Bytes := "Too Many Requests".toUTF8.toList

/-- Body prose for the rejection. -/
def tooManyBody : Bytes := "aggregated request limit exceeded\n".toUTF8.toList

/-- The `429 Too Many Requests` response the gate answers with when the source's
aggregated count reaches the threshold — status `429`. -/
def resp429 : Response := error4xx 429 reason429 tooManyBody

/-! ## The threshold decision -/

/-- **THE admission decision, over the CONFIGURED limit.** A request from a source
with `count` arrivals already counted in the current window is admitted iff the limit
is disabled (`limit = 0`, unlimited) or the source is strictly below it. Total,
saturation-free, and `limit` is an INPUT — never a constant baked into the decision.

This is exactly the reference rule the accept path runs
(`SharedStanding::rate_note`: `limit == 0` ⇒ never refuse; otherwise refuse once the
post-increment count exceeds `limit`, i.e. once the PRIOR count has reached it). -/
def admitsAt (limit count : Nat) : Bool := limit == 0 || count < limit

/-- A disabled limit (`0`) admits any arrival rate — the unlimited path, and the
reading every context that predates the knob gets. -/
theorem admitsAt_unlimited (count : Nat) : admitsAt 0 count = true := by
  simp [admitsAt]

/-- Strictly under the limit ⇒ admitted. -/
theorem admitsAt_under {limit count : Nat} (hpos : 0 < limit) (h : count < limit) :
    admitsAt limit count = true := by
  simp only [admitsAt, Bool.or_eq_true, decide_eq_true_eq]
  exact Or.inr h

/-- Exactly at the limit ⇒ refused (the boundary is closed against admission — the
`limit`-th arrival is served, the `limit + 1`-th is not). -/
theorem admitsAt_at_limit {limit : Nat} (hpos : 0 < limit) : admitsAt limit limit = false := by
  simp only [admitsAt, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true']
  simp [Nat.ne_of_gt hpos, Nat.lt_irrefl]

/-- At or over the limit (with a live limit) ⇒ refused. -/
theorem admitsAt_over {limit count : Nat} (hpos : 0 < limit) (h : limit ≤ count) :
    admitsAt limit count = false := by
  have h0 : (limit == 0) = false := by simp [Nat.ne_of_gt hpos]
  have h1 : decide (count < limit) = false := by simp [Nat.not_lt.mpr h]
  simp only [admitsAt, h0, h1, Bool.or_false]

/-- **Monotone in the count.** More arrivals never help: if a heavier count is
admitted at a limit, so is a lighter one. The defining monotonicity of a counter
gate. -/
theorem admitsAt_antitone {limit count count' : Nat} (h : count ≤ count')
    (ha : admitsAt limit count' = true) : admitsAt limit count = true := by
  simp only [admitsAt, Bool.or_eq_true, decide_eq_true_eq] at ha ⊢
  exact ha.imp id (fun hlt => Nat.lt_of_le_of_lt h hlt)

/-- A witness limit (`16`) — NOT the deployed one. The deployed limit is whatever the
operator's `rate-limit` threads (`limitOf`, default `0` = off); this constant only
names a concrete live limit for the model-level statements in
`Reactor/StandingCounters.lean` and for the non-vacuity witnesses below. -/
def threshold : Nat := 16

/-- **The threshold decision** on an aggregated count, at the witness limit — the
shared `admitsAt` instantiated, not a second rule. -/
def admits (count : Nat) : Bool := admitsAt threshold count

/-- Under the threshold ⇒ admitted. -/
theorem admits_under {count : Nat} (h : count < threshold) : admits count = true :=
  admitsAt_under (by decide) h

/-- At/over the threshold ⇒ rejected. -/
theorem admits_over {count : Nat} (h : threshold ≤ count) : admits count = false :=
  admitsAt_over (by decide) h

/-! ## Reading the source's standing count off the context -/

/-- Attribute key holding the source's standing aggregated request count (its
byte-length = the count the stick substrate has recorded for this source). -/
def countKey : String := "stick-count"

/-- Look the value bytes up for a key in the attribute bag (`[]` if absent). -/
def lookupBytes (c : Ctx) (k : String) : Bytes :=
  match c.attrs.find? (fun p => p.1 == k) with
  | some p => p.2
  | none   => []

/-- The source's in-window ARRIVAL COUNT, decoded from the `countKey` attr through the
shared positional word codec. `0` when absent or malformed — a source the host threaded
nothing for, which with the likewise-`0` limit leaves the gate off. -/
def countOf (c : Ctx) : Nat := Reactor.Stage.ConnLimit.decodeWordD 0 (lookupBytes c countKey)

/-- Attribute key holding the OPERATOR's configured per-source arrival limit
(`rate-limit`), positional, exactly eight bytes. Written by the host from the same
config value the accept path's own gate reads, so the two gates are one number. -/
def limitKey : String := "stick-limit"

/-- **The configured per-source arrival limit carried by the context** — the operator's
`rate-limit` where the host threaded one, `0` (OFF) otherwise. `0` is the deliberate
unconfigured reading: it is the only value under which a context that predates this
threading keeps its behaviour exactly. -/
def limitOf (c : Ctx) : Nat := Reactor.Stage.ConnLimit.decodeWordD 0 (lookupBytes c limitKey)

/-- **The real gate decision on the context.** Admit iff the source's threaded
in-window arrival count is under the limit the CONTEXT CARRIES. Both are inputs. -/
def ctxAdmits (c : Ctx) : Bool := admitsAt (limitOf c) (countOf c)

/-- **The decision IS the stick substrate's counter.** Reconstructing the source's live
table (`countAfter (countOf c)`) and reading it through the REAL base `getCount` gives
back exactly the threaded count (`getCount_countAfter`), so deciding on the threaded
number is deciding on the substrate counter — the gate is the stick table's, evaluated
in `O(1)` instead of rebuilding an `n`-bump table on every request. -/
theorem ctxAdmits_substrate (c : Ctx) :
    ctxAdmits c
      = admitsAt (limitOf c) (_root_.StickTable.getCount srcKey (countAfter (countOf c))) := by
  unfold ctxAdmits; rw [getCount_countAfter]

/-- **Unconfigured ⇒ OFF.** A context carrying no `stick-limit` attribute reads limit
`0`, and the gate admits WHATEVER the count is — for every count, not for a sampled
one. This is the no-regression fact every pre-threading context (every model context,
the plain `ctxOfMetered`) relies on. -/
theorem unlimited_by_default {c : Ctx} (h : lookupBytes c limitKey = []) :
    ctxAdmits c = true := by
  have hl : limitOf c = 0 := by rw [limitOf, h]; rfl
  simp [ctxAdmits, hl, admitsAt]

/-! ## The stage -/

/-- **The stick-table threshold gate stage.** Request phase: reconstruct the source's
aggregated stick counter and, when it reaches the threshold, `.respond resp429`
(short-circuit); otherwise `.continue`. Response phase: transparent. -/
def stickStage : Stage where
  name := "stick-table"
  onRequest  := fun c => cond (ctxAdmits c) (.continue c) (.respond resp429)
  onResponse := fun _ b => b

/-- At/over the threshold, the gate short-circuits with the `429`. -/
theorem stickStage_onReq_respond (c : Ctx) (hover : ctxAdmits c = false) :
    stickStage.onRequest c = .respond resp429 := by
  simp only [stickStage, hover, cond]

/-- Under the threshold, the gate passes the context through. -/
theorem stickStage_onReq_continue (c : Ctx) (hunder : ctxAdmits c = true) :
    stickStage.onRequest c = .continue c := by
  simp only [stickStage, hunder, cond]

/-! ## The byte effect -/

/-- **Gate byte-effect.** At/over the threshold, the BUILT pipeline response — for
ANY tail and handler — is the `429`. -/
theorem stickStage_gate_build (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (hover : ctxAdmits c = false) :
    runPipeline (stickStage :: rest) h c = runResp rest c (ResponseBuilder.ofResponse resp429) :=
  pipeline_gate_short_circuits stickStage rest h c resp429 (stickStage_onReq_respond c hover)

/-- The over-threshold response's status byte is `429` — through a status-stable onion. -/
theorem stickStage_over_status (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (hover : ctxAdmits c = false) (hst : ∀ t ∈ rest, Stage.statusStable t) :
    ((runPipeline (stickStage :: rest) h c).build).status = 429 :=
  pipeline_gate_status stickStage rest h c resp429 (stickStage_onReq_respond c hover) hst

/-- **Pass-through byte-effect.** Under the threshold, the stage is transparent. -/
theorem stickStage_pass (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (hunder : ctxAdmits c = true) :
    runPipeline (stickStage :: rest) h c = runPipeline rest h c := by
  rw [pipeline_stage_effect stickStage rest h c c (stickStage_onReq_continue c hunder)]
  rfl

/-! ## TTL bound — re-exported from the base substrate (boundedness) -/

/-- A concrete stick table with one entry for `srcKey`, last-seen at clock `0`. -/
def idleTable : _root_.StickTable.Table := [(srcKey, ⟨3, 0⟩)]

/-- **TTL read bound (base `lookup_expired`).** With time-to-idle `5` and the clock
advanced to `10`, the entry (last-seen `0`) is past its TTL, so `lookup` reads it back
as absent — the table does not serve stale counters. -/
theorem stick_lookup_expired :
    _root_.StickTable.lookup srcKey 5 10 idleTable = none :=
  _root_.StickTable.lookup_expired (t := idleTable) (e := ⟨3, 0⟩) rfl (by decide)

/-- `idleTable` is a finite key-unique map. -/
theorem idleTable_wf : _root_.StickTable.Wf idleTable := by
  simp [_root_.StickTable.Wf, _root_.StickTable.keys, idleTable]

/-- **TTL evict bound (base `evict_removes_expired`).** The same idle entry is
removed by `evict`, so the table is bounded (idle sources are reclaimed), not
monotonically growing. -/
theorem stick_evict_removes_expired :
    _root_.StickTable.find srcKey (_root_.StickTable.evict 5 10 idleTable) = none :=
  _root_.StickTable.evict_removes_expired (t := idleTable) (e := ⟨3, 0⟩)
    idleTable_wf rfl (by decide)

/-! ## Concrete over- and under-threshold contexts (non-vacuity) -/

/-- A context carrying an explicit CONFIGURED limit and an explicit in-window arrival
count — the shape the host builds per request. -/
def cfgCtx (limit count : Nat) : Ctx :=
  { input := [], req := {},
    attrs := [(limitKey, Reactor.Stage.ConnLimit.encodeCap limit),
              (countKey, Reactor.Stage.ConnLimit.encodeCap count)] }

/-- The configured limit is read back off `cfgCtx` exactly (any limit the host can
cross). -/
theorem cfgCtx_limit {limit : Nat} (count : Nat) (h : limit < 2 ^ 64) :
    limitOf (cfgCtx limit count) = limit := by
  have hl : lookupBytes (cfgCtx limit count) limitKey
      = Reactor.Stage.ConnLimit.encodeCap limit := by
    simp [lookupBytes, cfgCtx, limitKey, countKey]
  rw [limitOf, hl, Reactor.Stage.ConnLimit.decodeWordD_encodeCap 0 h]

/-- The arrival count is read back off `cfgCtx` exactly (any count the host can
cross). -/
theorem cfgCtx_count (limit : Nat) {count : Nat} (h : count < 2 ^ 64) :
    countOf (cfgCtx limit count) = count := by
  have hl : lookupBytes (cfgCtx limit count) countKey
      = Reactor.Stage.ConnLimit.encodeCap count := by
    simp [lookupBytes, cfgCtx, limitKey, countKey]
  rw [countOf, hl, Reactor.Stage.ConnLimit.decodeWordD_encodeCap 0 h]

/-- **THE KNOB MOVES THE GATE.** At the SAME five in-window arrivals, a source under a
configured `rate-limit` of `4` is REFUSED and a source under a configured `16` is
ADMITTED — and a source under the unconfigured `0` is admitted at a MILLION arrivals.
The decision follows the configured value; nothing here is a constant. -/
theorem knob_moves_the_gate :
    ctxAdmits (cfgCtx 4 5) = false
    ∧ ctxAdmits (cfgCtx 16 5) = true
    ∧ ctxAdmits (cfgCtx 0 1000000) = true := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ctxAdmits, cfgCtx_limit _ (by decide), cfgCtx_count _ (by decide)]
    exact admitsAt_over (by decide) (by decide)
  · rw [ctxAdmits, cfgCtx_limit _ (by decide), cfgCtx_count _ (by decide)]
    exact admitsAt_under (by decide) (by decide)
  · rw [ctxAdmits, cfgCtx_limit _ (by decide)]
    exact admitsAt_unlimited _

/-- **The boundary is where the accept path puts it.** Under a configured limit of `n`,
the source whose PRIOR in-window count is `n - 1` is admitted (that is its `n`-th
arrival) and the one whose prior count is `n` is refused (its `n + 1`-th). Stated for
every live `n`, so the served-per-window bound is exactly `n`. -/
theorem boundary_at_limit {n : Nat} (hpos : 0 < n) (hn : n < 2 ^ 64) :
    ctxAdmits (cfgCtx n (n - 1)) = true ∧ ctxAdmits (cfgCtx n n) = false := by
  constructor
  · rw [ctxAdmits, cfgCtx_limit _ hn, cfgCtx_count _ (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hn)]
    exact admitsAt_under hpos (by omega)
  · rw [ctxAdmits, cfgCtx_limit _ hn, cfgCtx_count _ hn]
    exact admitsAt_at_limit hpos

/-- A source whose in-window arrival count has reached its CONFIGURED limit — over the
limit, so this request is refused. The witness carries an explicit configured limit, so
it exercises the CONFIGURED path rather than a module constant. -/
def overCtx : Ctx := cfgCtx threshold threshold

/-- A fresh source (no threaded count, no configured limit) — the gate is off, admitted. -/
def underCtx : Ctx := { input := [], req := {}, attrs := [] }

/-- `overCtx` is at its configured limit — the real rule rejects it. -/
theorem overCtx_over : ctxAdmits overCtx = false := by
  rw [overCtx, ctxAdmits, cfgCtx_limit _ (by decide), cfgCtx_count _ (by decide)]
  exact admitsAt_at_limit (by decide)

/-- `underCtx` carries no limit — the gate is off and admits. -/
theorem underCtx_under : ctxAdmits underCtx = true :=
  unlimited_by_default (by simp [lookupBytes, underCtx])

/-- An over-threshold source emits a `429` (through a status-stable inner onion). -/
theorem overCtx_emits_429 (rest : List Stage) (h : Ctx → Response)
    (hst : ∀ t ∈ rest, Stage.statusStable t) :
    ((runPipeline (stickStage :: rest) h overCtx).build).status = 429 :=
  stickStage_over_status rest h overCtx overCtx_over hst

/-- An under-threshold source passes through to the tail unchanged. -/
theorem underCtx_passes (rest : List Stage) (h : Ctx → Response) :
    runPipeline (stickStage :: rest) h underCtx = runPipeline rest h underCtx :=
  stickStage_pass rest h underCtx underCtx_under

/-- **The gate genuinely drives the wire.** Same handler and tail, an over-threshold
and an under-threshold source emit different status bytes. -/
theorem stickStage_changes_bytes (h : Ctx → Response)
    (hstatus : (h underCtx).status ≠ 429) :
    ((runPipeline [stickStage] h overCtx).build).status
      ≠ ((runPipeline [stickStage] h underCtx).build).status := by
  rw [overCtx_emits_429 [] h (by intro t ht; exact absurd ht (List.not_mem_nil)),
      underCtx_passes [] h, pipeline_empty, build_ofResponse]
  exact fun heq => hstatus heq.symm

/-! ## Axiom audit -/

#print axioms getCount_countAfter
#print axioms countAfter_Wf
#print axioms stick_lookup_expired
#print axioms stick_evict_removes_expired
#print axioms admitsAt_unlimited
#print axioms admitsAt_at_limit
#print axioms admitsAt_antitone
#print axioms cfgCtx_limit
#print axioms cfgCtx_count
#print axioms knob_moves_the_gate
#print axioms boundary_at_limit
#print axioms unlimited_by_default
#print axioms ctxAdmits_substrate
#print axioms overCtx_over
#print axioms underCtx_under
#print axioms stickStage_gate_build
#print axioms stickStage_pass
#print axioms stickStage_changes_bytes

end Reactor.Stage.StickTable
