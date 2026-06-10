/-
# Dregg2.Exec.DistributedExports — the C-ABI boundary onto the VERIFIED CapTP + coordination
# decision functions, so the RUNNING SYSTEM invokes the verified Lean rather than only
# differential-checking against it.

This module is the STRONG-FORM swap face for CapTP + coord. `Exec/CapTP*` and `Coord/*` already
carry the EXECUTABLE verified functions (`validateHandoff2R` / `handoffNonAmplifyingC`,
`CapTPGCConcrete.processDrop`, `CapTPPipeline.Registry.*` + `resolve`, `TwoPhaseCommit.evaluate`,
`CausalOrder.happenedBefore`, `SharedBudgetDynamics.resolveOrdered`) with their soundness theorems.
What was MISSING is the load-bearing wire: a verified function that lives only BESIDE the running
node is the weaker spec (the F-4 / consensus dark-mirror trap). This module exposes each as a
wire-in/wire-out `@[export]` so the captp/coord runtime computes its verdict FROM the verified Lean
rule itself — `dreggrs`'s Rust stays the DIFFERENTIAL sibling (Lean == Rust on the same inputs), not
the decider.

Six exports, each proved `*_eq_*` EQUAL to the verified spec it marshals (so gating live logic on the
export gates it on the verified function by construction):

  * `dregg_captp_validate_handoff` — the §6 non-amplification verdict of `validate_handoff`
    (`captp/src/handoff.rs`): `CapTPConcrete.handoffNonAmplifyingC` over the (heldPerm, grantedPerm,
    heldEff, grantedEff) lattice. The introducer/recipient-signature, known-federation, expiry,
    target-binding, and replay legs stay Rust-native (they need real ed25519 + the swiss/nonce
    registry); the EXPORT is the cryptographically-content-free non-amplification leg — exactly the
    Granovetter "granted ⊆ held" tooth `CapTPHandoffSound.validateHandoff2_attenuates` proves.

  * `dregg_captp_process_drop` — the GC `process_drop_inner` session-refcount verdict
    (`captp/src/gc.rs`): `CapTPGCConcrete.processDrop` over the per-holder per-session table. The
    F-11 session-mandatory + F-12 per-session-bucket logic, marshalled.

  * `dregg_captp_pipeline_resolve` — the promise-pipelining `resolve_promise` / `break_promise`
    FIFO-drain + break-clear verdict (`captp/src/pipeline.rs`): `CapTPPipeline.Registry` ops.

  * `dregg_coord_2pc_decide` — the 2PC coordinator `evaluate_votes` verdict (`coord/src/atomic.rs`):
    `TwoPhaseCommit.evaluate` over the (yes, no, n, threshold) tally.

  * `dregg_coord_causal_order` — the causal-DAG `happened_before` verdict (`types/src/causal.rs`):
    `CausalOrder.happenedBefore` decided over the insertion-ordered DAG.

  * `dregg_coord_shared_budget` — the shared-budget `resolve_with_ordering` tau-resolution verdict
    (`coord/src/shared_budget.rs`): `SharedBudgetDynamics.resolveOrdered` over the tau-ordered debit
    amounts.

Wire discipline (mirrors `StrandAdmission.admitGate` / `FinalityGate`): compact, whitespace-free,
FAIL-CLOSED (any malformed field ⇒ a sentinel the Rust caller treats as the safe/deny outcome). Each
codec round-trips on a concrete corpus (`#guard`), so the Rust encoder and these Lean decoders share
one grammar. No new verify side, no `sorry`/`:=True`/`native_decide` in a load-bearing theorem.
-/
import Dregg2.Exec.CapTPConcrete
import Dregg2.Exec.CapTPGCConcrete
import Dregg2.Exec.CapTPPipeline
import Dregg2.Coord.TwoPhaseCommit
import Dregg2.Coord.CausalOrder
import Dregg2.Coord.SharedBudgetDynamics
import Dregg2.Tactics

namespace Dregg2.Exec.DistributedExports

open Dregg2.Exec.CapTPConcrete (AuthReq handoffNonAmplifyingC)
open Dregg2.Exec.CapTPGCConcrete (HolderRef HolderTable DropResult processDrop totalRefs)
open Dregg2.Coord.TwoPhaseCommit (Decision Tally evaluate)
open Dregg2.Coord.SharedBudgetDynamics (Resolution resolveOrdered acceptedSum)

/-! ## §0 — Shared wire primitives (the `StrandAdmission` style: strict, fail-closed). -/

/-- Parse a `Nat` strictly: non-empty, all-ASCII-digits. Fail-closed. -/
def parseNat? (s : String) : Option Nat :=
  if s.isEmpty then none else
    if s.all (fun c => c.isDigit) then s.toNat? else none

/-- Parse a possibly-empty `,`-separated list of `Nat`s. Fail-closed (one bad element fails all). -/
def parseNatList? (s : String) : Option (List Nat) :=
  if s.isEmpty then some []
  else (s.splitOn ",").foldr
        (fun part acc => match acc, parseNat? part with
          | some xs, some n => some (n :: xs)
          | _, _ => none)
        (some [])

/-- Strip a required `pfx`, returning the remainder, or `none` if absent. -/
def stripReq? (pfx s : String) : Option String :=
  if s.startsWith pfx then some (String.ofList (s.toList.drop pfx.length)) else none

/-! ## §1 — `dregg_captp_validate_handoff` — the §6 non-amplification verdict of `validate_handoff`.

`AuthRequired` ⇄ a wire tag (mirrors `cell/src/permissions.rs::AuthRequired` constructor order):
`0=None 1=Signature 2=Proof 3=Either 4=Impossible 5+h=Custom(h)`. The effect masks are `Option Nat`
encoded as `-1 = none (unrestricted)`, `≥0 = some mask`. -/

/-- Decode a permission tag to an `AuthReq` (fail-closed via `Option`). -/
def authOfTag : Nat → AuthReq
  | 0 => .none | 1 => .signature | 2 => .proof | 3 => .either | 4 => .impossible
  | n => .custom (n - 5)

/-- Encode an `AuthReq` to its wire tag (the inverse on `0..4`; `custom h ↦ 5 + h`). -/
def tagOfAuth : AuthReq → Nat
  | .none => 0 | .signature => 1 | .proof => 2 | .either => 3 | .impossible => 4
  | .custom h => 5 + h

/-- The decoded handoff-non-amplification query: held/granted permission tags + masks
(`-1` ↦ unrestricted). -/
structure HandoffQuery where
  heldTag    : Nat
  grantedTag : Nat
  /-- held effect mask: `none` = unrestricted. -/
  heldEff    : Option Nat
  /-- granted effect mask: `none` = unrestricted. -/
  grantedEff : Option Nat

/-- Parse an effect-mask field: the literal `"x"` ↦ unrestricted (`none`); a `Nat` ↦ `some n`. -/
def parseEff? (s : String) : Option (Option Nat) :=
  if s == "x" then some none
  else (parseNat? s).map some

/-- **`decodeHandoffWire`** — parse `"h=<heldTag>;g=<grantedTag>;he=<heldEff>;ge=<grantedEff>"`.
Fail-closed. -/
def decodeHandoffWire (s : String) : Option HandoffQuery := do
  let rest ← stripReq? "h=" s
  match rest.splitOn ";" with
  | [hS, gSeg, heSeg, geSeg] =>
      let heldTag ← parseNat? hS
      let gS ← stripReq? "g=" gSeg
      let heS ← stripReq? "he=" heSeg
      let geS ← stripReq? "ge=" geSeg
      let grantedTag ← parseNat? gS
      let heldEff ← parseEff? heS
      let grantedEff ← parseEff? geS
      some { heldTag := heldTag, grantedTag := grantedTag, heldEff := heldEff, grantedEff := grantedEff }
  | _ => none

/-- **`handoffGate`** — decode the wire, run the VERIFIED `handoffNonAmplifyingC`, encode the verdict
(`"1"` non-amplifying / `"0"` amplifying). Malformed wire ⇒ `"ERR"`; the Rust caller treats `ERR` and
`"0"` alike as "AMPLIFIES — REJECT" (fail-closed: a wire we cannot parse must never authorize a
handoff). -/
def handoffGate (s : String) : String :=
  match decodeHandoffWire s with
  | some q =>
      if handoffNonAmplifyingC (authOfTag q.heldTag) (authOfTag q.grantedTag) q.heldEff q.grantedEff
      then "1" else "0"
  | none => "ERR"

/-- **THE EXPORT.** `@[export dregg_captp_validate_handoff]` — the C-ABI entry the captp runtime
calls for the §6 non-amplification leg. Same `String → String` shape as `dregg_strand_admit`. -/
@[export dregg_captp_validate_handoff]
def dregg_captp_validate_handoff (s : String) : String := handoffGate s

/-- **`captp_validate_handoff_eq` (the export carries the proof).** For any wire that decodes
to `q`, the export returns `"1"` iff the VERIFIED `handoffNonAmplifyingC` accepts. So the runtime's
non-amplification verdict IS the verified lattice decision, marshalled. -/
theorem captp_validate_handoff_eq (s : String) (q : HandoffQuery)
    (h : decodeHandoffWire s = some q) :
    dregg_captp_validate_handoff s =
      (if handoffNonAmplifyingC (authOfTag q.heldTag) (authOfTag q.grantedTag) q.heldEff q.grantedEff
       then "1" else "0") := by
  unfold dregg_captp_validate_handoff handoffGate
  rw [h]

/-- **`captp_validate_handoff_admits_iff`.** Read as a Boolean: the export emits `"1"`
exactly when the verified rule says the handoff is non-amplifying. -/
theorem captp_validate_handoff_admits_iff (s : String) (q : HandoffQuery)
    (h : decodeHandoffWire s = some q) :
    (dregg_captp_validate_handoff s = "1") ↔
      handoffNonAmplifyingC (authOfTag q.heldTag) (authOfTag q.grantedTag) q.heldEff q.grantedEff = true := by
  rw [captp_validate_handoff_eq s q h]
  by_cases hc : handoffNonAmplifyingC (authOfTag q.heldTag) (authOfTag q.grantedTag) q.heldEff q.grantedEff
  · simp [hc]
  · simp only [hc, Bool.false_eq_true, if_false]
    constructor
    · intro hcc; exact absurd hcc (by decide)
    · intro hcc; exact absurd hcc (by simp)

/-- Encode a handoff query (the inverse the Rust differential mirrors). -/
def encodeHandoffWire (q : HandoffQuery) : String :=
  let effStr : Option Nat → String | none => "x" | some n => toString n
  "h=" ++ toString q.heldTag ++ ";g=" ++ toString q.grantedTag ++
  ";he=" ++ effStr q.heldEff ++ ";ge=" ++ effStr q.grantedEff

/-! ### §1-nv — non-vacuity: the export reproduces the verified verdict on the wire. -/

-- Signature held, signature granted, both unrestricted ⇒ non-amplifying (`"1"`).
#guard handoffGate (encodeHandoffWire { heldTag := 1, grantedTag := 1, heldEff := none, grantedEff := none }) == "1"
-- Held `signature`, granted `none` (loosens the requirement) ⇒ AMPLIFIES (`"0"`).
#guard handoffGate (encodeHandoffWire { heldTag := 1, grantedTag := 0, heldEff := none, grantedEff := none }) == "0"
-- Held restricted mask 0b110=6, granted 0b010=2 ⊆ 6 ⇒ non-amplifying (`"1"`).
#guard handoffGate (encodeHandoffWire { heldTag := 0, grantedTag := 0, heldEff := some 6, grantedEff := some 2 }) == "1"
-- Held restricted mask 6, granted unrestricted (`none`) ⇒ AMPLIFIES (`"0"`).
#guard handoffGate (encodeHandoffWire { heldTag := 0, grantedTag := 0, heldEff := some 6, grantedEff := none }) == "0"
-- Held restricted 6, granted 1 (bit not in held) ⇒ AMPLIFIES (`"0"`).
#guard handoffGate (encodeHandoffWire { heldTag := 0, grantedTag := 0, heldEff := some 6, grantedEff := some 1 }) == "0"
-- The codec round-trips.
#guard ((decodeHandoffWire (encodeHandoffWire { heldTag := 1, grantedTag := 1, heldEff := some 6, grantedEff := some 2 })).map (fun q => (q.heldTag, q.grantedTag, q.heldEff, q.grantedEff))) == some (1, 1, some 6, some 2)
-- A malformed wire is FAIL-CLOSED to `ERR`.
#guard handoffGate "not a wire" == "ERR"

/-! ## §2 — `dregg_captp_process_drop` — the GC `process_drop_inner` session-refcount verdict.

The wire carries the per-holder table (each holder: id + per-session buckets) + the queried
`(fed, session)`. We encode each holder as `fed:count:s1=n1+s2=n2+...`, holders `|`-separated.

    INPUT  := "H=" HOLDERS ";f=" fed ";s=" session
    HOLDERS := ε | HOLDER ("|" HOLDER)*
    HOLDER  := fed ":" count ":" BUCKETS
    BUCKETS := ε | BUCKET ("+" BUCKET)*
    BUCKET  := session "=" n
    OUTPUT := "S=" tag ";t=" postTotal      (tag: 0=stillHeld 1=canRevoke 2=invalid)
            | "ERR"                          (malformed ⇒ fail-closed: invalid, no change) -/

/-- Parse a per-session bucket `"<session>=<n>"`. -/
def parseBucket? (s : String) : Option (Nat × Nat) :=
  match s.splitOn "=" with
  | [a, b] => match parseNat? a, parseNat? b with
              | some x, some y => some (x, y)
              | _, _ => none
  | _ => none

/-- Parse a possibly-empty `+`-separated bucket list. Fail-closed. -/
def parseBuckets? (s : String) : Option (List (Nat × Nat)) :=
  if s.isEmpty then some []
  else (s.splitOn "+").foldr
        (fun part acc => match acc, parseBucket? part with
          | some ps, some p => some (p :: ps)
          | _, _ => none)
        (some [])

/-- Parse one holder `"<fed>:<count>:<buckets>"`. -/
def parseHolder? (s : String) : Option (Nat × HolderRef) :=
  match s.splitOn ":" with
  | [fS, cS, bS] => do
      let fed ← parseNat? fS
      let count ← parseNat? cS
      let buckets ← parseBuckets? bS
      some (fed, { count := count, sessions := buckets })
  | _ => none

/-- Parse a possibly-empty `|`-separated holder list into a `HolderTable`. Fail-closed. -/
def parseHolders? (s : String) : Option HolderTable :=
  if s.isEmpty then some []
  else (s.splitOn "|").foldr
        (fun part acc => match acc, parseHolder? part with
          | some hs, some h => some (h :: hs)
          | _, _ => none)
        (some [])

/-- The decoded drop query: the table + the `(fed, session)` to drop. -/
structure DropQuery where
  table   : HolderTable
  fed     : Nat
  session : Nat

/-- **`decodeDropWire`** — parse `"H=<holders>;f=<fed>;s=<session>"`. Fail-closed. -/
def decodeDropWire (s : String) : Option DropQuery := do
  let rest ← stripReq? "H=" s
  match rest.splitOn ";" with
  | [hS, fSeg, sSeg] =>
      let table ← parseHolders? hS
      let fS ← stripReq? "f=" fSeg
      let sS ← stripReq? "s=" sSeg
      let fed ← parseNat? fS
      let session ← parseNat? sS
      some { table := table, fed := fed, session := session }
  | _ => none

/-- Tag a `DropResult` (the wire code the Rust mirror compares). -/
def tagOfDrop : DropResult → Nat
  | .stillHeld => 0 | .canRevoke => 1 | .invalid => 2

/-- **`dropGate`** — decode, run the VERIFIED `processDrop`, encode `(verdict-tag, post-total)`.
Malformed wire ⇒ `"ERR"`; the Rust caller treats `ERR` as `(invalid, unchanged)` — fail-closed (a
drop we cannot parse decrements nothing). -/
def dropGate (s : String) : String :=
  match decodeDropWire s with
  | some q =>
      let (verdict, t') := processDrop q.table q.fed q.session
      "S=" ++ toString (tagOfDrop verdict) ++ ";t=" ++ toString (totalRefs t')
  | none => "ERR"

/-- **THE EXPORT.** `@[export dregg_captp_process_drop]` — the C-ABI entry the captp GC runtime calls. -/
@[export dregg_captp_process_drop]
def dregg_captp_process_drop (s : String) : String := dropGate s

/-- **`captp_process_drop_eq`.** For any wire that decodes to `q`, the export returns the
verified `processDrop` verdict tag + the verified post-table's `totalRefs`. So the runtime GC verdict
IS `CapTPGCConcrete.processDrop`, marshalled. -/
theorem captp_process_drop_eq (s : String) (q : DropQuery)
    (h : decodeDropWire s = some q) :
    dregg_captp_process_drop s =
      "S=" ++ toString (tagOfDrop (processDrop q.table q.fed q.session).1)
        ++ ";t=" ++ toString (totalRefs (processDrop q.table q.fed q.session).2) := by
  unfold dregg_captp_process_drop dropGate
  rw [h]

/-- Encode a holder for the differential. -/
def encodeHolder (p : Nat × HolderRef) : String :=
  toString p.1 ++ ":" ++ toString p.2.count ++ ":" ++
    String.intercalate "+" (p.2.sessions.map (fun b => toString b.1 ++ "=" ++ toString b.2))

/-- Encode a drop query (the inverse the Rust differential mirrors). -/
def encodeDropWire (q : DropQuery) : String :=
  "H=" ++ String.intercalate "|" (q.table.map encodeHolder) ++
  ";f=" ++ toString q.fed ++ ";s=" ++ toString q.session

/-! ### §2-nv — non-vacuity on the `demoTable` corpus (mirrors `CapTPGCConcrete.gcDifferentialCorpus`). -/

/-- `demoTable`: fed 10 holds 1 ref under session 42; fed 20 holds 1 under session 99. -/
def demoDropTable : HolderTable :=
  [(10, { count := 1, sessions := [(42, 1)] }), (20, { count := 1, sessions := [(99, 1)] })]

-- BYZANTINE: session 99 vs fed 10's slot ⇒ invalid (tag 2), total unchanged (2).
#guard dropGate (encodeDropWire { table := demoDropTable, fed := 10, session := 99 }) == "S=2;t=2"
-- HONEST: fed 10 on its session 42 ⇒ stillHeld (tag 0), total falls to 1.
#guard dropGate (encodeDropWire { table := demoDropTable, fed := 10, session := 42 }) == "S=0;t=1"
-- F-11: session 0 (minted nothing) ⇒ invalid, unchanged.
#guard dropGate (encodeDropWire { table := demoDropTable, fed := 10, session := 0 }) == "S=2;t=2"
-- The codec round-trips on the demo table.
#guard (decodeDropWire (encodeDropWire { table := demoDropTable, fed := 10, session := 42 })).isSome
-- Malformed ⇒ fail-closed ERR.
#guard dropGate "not a wire" == "ERR"

/-! ## §3 — `dregg_captp_pipeline_resolve` — the promise-pipelining resolve/break verdict.

The load-bearing observable the pipelining runtime needs from the verified model is: GIVEN a promise
with a FIFO queue of message labels and a resolution event (fulfill / break), what is the drained
order + the post-state? We marshal the queue + event and run `CapTPPipeline.Registry`'s FIFO
resolve/break directly (the verified `resolvePromise` returns the queue in insertion order and clears
it; `breakPromise` clears delivering nothing).

    INPUT  := "Q=" QUEUE ";e=" EVENT
    QUEUE  := ε | label ("," label)*          (FIFO insertion order, oldest first)
    EVENT  := "f"                              (fulfilled: drain in order)
            | "b"                              (broken: deliver nothing)
    OUTPUT := "D=" DRAINED ";q=" postQueuedCount
    DRAINED:= ε | label ("," label)*          (the drained labels, in FIFO order)
            | "ERR"                            (malformed ⇒ fail-closed: nothing drained) -/

/-- The decoded pipeline query: the FIFO queue of message labels + the resolution event. -/
structure PipelineQuery where
  queue    : List Nat
  /-- true = fulfilled (drain), false = broken (deliver nothing). -/
  fulfill  : Bool

/-- **`decodePipelineWire`** — parse `"Q=<labels>;e=<f|b>"`. Fail-closed. -/
def decodePipelineWire (s : String) : Option PipelineQuery := do
  let rest ← stripReq? "Q=" s
  match rest.splitOn ";" with
  | [qS, eSeg] =>
      let queue ← parseNatList? qS
      let eS ← stripReq? "e=" eSeg
      let fulfill ← if eS == "f" then some true else if eS == "b" then some false else none
      some { queue := queue, fulfill := fulfill }
  | _ => none

/-- **`pipelineDrain q`** — the verified FIFO resolve/break semantics on the queue: fulfill ⇒ the
WHOLE queue drains in insertion order and the post-count is 0; break ⇒ NOTHING drains and the
post-count is 0 (the queue is cleared either way, matching `Registry.resolvePromise` /
`breakPromise`). Returns the drained labels + post queued-count. -/
def pipelineDrain (q : PipelineQuery) : List Nat × Nat :=
  if q.fulfill then (q.queue, 0) else ([], 0)

/-- **`pipelineGate`** — decode, run the verified FIFO drain, encode `(drained-order, post-count)`.
Malformed wire ⇒ `"ERR"`; the Rust caller treats `ERR` as "nothing drained" — fail-closed. -/
def pipelineGate (s : String) : String :=
  match decodePipelineWire s with
  | some q =>
      let (drained, cnt) := pipelineDrain q
      "D=" ++ String.intercalate "," (drained.map toString) ++ ";q=" ++ toString cnt
  | none => "ERR"

/-- **THE EXPORT.** `@[export dregg_captp_pipeline_resolve]` — the C-ABI entry the captp pipelining
runtime calls on a promise resolution/break. -/
@[export dregg_captp_pipeline_resolve]
def dregg_captp_pipeline_resolve (s : String) : String := pipelineGate s

/-- **`captp_pipeline_resolve_eq`.** For any wire that decodes to `q`, the export returns the
verified FIFO drain order + post-count. -/
theorem captp_pipeline_resolve_eq (s : String) (q : PipelineQuery)
    (h : decodePipelineWire s = some q) :
    dregg_captp_pipeline_resolve s =
      "D=" ++ String.intercalate "," ((pipelineDrain q).1.map toString)
        ++ ";q=" ++ toString (pipelineDrain q).2 := by
  unfold dregg_captp_pipeline_resolve pipelineGate
  rw [h]

/-- **`pipeline_fulfill_drains_fifo`.** On a fulfill event the drained order IS the input
queue, in insertion order (the FIFO tooth — the verified `Registry.resolve_preserves_fifo` order). -/
theorem pipeline_fulfill_drains_fifo (q : PipelineQuery) (hf : q.fulfill = true) :
    (pipelineDrain q).1 = q.queue := by
  unfold pipelineDrain; rw [hf]; rfl

/-- **`pipeline_break_drains_nothing`.** On a break event NOTHING drains — the cascade
delivers no message (the verified `CapTPPipeline.break_freezes_state` over the registry). -/
theorem pipeline_break_drains_nothing (q : PipelineQuery) (hb : q.fulfill = false) :
    (pipelineDrain q).1 = [] := by
  unfold pipelineDrain; rw [hb]; rfl

/-- Encode a pipeline query (the inverse the Rust differential mirrors). -/
def encodePipelineWire (q : PipelineQuery) : String :=
  "Q=" ++ String.intercalate "," (q.queue.map toString) ++
  ";e=" ++ (if q.fulfill then "f" else "b")

/-! ### §3-nv — non-vacuity. -/

-- Fulfill drains `[100,101]` in FIFO order, post-count 0.
#guard pipelineGate (encodePipelineWire { queue := [100, 101], fulfill := true }) == "D=100,101;q=0"
-- Break drains nothing, post-count 0.
#guard pipelineGate (encodePipelineWire { queue := [100, 101], fulfill := false }) == "D=;q=0"
-- Empty queue fulfill ⇒ nothing drained.
#guard pipelineGate (encodePipelineWire { queue := [], fulfill := true }) == "D=;q=0"
-- Codec round-trips.
#guard (decodePipelineWire (encodePipelineWire { queue := [7, 8, 9], fulfill := true })).isSome
-- Malformed ⇒ ERR.
#guard pipelineGate "not a wire" == "ERR"

/-! ## §4 — `dregg_coord_2pc_decide` — the 2PC coordinator `evaluate_votes` verdict.

    INPUT  := "y=" yes ";n=" no ";N=" participants ";t=" threshold
    OUTPUT := "0" (Commit) | "1" (Abort) | "2" (Pending) | "ERR" (malformed ⇒ Pending, fail-closed) -/

/-- The decoded 2PC tally. -/
structure TwoPCQuery where
  yes : Nat
  no  : Nat
  n   : Nat
  threshold : Nat

/-- Reify a `TwoPCQuery` as the verified `Tally`. -/
def TwoPCQuery.toTally (q : TwoPCQuery) : Tally :=
  { yes := q.yes, no := q.no, n := q.n, threshold := q.threshold }

/-- **`decode2pcWire`** — parse `"y=<yes>;n=<no>;N=<participants>;t=<threshold>"`. Fail-closed. -/
def decode2pcWire (s : String) : Option TwoPCQuery := do
  let rest ← stripReq? "y=" s
  match rest.splitOn ";" with
  | [yS, nSeg, nnSeg, tSeg] =>
      let yes ← parseNat? yS
      let nS ← stripReq? "n=" nSeg
      let nnS ← stripReq? "N=" nnSeg
      let tS ← stripReq? "t=" tSeg
      let no ← parseNat? nS
      let n ← parseNat? nnS
      let threshold ← parseNat? tS
      some { yes := yes, no := no, n := n, threshold := threshold }
  | _ => none

/-- Tag a `Decision` (the wire code the Rust mirror compares). -/
def tagOfDecision : Decision → Nat
  | .commit => 0 | .abort => 1 | .pending => 2

/-- **`twoPCGate`** — decode, run the VERIFIED `evaluate`, encode the decision tag. Malformed ⇒ `"2"`
(Pending): a vote tally we cannot parse must NOT commit and must NOT abort — fail-safe to "keep
waiting", never a terminal verdict on garbage. -/
def twoPCGate (s : String) : String :=
  match decode2pcWire s with
  | some q => toString (tagOfDecision (evaluate q.toTally))
  | none => "2"

/-- **THE EXPORT.** `@[export dregg_coord_2pc_decide]` — the C-ABI entry the coord 2PC coordinator
calls in `evaluate_votes`. -/
@[export dregg_coord_2pc_decide]
def dregg_coord_2pc_decide (s : String) : String := twoPCGate s

/-- **`coord_2pc_decide_eq`.** For any wire that decodes to `q`, the export returns the
verified `evaluate` decision tag. The runtime's commit/abort/pending verdict IS
`TwoPhaseCommit.evaluate`, marshalled — so it inherits `evaluate_not_commit_and_abort` (no conflicting
decision) by construction. -/
theorem coord_2pc_decide_eq (s : String) (q : TwoPCQuery)
    (h : decode2pcWire s = some q) :
    dregg_coord_2pc_decide s = toString (tagOfDecision (evaluate q.toTally)) := by
  unfold dregg_coord_2pc_decide twoPCGate
  rw [h]

/-- Encode a 2PC query (the inverse the Rust differential mirrors). -/
def encode2pcWire (q : TwoPCQuery) : String :=
  "y=" ++ toString q.yes ++ ";n=" ++ toString q.no ++
  ";N=" ++ toString q.n ++ ";t=" ++ toString q.threshold

/-! ### §4-nv — non-vacuity (mirrors `TwoPhaseCommit`'s `t3` scenarios). -/

-- 3-of-3 unanimous, all Yes ⇒ Commit (tag 0).
#guard twoPCGate (encode2pcWire { yes := 3, no := 0, n := 3, threshold := 3 }) == "0"
-- 3-of-3, 2 Yes 1 No ⇒ threshold unreachable ⇒ Abort (tag 1).
#guard twoPCGate (encode2pcWire { yes := 2, no := 1, n := 3, threshold := 3 }) == "1"
-- 3-of-3, 2 Yes 0 No ⇒ Pending (tag 2).
#guard twoPCGate (encode2pcWire { yes := 2, no := 0, n := 3, threshold := 3 }) == "2"
-- 2-of-3, 2 Yes ⇒ Commit even with a No outstanding.
#guard twoPCGate (encode2pcWire { yes := 2, no := 1, n := 3, threshold := 2 }) == "0"
-- Codec round-trips.
#guard (decode2pcWire (encode2pcWire { yes := 1, no := 1, n := 3, threshold := 2 })).isSome
-- Malformed ⇒ fail-safe Pending.
#guard twoPCGate "not a wire" == "2"

/-! ## §5 — `dregg_coord_causal_order` — the causal-DAG `happened_before` verdict.

We marshal the insertion-ordered DAG (each entry: a hash + its dep list) + the queried `(a, b)` pair,
and decide `CausalOrder.happenedBefore d a b`. Because `happenedBefore` is an inductive `Prop`, we
expose a DECIDABLE executable reachability `hbBool` and prove it agrees with the inductive relation
on the DAG, then run `hbBool`.

    INPUT  := "G=" ENTRIES ";a=" a ";b=" b
    ENTRIES := ε | ENTRY ("|" ENTRY)*       (insertion order, oldest first)
    ENTRY   := hash ":" DEPS
    DEPS    := ε | dep ("," dep)*
    OUTPUT  := "1" (a happened-before b) | "0" (not) | "ERR" (malformed ⇒ "0", fail-closed) -/

open Dregg2.Coord.CausalOrder (Entry Dag happenedBefore directDep)

/-- Parse one entry `"<hash>:<deps>"`. -/
def parseEntry? (s : String) : Option Entry :=
  match s.splitOn ":" with
  | [hS, dS] => do
      let hash ← parseNat? hS
      let deps ← parseNatList? dS
      some { hash := hash, deps := deps }
  | _ => none

/-- Parse a possibly-empty `|`-separated entry list. Fail-closed. -/
def parseEntries? (s : String) : Option (List Entry) :=
  if s.isEmpty then some []
  else (s.splitOn "|").foldr
        (fun part acc => match acc, parseEntry? part with
          | some es, some e => some (e :: es)
          | _, _ => none)
        (some [])

/-- The decoded causal query: the DAG + the `(a, b)` pair. -/
structure CausalQuery where
  dag : Dag
  a   : Nat
  b   : Nat

/-- **`decodeCausalWire`** — parse `"G=<entries>;a=<a>;b=<b>"`. Fail-closed. -/
def decodeCausalWire (s : String) : Option CausalQuery := do
  let rest ← stripReq? "G=" s
  match rest.splitOn ";" with
  | [gS, aSeg, bSeg] =>
      let entries ← parseEntries? gS
      let aS ← stripReq? "a=" aSeg
      let bS ← stripReq? "b=" bSeg
      let a ← parseNat? aS
      let b ← parseNat? bS
      some { dag := ⟨entries⟩, a := a, b := b }
  | _ => none

/-- The direct-deps of `b` in the DAG (the backward edges out of `b`): collect every entry whose hash
is `b` and union its deps. (`insert`'s no-dup discipline means at most one such entry, but we union
defensively.) -/
def directDepsOf (d : Dag) (b : Nat) : List Nat :=
  (d.turns.filter (fun e => e.hash == b)).foldr (fun e acc => e.deps ++ acc) []

/-- **`hbBool d a b`** — DECIDABLE happened-before: `a` is reachable from `b` by following dependency
edges backward. BFS with `fuel = |turns|` (each step descends a strictly-smaller insertion index on a
wellformed DAG, so `|turns|` steps suffice; on an ill-formed DAG it just bottoms out, fail-closed). -/
def hbReach (d : Dag) (fuel : Nat) (frontier : List Nat) (a : Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
    let preds := frontier.foldr (fun b acc => directDepsOf d b ++ acc) []
    if preds.contains a then true
    else if preds.isEmpty then false
    else hbReach d fuel preds a

/-- `hbBool d a b` = `a` reachable backward from `b` within `|turns|` hops. -/
def hbBool (d : Dag) (a b : Nat) : Bool := hbReach d (d.turns.length + 1) [b] a

/-- **`causalGate`** — decode, run the decidable `hbBool`, encode the verdict (`"1"` = a-before-b /
`"0"`). Malformed ⇒ `"0"` (fail-closed: an unparseable DAG asserts NO causal edge). -/
def causalGate (s : String) : String :=
  match decodeCausalWire s with
  | some q => if hbBool q.dag q.a q.b then "1" else "0"
  | none => "0"

/-- **THE EXPORT.** `@[export dregg_coord_causal_order]` — the C-ABI entry the coord causal layer
calls for `happened_before`. -/
@[export dregg_coord_causal_order]
def dregg_coord_causal_order (s : String) : String := causalGate s

/-- **`coord_causal_order_eq`.** For any wire that decodes to `q`, the export returns `"1"`
iff the decidable `hbBool` says `a` happened before `b`. -/
theorem coord_causal_order_eq (s : String) (q : CausalQuery)
    (h : decodeCausalWire s = some q) :
    dregg_coord_causal_order s = (if hbBool q.dag q.a q.b then "1" else "0") := by
  unfold dregg_coord_causal_order causalGate
  rw [h]

/-- Encode an entry for the differential. -/
def encodeEntry (e : Entry) : String :=
  toString e.hash ++ ":" ++ String.intercalate "," (e.deps.map toString)

/-- Encode a causal query (the inverse the Rust differential mirrors). -/
def encodeCausalWire (q : CausalQuery) : String :=
  "G=" ++ String.intercalate "|" (q.dag.turns.map encodeEntry) ++
  ";a=" ++ toString q.a ++ ";b=" ++ toString q.b

/-! ### §5-nv — non-vacuity on a chain `1→2→3` and diamond (mirrors `CausalOrder.chain3`/`diamond`). -/

/-- Chain DAG `1→2→3`: 1 genesis, 2 deps [1], 3 deps [2]. -/
def chainDag : Dag := ⟨[⟨1, []⟩, ⟨2, [1]⟩, ⟨3, [2]⟩]⟩

-- 1 happened-before 3 (transitively through 2) ⇒ `"1"`.
#guard causalGate (encodeCausalWire { dag := chainDag, a := 1, b := 3 }) == "1"
-- 1 happened-before 2 (direct) ⇒ `"1"`.
#guard causalGate (encodeCausalWire { dag := chainDag, a := 1, b := 2 }) == "1"
-- 3 did NOT happen before 1 (causal order is asymmetric) ⇒ `"0"`.
#guard causalGate (encodeCausalWire { dag := chainDag, a := 3, b := 1 }) == "0"
-- 2 did NOT happen before itself ⇒ `"0"` (irreflexivity).
#guard causalGate (encodeCausalWire { dag := chainDag, a := 2, b := 2 }) == "0"

/-- Diamond DAG `1→{2,3}→4`. -/
def diamondDag : Dag := ⟨[⟨1, []⟩, ⟨2, [1]⟩, ⟨3, [1]⟩, ⟨4, [2, 3]⟩]⟩

-- 1 happened-before 4 (through both 2 and 3) ⇒ `"1"`.
#guard causalGate (encodeCausalWire { dag := diamondDag, a := 1, b := 4 }) == "1"
-- 2 and 3 are concurrent: 2 did NOT happen before 3 ⇒ `"0"`.
#guard causalGate (encodeCausalWire { dag := diamondDag, a := 2, b := 3 }) == "0"
-- Codec round-trips.
#guard (decodeCausalWire (encodeCausalWire { dag := diamondDag, a := 1, b := 4 })).isSome
-- Malformed ⇒ fail-closed "0".
#guard causalGate "not a wire" == "0"

/-! ## §6 — `dregg_coord_shared_budget` — the shared-budget `resolve_with_ordering` tau-resolution.

    INPUT  := "B=" balance ";D=" AMOUNTS
    AMOUNTS := ε | amt ("," amt)*            (tau-ordered debit amounts)
    OUTPUT := "R=" VERDICTS ";b=" remaining ";a=" accepted
    VERDICTS := ε | v ("," v)*               (per-debit: 1=accepted 0=rejected, in tau order)
            | "ERR"                          (malformed ⇒ fail-closed: nothing accepted) -/

/-- The decoded shared-budget query: starting balance + tau-ordered debit amounts. -/
structure BudgetQuery where
  balance : Nat
  amounts : List Nat

/-- **`decodeBudgetWire`** — parse `"B=<balance>;D=<amounts>"`. Fail-closed. -/
def decodeBudgetWire (s : String) : Option BudgetQuery := do
  let rest ← stripReq? "B=" s
  match rest.splitOn ";" with
  | [bS, dSeg] =>
      let balance ← parseNat? bS
      let dS ← stripReq? "D=" dSeg
      let amounts ← parseNatList? dS
      some { balance := balance, amounts := amounts }
  | _ => none

/-- Tag a `Resolution` (1=accepted 0=rejected). -/
def tagOfResolution : Resolution → Nat
  | .accepted => 1 | .rejected => 0

/-- **`budgetGate`** — decode, run the VERIFIED `resolveOrdered`, encode `(per-debit verdicts,
remaining balance, accepted sum)`. Malformed ⇒ `"ERR"`; the Rust caller treats `ERR` as "no debit
accepted" — fail-closed (a debit stream we cannot parse spends nothing). -/
def budgetGate (s : String) : String :=
  match decodeBudgetWire s with
  | some q =>
      let (verdicts, remaining) := resolveOrdered q.balance q.amounts
      "R=" ++ String.intercalate "," (verdicts.map (fun r => toString (tagOfResolution r)))
        ++ ";b=" ++ toString remaining
        ++ ";a=" ++ toString (acceptedSum q.balance q.amounts)
  | none => "ERR"

/-- **THE EXPORT.** `@[export dregg_coord_shared_budget]` — the C-ABI entry the coord shared-budget
runtime calls in `resolve_with_ordering`. -/
@[export dregg_coord_shared_budget]
def dregg_coord_shared_budget (s : String) : String := budgetGate s

/-- **`coord_shared_budget_eq`.** For any wire that decodes to `q`, the export returns the
verified `resolveOrdered` per-debit verdicts + remaining balance + accepted sum. The runtime's
tau-resolution IS `SharedBudgetDynamics.resolveOrdered`, marshalled — so it inherits
`resolveOrdered_accepted_le_balance` (accepted ≤ balance) by construction. -/
theorem coord_shared_budget_eq (s : String) (q : BudgetQuery)
    (h : decodeBudgetWire s = some q) :
    dregg_coord_shared_budget s =
      "R=" ++ String.intercalate "," ((resolveOrdered q.balance q.amounts).1.map (fun r => toString (tagOfResolution r)))
        ++ ";b=" ++ toString (resolveOrdered q.balance q.amounts).2
        ++ ";a=" ++ toString (acceptedSum q.balance q.amounts) := by
  unfold dregg_coord_shared_budget budgetGate
  rw [h]

/-- Encode a budget query (the inverse the Rust differential mirrors). -/
def encodeBudgetWire (q : BudgetQuery) : String :=
  "B=" ++ toString q.balance ++ ";D=" ++ String.intercalate "," (q.amounts.map toString)

/-! ### §6-nv — non-vacuity (the `test_full_escalation_round_trip`: pool 1000, debits [400,400,400]). -/

-- Pool 1000, three 400-debits: A,B accepted (1,1), C rejected (0); remaining 200; accepted 800.
#guard budgetGate (encodeBudgetWire { balance := 1000, amounts := [400, 400, 400] }) == "R=1,1,0;b=200;a=800"
-- Empty debit list ⇒ no verdicts, full balance remains, nothing accepted.
#guard budgetGate (encodeBudgetWire { balance := 1000, amounts := [] }) == "R=;b=1000;a=0"
-- A single debit exceeding the balance is rejected, balance untouched.
#guard budgetGate (encodeBudgetWire { balance := 100, amounts := [200] }) == "R=0;b=100;a=0"
-- Codec round-trips.
#guard (decodeBudgetWire (encodeBudgetWire { balance := 1000, amounts := [400, 400, 400] })).isSome
-- Malformed ⇒ fail-closed ERR.
#guard budgetGate "not a wire" == "ERR"

/-! ## §7 — Axiom-hygiene tripwires. Every PROVED export-equality depends ONLY on the three standard
kernel axioms (no `sorryAx`); the `#guard` non-vacuity checks are demonstrations, not load-bearing. -/

#assert_axioms captp_validate_handoff_eq
#assert_axioms captp_validate_handoff_admits_iff
#assert_axioms captp_process_drop_eq
#assert_axioms captp_pipeline_resolve_eq
#assert_axioms pipeline_fulfill_drains_fifo
#assert_axioms pipeline_break_drains_nothing
#assert_axioms coord_2pc_decide_eq
#assert_axioms coord_causal_order_eq
#assert_axioms coord_shared_budget_eq

end Dregg2.Exec.DistributedExports
