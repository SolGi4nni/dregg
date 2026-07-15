import Datapath.ServeDenseIdx

/-!
# Datapath.HeadIdx — the INDEX-NATIVE request-head VIEW (arm decisions with no head-list)

`Datapath.ServeDenseIdx` decides the dense arms off `parseIndexNative` — the parse
itself is index-native, but its LAST step (`Reactor.Config.arenaToProto` →
`protoReqOf`) materializes the WHOLE head as `List`s: method, target, version, and
EVERY header name/value are resolved to per-byte cons-lists (`resolveBytes … .toList`)
before a single arm conjunct is decided — and the conjuncts then re-walk those lists
(`acceptsGzip` even conses a LOWERED copy of every header name per request). That
per-request head materialization + dec-ref churn is the serve-thread wall once the
body copies are gone.

This module is the head VIEW that never materializes those lists. The arena
`Request` (`Arena.Parse.Request`) already IS a span view — `Entry = (tag, off, len)`
into the flat main/sidecar arenas. What was missing is deciding the deployed arm
predicates directly ON that view:

* `litProbe f arr lit i` — compare a literal against `map f` of the window at `i`
  by INDEX PROBES (`arr.getD`), materializing nothing (`f := lowerByte` gives the
  case-insensitive compare with NO lowered copy);
* `entryMapEqB` / `entryEqB` — an arena entry's bytes vs a literal, by index,
  proven equal to the `resolveBytes` list compare (the list appears on the spec
  side only);
* `findValIdx` — the header lookup: scan the parsed headers comparing each
  CANONICAL NAME entry against a lowercase literal by index; the hit's VALUE stays
  a span (`Arena.Entry`), resolved only if the predicate genuinely needs the bytes;
* `bulkIdxB` / `healthIdxB` — the FULL `/bulk` and `/health` arm decisions on the
  arena head, proven **Boolean-equal** (`bulkIdxB_eq` / `healthIdxB_eq`) to the
  deployed `decide (ReqArm (protoReqOf areq))` — same decision on EVERY request,
  not a sound-but-narrower guard.

## What still allocates on the deciding path (honest scope)

* the TARGET is resolved once (`resolveBytes`, one small `O(|target|)` list) and the
  deployed target predicates (`targetSegments`/`targetEscapes`/`policyReserved`/…)
  run on it as-is — they are `String`-specified (`splitOn`/`normalize`), so an
  index-native re-proof of each is a separate project; the target is a few bytes,
  not the head;
* a matched header VALUE (host / origin / a name-matched accept-encoding) is
  resolved on demand — again `O(|value|)`, only on a hit;
* what NO LONGER exists per request: `protoReqOf` (method/version/every header
  name+value as lists), `deriveKeepAlive`, and `acceptsGzip`'s lowered per-name
  copies. Header NAMES are never materialized at all.
-/

namespace Datapath.HeadIdx

open Proto (Bytes)
open Reactor.Config (resolveBytes protoReqOf)
open Datapath.ServeDenseIdx (reqCtx ReqArm ReqArmHealth HealthArm)
open Datapath.ServeDenseReal (BulkArm)

/-! ## 1. Generic index probes against an arena window -/

/-- `(a == b) = decide (a = b)` for a lawful `BEq` — the bridge between the
deployed `==` scans and the `decide` atoms the arm `Prop`s carry. -/
theorem beq_eq_decide {α : Type _} [BEq α] [LawfulBEq α] [DecidableEq α] (a b : α) :
    (a == b) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · simp [h]

/-- Match `lit` against `map f` of the buffer window starting at `i`, by INDEX
PROBES (`arr.getD`) — no window list, no mapped copy. `f := id` is the exact
compare; `f := lowerByte` is the case-insensitive compare with no lowered cons. -/
def litProbe (f : UInt8 → UInt8) (arr : Array UInt8) : List UInt8 → Nat → Bool
  | [], _ => true
  | b :: rest, i => b == f (arr.getD i 0) && litProbe f arr rest (i + 1)

/-- The index probe decides exactly the mapped-window list equality (the window
list is on the spec side only). -/
theorem litProbe_eq (f : UInt8 → UInt8) (arr : Array UInt8) (lit : List UInt8) :
    ∀ i, i + lit.length ≤ arr.size →
      litProbe f arr lit i
        = decide (((arr.toList.drop i).take lit.length).map f = lit) := by
  induction lit with
  | nil => intro i _; simp [litProbe]
  | cons b rest ih =>
    intro i h
    have hi : i < arr.size := by
      simp only [List.length_cons] at h; omega
    have hi' : i < arr.toList.length := by rw [Array.length_toList]; exact hi
    have hgd : arr.getD i 0 = arr.toList[i]'hi' := by
      rw [Array.getElem_toList]
      simp only [Array.getD]
      rw [dif_pos hi]
      exact rfl
    simp only [litProbe]
    rw [ih (i + 1) (by simp only [List.length_cons] at h; omega),
      List.length_cons, List.drop_eq_getElem_cons hi', List.take_succ_cons,
      List.map_cons, hgd]
    by_cases hfb : f (arr.toList[i]'hi') = b
    · rw [← hfb]
      simp
    · have h1 : (b == f (arr.toList[i]'hi')) = false := by
        rw [beq_eq_false_iff_ne]
        exact fun he => hfb he.symm
      rw [h1, Bool.false_and]
      symm
      apply decide_eq_false
      intro hc
      exact hfb (List.cons_eq_cons.mp hc).1

/-- `resolveBytes` characterized as the drop/take window of the addressed arena
(the shape the probe lemmas rewrite against). -/
theorem resolveBytes_eq (s : Arena.Store) (e : Arena.Entry) :
    resolveBytes s e
      = if e.physOff + e.len.toNat ≤ (s.arenaOf e).size then
          ((s.arenaOf e).toList.drop e.physOff).take e.len.toNat
        else [] := by
  show (match (if e.physOff + e.len.toNat ≤ (s.arenaOf e).size then
            some ((s.arenaOf e).extract e.physOff (e.physOff + e.len.toNat))
          else none) with
        | some b => b.toList
        | none => ([] : Bytes)) = _
  by_cases hb : e.physOff + e.len.toNat ≤ (s.arenaOf e).size
  · rw [if_pos hb, if_pos hb]
    show ((s.arenaOf e).extract e.physOff (e.physOff + e.len.toNat)).toList = _
    rw [Array.toList_extract, List.extract_eq_drop_take, Nat.add_sub_cancel_left]
  · rw [if_neg hb, if_neg hb]

/-- **The index-native entry compare (through a byte map).** In bounds: length
gate + `litProbe`; out of bounds the spec resolves to `[]`. -/
def entryMapEqB (f : UInt8 → UInt8) (s : Arena.Store) (e : Arena.Entry)
    (lit : List UInt8) : Bool :=
  if e.physOff + e.len.toNat ≤ (s.arenaOf e).size then
    e.len.toNat == lit.length && litProbe f (s.arenaOf e) lit e.physOff
  else lit.isEmpty

/-- The index compare decides exactly the mapped `resolveBytes` equality — for
EVERY entry (in- or out-of-bounds). The resolved list is spec-side only. -/
theorem entryMapEqB_eq (f : UInt8 → UInt8) (s : Arena.Store) (e : Arena.Entry)
    (lit : List UInt8) :
    entryMapEqB f s e lit = decide ((resolveBytes s e).map f = lit) := by
  unfold entryMapEqB
  rw [resolveBytes_eq]
  by_cases hb : e.physOff + e.len.toNat ≤ (s.arenaOf e).size
  · rw [if_pos hb, if_pos hb]
    by_cases hn : e.len.toNat = lit.length
    · rw [hn] at hb ⊢
      rw [beq_self_eq_true, Bool.true_and, litProbe_eq f (s.arenaOf e) lit e.physOff hb]
    · have h1 : (e.len.toNat == lit.length) = false := by
        rw [beq_eq_false_iff_ne]; exact hn
      rw [h1, Bool.false_and]
      symm
      apply decide_eq_false
      intro heq
      apply hn
      have hlen := congrArg List.length heq
      rw [List.length_map, List.length_take, List.length_drop,
        Array.length_toList] at hlen
      omega
  · rw [if_neg hb, if_neg hb]
    cases lit with
    | nil => simp
    | cons a t => simp

/-- The exact (unmapped) index-native entry compare. -/
def entryEqB (s : Arena.Store) (e : Arena.Entry) (lit : List UInt8) : Bool :=
  entryMapEqB id s e lit

theorem entryEqB_eq (s : Arena.Store) (e : Arena.Entry) (lit : List UInt8) :
    entryEqB s e lit = decide (resolveBytes s e = lit) := by
  unfold entryEqB
  rw [entryMapEqB_eq]
  exact decide_eq_decide.mpr (by rw [List.map_id])

/-! ## 2. The header lookup on the span view — names compared by index,
values kept as spans -/

/-- Find the first header whose CANONICAL NAME entry matches `nameLit` by index
compare; the hit's VALUE stays an `Arena.Entry` (a span — resolved only if the
caller genuinely needs the bytes). No name is ever materialized. -/
def findValIdx (s : Arena.Store) (nameLit : List UInt8) :
    List Arena.Parse.ParsedHeader → Option Arena.Entry
  | [] => none
  | h :: t => if entryEqB s h.name nameLit then some h.value else findValIdx s nameLit t

/-- The deployed `lookup` over the materialized header list is the index-native
find with the hit resolved — the materialized list is spec-side only. -/
theorem lookup_findValIdx (s : Arena.Store) (nameLit : List UInt8)
    (hs : List Arena.Parse.ParsedHeader) :
    (hs.map fun (h : Arena.Parse.ParsedHeader) => (resolveBytes s h.name, resolveBytes s h.value)).lookup nameLit
      = (findValIdx s nameLit hs).map (resolveBytes s) := by
  induction hs with
  | nil => rfl
  | cons h t ih =>
    simp only [List.map_cons, findValIdx]
    by_cases hk : resolveBytes s h.name = nameLit
    · have hbeq : (nameLit == resolveBytes s h.name) = true := beq_iff_eq.mpr hk.symm
      have hdec : entryEqB s h.name nameLit = true := by
        rw [entryEqB_eq]; exact decide_eq_true hk
      rw [hdec, if_pos rfl]
      simp only [List.lookup, hbeq]
      rfl
    · have hbeq : (nameLit == resolveBytes s h.name) = false :=
        beq_eq_false_iff_ne.mpr (fun he => hk he.symm)
      have hdec : entryEqB s h.name nameLit = false := by
        rw [entryEqB_eq]; exact decide_eq_false hk
      rw [hdec, if_neg Bool.false_ne_true]
      simp only [List.lookup, hbeq]
      exact ih

/-- The deployed `find?` (name-keyed) over the materialized header list is the
index-native find with the hit's pair reconstructed — the matched name IS the
literal (lawful `==`), so no name bytes are needed. -/
theorem find?_findValIdx (s : Arena.Store) (nameLit : List UInt8)
    (hs : List Arena.Parse.ParsedHeader) :
    (hs.map fun (h : Arena.Parse.ParsedHeader) => (resolveBytes s h.name, resolveBytes s h.value)).find?
        (fun p => p.1 == nameLit)
      = (findValIdx s nameLit hs).map (fun ve => (nameLit, resolveBytes s ve)) := by
  induction hs with
  | nil => rfl
  | cons h t ih =>
    simp only [List.map_cons, findValIdx]
    by_cases hk : resolveBytes s h.name = nameLit
    · have hdec : entryEqB s h.name nameLit = true := by
        rw [entryEqB_eq]; exact decide_eq_true hk
      rw [hdec, if_pos rfl,
        List.find?_cons_of_pos _ (by
          show (resolveBytes s h.name == nameLit) = true
          exact beq_iff_eq.mpr hk)]
      rw [hk]
      rfl
    · have hdec : entryEqB s h.name nameLit = false := by
        rw [entryEqB_eq]; exact decide_eq_false hk
      rw [hdec, if_neg Bool.false_ne_true,
        List.find?_cons_of_neg _ (by
          show ¬ (resolveBytes s h.name == nameLit) = true
          simp [hk])]
      exact ih

/-! ## 3. The index-native arm conjuncts that read headers -/

/-- **The `Accept-Encoding: … gzip …` scan, index-native.** Per header: the
case-insensitive NAME compare is `litProbe lowerByte` (no lowered name cons —
the deployed scan conses a lowered copy of EVERY header name per request); only
a name HIT resolves the value for the real token scan. -/
def gzipAnyIdx (s : Arena.Store) : List Arena.Parse.ParsedHeader → Bool
  | [] => false
  | h :: t =>
      (entryMapEqB Reactor.Stage.Gzip.lowerByte s h.name Reactor.Stage.Gzip.aeName
        && Reactor.Stage.Gzip.isInfix Reactor.Stage.Gzip.gzipTok
             (Reactor.Stage.Gzip.lower (resolveBytes s h.value)))
      || gzipAnyIdx s t

/-- The index-native scan decides exactly the deployed `acceptsGzip` over the
materialized headers (spec side only). -/
theorem gzipAnyIdx_eq (s : Arena.Store) (hs : List Arena.Parse.ParsedHeader) :
    gzipAnyIdx s hs
      = (hs.map fun (h : Arena.Parse.ParsedHeader) => (resolveBytes s h.name, resolveBytes s h.value)).any
          (fun nv => Reactor.Stage.Gzip.lower nv.1 == Reactor.Stage.Gzip.aeName
            && Reactor.Stage.Gzip.isInfix Reactor.Stage.Gzip.gzipTok
                 (Reactor.Stage.Gzip.lower nv.2)) := by
  induction hs with
  | nil => rfl
  | cons h t ih =>
    simp only [gzipAnyIdx, List.map_cons, List.any_cons, ih]
    congr 2
    rw [entryMapEqB_eq]
    show decide ((resolveBytes s h.name).map Reactor.Stage.Gzip.lowerByte
          = Reactor.Stage.Gzip.aeName)
        = (Reactor.Stage.Gzip.lower (resolveBytes s h.name) == Reactor.Stage.Gzip.aeName)
    rw [beq_eq_decide]
    rfl

/-- **The CORS admit conjunct, index-native.** The `origin` lookup scans names by
index; an absent origin is the deployed denied-empty token (a closed fact); a
present origin resolves the (rare) value on demand and runs the REAL policy
decision. -/
def corsNoneIdx (s : Arena.Store) (hs : List Arena.Parse.ParsedHeader) : Bool :=
  match findValIdx s Reactor.Deploy.corsOriginNameLower hs with
  | some ve => (Cors.acaoValue Reactor.Stage.Cors.corsPolicy
      (Reactor.Stage.Cors.bytesToStr (resolveBytes s ve))).isNone
  | none => true

/-- The index-native CORS conjunct is exactly the deployed decision over the
materialized headers (spec side only). -/
theorem corsNoneIdx_eq (s : Arena.Store) (hs : List Arena.Parse.ParsedHeader) :
    corsNoneIdx s hs
      = (Cors.acaoValue Reactor.Stage.Cors.corsPolicy
          (match (hs.map fun (h : Arena.Parse.ParsedHeader) => (resolveBytes s h.name, resolveBytes s h.value)).lookup
              Reactor.Deploy.corsOriginNameLower with
           | some v => Reactor.Stage.Cors.bytesToStr v
           | none => "")).isNone := by
  unfold corsNoneIdx
  rw [lookup_findValIdx]
  cases findValIdx s Reactor.Deploy.corsOriginNameLower hs with
  | none =>
    show true = (Cors.acaoValue Reactor.Stage.Cors.corsPolicy "").isNone
    decide
  | some ve => rfl

/-- The canonical lowercase `host` header name — a top-level constant (consed
once at initialization, never per request). -/
def hostKey : Bytes := "host".toUTF8.toList

/-- **The vhost-shape conjunct, index-native.** The `host` lookup scans names by
index; an absent host is the deployed empty-labels case (closed); a present host
resolves the value on demand and splits it exactly as the deployed
`hostLabelsOf` does. -/
def hostNeIdx (s : Arena.Store) (hs : List Arena.Parse.ParsedHeader) : Bool :=
  match findValIdx s hostKey hs with
  | some ve =>
      let ls := (Reactor.App.bytesToString (resolveBytes s ve)).splitOn "."
      !decide (ls = ["a", "example"]) && !decide (ls = ["b", "example"])
  | none => true

/-- The deployed `hostLabelsOf` over the materialized headers, re-read through
the index-native lookup. -/
theorem hostLabelsOf_idx (s : Arena.Store) (hs : List Arena.Parse.ParsedHeader)
    (req : Proto.Request)
    (hh : req.headers = hs.map fun (h : Arena.Parse.ParsedHeader) => (resolveBytes s h.name, resolveBytes s h.value)) :
    Reactor.App.hostLabelsOf req
      = match findValIdx s hostKey hs with
        | some ve => (Reactor.App.bytesToString (resolveBytes s ve)).splitOn "."
        | none => [] := by
  unfold Reactor.App.hostLabelsOf
  rw [hh]
  have hfun : (fun (h : Bytes × Bytes) => h.1 == "host".toUTF8.toList)
      = (fun (h : Bytes × Bytes) => h.1 == hostKey) := rfl
  rw [hfun, find?_findValIdx]
  cases findValIdx s hostKey hs with
  | none => rfl
  | some ve => rfl

/-- The index-native vhost conjunct decides exactly the pair of deployed
label inequalities. -/
theorem hostNeIdx_iff (s : Arena.Store) (hs : List Arena.Parse.ParsedHeader)
    (req : Proto.Request)
    (hh : req.headers = hs.map fun (h : Arena.Parse.ParsedHeader) => (resolveBytes s h.name, resolveBytes s h.value)) :
    hostNeIdx s hs = true
      ↔ (Reactor.App.hostLabelsOf req ≠ ["a", "example"]
          ∧ Reactor.App.hostLabelsOf req ≠ ["b", "example"]) := by
  rw [hostLabelsOf_idx s hs req hh]
  unfold hostNeIdx
  cases findValIdx s hostKey hs with
  | none => simp
  | some ve =>
    simp [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]

/-! ## 4. The rate conjunct is a constant on a bare-request ctx -/

/-- On the bare request ctx (`attrs = []`, a fresh unmetered connection) the
deployed rate gate admits — the bucket is full by construction. -/
theorem rate_admits_reqCtx (req : Proto.Request) :
    Reactor.Stage.Rate.admits (reqCtx req) = true := rfl

/-! ## 5. The FULL arm decisions on the arena head -/

/-- The target-only request shim: the deployed target predicates read ONLY
`req.target`, so they run against this thin view (the one on-demand-resolved
field) and are definitionally the predicates on `protoReqOf`. -/
def tqOf (areq : Arena.Parse.Request) : Proto.Request :=
  { method := [], target := resolveBytes areq.store areq.target,
    version := [], headers := [] }

/-- **The FULL index-native `/bulk` arm decision** on the arena head. Header
names: never materialized (index probes). Header values: resolved only on a
name hit. Target: resolved once, fed to the deployed target predicates.
`protoReqOf` (the whole-head materialization) is never called. -/
def bulkIdxB (areq : Arena.Parse.Request) : Bool :=
  let tq := tqOf areq
  !Reactor.Deploy.isAdminPath tq
  && !Reactor.Stage.BasicAuth.isProtectedPath tq
  && !decide (tq.target = Reactor.Stage.Redirect.ruleTarget)
  && !Reactor.Deploy.targetEscapes tq
  && !Reactor.Deploy.policyReserved tq
  && !gzipAnyIdx areq.store areq.headers
  && corsNoneIdx areq.store areq.headers
  && decide (Reactor.App.targetSegments tq.target = ["bulk"])
  && hostNeIdx areq.store areq.headers

/-- **The FULL index-native `/health` arm decision** — same kit, the route pinned
to `["health"]`, no vhost conjuncts (the route matches first from any host). -/
def healthIdxB (areq : Arena.Parse.Request) : Bool :=
  let tq := tqOf areq
  !Reactor.Deploy.isAdminPath tq
  && !Reactor.Stage.BasicAuth.isProtectedPath tq
  && !decide (tq.target = Reactor.Stage.Redirect.ruleTarget)
  && !Reactor.Deploy.targetEscapes tq
  && !Reactor.Deploy.policyReserved tq
  && !gzipAnyIdx areq.store areq.headers
  && corsNoneIdx areq.store areq.headers
  && decide (Reactor.App.targetSegments tq.target = ["health"])

/-- **The `/bulk` decision equivalence.** The index-native decision holds exactly
when the deployed request-level arm (`ReqArm` on the MATERIALIZED head) holds —
both directions, so the dense arm fires on exactly the same requests. -/
theorem bulkIdxB_iff (areq : Arena.Parse.Request) :
    bulkIdxB areq = true ↔ ReqArm (protoReqOf areq) := by
  have hgz : gzipAnyIdx areq.store areq.headers
      = Reactor.Stage.Gzip.acceptsGzip (protoReqOf areq) :=
    gzipAnyIdx_eq areq.store areq.headers
  have hcors : corsNoneIdx areq.store areq.headers
      = (Cors.acaoValue Reactor.Stage.Cors.corsPolicy
          (Reactor.Deploy.corsOriginOf (reqCtx (protoReqOf areq)))).isNone :=
    corsNoneIdx_eq areq.store areq.headers
  have hhost := hostNeIdx_iff areq.store areq.headers (protoReqOf areq) rfl
  unfold bulkIdxB
  show (!Reactor.Deploy.isAdminPath (tqOf areq)
      && !Reactor.Stage.BasicAuth.isProtectedPath (tqOf areq)
      && !decide ((tqOf areq).target = Reactor.Stage.Redirect.ruleTarget)
      && !Reactor.Deploy.targetEscapes (tqOf areq)
      && !Reactor.Deploy.policyReserved (tqOf areq)
      && !gzipAnyIdx areq.store areq.headers
      && corsNoneIdx areq.store areq.headers
      && decide (Reactor.App.targetSegments (tqOf areq).target = ["bulk"])
      && hostNeIdx areq.store areq.headers) = true
    ↔ _
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩
    rw [hgz] at h6
    rw [hcors] at h7
    obtain ⟨h9a, h9b⟩ := hhost.mp h9
    exact ⟨h1, h2, rate_admits_reqCtx _, h3, h4, h5, h6,
      Option.isNone_iff_eq_none.mp h7, h8, h9a, h9b⟩
  · rintro ⟨k1, k2, _, k4, k5, k6, k7, k8, k9, k10, k11⟩
    have k7' : Reactor.Stage.Gzip.acceptsGzip (protoReqOf areq) = false := k7
    rw [← hgz] at k7'
    refine ⟨⟨⟨⟨⟨⟨⟨⟨k1, k2⟩, k4⟩, k5⟩, k6⟩, k7'⟩, ?_⟩, k9⟩, hhost.mpr ⟨k10, k11⟩⟩
    rw [hcors]
    have k8' : Cors.acaoValue Reactor.Stage.Cors.corsPolicy
        (Reactor.Deploy.corsOriginOf (reqCtx (protoReqOf areq))) = none := k8
    exact Option.isNone_iff_eq_none.mpr k8'

/-- The Bool form of the `/bulk` equivalence — what the guard-rewrite consumes. -/
theorem bulkIdxB_eq (areq : Arena.Parse.Request) :
    bulkIdxB areq = decide (ReqArm (protoReqOf areq)) := by
  by_cases h : ReqArm (protoReqOf areq)
  · rw [decide_eq_true h]; exact (bulkIdxB_iff areq).mpr h
  · rw [decide_eq_false h]
    cases hb : bulkIdxB areq with
    | false => rfl
    | true => exact absurd ((bulkIdxB_iff areq).mp hb) h

/-- **The `/health` decision equivalence** — both directions. -/
theorem healthIdxB_iff (areq : Arena.Parse.Request) :
    healthIdxB areq = true ↔ ReqArmHealth (protoReqOf areq) := by
  have hgz : gzipAnyIdx areq.store areq.headers
      = Reactor.Stage.Gzip.acceptsGzip (protoReqOf areq) :=
    gzipAnyIdx_eq areq.store areq.headers
  have hcors : corsNoneIdx areq.store areq.headers
      = (Cors.acaoValue Reactor.Stage.Cors.corsPolicy
          (Reactor.Deploy.corsOriginOf (reqCtx (protoReqOf areq)))).isNone :=
    corsNoneIdx_eq areq.store areq.headers
  unfold healthIdxB
  show (!Reactor.Deploy.isAdminPath (tqOf areq)
      && !Reactor.Stage.BasicAuth.isProtectedPath (tqOf areq)
      && !decide ((tqOf areq).target = Reactor.Stage.Redirect.ruleTarget)
      && !Reactor.Deploy.targetEscapes (tqOf areq)
      && !Reactor.Deploy.policyReserved (tqOf areq)
      && !gzipAnyIdx areq.store areq.headers
      && corsNoneIdx areq.store areq.headers
      && decide (Reactor.App.targetSegments (tqOf areq).target = ["health"])) = true
    ↔ _
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩
    rw [hgz] at h6
    rw [hcors] at h7
    exact ⟨h1, h2, rate_admits_reqCtx _, h3, h4, h5, h6,
      Option.isNone_iff_eq_none.mp h7, h8⟩
  · rintro ⟨k1, k2, _, k4, k5, k6, k7, k8, k9⟩
    have k7' : Reactor.Stage.Gzip.acceptsGzip (protoReqOf areq) = false := k7
    rw [← hgz] at k7'
    refine ⟨⟨⟨⟨⟨⟨⟨k1, k2⟩, k4⟩, k5⟩, k6⟩, k7'⟩, ?_⟩, k9⟩
    rw [hcors]
    have k8' : Cors.acaoValue Reactor.Stage.Cors.corsPolicy
        (Reactor.Deploy.corsOriginOf (reqCtx (protoReqOf areq))) = none := k8
    exact Option.isNone_iff_eq_none.mpr k8'

/-- The Bool form of the `/health` equivalence. -/
theorem healthIdxB_eq (areq : Arena.Parse.Request) :
    healthIdxB areq = decide (ReqArmHealth (protoReqOf areq)) := by
  by_cases h : ReqArmHealth (protoReqOf areq)
  · rw [decide_eq_true h]; exact (healthIdxB_iff areq).mpr h
  · rw [decide_eq_false h]
    cases hb : healthIdxB areq with
    | false => rfl
    | true => exact absurd ((healthIdxB_iff areq).mp hb) h

/-! ## 6. Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}, 0 sorryAx. -/

#print axioms entryMapEqB_eq
#print axioms lookup_findValIdx
#print axioms find?_findValIdx
#print axioms gzipAnyIdx_eq
#print axioms corsNoneIdx_eq
#print axioms hostNeIdx_iff
#print axioms bulkIdxB_eq
#print axioms healthIdxB_eq

end Datapath.HeadIdx
