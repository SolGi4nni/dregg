import Reactor.Pipeline
import Proto.Decimal

/-!
# Reactor.Stage.StaleWhileRevalidate — RFC 5861 stale-content directives (ca.1 residual)

RFC 5861 extends `Cache-Control` with `stale-while-revalidate=N` (a cache MAY serve a
stale response for up to `N` seconds past freshness while it revalidates in the
background) and bounds it hard: past the window the stale response MUST NOT be served
without revalidation. The deployed drorb serve emits NO `Cache-Control` at all and
ignores the directive entirely.

## Ground truth — curl against the running dataplane (io_uring, port 8144, 2026-07-11)

```
$ curl -s -D - -o /dev/null -H 'Cache-Control: stale-while-revalidate=60' \
    http://127.0.0.1:8144/static/app.js
HTTP/1.1 200 OK
ETag: "9e983f35"
Accept-Ranges: bytes
Content-Type: application/javascript
…                              ← no Cache-Control on the response, directive ignored
```

This module adds BOTH halves as one self-contained lib:

1. **The consumer-side policy core** (`classify`): the three-state freshness decision
   (fresh / stale-but-serve-and-revalidate / expired) an RFC 5861 cache makes from
   `age`, `max-age`, and the `stale-while-revalidate` window — with the MUST-NOT bound
   proved.
2. **The directive codec** (`findSwr`): parse `stale-while-revalidate=N` out of a
   `Cache-Control` value, with a genuine render→parse round-trip over the serializer's
   real decimal rendering (`Proto.Dec.natToDec`).
3. **The emit-side stage** (`swrStage`): stamp `Cache-Control: max-age=60,
   stale-while-revalidate=30` onto `200` responses that carry no `Cache-Control`,
   never clobbering an origin-set policy — so downstream caches GET a stale-serve
   window from this edge.

## What is proved (pure-kernel; no `native_decide`, no `Lean.ofReduceBool`)

* `classify_fresh` / `classify_swr` / `classify_expired` — the decision fires in
  exactly its RFC window, for ALL `age`/`maxAge`/`swr`.
* `served_staleness_bounded` — **the RFC 5861 §3 MUST NOT**: whenever the policy
  serves a stored response, `age ≤ maxAge + swr`; a response past the window is
  NEVER served stale.
* `stale_serve_revalidates` — a stale-served response always triggers revalidation
  (stale-while-REVALIDATE, not stale-forever).
* `no_directive_no_stale` — with a zero window (directive absent), the policy NEVER
  serves stale: the extension is strictly opt-in.
* `findSwr_render` — **round-trip**: `findSwr (swrTok ++ Proto.Dec.natToDec n) = some n` for
  EVERY `n`, over the deployed serializer's decimal rendering (via
  `Proto.Dec.dval_natToDec`).
* `stampCc_has` / `stampCc_noop` / `stampCc_prefix` / `stampCc_idem` — the stamp adds
  the policy exactly once and never rewrites an origin `Cache-Control`.
* `applyCc_status` / `swrStage_statusStable` — the stage never touches the status.
* `swrStage_effect` — the stage's response phase is exactly `applyCc` on the
  finalized response, for ANY tail/handler (via `pipeline_stage_effect`).
* `demo_*` — concrete non-vacuous witnesses through the real `runPipeline` fold,
  including `findSwr defaultCc = some 30`: the value this stage emits parses back to
  the window it promises, and that window classifies correctly (`demo_window`).

Residual (named): wire into `deployStagesFull2` + curl through the running socket
(dataplane rebuild deferred — box-safety this session); the cache-side integration
(feeding `classify` from the deployed cache's stored-entry age) and `stale-if-error`.
-/

namespace Reactor.Stage.StaleWhileRevalidate

open Reactor.Pipeline
open Proto (Bytes Request)
open Proto.Dec (dval dval_natToDec natToDec_eq natToDec_isDigit)

/-! ## 1. The RFC 5861 policy core -/

/-- The three-state freshness decision of an RFC 5861 cache. -/
inductive Freshness where
  /-- Within freshness lifetime: serve stored, no revalidation. -/
  | fresh
  /-- Stale, but within the `stale-while-revalidate` window: serve stored NOW and
  revalidate in the background (RFC 5861 §3). -/
  | staleRevalidate
  /-- Past the window: MUST revalidate before serving (RFC 5861 §3 MUST NOT). -/
  | expired
deriving DecidableEq, Repr

/-- Classify a stored response: `age` seconds old, freshness lifetime `maxAge`,
stale-while-revalidate window `swr`. -/
def classify (age maxAge swr : Nat) : Freshness :=
  if age ≤ maxAge then .fresh
  else if age ≤ maxAge + swr then .staleRevalidate
  else .expired

/-- Does the decision serve the stored response (without blocking)? -/
def servesStored : Freshness → Bool
  | .fresh => true
  | .staleRevalidate => true
  | .expired => false

/-- Does the decision trigger a revalidation? -/
def needsRevalidation : Freshness → Bool
  | .fresh => false
  | .staleRevalidate => true
  | .expired => true

/-- A fresh response is served fresh — no stale window consulted. -/
theorem classify_fresh (age maxAge swr : Nat) (h : age ≤ maxAge) :
    classify age maxAge swr = .fresh := by
  unfold classify; rw [if_pos h]

/-- In the window (stale but within `maxAge + swr`) the response is served stale
with a background revalidation — the RFC 5861 §3 MAY. -/
theorem classify_swr (age maxAge swr : Nat) (h1 : maxAge < age)
    (h2 : age ≤ maxAge + swr) : classify age maxAge swr = .staleRevalidate := by
  unfold classify
  rw [if_neg (by omega : ¬ age ≤ maxAge), if_pos h2]

/-- Past the window the response is expired — revalidation is mandatory. -/
theorem classify_expired (age maxAge swr : Nat) (h : maxAge + swr < age) :
    classify age maxAge swr = .expired := by
  unfold classify
  rw [if_neg (by omega : ¬ age ≤ maxAge), if_neg (by omega : ¬ age ≤ maxAge + swr)]

/-- **The RFC 5861 §3 MUST NOT.** Whenever the policy serves the stored response,
its age is within `maxAge + swr` — a response past the stale window is NEVER served
without revalidation, for ALL ages/lifetimes/windows. -/
theorem served_staleness_bounded (age maxAge swr : Nat)
    (h : servesStored (classify age maxAge swr) = true) : age ≤ maxAge + swr := by
  unfold classify at h
  by_cases h1 : age ≤ maxAge
  · omega
  · rw [if_neg h1] at h
    by_cases h2 : age ≤ maxAge + swr
    · exact h2
    · rw [if_neg h2] at h
      exact absurd h (by decide)

/-- **Stale-while-REVALIDATE.** A response served stale ALWAYS triggers a
revalidation — the window never becomes stale-forever. -/
theorem stale_serve_revalidates (age maxAge swr : Nat) (h1 : maxAge < age)
    (h2 : servesStored (classify age maxAge swr) = true) :
    needsRevalidation (classify age maxAge swr) = true := by
  rw [classify_swr age maxAge swr h1 (served_staleness_bounded age maxAge swr h2)]
  rfl

/-- **Opt-in only.** With a zero window (no `stale-while-revalidate` directive) the
policy never serves stale — absence of the extension degrades to plain RFC 9111. -/
theorem no_directive_no_stale (age maxAge : Nat) :
    classify age maxAge 0 ≠ .staleRevalidate := by
  unfold classify
  by_cases h1 : age ≤ maxAge
  · rw [if_pos h1]; decide
  · rw [if_neg h1, if_neg (by omega : ¬ age ≤ maxAge + 0)]
    decide

/-! ## 2. The directive codec -/

/-- Is this byte an ASCII decimal digit? -/
def isDigitB (b : UInt8) : Bool := decide (48 ≤ b.toNat) && decide (b.toNat ≤ 57)

/-- The directive token TAIL (`"tale-while-revalidate="` — everything after the
leading `s`, split off so `swrTok ++ rest` is definitionally a `cons`). -/
def swrTokT : Bytes :=
  [116, 97, 108, 101, 45, 119, 104, 105, 108, 101, 45, 114, 101, 118, 97, 108,
   105, 100, 97, 116, 101, 61]

/-- The directive token `"stale-while-revalidate="` (lowercase, ASCII). -/
def swrTok : Bytes := 115 :: swrTokT

/-- Is `p` a prefix of `l`? -/
def isPrefixB (p l : Bytes) : Bool := p == l.take p.length

/-- **Parse the directive.** Scan a (lowercased) `Cache-Control` value for
`stale-while-revalidate=` and read the decimal digits after the `=`; `none` when the
directive is absent or carries no digits. -/
def findSwr : Bytes → Option Nat
  | [] => none
  | b :: t =>
    if isPrefixB swrTok (b :: t) then
      let ds := ((b :: t).drop swrTok.length).takeWhile isDigitB
      if ds.isEmpty then none else some (dval 0 ds)
    else findSwr t

/-- A list is a `isPrefixB`-prefix of itself appended with anything. -/
theorem isPrefixB_self_append (p r : Bytes) : isPrefixB p (p ++ r) = true := by
  simp [isPrefixB, List.take_left]

/-- `takeWhile` keeps a list all of whose elements satisfy the predicate. -/
theorem takeWhile_all {p : UInt8 → Bool} (l : Bytes) (h : ∀ b ∈ l, p b = true) :
    l.takeWhile p = l := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    have hx : p x = true := h x (List.mem_cons_self x t)
    simp [List.takeWhile_cons, hx,
          ih (fun b hb => h b (List.mem_cons_of_mem x hb))]

/-- Every byte of the serializer's decimal rendering is a digit (bridges
`Proto.Dec.natToDec_isDigit` to the parser's `isDigitB`). -/
theorem natToDec_all_digits (n : Nat) : ∀ b ∈ Proto.Dec.natToDec n, isDigitB b = true := by
  intro b hb
  obtain ⟨h1, h2⟩ := natToDec_isDigit n b hb
  simp only [isDigitB, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨h1, h2⟩

/-- The decimal rendering is never empty. -/
theorem natToDec_ne_nil (n : Nat) : Proto.Dec.natToDec n ≠ [] := by
  intro h
  have hd := dval_natToDec n
  rw [h] at hd
  -- `hd : dval 0 [] = n`, and `dval 0 []` is definitionally `0`
  have hn : n = 0 := hd.symm
  have h48 : Proto.Dec.natToDec 0 = [48] := by rw [natToDec_eq]; rfl
  rw [hn, h48] at h
  exact List.noConfusion h

/-- **Round-trip.** For EVERY `n`, parsing the rendered directive
`stale-while-revalidate=<Proto.Dec.natToDec n>` recovers exactly `n` — the parser inverts the
deployed serializer's decimal rendering (`Proto.Dec.dval_natToDec`). -/
theorem findSwr_render (n : Nat) : findSwr (swrTok ++ Proto.Dec.natToDec n) = some n := by
  have h1 : findSwr (swrTok ++ Proto.Dec.natToDec n)
      = if isPrefixB swrTok (swrTok ++ Proto.Dec.natToDec n) then
          (if (((swrTok ++ Proto.Dec.natToDec n).drop swrTok.length).takeWhile isDigitB).isEmpty
           then none
           else some (dval 0 (((swrTok ++ Proto.Dec.natToDec n).drop swrTok.length).takeWhile isDigitB)))
        else findSwr (swrTokT ++ Proto.Dec.natToDec n) := rfl
  have hne : (Proto.Dec.natToDec n).isEmpty = false := by
    cases hn : Proto.Dec.natToDec n with
    | nil => exact absurd hn (natToDec_ne_nil n)
    | cons a t => rfl
  rw [h1, List.drop_left, takeWhile_all (Proto.Dec.natToDec n) (natToDec_all_digits n),
      isPrefixB_self_append, hne]
  simp [dval_natToDec]

/-! ## 3. The emit-side stage -/

/-- ASCII-lowercase one byte. -/
def lowerByte (b : UInt8) : UInt8 := if 65 ≤ b && b ≤ 90 then b + 32 else b

/-- ASCII-lowercase a byte string. -/
def lower (bs : Bytes) : Bytes := bs.map lowerByte

/-- Lowercase field-name token `"cache-control"`. -/
def ccTok : Bytes := [99, 97, 99, 104, 101, 45, 99, 111, 110, 116, 114, 111, 108]

/-- The emitted field name `"Cache-Control"`. -/
def ccName : Bytes := [67, 97, 99, 104, 101, 45, 67, 111, 110, 116, 114, 111, 108]

/-- The emitted value `"max-age=60, stale-while-revalidate=30"`. -/
def defaultCc : Bytes :=
  [109, 97, 120, 45, 97, 103, 101, 61, 54, 48, 44, 32] ++ swrTok ++ [51, 48]

/-- Is this field name `Cache-Control` (case-insensitive)? -/
def isCc (name : Bytes) : Bool := lower name == ccTok

/-- Does the header list already carry a `Cache-Control` (case-insensitive)? -/
def hasCc (hs : List (Bytes × Bytes)) : Bool := hs.any (fun nv => isCc nv.1)

/-- Stamp the default stale-while-revalidate policy unless the origin set its own. -/
def stampCc (hs : List (Bytes × Bytes)) : List (Bytes × Bytes) :=
  if hasCc hs then hs else hs ++ [(ccName, defaultCc)]

/-- The appended entry is seen by the detector, whatever precedes it. -/
theorem hasCc_append (hs : List (Bytes × Bytes)) :
    hasCc (hs ++ [(ccName, defaultCc)]) = true := by
  unfold hasCc
  rw [List.any_append]
  have hlast : List.any [(ccName, defaultCc)] (fun nv => isCc nv.1) = true := by decide
  rw [hlast, Bool.or_true]

/-- **Presence.** After stamping, a `Cache-Control` is present — for ANY headers. -/
theorem stampCc_has (hs : List (Bytes × Bytes)) : hasCc (stampCc hs) = true := by
  unfold stampCc
  by_cases h : hasCc hs = true
  · rw [if_pos h]; exact h
  · rw [if_neg h]; exact hasCc_append hs

/-- **No clobber.** An origin-set `Cache-Control` is returned UNCHANGED — the edge
never rewrites an explicit caching policy. -/
theorem stampCc_noop (hs : List (Bytes × Bytes)) (h : hasCc hs = true) :
    stampCc hs = hs := by
  unfold stampCc; rw [if_pos h]

/-- **Append-only.** The original headers are a prefix of the stamped list. -/
theorem stampCc_prefix (hs : List (Bytes × Bytes)) : hs <+: stampCc hs := by
  unfold stampCc
  by_cases h : hasCc hs = true
  · rw [if_pos h]
    exact List.prefix_refl hs
  · rw [if_neg h]
    exact List.prefix_append hs _

/-- **Idempotence.** Stamping a stamped list changes nothing. -/
theorem stampCc_idem (hs : List (Bytes × Bytes)) :
    stampCc (stampCc hs) = stampCc hs :=
  stampCc_noop _ (stampCc_has hs)

/-- The response transform: stamp the policy onto a `200`, touch nothing else. -/
def applyCc (r : Response) : Response :=
  if r.status == 200 then { r with headers := stampCc r.headers } else r

/-- The transform never changes the status. -/
theorem applyCc_status (r : Response) : (applyCc r).status = r.status := by
  unfold applyCc; split <;> rfl

/-- A `200` leaves the transform carrying a `Cache-Control`. -/
theorem applyCc_200_has (r : Response) (h : r.status = 200) :
    hasCc (applyCc r).headers = true := by
  unfold applyCc
  rw [if_pos (show (r.status == 200) = true by rw [h]; rfl)]
  exact stampCc_has r.headers

/-- A non-`200` passes through untouched (no policy invented for errors/redirects). -/
theorem applyCc_non200 (r : Response) (h : (r.status == 200) = false) :
    applyCc r = r := by
  unfold applyCc; rw [h]; rfl

/-- An origin-set `Cache-Control` passes through byte-identical, whatever the status. -/
theorem applyCc_no_clobber (r : Response) (h : hasCc r.headers = true) :
    applyCc r = r := by
  unfold applyCc
  split
  · rw [stampCc_noop r.headers h]
  · rfl

/-- **The stale-while-revalidate stage.** Request phase: pass through. Response
phase: `applyCc` on the finalized response (one affine `mapResp`). Never gates. -/
def swrStage : Stage where
  name := "stale-while-revalidate"
  onRequest := fun c => .continue c
  onResponse := fun _ b => b.mapResp applyCc

/-- **The byte-effect.** The stage's response phase is exactly `applyCc` on the
finalized response, for ANY tail and handler. -/
theorem swrStage_effect (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    (runPipeline (swrStage :: rest) h c).build
      = applyCc ((runPipeline rest h c).build) := by
  rw [pipeline_stage_effect swrStage rest h c c rfl]
  rfl

/-- The stage never changes the status — safe to braid into a status-stable onion. -/
theorem swrStage_statusStable : swrStage.statusStable :=
  fun _ b => applyCc_status b.build

/-! ## End-to-end witnesses (non-vacuous) -/

/-- A bare 200 with one unrelated header (`X: Y`) and no caching policy. -/
def bareHandler : Ctx → Response :=
  fun _ => { status := 200, reason := [], headers := [([88], [89])], body := [] }

/-- A 200 whose origin already set `Cache-Control: no-store`. -/
def originCcHandler : Ctx → Response :=
  fun _ => { status := 200, reason := [],
             headers := [(ccName, [110, 111, 45, 115, 116, 111, 114, 101])], body := [] }

/-- A 304 with no headers. -/
def notModifiedHandler : Ctx → Response :=
  fun _ => { status := 304, reason := [], headers := [], body := [] }

/-- An empty request context. -/
def demoCtx : Ctx := { input := [], req := {}, attrs := [] }

/-- **End-to-end.** The single-stage pipeline serves the bare `200` with EXACTLY the
original header followed by the default policy — appended, nothing else touched. -/
theorem demo_stamps :
    ((runPipeline [swrStage] bareHandler demoCtx).build).headers
      = [([88], [89]), (ccName, defaultCc)] := by decide

/-- **End-to-end, no clobber.** An origin `Cache-Control: no-store` passes through
byte-identical. -/
theorem demo_no_clobber :
    ((runPipeline [swrStage] originCcHandler demoCtx).build).headers
      = [(ccName, [110, 111, 45, 115, 116, 111, 114, 101])] := by decide

/-- **End-to-end, non-200.** A `304` gains no invented policy. -/
theorem demo_non200_untouched :
    ((runPipeline [swrStage] notModifiedHandler demoCtx).build).headers = [] := by
  decide

/-- **The emitted value parses back.** The exact bytes this stage stamps carry a
`stale-while-revalidate=30` the parser recovers (emit and consume sides agree). -/
theorem demo_emitted_parses : findSwr defaultCc = some 30 := by decide

/-- **The promised window classifies correctly** (`maxAge=60`, `swr=30`): age 50 is
fresh, age 70 is stale-served-with-revalidation, age 95 is expired. -/
theorem demo_window :
    classify 50 60 30 = .fresh
      ∧ classify 70 60 30 = .staleRevalidate
      ∧ classify 95 60 30 = .expired := by decide

#print axioms Reactor.Stage.StaleWhileRevalidate.classify_fresh
#print axioms Reactor.Stage.StaleWhileRevalidate.classify_swr
#print axioms Reactor.Stage.StaleWhileRevalidate.classify_expired
#print axioms Reactor.Stage.StaleWhileRevalidate.served_staleness_bounded
#print axioms Reactor.Stage.StaleWhileRevalidate.stale_serve_revalidates
#print axioms Reactor.Stage.StaleWhileRevalidate.no_directive_no_stale
#print axioms Reactor.Stage.StaleWhileRevalidate.findSwr_render
#print axioms Reactor.Stage.StaleWhileRevalidate.stampCc_has
#print axioms Reactor.Stage.StaleWhileRevalidate.stampCc_noop
#print axioms Reactor.Stage.StaleWhileRevalidate.stampCc_idem
#print axioms Reactor.Stage.StaleWhileRevalidate.applyCc_no_clobber
#print axioms Reactor.Stage.StaleWhileRevalidate.swrStage_effect
#print axioms Reactor.Stage.StaleWhileRevalidate.swrStage_statusStable
#print axioms Reactor.Stage.StaleWhileRevalidate.demo_stamps
#print axioms Reactor.Stage.StaleWhileRevalidate.demo_emitted_parses
#print axioms Reactor.Stage.StaleWhileRevalidate.demo_window

end Reactor.Stage.StaleWhileRevalidate
