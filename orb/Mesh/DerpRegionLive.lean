/-
# DerpRegionLive — driving the proven DERP region selection (no crypto, `me.*` inert)

The coordination server hands each node a **DERP map** of relay regions
(`Control.Derp.DerpMap` / `DerpRegion` — the distribution soundness proven in
`Control/Derp.lean`). A node then runs a `netcheck`-style latency probe against
those regions and picks its **home** region: the reachable region with the lowest
measured round-trip latency (the `preferredDERP` home). A region that is *down*
does not answer the probe, so it is simply absent from the latency report; when the
current home goes down, the node re-runs selection over the regions that remain and
**fails over** to the next lowest-latency reachable region.

Region selection is pure, inert, latency-arithmetic — **no crypto**. This module
models it as a total function over the ground-truth `Control.Derp` map, proves the
two selection properties, and drives them in a runnable selftest:

  * `derp_region_selects_reachable` — the selected home is a region that actually
    answered the probe (reachable), and no reachable region has lower latency; and
    if every probed region is a real member of the distributed map, the home is a
    genuine map region (`derp_home_is_map_region`).
  * `derp_region_failover` — after a region goes down (drops out of the report),
    the newly selected home is *not* the downed region, is still a genuinely
    reachable region, and is the lowest-latency region among those still up.

## Honesty / realization boundary

This is a `me.*`-inert, **no-crypto** lane: region selection is *client-side*
latency arithmetic (`netcheck` → `preferredDERP`), not a wire endpoint the
dataplane serves — there is nothing on a socket to open and no HTTP route to
`curl`. The selftest therefore drives the PROVEN pure selection on the real
`Control.Derp` map structures and cross-checks each decision against an independent
brute-force oracle (a fold that recomputes the minimum), witnessing on concrete
data exactly what `derp_region_selects_reachable` / `derp_region_failover` prove.
It calls **no** FFI and **no** crypto. (Finding: the deployed engine exposes no
region-selection endpoint to curl — this is correct; preferredDERP is a node-local
netcheck decision, not a served resource, so `prove-what-runs` here is the
interpreter run of the pure logic against the proof, quoted below.)

Usage:
  derp-region-live selftest
-/
import Control.Derp

namespace DerpRegionLive

open Control.Derp

/-! ## The region-selection model (inert, pure, no crypto) -/

/-- A DERP **latency report** (the output of a `netcheck` probe): for every region
that answered, the round-trip latency the node measured, in milliseconds. A region
that is down / unreachable is *absent* — the probe got no reply. -/
abbrev Report := List (Nat × Nat)

/-- The reachable region of least latency. The head wins ties (`≤`), so the choice
is deterministic and stable — a leftmost, lowest-latency region. `none` iff the
report is empty (nothing is reachable). -/
def bestRegion : Report → Option (Nat × Nat)
  | [] => none
  | (id, lat) :: t =>
    match bestRegion t with
    | none => some (id, lat)
    | some (bid, blat) => if lat ≤ blat then some (id, lat) else some (bid, blat)

/-- `preferredDERP`: the home region id a latency report selects — the lowest-latency
reachable region, or `none` if the node reached no region (fail-closed: no home). -/
def selectHome (r : Report) : Option Nat := (bestRegion r).map (·.1)

/-! ## Selection is sound: reachable, minimal, and a real map region -/

/-- A non-empty report always selects some region (selection never fails when at
least one region is reachable). -/
theorem bestRegion_cons_ne_none (a : Nat × Nat) (t : Report) :
    bestRegion (a :: t) ≠ none := by
  obtain ⟨id, lat⟩ := a
  simp only [bestRegion]
  split
  · simp
  · split <;> simp

/-- The selected region genuinely appears in the report — it is reachable, not
fabricated. -/
theorem bestRegion_mem : ∀ (r : Report) (p : Nat × Nat),
    bestRegion r = some p → p ∈ r := by
  intro r
  induction r with
  | nil => intro p h; simp [bestRegion] at h
  | cons hd t ih =>
    obtain ⟨hid, hlat⟩ := hd
    intro p h
    simp only [bestRegion] at h
    cases hb : bestRegion t with
    | none =>
      simp only [hb, Option.some.injEq] at h
      subst h
      exact List.mem_cons.mpr (Or.inl rfl)
    | some bp =>
      obtain ⟨bid, blat⟩ := bp
      simp only [hb] at h
      split at h
      · simp only [Option.some.injEq] at h; subst h
        exact List.mem_cons.mpr (Or.inl rfl)
      · simp only [Option.some.injEq] at h; subst h
        exact List.mem_cons.mpr (Or.inr (ih (bid, blat) hb))

/-- The selected region's latency is `≤` every reachable region's latency — it is a
genuine minimum, so no reachable region is closer. -/
theorem bestRegion_min : ∀ (r : Report) (id lat : Nat),
    bestRegion r = some (id, lat) → ∀ q ∈ r, lat ≤ q.2 := by
  intro r
  induction r with
  | nil => intro id lat h; simp [bestRegion] at h
  | cons hd t ih =>
    obtain ⟨hid, hlat⟩ := hd
    intro id lat h q hq
    simp only [bestRegion] at h
    cases hb : bestRegion t with
    | none =>
      -- `bestRegion t = none` forces `t = []`, so the only member is the head.
      have ht : t = [] := by
        cases t with
        | nil => rfl
        | cons a t' => exact absurd hb (bestRegion_cons_ne_none a t')
      subst ht
      simp only [hb, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, e2⟩ := h
      simp only [List.mem_singleton] at hq
      subst hq
      show lat ≤ hlat
      omega
    | some bp =>
      obtain ⟨bid, blat⟩ := bp
      have ihb : ∀ q ∈ t, blat ≤ q.2 := ih bid blat hb
      simp only [hb] at h
      split at h
      · rename_i hle
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, e2⟩ := h
        rcases List.mem_cons.mp hq with hqh | hqt
        · subst hqh; show lat ≤ hlat; omega
        · have := ihb q hqt; omega
      · rename_i hgt
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, e2⟩ := h
        rcases List.mem_cons.mp hq with hqh | hqt
        · subst hqh; show lat ≤ hlat; omega
        · have := ihb q hqt; omega

/-- **Selection picks a reachable, lowest-latency region.** If a report selects home
`rid`, then `rid` answered the probe (is a member of the report) with some latency
`lat`, and no reachable region has latency below `lat`. -/
theorem derp_region_selects_reachable (r : Report) (rid : Nat)
    (h : selectHome r = some rid) :
    ∃ lat, (rid, lat) ∈ r ∧ ∀ q ∈ r, lat ≤ q.2 := by
  unfold selectHome at h
  cases hb : bestRegion r with
  | none => rw [hb] at h; simp at h
  | some p =>
    obtain ⟨bid, blat⟩ := p
    rw [hb] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    exact ⟨blat, bestRegion_mem r (bid, blat) hb, bestRegion_min r bid blat hb⟩

/-- **The selected home is a genuine map region.** If every probed region is a real
member of the distributed `DerpMap`, then the selected home is too — selection never
routes the node to a region outside the map it was handed. Ties selection to the
ground-truth `Control.Derp` distribution. -/
theorem derp_home_is_map_region (dm : DerpMap) (r : Report) (rid : Nat)
    (hcov : ∀ q ∈ r, dm.hasRegion q.1 = true)
    (h : selectHome r = some rid) :
    dm.hasRegion rid = true := by
  obtain ⟨lat, hmem, _⟩ := derp_region_selects_reachable r rid h
  exact hcov (rid, lat) hmem

/-! ## Failover: a downed region routes to the next reachable one -/

/-- **Failover to the next reachable region.** When region `down` goes down it drops
out of the report; selecting over what remains yields a home `rid` that (1) is *not*
the downed region, (2) is still a genuinely reachable region of the original report,
and (3) is the lowest-latency region among all regions that did **not** go down. So
losing the current home fails the node over to the next-best reachable region. -/
theorem derp_region_failover (r : Report) (down rid : Nat)
    (h : selectHome (r.filter (fun p => p.1 != down)) = some rid) :
    rid ≠ down ∧ ∃ lat, (rid, lat) ∈ r ∧ ∀ q ∈ r, q.1 ≠ down → lat ≤ q.2 := by
  obtain ⟨lat, hmem, hmin⟩ := derp_region_selects_reachable _ rid h
  rw [List.mem_filter] at hmem
  obtain ⟨hin, hne⟩ := hmem
  refine ⟨by simpa using hne, lat, hin, ?_⟩
  intro q hq hqne
  have hqf : q ∈ r.filter (fun p => p.1 != down) := by
    rw [List.mem_filter]
    exact ⟨hq, by simpa using hqne⟩
  exact hmin q hqf

#print axioms derp_region_selects_reachable
#print axioms derp_home_is_map_region
#print axioms derp_region_failover

/-! ## Non-vacuous evaluation — a concrete 4-region netcheck exercised

Four regions in the distributed map: NYC (1), SFO (2), LHR (3), SIN (4). The node's
netcheck measures NYC=34ms, SFO=12ms, LHR=88ms, SIN=150ms. SFO is closest ⇒ home 2.
SFO then goes down ⇒ home fails over to NYC (1, next lowest). NYC also down ⇒ LHR (3).
All four down ⇒ no home (fail-closed). Every selected home is a real map region. -/

private def regionsDemo : List DerpRegion :=
  [ { regionID := 1, regionCode := "nyc".toUTF8.toList, nodes := [] },
    { regionID := 2, regionCode := "sfo".toUTF8.toList, nodes := [] },
    { regionID := 3, regionCode := "lhr".toUTF8.toList, nodes := [] },
    { regionID := 4, regionCode := "sin".toUTF8.toList, nodes := [] } ]

private def mapDemo : DerpMap := { regions := regionsDemo }

private def reportDemo : Report := [(1, 34), (2, 12), (3, 88), (4, 150)]

-- SFO (region 2) is closest — it becomes home.
#guard selectHome reportDemo = some 2
-- The selected home is a real region of the distributed map.
#guard mapDemo.hasRegion 2 = true
-- SFO goes down: fail over to NYC (region 1), the next lowest latency.
#guard selectHome (reportDemo.filter (fun p => p.1 != 2)) = some 1
-- NYC also down: fail over to LHR (region 3).
#guard selectHome ((reportDemo.filter (fun p => p.1 != 2)).filter (fun p => p.1 != 1)) = some 3
-- Every region down: no reachable region ⇒ no home (fail-closed).
#guard selectHome [] = none
-- The home never leaves the map.
#guard (selectHome reportDemo).map mapDemo.hasRegion = some true

end DerpRegionLive

/-! ## The runnable selftest -/

open DerpRegionLive Control.Derp

/-- Independent oracle: recompute the minimum-latency region by a left fold that
replaces only on a *strictly* smaller latency (keeps the leftmost minimum) — a
different recursion from `bestRegion`, so agreement is a real cross-check, not a
restatement. -/
def oracleBest (r : Report) : Option (Nat × Nat) :=
  r.foldl (fun acc p =>
    match acc with
    | none => some p
    | some b => if p.2 < b.2 then some p else acc) none

/-- Render a report as `code=lat` using a region map, for legible output. -/
def showReport (dm : DerpMap) (r : Report) : String :=
  String.intercalate "  " (r.map (fun p =>
    let code := (dm.lookup p.1).map (fun rg => (String.fromUTF8? (⟨rg.regionCode.toArray⟩)).getD s!"r{p.1}")
    s!"{code.getD s!"r{p.1}"}={p.2}ms"))

def selftest : IO UInt32 := do
  IO.println "== derp-region-live selftest : DERP region selection (netcheck preferredDERP), no crypto =="
  let regions : List DerpRegion :=
    [ { regionID := 1, regionCode := "nyc".toUTF8.toList, nodes := [] },
      { regionID := 2, regionCode := "sfo".toUTF8.toList, nodes := [] },
      { regionID := 3, regionCode := "lhr".toUTF8.toList, nodes := [] },
      { regionID := 4, regionCode := "sin".toUTF8.toList, nodes := [] } ]
  let dm : DerpMap := { regions := regions }
  let report : Report := [(1, 34), (2, 12), (3, 88), (4, 150)]
  IO.println s!"distributed DERP map : {regions.length} regions ({String.intercalate ", " (regions.map (fun rg => s!"{rg.regionID}"))})"
  IO.println s!"netcheck latencies   : {showReport dm report}"

  -- ── selection: lowest-latency reachable region becomes home ──
  let some home := selectHome report
    | do IO.eprintln "FAIL: no home selected from a non-empty report"; return 1
  let some (obid, oblat) := oracleBest report
    | do IO.eprintln "FAIL: oracle produced no region"; return 1
  let selMatchesOracle := home == obid
  -- the two selection-soundness facts, witnessed on the bytes:
  let reachable := report.any (fun p => p.1 == home)
  let homeLat := (report.find? (fun p => p.1 == home)).map (·.2)
  let minimal := match homeLat with
    | some hl => report.all (fun p => hl ≤ p.2)
    | none => false
  let realRegion := dm.hasRegion home
  IO.println s!"\n-- selection (derp_region_selects_reachable) --"
  IO.println s!"selected home region : {home}  (oracle fold: {obid} @ {oblat}ms)"
  IO.println s!"home == oracle min   : {selMatchesOracle}"
  IO.println s!"home is reachable    : {reachable}"
  IO.println s!"home is lowest-latency: {minimal}"
  IO.println s!"home is a real map region (derp_home_is_map_region): {realRegion}"

  -- ── failover: the home goes down, selection moves to the next ──
  IO.println s!"\n-- failover (derp_region_failover) --"
  let mut cur := report
  let mut chain : List Nat := []
  let mut ok := true
  -- knock out the current home region by region; each time re-select over what remains
  for _ in [0, 1, 2, 3] do
    match selectHome cur with
    | none => ok := false
    | some h =>
      chain := chain ++ [h]
      let downFilter := cur.filter (fun p => p.1 != h)
      -- the failover theorem's guarantees, witnessed:
      let nextSel := selectHome downFilter
      let notSame := match nextSel with | some h2 => h2 != h | none => true
      IO.println s!"home {h} DOWN -> next home {nextSel}  (next ≠ down : {notSame})"
      if !notSame then ok := false
      cur := downFilter
  -- after all reachable regions are exhausted, no home (fail-closed)
  let exhausted := selectHome (report.filter (fun p => !(chain.contains p.1)))
  IO.println s!"selection chain      : {chain}  (SFO->NYC->LHR->SIN by ascending latency)"
  IO.println s!"all-down -> no home  : {exhausted == none}"

  let failoverOk := chain == [2, 1, 3, 4] && exhausted == none
  let selectionOk := selMatchesOracle && reachable && minimal && realRegion

  IO.println ""
  if selectionOk && failoverOk && ok then do
    IO.println "PASS — lowest-latency reachable region selected as home; each downed region"
    IO.println "       fails over to the next reachable region (2->1->3->4), all-down = no home;"
    IO.println "       every decision equals the proven model (derp_region_selects_reachable,"
    IO.println "       derp_region_failover, derp_home_is_map_region), no crypto, no FFI."
    return 0
  else do
    IO.eprintln "FAIL — a selection/failover decision did not cross-check against the model."
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["selftest"] => selftest
  | _ => do IO.eprintln "usage: derp-region-live selftest"; return 1
