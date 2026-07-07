/-
MaxConn — per-upstream connection-cap enforcement at selection time.

A reference proxy lets each upstream declare a maximum number of concurrent
connections; a backend at its cap must not receive NEW connections (existing
ones are untouched — the same new-work-only semantics as `Status.draining`).
What happens to the refused request (queue, spill to another tier, 503) is
dataplane policy; this module owns the SELECTION-side guarantee: a capped-out
backend is never chosen.

The cap travels as a map `cap : Nat → Option Nat` from backend identity to its
configured limit (`none` = unlimited), so the `Backend` snapshot itself is
unchanged. Enforcement is a pool refinement: filter to the under-cap subset,
then run the ordinary tiered selector — which keeps every existing selection
theorem applicable to the refined pool.

Theorems:

  * `selectCapped_under_cap` / `selectChainCapped_under_cap` — **the cap
    binds**: a chosen backend is strictly below its configured limit;
  * `selectCapped_eligible` — the capped selector still only picks eligible
    members of the original list (cap refines, never widens);
  * `selectCapped_leastConn_total` — **totality survives the cap**: an
    eligible under-cap backend exists ⇒ selection succeeds;
  * `capPool_unlimited` / `selectCapped_unlimited` — **conservativity**: with
    no caps configured the capped selector IS the plain selector;
  * `capPool_all_capped` — when every backend is at its cap the pool is empty
    and selection yields `none` — the "queue or 503" verdict is explicit,
    never a silent overload of a full backend.
-/

import Proxy.Balance

namespace Proxy

/-- A per-upstream connection-cap table: backend id ↦ configured maximum
concurrent connections (`none` = unlimited). -/
abbrev CapTable := Nat → Option Nat

/-- `b` may accept a NEW connection under `cap`: unlimited, or strictly below
its limit. At `conns = limit` the backend is full — the next connection would
exceed the cap. -/
def underCap (cap : CapTable) (b : Backend) : Bool :=
  match cap b.id with
  | none => true
  | some m => b.conns < m

theorem underCap_spec {cap : CapTable} {b : Backend}
    (h : underCap cap b = true) : ∀ m, cap b.id = some m → b.conns < m := by
  intro m hm
  simp only [underCap, hm] at h
  simpa using h

/-- The under-cap subset of a pool. -/
def capPool (cap : CapTable) (bs : List Backend) : List Backend :=
  bs.filter (underCap cap)

theorem mem_capPool {cap : CapTable} {bs : List Backend} {b : Backend} :
    b ∈ capPool cap bs ↔ b ∈ bs ∧ underCap cap b = true := List.mem_filter

/-- The capped tiered selector: enforce the caps, then select as usual. -/
def selectCapped (p : Policy) (ctx : Ctx) (cap : CapTable)
    (bs : List Backend) : Option Backend :=
  select p ctx (capPool cap bs)

/-- The capped policy chain. -/
def selectChainCapped (ps : List Policy) (ctx : Ctx) (cap : CapTable)
    (bs : List Backend) : Option Backend :=
  selectChain ps ctx (capPool cap bs)

/-- **The cap binds.** A backend chosen by the capped selector is strictly
below its configured connection limit. -/
theorem selectCapped_under_cap {p : Policy} {ctx : Ctx} {cap : CapTable}
    {bs : List Backend} {b : Backend} (h : selectCapped p ctx cap bs = some b) :
    ∀ m, cap b.id = some m → b.conns < m :=
  underCap_spec (mem_capPool.mp (select_eligible h).1).2

/-- **The cap binds through a chain.** -/
theorem selectChainCapped_under_cap {ps : List Policy} {ctx : Ctx}
    {cap : CapTable} {bs : List Backend} {b : Backend}
    (h : selectChainCapped ps ctx cap bs = some b) :
    ∀ m, cap b.id = some m → b.conns < m :=
  underCap_spec (mem_capPool.mp (selectChain_eligible h).1).2

/-- The capped selector refines, never widens: its verdicts are eligible
members of the ORIGINAL list. -/
theorem selectCapped_eligible {p : Policy} {ctx : Ctx} {cap : CapTable}
    {bs : List Backend} {b : Backend} (h : selectCapped p ctx cap bs = some b) :
    b ∈ bs ∧ b.eligible = true :=
  let spec := select_eligible h
  ⟨(mem_capPool.mp spec.1).1, spec.2⟩

/-- **Totality survives the cap** (least-connections link): an eligible
backend with headroom exists ⇒ selection succeeds. -/
theorem selectCapped_leastConn_total {ctx : Ctx} {cap : CapTable}
    {bs : List Backend} {w : Backend} (hmem : w ∈ bs)
    (helig : w.eligible = true) (hcap : underCap cap w = true) :
    (selectCapped .leastConnections ctx cap bs).isSome :=
  select_leastConn_total (mem_capPool.mpr ⟨hmem, hcap⟩) helig

/-- With no caps configured, the refinement is the identity on pools. -/
theorem capPool_unlimited {bs : List Backend} {cap : CapTable}
    (h : ∀ i, cap i = none) : capPool cap bs = bs := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    have hb : underCap cap b = true := by simp [underCap, h b.id]
    simp [capPool, List.filter, hb] at ih ⊢
    exact ih

/-- **Conservativity.** With no caps configured, the capped selector is the
plain tiered selector. -/
theorem selectCapped_unlimited {p : Policy} {ctx : Ctx} {cap : CapTable}
    {bs : List Backend} (h : ∀ i, cap i = none) :
    selectCapped p ctx cap bs = select p ctx bs := by
  unfold selectCapped
  rw [capPool_unlimited h]

/-- When every backend is full, the pool is empty: selection can only answer
`none` — overload is surfaced, never absorbed by a full backend. -/
theorem capPool_all_capped {bs : List Backend} {cap : CapTable}
    (h : ∀ b ∈ bs, underCap cap b = false) : capPool cap bs = [] := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    have hb := h b (List.mem_cons_self b rest)
    have hrest : ∀ c ∈ rest, underCap cap c = false :=
      fun c hc => h c (List.mem_cons_of_mem _ hc)
    have htail : capPool cap rest = [] := ih hrest
    simp only [capPool, List.filter, hb]
    exact htail

end Proxy
