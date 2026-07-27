/-
CanaryRoute — deterministic canary / weighted-deployment routing.

A canary rollout runs two versions of an upstream behind one route: the
established `stable` version and the new `canary` version. A configured canary
*weight* `W` out of a bucket count `total` selects the fraction `W / total` of
traffic that reaches the canary; the remainder stays on stable.

Routing is a pure function of a *request key* alone (client id / cookie /
header hash — whatever the operator keys affinity on), hashed by an opaque
oracle `hashKey` and reduced to a bucket in `[0, total)`. The low `W` buckets
are canary. Two consequences the operator relies on:

  * a request key ALWAYS lands on the same version (`canary_sticky`) — the
    version is a function of the key, so retries, follow-up requests, and other
    varying request fields (sequence, timestamp) never flip a session between
    versions mid-rollout;
  * exactly `W` of the `total` buckets are canary (`canary_split`) — the split
    is exact over the bucket space, so with a uniform key hash the canary sees
    the intended `W / total` share. Distribution quality of `hashKey` is a
    statistical property, measured not proved; every theorem here holds for
    EVERY `hashKey : Nat → Nat`, so nothing depends on it.

`hashKey` is an opaque oracle: it appears only as a universally-quantified
function parameter, never axiomatized and never invoked with an invented
implementation. The theorems constrain the routing DECISION structure around
the hash, not the hash itself.

Boundary cases are pinned: weight `0` sends nothing to the canary
(`canary_zero_no_canary`, the "rollout not yet started" state) and a weight at
or above `total` sends everything (`canary_full`, the "promoted" state).

The exact-count proof reuses the self-contained window counter `cnt` and its
split/congruence lemmas from `Proxy.Wrr` (the same machinery that proves WRR
exact window fairness) — canary weighting is the two-version specialization of
weighted selection over a fixed key.
-/

import Proxy.Wrr

namespace Proxy.Canary

/-- The two deployment versions behind a canary route. -/
inductive Version where
  | stable
  | canary
deriving DecidableEq, Repr

/-- A request as the router sees it: the affinity `key` the version decision is
made on, plus other fields (`seq`: sequence number / timestamp / retry index)
that MUST NOT influence the version — that non-influence is `canary_sticky`. -/
structure Request where
  key : Nat
  seq : Nat
deriving DecidableEq, Repr

/-- Canary deployment config: `weight` of the `total` buckets route to the
canary version, the rest to stable. `weight = 0` is a dormant rollout;
`total ≤ weight` is a completed promotion. -/
structure Deploy where
  weight : Nat
  total : Nat
deriving DecidableEq, Repr

/-- The bucket a key lands in: the opaque key hash reduced modulo the bucket
count. -/
def bucket (hashKey : Nat → Nat) (d : Deploy) (key : Nat) : Nat :=
  hashKey key % d.total

/-- Route a bucket: the low `weight` buckets are canary, the rest stable. -/
def bucketRoute (d : Deploy) (r : Nat) : Version :=
  if r < d.weight then .canary else .stable

/-- The router: hash the request key, route by its bucket. The whole decision
is a function of `req.key` (and the config) — nothing else about the request. -/
def route (hashKey : Nat → Nat) (d : Deploy) (req : Request) : Version :=
  bucketRoute d (bucket hashKey d req.key)

/-! ### Determinism / stickiness -/

/-- Routing depends only on the affinity key: two requests with equal keys get
the same version regardless of any other request field. A session keyed on a
stable value therefore never oscillates between stable and canary across
retries or follow-ups. -/
theorem canary_sticky (hashKey : Nat → Nat) (d : Deploy) (req₁ req₂ : Request)
    (h : req₁.key = req₂.key) : route hashKey d req₁ = route hashKey d req₂ := by
  simp only [route, bucket, h]

/-- The version decision is exactly `bucket < weight`, tying the canary verdict
to the hash of the key. -/
theorem route_canary_iff (hashKey : Nat → Nat) (d : Deploy) (req : Request) :
    route hashKey d req = Version.canary
      ↔ hashKey req.key % d.total < d.weight := by
  simp only [route, bucket, bucketRoute]
  split
  · rename_i h; simp [h]
  · rename_i h; simp [h]

/-! ### Boundary cases -/

/-- **Dormant rollout.** Weight `0` routes NOTHING to the canary. -/
theorem canary_zero_no_canary (hashKey : Nat → Nat) (d : Deploy) (req : Request)
    (h : d.weight = 0) : route hashKey d req = Version.stable := by
  simp only [route, bucket, bucketRoute, h]
  simp

/-- **Completed promotion.** A weight at or above `total` (with a nonempty
bucket space) routes EVERYTHING to the canary — every bucket is below the
weight. -/
theorem canary_full (hashKey : Nat → Nat) (d : Deploy) (req : Request)
    (ht : 0 < d.total) (h : d.total ≤ d.weight) :
    route hashKey d req = Version.canary := by
  have hb : hashKey req.key % d.total < d.total := Nat.mod_lt _ ht
  simp only [route, bucket, bucketRoute]
  rw [if_pos (by omega)]

/-! ### Exact split -/

/-- **Exact canary share.** Over the whole bucket space `[0, total)`, exactly
`weight` buckets route to the canary. The split is exact (not ±1): with a
uniform key hash the canary receives precisely the `weight / total` fraction of
keys, and the stable version the rest.

Proved via the `Proxy.Wrr` window counter: the canary predicate on a bucket is
exactly `bucket < weight`, which is `true` on the first `weight` buckets and
`false` afterwards. -/
theorem canary_split (d : Deploy) (h : d.weight ≤ d.total) :
    cnt (fun r => decide (bucketRoute d r = Version.canary)) d.total = d.weight := by
  have hpred : (fun r => decide (bucketRoute d r = Version.canary))
      = (fun r => decide (r < d.weight)) := by
    funext r
    by_cases hr : r < d.weight
    · simp [bucketRoute, hr]
    · simp [bucketRoute, hr]
  rw [hpred]
  have hsplit : d.total = d.weight + (d.total - d.weight) := by omega
  rw [hsplit, cnt_split]
  have h1 : cnt (fun r => decide (r < d.weight)) d.weight = d.weight := by
    rw [cnt_congr (q := fun _ => true) (fun j hj => by simp [hj])]
    exact cnt_true _
  have h2 : cnt (fun j => decide (d.weight + j < d.weight)) (d.total - d.weight)
      = 0 := by
    rw [cnt_congr (q := fun _ => false) (fun j _ => by simp)]
    exact cnt_false _
  rw [h1, h2]; omega

/-- The stable side is the complement: over `[0, total)` exactly `total -
weight` buckets stay on stable. -/
theorem stable_split (d : Deploy) (h : d.weight ≤ d.total) :
    cnt (fun r => decide (bucketRoute d r = Version.stable)) d.total
      = d.total - d.weight := by
  have hpred : (fun r => decide (bucketRoute d r = Version.stable))
      = (fun r => decide (¬ r < d.weight)) := by
    funext r
    by_cases hr : r < d.weight
    · simp [bucketRoute, hr]
    · simp [bucketRoute, hr]
  rw [hpred]
  have hsplit : d.total = d.weight + (d.total - d.weight) := by omega
  rw [hsplit, cnt_split]
  have h1 : cnt (fun r => decide (¬ r < d.weight)) d.weight = 0 := by
    rw [cnt_congr (q := fun _ => false) (fun j hj => by simp [hj])]
    exact cnt_false _
  have h2 : cnt (fun j => decide (¬ d.weight + j < d.weight)) (d.total - d.weight)
      = d.total - d.weight := by
    rw [cnt_congr (q := fun _ => true) (fun j _ => by simp)]
    exact cnt_true _
  rw [h1, h2]; omega

end Proxy.Canary
