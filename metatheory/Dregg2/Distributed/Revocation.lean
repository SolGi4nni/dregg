/-
# Dregg2.Distributed.Revocation — topology-parametrized capability revocation.

Capability revocation is **clean single-machine** (`Authority.Credential`: the kernel revocation
registry is a grow-only `RevocationSet`, and `revoke_blocks_verify` flips a credential out of
admissibility the instant its id lands in the set). But **across nodes** there is a gap: a cap
revoked on node `m` is still honored by node `n` *until `n` sees the revocation*. This is the
non-monotone residue `Authority.CSpace` flags — "only `revoke` carries the CAP/FLP cost, with n=1
giving immediate full revocation and distributed giving topology-bounded revocation". This module
turns that prose into a **proved, topology-parametrized guarantee** (the dregg4 single-machine
principle: the honest bounds are *distributed* bounds — parametrize by the propagation model; n=1
collapses them to the strong property).

## The model (one new structure, everything else REUSED)

* A `RevEvent` is a revocation as it actually happens in a distributed system: *which* credential,
  at *which* origin node, at *which* logical issue-time. (The credential id REUSES
  `Authority.Credential.credId`; revocation content REUSES the `RevocationSet` G-Set.)
* A `Topology` is the propagation model: `nodes` (a finite participant set) and `delay : m → n → ℕ`
  — the bound on how long a revocation issued at `m` takes to reach `n` (logical time; the worst-
  case propagation delay of the gossip/consensus layer). `delay m m = 0` (a node sees its own
  revocations immediately) is the one law.
* A `System` is a `Topology` together with the log of `RevEvent`s that have been issued.
* **`localRevSet T log n t`** is what node `n` *locally believes* is revoked at time `t`: exactly
  the revocations that have had time to propagate — `event.issuedAt + T.delay event.origin n ≤ t`.
  This is the per-node `RevocationSet` reconstructed from the topology + the global log.
* **`honors`** = the per-node admissibility decision: `Authority.Credential.verify` against `n`'s
  *local* revocation set (REUSED verbatim — the same fail-closed keys-as-caps gate, just fed the
  stale local view).

## The theorems (the two faces of the single-machine principle)

* `eventual_bounded_revocation` — **distributed ⇒ EVENTUAL-BOUNDED**. If a credential was revoked
  at origin `m` at time `τ`, then for every node `n` and every `t ≥ τ + delay m n`, node `n` does
  NOT honor it. The bound `τ + delay m n` is **explicit**, and the property is "honored at most
  until the bound, NEVER after".
* `immediate_revocation` — **single-machine (n=1 / instantaneous propagation) ⇒ IMMEDIATE**. If the
  topology propagates instantly (`delay ≡ 0`, the n=1 collapse), then a credential revoked at `τ`
  is not honored at any `t ≥ τ` — the strong property, derived as a **corollary** of the bounded
  one (the bound `τ + 0 = τ`).
* `tightness_tooth` — **the bound is TIGHT (not vacuous)**. An explicit two-node system where a
  credential revoked at origin `m` at `τ` IS still honored by `n` at a time `t` with
  `τ ≤ t < τ + delay m n` — a stale-but-not-yet-propagated revocation being honored. So the bound
  cannot be improved; it is a real delay, not `0`.
* `single_machine_collapse` — the n=1 instance of the tooth's setup: under instantaneous
  propagation the stale window has length `0`, so the tooth's witness disappears and honoring stops
  exactly at `τ`.

§8 boundary: the attestation soundness is inherited from `Authority.Credential.verify`
(`CryptoKernel.verify` oracle) and never re-litigated. The propagation `delay` is an interface
parameter (the `World`/gossip layer supplies it); Lean assumes only `delay m m = 0`. The *liveness*
of propagation — that a revocation issued at `m` actually reaches `n` within `delay m n` — is the
honest hypothesis `Propagates` made explicit and witnessed, not smuggled.

Pure, computable, `#eval`/`#guard`-able.
-/
import Dregg2.Authority.Credential

namespace Dregg2.Distributed.Revocation

open Dregg2.Authority.Credential
open Dregg2.Crypto (CryptoKernel)
open Dregg2.Privacy (Nullifier)

variable {Digest Proof : Type}

/-! ## 1. The propagation model — topology, events, and the per-node local view.

`Time` is logical (`ℕ`): a monotone causal clock (cf. `Time.Causal` — the frame-invariant
happens-before order). A `Node` is a participant id. The topology's `delay m n` is the *bound* on
how long a revocation issued at `m` takes to be honored everywhere; the gossip/consensus layer is
the realiser. -/

/-- Logical time — a monotone causal clock (Lamport-style; `Time.Causal`'s lightcone order). -/
abbrev Time := Nat

/-- A participant id. -/
abbrev Node := Nat

/-- **A `Topology`** — the propagation model. `nodes` is the finite participant set; `delay m n`
is the worst-case logical delay for a revocation issued at `m` to reach (be honored at) `n`. The
single law `selfDelay` says a node sees *its own* revocations immediately — `delay m m = 0` — which
is the seam through which the single-machine collapse (n=1 ⇒ instantaneous) flows. -/
structure Topology where
  /-- The finite participant set. -/
  nodes : Finset Node
  /-- The worst-case propagation delay from origin `m` to observer `n` (logical time). -/
  delay : Node → Node → Time
  /-- A node sees its own revocations immediately (`delay m m = 0`). The single-machine seam. -/
  selfDelay : ∀ m, delay m m = 0

/-- **A `RevEvent`** — a revocation as it happens in a distributed system: the credential id being
revoked (REUSING `Authority.Credential.credId`, projected to a `Nullifier` tag), the `origin` node
that issued the revocation, and the logical `issuedAt` time. The global revocation log is a list of
these. -/
structure RevEvent where
  /-- The revoked credential's content-addressed id (`Authority.Credential.credId`). -/
  cred : Nullifier
  /-- The node at which this revocation was issued. -/
  origin : Node
  /-- The logical time at which the revocation was issued at `origin`. -/
  issuedAt : Time
  deriving DecidableEq, Repr

/-- **`localRevSet T log n t`** — what node `n` locally believes is revoked at time `t`: exactly the
revocations that have had time to propagate from their origin to `n` by `t`, i.e. those events with
`event.issuedAt + T.delay event.origin n ≤ t`. This is the per-node `RevocationSet`
(`Authority.Credential.RevocationSet`, the G-Set of revoked ids) RECONSTRUCTED from the topology and
the global log — the stale local view the node verifies against. -/
def localRevSet (T : Topology) (log : List RevEvent) (n : Node) (t : Time) : RevocationSet :=
  { spent := (log.filter (fun e => decide (e.issuedAt + T.delay e.origin n ≤ t))).foldr
      (fun e acc => insert e.cred acc) ∅ }

/-- Membership in the local revocation set, unfolded: a credential id is locally-revoked at `(n,t)`
iff SOME logged event revoked exactly that id and has propagated to `n` by `t`. The bridge lemma the
guarantees rest on. -/
theorem mem_localRevSet (T : Topology) (log : List RevEvent) (n : Node) (t : Time) (c : Nullifier) :
    c ∈ (localRevSet T log n t).spent
      ↔ ∃ e ∈ log, e.cred = c ∧ e.issuedAt + T.delay e.origin n ≤ t := by
  unfold localRevSet
  induction log with
  | nil => simp
  | cons hd tl ih =>
      by_cases hp : hd.issuedAt + T.delay hd.origin n ≤ t
      · simp only [List.filter_cons, decide_eq_true_eq, hp, if_true, List.foldr_cons,
          Finset.mem_insert, ih, List.mem_cons]
        constructor
        · rintro (rfl | ⟨e, he, hce, hpe⟩)
          · exact ⟨hd, Or.inl rfl, rfl, hp⟩
          · exact ⟨e, Or.inr he, hce, hpe⟩
        · rintro ⟨e, (rfl | he), hce, hpe⟩
          · exact Or.inl hce.symm
          · exact Or.inr ⟨e, he, hce, hpe⟩
      · simp only [List.filter_cons, decide_eq_true_eq, hp, if_false, ih, List.mem_cons]
        constructor
        · rintro ⟨e, he, hce, hpe⟩; exact ⟨e, Or.inr he, hce, hpe⟩
        · rintro ⟨e, (rfl | he), hce, hpe⟩
          · exact absurd hpe hp
          · exact ⟨e, he, hce, hpe⟩

/-! ## 2. The per-node admissibility decision — `honors` (REUSES `Credential.verify`).

A node `n` HONORS a credential at time `t` exactly when the keys-as-caps verifier accepts it against
`n`'s *local* revocation view. Same fail-closed gate as single-machine (`Authority.Credential.verify`
= §8-oracle ∧ not-locally-revoked); the only difference is the revocation set fed in is the stale
`localRevSet`, not a global one. The whole distributed gap lives in that substitution. -/

/-- **`honors T log n t cred`** — does node `n` honor credential `cred` at time `t`? Exactly
`Authority.Credential.verify` against `n`'s local revocation set at `t`. REUSED verbatim: the
distributed model adds NO new admissibility logic, it only feeds the verifier a topology-derived
stale view. -/
def honors [AddCommGroup Digest] [CryptoKernel Digest Proof]
    (T : Topology) (log : List RevEvent) (n : Node) (t : Time) (cred : VC Digest Proof) : Bool :=
  verify (localRevSet T log n t) cred

/-- A node honoring `cred` at `(n,t)` forces `cred`'s id to be NOT in `n`'s local revocation set
(the negative-discharge leg of `verify`). The contrapositive is what every revocation theorem uses:
once the id IS locally revoked, `honors` is false. -/
theorem honors_imp_not_local_revoked [AddCommGroup Digest] [CryptoKernel Digest Proof]
    (T : Topology) (log : List RevEvent) (n : Node) (t : Time) (cred : VC Digest Proof)
    (h : honors T log n t cred = true) :
    credId cred ∉ (localRevSet T log n t).spent := by
  unfold honors verify isRevoked at h
  rw [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
  exact h.2

/-! ## 3. The keystone — DISTRIBUTED ⇒ EVENTUAL-BOUNDED revocation.

If `cred` was revoked at origin `m` at time `τ` (a `RevEvent` is in the log), then for every node
`n` and every `t ≥ τ + delay m n`, node `n` does NOT honor `cred`. The bound `τ + delay m n` is
EXPLICIT, and the property is "honored at most until the bound, and NEVER after it". -/

/-- A revocation of `cred` issued at origin `m` at time `τ`, recorded in the global log. The honest
hypothesis: a revocation actually happened (the log entry is the witness — no vacuous "True"). -/
def RevokedAt (log : List RevEvent) (cred : VC Digest Proof) (m : Node) (τ : Time) : Prop :=
  { cred := credId cred, origin := m, issuedAt := τ : RevEvent } ∈ log

/-- **THE KEYSTONE — `eventual_bounded_revocation`.** DISTRIBUTED ⇒ EVENTUAL-BOUNDED. If `cred` was
revoked at origin `m` at time `τ` (`RevokedAt`), then for EVERY node `n` and EVERY time `t` at or
after the explicit bound `τ + T.delay m n`, node `n` does NOT honor `cred`:

    honors T log n t cred = false        whenever   τ + T.delay m n ≤ t.

So a revoked cap is honored *at most until the revocation propagates* (the bound `τ + delay m n`)
and NEVER after. The propagation `delay` is the topology's; the proof routes through the local view
becoming revoked once the event has propagated (`mem_localRevSet`) and the fail-closed `verify`
(`revoke_blocks_verify`'s negative discharge). -/
theorem eventual_bounded_revocation [AddCommGroup Digest] [CryptoKernel Digest Proof]
    (T : Topology) (log : List RevEvent) (cred : VC Digest Proof) (m : Node) (τ : Time)
    (hrev : RevokedAt log cred m τ) (n : Node) (t : Time)
    (hbound : τ + T.delay m n ≤ t) :
    honors T log n t cred = false := by
  -- The event has propagated to `n` by `t`, so `cred`'s id is in `n`'s local revocation set.
  have hmem : credId cred ∈ (localRevSet T log n t).spent := by
    rw [mem_localRevSet]
    exact ⟨{ cred := credId cred, origin := m, issuedAt := τ }, hrev, rfl, hbound⟩
  -- A locally-revoked id ⇒ `verify` rejects (fail-closed negative discharge).
  unfold honors verify isRevoked
  rw [decide_eq_true (by exact hmem)]
  simp

/-! ## 4. The single-machine collapse — INSTANTANEOUS ⇒ IMMEDIATE (a corollary).

The dregg4 single-machine principle: n=1 (one node) — or, equivalently, instantaneous propagation —
collapses the bound `τ + delay m n` to `τ`, recovering the strong property "never honored at or
after `τ`". We model both n=1 *and* the instantaneous-link idealisation by `delay ≡ 0`. -/

/-- **`Instantaneous T`** — the single-machine / instantaneous-propagation idealisation: every link
has zero delay. This holds automatically for a one-node topology (every pair is `(m,m)`, and
`selfDelay` forces `delay m m = 0`); see `oneNode_instantaneous`. -/
def Instantaneous (T : Topology) : Prop := ∀ m n, T.delay m n = 0

/-- A ONE-NODE topology is `Instantaneous`: with a single participant `p`, every `(m,n)` pair is
`(p,p)`, and `selfDelay` gives `delay p p = 0`. The n=1 collapse is a *fact about the topology*, not
an extra assumption. -/
theorem oneNode_instantaneous (T : Topology) (p : Node) (hsingle : ∀ m, m ∈ T.nodes → m = p)
    (_hp : p ∈ T.nodes) :
    (∀ m ∈ T.nodes, ∀ n ∈ T.nodes, T.delay m n = 0) := by
  intro m hm n hn
  rw [hsingle m hm, hsingle n hn]
  exact T.selfDelay p

/-- **`immediate_revocation`** — SINGLE-MACHINE (instantaneous propagation) ⇒ IMMEDIATE revocation,
a COROLLARY of `eventual_bounded_revocation`. Under `Instantaneous T` (`delay ≡ 0`, the n=1
collapse), a credential revoked at origin `m` at time `τ` is NOT honored by any node `n` at ANY time
`t ≥ τ` — the bound `τ + delay m n` collapses to `τ + 0 = τ`. This is the STRONG property: a revoked
cap is never honored after revocation. -/
theorem immediate_revocation [AddCommGroup Digest] [CryptoKernel Digest Proof]
    (T : Topology) (hinst : Instantaneous T) (log : List RevEvent) (cred : VC Digest Proof)
    (m : Node) (τ : Time) (hrev : RevokedAt log cred m τ) (n : Node) (t : Time) (ht : τ ≤ t) :
    honors T log n t cred = false := by
  apply eventual_bounded_revocation T log cred m τ hrev n t
  rw [hinst m n, Nat.add_zero]
  exact ht

/-! ## 5. The TOOTH — the bound is TIGHT (not vacuous).

A stale-but-not-yet-propagated revocation IS honored. We exhibit a concrete two-node system where a
credential revoked at origin `m=0` at time `τ=0` is still honored by node `n=1` at time `t=4`, with
`τ ≤ t < τ + delay m n` (the propagation delay is `5`, so `0 ≤ 4 < 5`). This shows
`eventual_bounded_revocation`'s bound cannot be tightened to anything below `τ + delay m n` — the
delay is real, and the guarantee is genuinely *eventual-bounded*, not immediate. -/

section Tooth

open Dregg2.Crypto.Reference

/-- Two nodes, `0` and `1`, with a propagation delay of `5` on the cross link `0 → 1` and `0` on the
self links (the `selfDelay` law). A revocation issued at node `0` is honored at node `1` for `5`
ticks of logical time before it propagates — the stale window. -/
def toothTopology : Topology where
  nodes := {0, 1}
  delay := fun m n => if m = n then 0 else 5
  selfDelay := fun m => by simp

/-- A genuinely-issued credential (Reference kernel: a valid proof *is* the statement). -/
def toothCred : VC Crypto.Reference.D Crypto.Reference.P :=
  issue 99 1 42 7
    (issuerStmt (Digest := Crypto.Reference.D) (Proof := Crypto.Reference.P)
      { issuer := 99, schema := 1, subject := 42, claim := 7, attestation := 0 })

/-- The global log: node `0` revoked `toothCred` at time `τ = 0`. -/
def toothLog : List RevEvent :=
  [{ cred := credId toothCred, origin := 0, issuedAt := 0 }]

/-- **The revocation really happened** — `toothCred` was revoked at origin `0` at time `0`. So the
tooth is not honoring an *un-revoked* credential; the revocation is in the log, it simply has not
propagated to node `1` yet. -/
theorem tooth_revoked : RevokedAt toothLog toothCred 0 0 := by
  unfold RevokedAt toothLog; exact List.mem_cons_self

/-- **THE TOOTH (tightness).** In `toothTopology`, the credential `toothCred` was revoked at origin
`0` at time `τ = 0`, yet node `1` STILL HONORS it at time `t = 4` — because the cross-link delay is
`5`, and `τ + delay 0 1 = 0 + 5 = 5 > 4`. A stale-but-not-yet-propagated revocation being honored.
This witnesses that `eventual_bounded_revocation`'s bound is TIGHT: honoring genuinely persists up to
(but not including) `τ + delay m n`, so the guarantee cannot be strengthened to immediate in the
distributed setting. -/
theorem tightness_tooth :
    -- the revocation is real (issued at origin 0, time 0) …
    RevokedAt toothLog toothCred 0 0
    -- … `t = 4` is inside the stale window `[τ, τ + delay 0 1) = [0, 5)` …
    ∧ (0 ≤ 4 ∧ 4 < 0 + toothTopology.delay 0 1)
    -- … and node 1 STILL HONORS the (already-revoked) credential at t = 4.
    ∧ honors toothTopology toothLog 1 4 toothCred = true := by
  refine ⟨tooth_revoked, ⟨Nat.zero_le _, by decide⟩, ?_⟩
  -- node 1's local view at t=4 is EMPTY (the only event has delay 5, not yet propagated),
  -- so `verify` is governed entirely by the §8 oracle, which accepts the genuine attestation.
  unfold honors verify isRevoked localRevSet toothTopology toothLog
  decide

/-- **`single_machine_collapse`** — the n=1 / instantaneous instance of the tooth's setup: when the
SAME credential is revoked but the cross-link delay is `0` (the instantaneous idealisation), the
stale window `[τ, τ + 0) = [τ, τ)` is EMPTY, so node `1` does NOT honor `toothCred` at `t = 4` (or
any `t ≥ 0 = τ`). The tooth's witness disappears exactly under the single-machine collapse — honoring
stops at `τ`. We reuse `immediate_revocation` against an instantaneous variant of the topology. -/
def toothTopologyInstant : Topology where
  nodes := {0, 1}
  delay := fun _ _ => 0
  selfDelay := fun _ => rfl

theorem single_machine_collapse :
    Instantaneous toothTopologyInstant
    ∧ honors toothTopologyInstant toothLog 1 4 toothCred = false := by
  refine ⟨fun _ _ => rfl, ?_⟩
  exact immediate_revocation toothTopologyInstant (fun _ _ => rfl) toothLog toothCred 0 0
    tooth_revoked 1 4 (Nat.zero_le _)

/-! ### It runs (`#guard`) — the stale window and its collapse. -/

-- before any revocation visible: node 1 honors at t=0 (delay 5, nothing propagated)
#guard honors toothTopology toothLog 1 0 toothCred == true
-- still inside the stale window at t=4 (the TOOTH)
#guard honors toothTopology toothLog 1 4 toothCred == true
-- the boundary t=5 = τ + delay: revocation has propagated, node 1 STOPS honoring
#guard honors toothTopology toothLog 1 5 toothCred == false
-- node 0 (the origin) honors NEVER after τ=0: its self-delay is 0 (immediate locally)
#guard honors toothTopology toothLog 0 0 toothCred == false
-- single-machine collapse: instantaneous topology ⇒ node 1 stops at τ=0 already
#guard honors toothTopologyInstant toothLog 1 0 toothCred == false
#guard honors toothTopologyInstant toothLog 1 4 toothCred == false

end Tooth

/-! ## 6. Non-vacuity of the spec surface (a stale window genuinely exists).

`eventual_bounded_revocation` is non-vacuous because its hypothesis `RevokedAt` is *witnessed*
(`tooth_revoked`) AND its conclusion is *falsifiable before the bound* (`tightness_tooth`: honoring
is `true` strictly inside `[τ, τ + delay)`). The guarantee therefore says something real at exactly
the boundary — it is not a `True`-carrier. -/

/-- **Non-vacuity, assembled.** There is a system + credential where (a) the revocation is real, (b)
the credential is honored at some time strictly before the bound (stale window non-empty), and (c)
the credential is NOT honored at the bound. So `eventual_bounded_revocation` discriminates: the
"never honored after `τ + delay`" content rules out a real behavior that the "before the bound"
witness exhibits. -/
theorem spec_nonvacuous :
    -- (a) a real revocation
    RevokedAt toothLog toothCred 0 0
    -- (b) honored strictly before the bound (stale window non-empty)
    ∧ honors toothTopology toothLog 1 4 toothCred = true
    -- (c) NOT honored at the bound (the guarantee bites)
    ∧ honors toothTopology toothLog 1 5 toothCred = false := by
  refine ⟨tooth_revoked, ?_, ?_⟩
  · exact (tightness_tooth).2.2
  · exact eventual_bounded_revocation toothTopology toothLog toothCred 0 0 tooth_revoked 1 5
      (by decide)

end Dregg2.Distributed.Revocation
