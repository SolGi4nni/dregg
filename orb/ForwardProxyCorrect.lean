import AccessControlProxy
import ForwardProxy

/-!
# ForwardProxyCorrect — forward-proxy CONNECT admission *correctness*

`AccessControlProxy` proves SAFETY-flavoured facts about its admission gate
`AccessControlProxy.admit`: with `defaultDeny` an unlisted destination is never
admitted (`acl_default_deny`), an empty client allowlist admits no one
(`acl_empty_allowlist_denies`), and admission implies cap headroom
(`admit_under_cap`). Each pins one *necessary* condition on the gate. None of
them, alone or together, says the gate makes exactly the decision RFC 9110
§9.3.6 dictates: they are one-directional (they constrain when the gate may
*refuse*, or a consequence of an admit), and they say nothing about *which*
refusal reason is returned. A gate that refused every request, or that reported
`capReached` where the destination was actually denied, satisfies them all.

This file closes that gap for the CONNECT admission decision. It gives, *without
any reference to* `admit`, `clientOk`, or `dstOk`, an independent specification
of what the decision SHOULD be — derived from the standard — and proves the
deployed `AccessControlProxy.admit` equals it on every input.

## RFC grounding (RFC 9110 §9.3.6, CONNECT)

"The CONNECT method requests that the recipient establish a tunnel to the
destination origin server … There are significant risks in establishing a tunnel
to arbitrary servers … A proxy that supports CONNECT SHOULD restrict its use to a
limited set of known ports or a configurable list of safe request targets."

Read against a default-deny access-control policy, a CONNECT admission gate MUST:

1. admit the tunnel **iff** the request passes access control, i.e. the client is
   on the allowlist, the destination is *permitted* (not on the denylist, and —
   under default-deny — on the allowlist), and the client is under its
   per-client concurrent-connection cap;
2. otherwise refuse, and the refusal MUST name the *first* failing gate: a
   blocked client, then a denied destination (the 403 case — no tunnel), then the
   connection cap (over-cap rejection).

`admitSpec` (below) states exactly this, using only set-membership predicates
(`∈`, `∃ … ∈`, `<`) — never the deployed helpers. `admit_refines_spec` proves the
deployed gate matches it pointwise.

## What this buys over the SAFETY theorems

* **Both directions.** `acl_default_deny` gives one implication; `admit_refines_spec`
  gives the biconditional — the gate admits *precisely* the admissible requests
  and refuses *precisely* the rest.
* **Reason exactness.** The spec fixes the refusal reason by priority. So the
  "denied destination ⇒ 403, no tunnel" and "over-cap ⇒ rejection" clauses of the
  standard are proven distinct, not conflated.
* **Non-vacuity.** `spec_rejects_capIgnoring` / `spec_rejects_denyIgnoring` exhibit
  two wrong gates (one that ignores the cap, one that tunnels a denied target) and
  prove each *disagrees* with the spec at a concrete witness — so the theorem
  cannot be satisfied by an incorrect implementation.

## FINDING — the deployed CONNECT tunnel FSM is not wired to the ACL gate

The deployed tunnel state machine `ForwardProxy.tstep` establishes `connected`
on the boundary event `upstreamOk` **with no reference to `admit`**. There is no
deployed function composing tunnel establishment with the admission decision:
`Reactor.WireAccessControlProxy` gates the *serve* path on `admit`, and
`Reactor.WireRest` attaches the tunnel *relay* theorems to the deployed body, but
nothing gates tunnel *establishment* on the ACL decision. Consequently the
"tunnel established **iff** the target passes access control" clause of the spec
is *not* enforced by the deployed composition: `tunnel_ignores_acl_finding`
proves the deployed `tstep` reaches `connected` on `upstreamOk` even for a
destination the deployed `admit` refuses. The admission decision is correct; the
tunnel FSM does not consult it. See the section "Deployed tunnel gap" below.

## Boundaries

* CIDR containment (`inCidr`) and set membership are the standard's own primitive
  vocabulary and are shared with the spec; the *decision logic* under test — the
  branch structure, reason priority, and cap comparison — is specified
  independently.
* The 403 status code is the HTTP surface of the `dstBlocked` refusal; this file
  proves the *decision* (refuse, reason `dstBlocked`, no tunnel), which is what
  the deployed gate computes. The status-line rendering is out of scope.
-/

namespace ForwardProxyCorrect

open AccessControlProxy

/-! ## BEq/membership bridge for destinations

The deployed `dstOk` tests denylist/allowlist membership with `List.contains`
(a `BEq` test); the spec uses propositional membership `∈`. `Dest` derives
`DecidableEq` and `BEq`; the following establishes that its `BEq` is lawful, so
`List.contains` and `∈` agree. This is bridge plumbing, not decision logic. -/

/-- `Dest`'s derived boolean equality decides propositional equality. -/
theorem dest_beq_eq (a b : Dest) : (a == b) = decide (a = b) := by
  cases a with | mk ah ap =>
  cases b with | mk bh bp =>
  show (ah == bh && ap == bp)
      = decide (({host := ah, port := ap} : Dest) = {host := bh, port := bp})
  by_cases h1 : ah = bh <;> by_cases h2 : ap = bp <;>
    simp_all [Dest.mk.injEq, beq_iff_eq]

instance : LawfulBEq Dest where
  eq_of_beq {a b} h := of_decide_eq_true (by rw [← dest_beq_eq]; exact h)
  rfl {a} := by rw [dest_beq_eq]; exact decide_eq_true rfl

theorem contains_true_iff (l : List Dest) (d : Dest) :
    l.contains d = true ↔ d ∈ l := List.contains_iff_mem

theorem contains_false_iff (l : List Dest) (d : Dest) :
    l.contains d = false ↔ d ∉ l := by
  rw [← contains_true_iff]; cases l.contains d <;> simp

/-! ## The independent specification (RFC 9110 §9.3.6)

Every predicate here is stated in terms of set membership only — it does not
mention `admit`, `clientOk`, or `dstOk`. -/

/-- **Client admissibility.** The client address `ip` is on the allowlist iff some
configured CIDR block contains it. (An empty allowlist admits no one.) -/
def SpecClientAllowed (pol : Policy) (ip : Nat) : Prop :=
  ∃ c ∈ pol.allowCidrs, inCidr c ip = true

/-- **Destination permission (default-deny).** The destination is permitted iff it
is not on the denylist and — when the policy is default-deny — it is on the
allowlist. Phrased with an explicit disjunction so it is manifestly decidable. -/
def SpecDestPermitted (pol : Policy) (dst : Dest) : Prop :=
  dst ∉ pol.denyDst ∧ (pol.defaultDeny ≠ true ∨ dst ∈ pol.allowDst)

/-- **Cap headroom.** The client is strictly below its per-client cap. -/
def SpecUnderCap (pol : Policy) (n : Nat) : Prop :=
  n < pol.connCap

instance (pol : Policy) (ip : Nat) : Decidable (SpecClientAllowed pol ip) := by
  unfold SpecClientAllowed; infer_instance
instance (pol : Policy) (dst : Dest) : Decidable (SpecDestPermitted pol dst) := by
  unfold SpecDestPermitted; infer_instance
instance (pol : Policy) (n : Nat) : Decidable (SpecUnderCap pol n) := by
  unfold SpecUnderCap; infer_instance

/-- **The mandated CONNECT admission decision.** Refuse the first failing gate,
naming its reason: a blocked client, then a denied destination (the 403 case, no
tunnel), then the over-cap rejection; admit only when all three pass. This is the
decision the standard dictates, written independently of the implementation. -/
def admitSpec (pol : Policy) (ip : Nat) (dst : Dest) (n : Nat) : Decision :=
  if ¬ SpecClientAllowed pol ip then .refuse .clientBlocked
  else if ¬ SpecDestPermitted pol dst then .refuse .dstBlocked
  else if ¬ SpecUnderCap pol n then .refuse .capReached
  else .admit

/-! ## Condition bridges — deployed helpers ↔ spec predicates -/

/-- `clientOk` (a `List.any` over `inCidr`) holds iff the spec's client predicate. -/
theorem clientOk_iff (pol : Policy) (ip : Nat) :
    clientOk pol ip = true ↔ SpecClientAllowed pol ip := by
  unfold clientOk SpecClientAllowed
  exact List.any_eq_true

/-- `dstOk` (denylist-then-allowlist `List.contains`) holds iff the destination is
permitted by the spec. -/
theorem dstOk_iff (pol : Policy) (dst : Dest) :
    dstOk pol dst = true ↔ SpecDestPermitted pol dst := by
  unfold dstOk SpecDestPermitted
  by_cases hden : pol.denyDst.contains dst = true
  · rw [if_pos hden]
    have : dst ∈ pol.denyDst := (contains_true_iff _ _).1 hden
    simp [this]
  · have hden' : pol.denyDst.contains dst = false := by
      cases h : pol.denyDst.contains dst with
      | false => rfl
      | true => exact absurd h hden
    rw [if_neg hden]
    have hnmem : dst ∉ pol.denyDst := (contains_false_iff _ _).1 hden'
    by_cases hdd : pol.defaultDeny = true
    · rw [if_pos hdd]
      constructor
      · intro hc
        exact ⟨hnmem, Or.inr ((contains_true_iff _ _).1 hc)⟩
      · rintro ⟨_, hor⟩
        rcases hor with hne | hmem
        · exact absurd hdd hne
        · exact (contains_true_iff _ _).2 hmem
    · rw [if_neg hdd]
      exact ⟨fun _ => ⟨hnmem, Or.inl hdd⟩, fun _ => rfl⟩

/-- The cap comparison is the spec's cap predicate. -/
theorem underCap_iff (pol : Policy) (n : Nat) :
    (n < pol.connCap) ↔ SpecUnderCap pol n := Iff.rfl

/-! ## The refinement theorem — deployed `admit` ≡ spec -/

/-- **`admit_refines_spec` — the deployed CONNECT admission gate is exactly the
RFC-mandated decision.** For every policy, client address, destination, and
current connection count, the deployed `AccessControlProxy.admit` returns the same
`Decision` — admit/refuse *and refusal reason* — as the independent `admitSpec`.

This binds the deployed function the engine invokes (the same `admit` that
`Reactor.WireAccessControlProxy.proxyServe` gates the serve on, and that the
`sample_*` deployment witnesses `decide`), not a wrapper. -/
theorem admit_refines_spec (pol : Policy) (ip : Nat) (dst : Dest) (n : Nat) :
    admit pol ip dst n = admitSpec pol ip dst n := by
  unfold admit admitSpec
  by_cases hc : SpecClientAllowed pol ip
  · have hcb : clientOk pol ip = true := (clientOk_iff _ _).2 hc
    by_cases hd : SpecDestPermitted pol dst
    · have hdb : dstOk pol dst = true := (dstOk_iff _ _).2 hd
      by_cases hn : SpecUnderCap pol n
      · simp [hcb, hdb, hc, hd, hn, (underCap_iff pol n).2 hn]
      · have hnb : ¬ (n < pol.connCap) := fun h => hn ((underCap_iff _ _).1 h)
        simp [hcb, hdb, hnb, hc, hd, hn]
    · have hdb : dstOk pol dst = false := by
        cases h : dstOk pol dst with
        | false => rfl
        | true => exact absurd ((dstOk_iff _ _).1 h) hd
      simp [hcb, hdb, hc, hd]
  · have hcb : clientOk pol ip = false := by
      cases h : clientOk pol ip with
      | false => rfl
      | true => exact absurd ((clientOk_iff _ _).1 h) hc
    simp [hcb, hc]

/-! ## The RFC clauses, read off the refinement -/

/-- **Tunnel admitted iff access control passes.** The deployed gate returns
`.admit` exactly when the client is allowed, the destination is permitted, and the
client is under the cap. This is the biconditional the SAFETY theorems left
one-directional. -/
theorem admit_iff_admissible (pol : Policy) (ip : Nat) (dst : Dest) (n : Nat) :
    admit pol ip dst n = .admit ↔
      (SpecClientAllowed pol ip ∧ SpecDestPermitted pol dst ∧ SpecUnderCap pol n) := by
  rw [admit_refines_spec]
  unfold admitSpec
  by_cases hc : SpecClientAllowed pol ip
  · by_cases hd : SpecDestPermitted pol dst
    · by_cases hn : SpecUnderCap pol n
      · simp [hc, hd, hn]
      · simp [hc, hd, hn]
    · simp [hc, hd]
  · simp [hc]

/-- **A denied destination yields the 403 refusal and no tunnel.** For a permitted
client whose destination is *not* permitted (denylisted, or absent under
default-deny), the deployed gate refuses with reason `dstBlocked` — the decision
the 403 renders — regardless of the cap. -/
theorem denied_dst_is_dstBlocked (pol : Policy) (ip : Nat) (dst : Dest) (n : Nat)
    (hc : SpecClientAllowed pol ip) (hd : ¬ SpecDestPermitted pol dst) :
    admit pol ip dst n = .refuse .dstBlocked := by
  rw [admit_refines_spec]; unfold admitSpec; simp [hc, hd]

/-- **An over-cap request is rejected with `capReached`.** For a permitted client
and permitted destination at or above the cap, the deployed gate refuses with
reason `capReached` — distinct from the denied-destination 403. -/
theorem overcap_is_capReached (pol : Policy) (ip : Nat) (dst : Dest) (n : Nat)
    (hc : SpecClientAllowed pol ip) (hd : SpecDestPermitted pol dst)
    (hn : ¬ SpecUnderCap pol n) :
    admit pol ip dst n = .refuse .capReached := by
  rw [admit_refines_spec]; unfold admitSpec; simp [hc, hd, hn]

/-! ## Non-vacuity — wrong gates disagree with the spec

Two mutants that break exactly the two hard clauses of the standard. Each is
proven to *disagree* with `admitSpec` at a concrete witness, so a proof of
`(mutant … = admitSpec …)` for all inputs is impossible — the spec is not the
implementation renamed. -/

/-- A witness policy: any client (`0.0.0.0/0`), no denials, one allowed
destination, cap 1, default-deny. -/
def witnessPolicy : Policy :=
  { allowCidrs  := [⟨0, 0⟩]
    denyDst     := []
    allowDst    := [⟨"ok.example", 443⟩]
    connCap     := 1
    defaultDeny := true }

/-- Mutant gate #1: **ignores the connection cap** (admits whenever client and
destination pass). -/
def admitNoCap (pol : Policy) (ip : Nat) (dst : Dest) : Decision :=
  if clientOk pol ip then
    (if dstOk pol dst then .admit else .refuse .dstBlocked)
  else .refuse .clientBlocked

/-- The cap-ignoring gate **disagrees** with the spec: at the cap (`n = 1`) it
admits an over-cap request the spec rejects with `capReached`. A cap-ignoring
proxy therefore cannot satisfy the refinement. -/
theorem spec_rejects_capIgnoring :
    admitNoCap witnessPolicy 2130706433 ⟨"ok.example", 443⟩
      ≠ admitSpec witnessPolicy 2130706433 ⟨"ok.example", 443⟩ 1 := by
  decide

/-- Mutant gate #2: **tunnels a denied destination** (skips the destination check
entirely). -/
def admitNoDst (pol : Policy) (ip : Nat) (n : Nat) : Decision :=
  if clientOk pol ip then
    (if n < pol.connCap then .admit else .refuse .capReached)
  else .refuse .clientBlocked

/-- The destination-ignoring gate **disagrees** with the spec: on a destination
absent from the allowlist under default-deny it admits (opening a tunnel to a
denied target) where the spec refuses with `dstBlocked`. -/
theorem spec_rejects_denyIgnoring :
    admitNoDst witnessPolicy 2130706433 0
      ≠ admitSpec witnessPolicy 2130706433 ⟨"evil.example", 22⟩ 0 := by
  decide

/-- Sanity: on the *correct* inputs the deployed gate and the spec agree at a
concrete point (admit) — the disagreements above are genuine, not blanket. -/
theorem witness_admit :
    admit witnessPolicy 2130706433 ⟨"ok.example", 443⟩ 0 = .admit := by decide
theorem witness_denied :
    admit witnessPolicy 2130706433 ⟨"evil.example", 22⟩ 0 = .refuse .dstBlocked := by
  decide

/-! ## Deployed tunnel gap — the FINDING, formalized

The admission decision above is correct. But the deployed CONNECT *tunnel* FSM
`ForwardProxy.tstep` does not consult it. The mandated behaviour is: establish the
tunnel (reach `connected`) only for an admitted request. The deployed FSM reaches
`connected` on the boundary event `upstreamOk` for *every* request. -/

/-- **The mandated gated establishment.** A CONNECT reaches the tunnel-established
phase only when the ACL admits it *and* the upstream connect succeeds. This is the
function the deployed engine *should* invoke; it is written here as the spec, not
claimed to be deployed. -/
def establishSpec (pol : Policy) (ip : Nat) (dst : Dest) (n : Nat)
    (upstreamOk : Bool) : ForwardProxy.TPhase :=
  match admit pol ip dst n, upstreamOk with
  | .admit, true  => .connected
  | .admit, false => .failed
  | .refuse _, _  => .failed

/-- Under the spec, a refused request never reaches `connected` — no tunnel. -/
theorem establishSpec_denied_no_tunnel (pol : Policy) (ip : Nat) (dst : Dest)
    (n : Nat) (u : Bool) (h : admit pol ip dst n ≠ .admit) :
    establishSpec pol ip dst n u ≠ .connected := by
  unfold establishSpec
  cases hdec : admit pol ip dst n with
  | admit => exact absurd hdec h
  | refuse r => cases u <;> simp

/-- **`tunnel_ignores_acl_finding` — the deployed tunnel FSM is not gated by the
deployed ACL.** For *any* policy/client/destination the deployed `admit` refuses,
the deployed `ForwardProxy.tstep` still transitions from `connecting` to
`connected` on `upstreamOk`. The tunnel-establishment step never references the
admission decision, so it violates the spec's "established iff admitted" clause
(`establishSpec` refuses; `tstep` establishes). -/
theorem tunnel_ignores_acl_finding
    (pol : Policy) (ip : Nat) (dst : Dest) (n : Nat)
    (hdenied : admit pol ip dst n ≠ .admit) :
    -- the deployed FSM establishes the tunnel …
    ForwardProxy.tstep .connecting .upstreamOk = .connected
    -- … exactly where the spec forbids it.
    ∧ establishSpec pol ip dst n true ≠ .connected := by
  refine ⟨rfl, establishSpec_denied_no_tunnel pol ip dst n true hdenied⟩

/-- The gap made concrete: `evil.example:22` is denied by the deployed `admit`
under `witnessPolicy`, yet the deployed `tstep` tunnels it on `upstreamOk`. -/
theorem tunnel_gap_witness :
    ForwardProxy.tstep .connecting .upstreamOk = .connected
    ∧ establishSpec witnessPolicy 2130706433 ⟨"evil.example", 22⟩ 0 true
        ≠ .connected :=
  tunnel_ignores_acl_finding witnessPolicy 2130706433 ⟨"evil.example", 22⟩ 0
    (by decide)

/-! ## Axiom audit -/

#print axioms admit_refines_spec
#print axioms admit_iff_admissible
#print axioms denied_dst_is_dstBlocked
#print axioms overcap_is_capReached
#print axioms spec_rejects_capIgnoring
#print axioms spec_rejects_denyIgnoring
#print axioms tunnel_ignores_acl_finding

end ForwardProxyCorrect
