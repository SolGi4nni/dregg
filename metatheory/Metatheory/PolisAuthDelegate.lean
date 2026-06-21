/-
# Metatheory.PolisAuthDelegate — GENUINE inter-agent delegation in the derivation closure.

`PolisAuthReachDatalog.ReachesD` is REAL multi-step derivation, but per-agent: every rule in
`grantRules b` has head AND body atoms scoped to the SAME agent `b` (`atomOf b _ ← [atomOf b _]`).
That models one agent climbing its own delegation ladder. It does NOT model one agent's authority
unlocking ANOTHER agent's — the actual social object of a polis: who-can-grant-whom.

This file builds the inter-agent layer. Using the SAME proven-injective `atomOf` encoding, the rules
mix DIFFERENT agents' atoms in head and body:

    atomOf Y target ← [atomOf X grant]      -- "X delegates `target` to Y": X's grant unlocks Y

So Y's authority is derived from X's facts — pooled, cross-agent. The deliverables:

  * `delegation_unlocks_other` — Y reaches `target` ONLY via X's grant (Derivable from the pooled
    inter-agent facts X ∪ Y), and NOT from Y's own facts alone — genuine cross-agent unlock.
  * `inter_agent_foreclosure` — drop X's grant-atom from the pool and Y can no longer derive `target`:
    X's revocation forecloses Y. X dominates Y's reachability — real inter-agent domination.
  * `delegation_chain_three_agents` — a 3-hop chain X→Y→Z, each delegating onward, Derivable across
    exactly 3 rounds and NOT fewer.

All `decide`-checked, no `sorry`, no load-bearing `True`. This is the genuine multi-agent
knowledge/authority coordination over the real Datalog derivation closure.
-/
import Metatheory.PolisDatalog
import Metatheory.PolisAuthReachDatalog
import Dregg2.Authority.Positional

namespace Metatheory.PolisAuthDelegate

open Dregg2.Authority Metatheory.PolisDatalog
open Metatheory.PolisAuthReachDatalog (atomOf atomOf_injective)

/-! ## §1. Three agents, one shared target authority. -/

/-- The three agents of the delegation society. -/
def X : Label := 0
def Y : Label := 1
def Z : Label := 2

/-- The authority being delegated around (any non-grant authority works as the unlock target). -/
def target : Auth := Auth.read

/-! ## §2. Inter-agent delegation rules: bodies and heads mix DIFFERENT agents.

The genuinely-new object. Each rule's body atom belongs to one agent and its head atom to ANOTHER —
agent X's facts derive agent Y's authority. This is impossible to express with `grantRules` (whose
every rule is intra-agent). -/

/-- **The single-hop delegation rule.** Head `atomOf Y target` is Y's reach-fact; body
`atomOf X .grant` is X's grant-fact. So Y reaches `target` BECAUSE X holds `grant` and delegates it.
Different agents in head vs body — the cross-agent edge. -/
def delegRules : List Rule :=
  [⟨atomOf Y target, [atomOf X .grant]⟩]   -- X grants `target` to Y

/-- **Pooled facts**: X holds `grant` (and nothing relevant else), Y holds nothing on its own.
A polis pools the participants' reach-facts into one shared derivation base. -/
def pooledFacts : List Atom := [atomOf X .grant]

/-- **Y's OWN facts alone** — Y holds nothing that could derive `target`. (Empty here: Y has no
self-path to the target; its only route is X's delegation.) -/
def yOwnFacts : List Atom := []

/-- **X's grant revoked** from the pool — the body atom is gone, so the delegation rule never fires. -/
def pooledRevokeX : List Atom := []

/-! ## §3. THE DELIVERABLES (single-hop inter-agent delegation). -/

/-- **`delegation_unlocks_other`.** Y reaches `target` from the POOLED inter-agent facts — but ONLY
because X's grant is in the pool. The rule `atomOf Y target ← [atomOf X grant]` fires on X's fact,
deriving Y's authority. This is one agent's grant unlocking ANOTHER agent's target. -/
theorem delegation_unlocks_other :
    Derivable delegRules pooledFacts (atomOf Y target) 1 := by decide

/-- **Y cannot reach `target` from its OWN facts alone.** With only `yOwnFacts` (Y holds nothing),
the delegation rule's body `atomOf X grant` is never present, so no round adds `atomOf Y target`.
Y's authority here is genuinely X-derived, not self-derived. -/
theorem y_alone_cannot :
    ¬ Derivable delegRules yOwnFacts (atomOf Y target) 5 := by decide

/-- The unlock is strictly cross-agent: Y reaches `target` from the pool, but not from its own facts.
The DIFFERENCE is exactly X's contributed grant-fact. -/
theorem unlock_is_cross_agent :
    Derivable delegRules pooledFacts (atomOf Y target) 1
      ∧ ¬ Derivable delegRules yOwnFacts (atomOf Y target) 5 :=
  ⟨delegation_unlocks_other, y_alone_cannot⟩

/-- **`inter_agent_foreclosure`.** Drop X's grant-atom from the pool (X revokes its delegation) and Y
can NO LONGER derive `target`: the rule body is unsatisfied, the closure never adds `atomOf Y target`.
X's revocation forecloses Y — genuine inter-agent domination, X dominating Y's reachability. -/
theorem inter_agent_foreclosure :
    ¬ Derivable delegRules pooledRevokeX (atomOf Y target) 5 := by decide

/-- X dominates Y: Y reaches `target` exactly when X's grant is present, and not when it is revoked.
The same rule-base, the same goal — only X's contributed fact toggles Y's reachability. -/
theorem x_dominates_y :
    Derivable delegRules pooledFacts (atomOf Y target) 1
      ∧ ¬ Derivable delegRules pooledRevokeX (atomOf Y target) 5 :=
  ⟨delegation_unlocks_other, inter_agent_foreclosure⟩

/-! ## §4. The 3-hop chain X → Y → Z, each delegating onward.

A delegation society where the grant flows down a chain of THREE distinct agents. Each agent, upon
acquiring `grant`, delegates `grant` to the next — and the final agent converts its acquired grant
into the `target` authority. The body/head agents differ at every hop: a genuine inter-agent chain.

  hop 1 (round 1):  atomOf Y .grant   ← [atomOf X .grant]    -- X delegates grant to Y
  hop 2 (round 2):  atomOf Z .grant   ← [atomOf Y .grant]    -- Y delegates grant to Z
  hop 3 (round 3):  atomOf Z target   ← [atomOf Z .grant]    -- Z exercises grant ⟹ target

Z reaching `target` therefore takes EXACTLY 3 rounds — fewer than 3 does not suffice. -/

/-- The 3-hop inter-agent delegation chain. Every rule crosses an agent boundary except the final
exercise step (Z converting its OWN acquired grant into `target`). -/
def chainRules3 : List Rule :=
  [⟨atomOf Y .grant, [atomOf X .grant]⟩,   -- X → Y
   ⟨atomOf Z .grant, [atomOf Y .grant]⟩,   -- Y → Z
   ⟨atomOf Z target, [atomOf Z .grant]⟩]   -- Z exercises grant ⟹ target

/-- The chain is SEEDED by X alone: only X starts with `grant`. The chain must carry it to Z. -/
def chainSeed : List Atom := [atomOf X .grant]

/-- **`delegation_chain_three_agents`.** From X's grant alone, Z reaches `target` — but only after the
grant has flowed X → Y → Z and Z has exercised it. Three distinct agents, three onward delegations. -/
theorem delegation_chain_three_agents :
    Derivable chainRules3 chainSeed (atomOf Z target) 3 := by decide

/-- **The chain is genuinely 3 rounds — NOT fewer.** At budget 2, Z does not yet reach `target`
(round 1 gives Y grant, round 2 gives Z grant, only round 3 gives Z target). So this is a real 3-hop
inter-agent chain, not a collapsed shortcut. -/
theorem chain_needs_three_rounds :
    ¬ Derivable chainRules3 chainSeed (atomOf Z target) 2 := by decide

/-- The chain length is exact: derivable at 3 rounds, not at 2. -/
theorem chain_is_exactly_three :
    Derivable chainRules3 chainSeed (atomOf Z target) 3
      ∧ ¬ Derivable chainRules3 chainSeed (atomOf Z target) 2 :=
  ⟨delegation_chain_three_agents, chain_needs_three_rounds⟩

/-- **Inter-agent foreclosure on the chain too**: revoke X's seed grant (the only seed) and Z never
reaches `target` — the head of the chain dominates the whole society's tail. -/
theorem chain_foreclosure_from_head :
    ¬ Derivable chainRules3 [] (atomOf Z target) 5 := by decide

/-! ## §5. The atoms are genuinely distinct agents (faithfulness of the cross-agent claim).

The cross-agent rules are meaningful only because `atomOf X _`, `atomOf Y _`, `atomOf Z _` are
DISTINCT atoms — otherwise "X's grant" and "Y's grant" would collide and the delegation would be
vacuous self-derivation. `atomOf_injective` certifies this. -/

/-- X's grant-atom and Y's grant-atom are different atoms: the delegation crosses a real boundary,
it is not Y deriving from itself under an alias. -/
theorem agents_are_distinct_atoms : atomOf X .grant ≠ atomOf Y .grant := by
  intro h
  have := (atomOf_injective h).1   -- X = Y
  exact absurd this (by decide)

/-! ## §6. Runnable — watch the inter-agent delegation decide on the real engine. -/

-- Single hop: from X's grant the pool derives Y's target (one round). True.
#eval decide (Derivable delegRules pooledFacts (atomOf Y target) 1)
-- Y alone (no X grant): cannot. False.
#eval decide (Derivable delegRules yOwnFacts (atomOf Y target) 5)
-- X's grant revoked: Y foreclosed. False.
#eval decide (Derivable delegRules pooledRevokeX (atomOf Y target) 5)
-- The 3-hop chain X→Y→Z reaches Z's target at round 3. True.
#eval decide (Derivable chainRules3 chainSeed (atomOf Z target) 3)
-- ...but NOT at round 2 (genuinely 3 hops). False.
#eval decide (Derivable chainRules3 chainSeed (atomOf Z target) 2)
-- Watch the grant flow X→Y→Z across rounds:
#eval deriveWithin chainRules3 chainSeed 3

/-! ## §7. Axiom hygiene. -/

#print axioms delegation_unlocks_other
#print axioms inter_agent_foreclosure
#print axioms delegation_chain_three_agents
#print axioms chain_needs_three_rounds
#print axioms agents_are_distinct_atoms

/-!
Inter-agent delegation, in one breath:

  1. The SAME proven-injective `atomOf : Label → Auth → Atom`, so distinct agents are distinct atoms
     (`agents_are_distinct_atoms`).
  2. Rules whose body and head name DIFFERENT agents — `atomOf Y target ← [atomOf X grant]` — so one
     agent's grant derives another's authority over the real Datalog closure (impossible with the
     intra-agent `grantRules`).
  3. `delegation_unlocks_other` (Y reaches target ONLY via X's pooled grant) + `y_alone_cannot`
     (Y's own facts cannot) + `inter_agent_foreclosure` (revoke X's grant ⟹ Y foreclosed: X dominates
     Y) + `delegation_chain_three_agents` (X→Y→Z, exactly 3 rounds, `chain_needs_three_rounds`) —
     all `decide`-checked. The genuine who-can-grant-whom of a polis.
-/

end Metatheory.PolisAuthDelegate
