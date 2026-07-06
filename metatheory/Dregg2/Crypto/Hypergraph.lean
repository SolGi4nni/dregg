/-
# Dregg2.Crypto.Hypergraph — arbitrary hypergraph reductions as ZK-checkable certificates.

The `Crypto/Cfg` parse certificate (a `producesChain`: sentential forms threaded by single-rule
rewrites, bridged to `input ∈ language`) is a special case of a FAR more general fact: for ANY reduction
relation `R : α → α → Prop`, a locally-checkable CHAIN certificate `[start, …, goal]` (consecutive
elements related by one `R`-step) exists IFF `start` reduces to `goal` in the reflexive-transitive closure
`ReflTransGen R`. That generic bridge is `Hypergraph.bridge`, and it is exactly "a proof of an arbitrary
reduction": the prover exhibits the chain, the verifier checks each step, and the bridge certifies the
whole reduction.

Instantiating `R` at a hyperedge-replacement relation on HYPERGRAPHS gives
`hypergraph_reduction_bridge` — a ZK-checkable certificate for arbitrary hypergraph reductions (hyperedge
replacement is the hypergraph generalization of a context-free rewrite). Instantiating the SAME bridge at
a grammar's `Produces` recovers CFG parsing (`cfg_parse_via_reduction`): context-free parsing is the
linear/string instance of hypergraph reduction. One verified certificate framework covers both.

    bridge                      : (∃ c, Cert R start goal c) ↔ ReflTransGen R start goal   (ANY R)
    hypergraph_reduction_bridge : … instantiated at hyperedge replacement
    cfg_parse_via_reduction     : … instantiated at `g.Produces` ⇒ `input ∈ g.language`
-/
import Dregg2.Crypto.Cfg
import Dregg2.Tactics

namespace Dregg2.Crypto.Hypergraph

open ContextFreeGrammar

universe u

/-! ## The GENERIC reduction bridge — a locally-checkable chain certifies an arbitrary reduction. -/

section Generic

variable {α : Type u}

/-- **`chain R c`** — every consecutive pair of the sequence `c` is one `R`-reduction step. The generic
`producesChain`: the locally-checkable heart of a reduction certificate. -/
def chain (R : α → α → Prop) : List α → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => R a b ∧ chain R (b :: rest)

/-- **`Cert R start goal c`** — a reduction certificate: `c` is a NON-EMPTY chain from `start` to `goal`
with every step a valid `R`-reduction. The verifier checks `chain R c` locally + the two endpoints. -/
def Cert (R : α → α → Prop) (start goal : α) (c : List α) : Prop :=
  c.head? = some start ∧ c.getLast? = some goal ∧ chain R c

/-- A reflexive-transitive reduction unrolls to a certificate chain (prepend at each head-step). -/
theorem to_chain (R : α → α → Prop) {u v : α} (h : Relation.ReflTransGen R u v) :
    ∃ c, c.head? = some u ∧ c.getLast? = some v ∧ chain R c := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[v], rfl, rfl, trivial⟩
  | @head a c h' _hcv ih =>
    obtain ⟨cc, hhead, hlast, hpc⟩ := ih
    cases cc with
    | nil => simp at hhead
    | cons c' rest =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      refine ⟨a :: c' :: rest, rfl, ?_, ?_⟩
      · rw [List.getLast?_cons_cons]; exact hlast
      · exact ⟨h', hpc⟩

/-- A certificate chain from `u` to `v` witnesses `ReflTransGen R u v` (fold each step in at the head). -/
theorem of_chain (R : α → α → Prop) :
    ∀ (c : List α) {u v : α},
      c.head? = some u → c.getLast? = some v → chain R c → Relation.ReflTransGen R u v := by
  intro c
  induction c with
  | nil => intro u v hhead _ _; simp at hhead
  | cons x xs ih =>
    intro u v hhead hlast hpc
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    cases xs with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      subst hlast; exact Relation.ReflTransGen.refl
    | cons y ys =>
      obtain ⟨hxy, hrest⟩ := hpc
      rw [List.getLast?_cons_cons] at hlast
      exact Relation.ReflTransGen.head hxy (ih rfl hlast hrest)

/-- **`bridge`** — the generic reduction bridge: a chain certificate from `start` to `goal` exists IFF
`start` reduces to `goal` in the reflexive-transitive closure of `R`. This is the ZK-checkable proof of
an ARBITRARY reduction — the verifier checks each local step, the bridge certifies the whole reduction. -/
theorem bridge (R : α → α → Prop) (start goal : α) :
    (∃ c, Cert R start goal c) ↔ Relation.ReflTransGen R start goal := by
  constructor
  · rintro ⟨c, hhead, hlast, hpc⟩; exact of_chain R c hhead hlast hpc
  · intro h; obtain ⟨c, hhead, hlast, hpc⟩ := to_chain R h; exact ⟨c, hhead, hlast, hpc⟩

end Generic

#assert_axioms bridge

/-! ## Hypergraphs + hyperedge-replacement reduction. -/

/-- A hyperedge: a `label` together with its ordered attachment `nodes`. -/
abbrev Hyperedge (L V : Type) := L × List V

/-- A hypergraph: a list of hyperedges over a shared node set. -/
structure Hypergraph (L V : Type) where
  /-- The hyperedges. -/
  edges : List (Hyperedge L V)
  deriving Repr

/-- **`Reduces rule g g'`** — one hyperedge-replacement step: an edge `e` occurring in edge-context
`pre`/`post` is replaced by the edges `rhs`, where `rule e rhs` licenses the replacement. This IS the
hyperedge-replacement operation — the hypergraph generalization of a context-free rewrite (a context-free
rewrite is the special case where every hyperedge is a length-2 "string" edge). -/
inductive Reduces {L V : Type} (rule : Hyperedge L V → List (Hyperedge L V) → Prop) :
    Hypergraph L V → Hypergraph L V → Prop where
  /-- Replace edge `e` (between contexts `pre`, `post`) by `rhs`, licensed by `rule`. -/
  | replace (pre post : List (Hyperedge L V)) (e : Hyperedge L V) (rhs : List (Hyperedge L V))
      (h : rule e rhs) :
      Reduces rule ⟨pre ++ e :: post⟩ ⟨pre ++ rhs ++ post⟩

/-- **`hypergraph_reduction_bridge`** — the generic bridge INSTANTIATED at hypergraph reduction: a
reduction certificate (a chain of hypergraphs, each obtained from the previous by ONE hyperedge
replacement) from `g` to `g'` exists IFF `g` reduces to `g'` in the reflexive-transitive reduction
relation. A ZK-checkable proof of an ARBITRARY hypergraph reduction — the same certificate machinery
`Crypto/Cfg` uses for parse certificates. -/
theorem hypergraph_reduction_bridge {L V : Type}
    (rule : Hyperedge L V → List (Hyperedge L V) → Prop) (g g' : Hypergraph L V) :
    (∃ c, Cert (Reduces rule) g g' c) ↔ Relation.ReflTransGen (Reduces rule) g g' :=
  bridge (Reduces rule) g g'

/-- **`cfg_parse_via_reduction`** — the SAME generic bridge INSTANTIATED at a grammar's `Produces`
recovers context-free parsing: a `Produces`-chain from the start symbol to the input word exists IFF the
input is in the grammar's language. So CFG parsing is the linear/string instance of hypergraph reduction:
one verified reduction-certificate framework certifies both. -/
theorem cfg_parse_via_reduction {T : Type} (g : ContextFreeGrammar T) (input : List T) :
    (∃ c, Cert g.Produces [Symbol.nonterminal g.initial] (input.map Symbol.terminal) c)
      ↔ input ∈ g.language := by
  rw [mem_language_iff]
  exact bridge g.Produces _ _

#assert_axioms hypergraph_reduction_bridge
#assert_axioms cfg_parse_via_reduction

/-! ## Non-vacuity — a concrete hypergraph reduction, certified. -/

namespace Reference

/-- Edge labels: a "nonterminal" `A` and two "terminals" `B`, `C`. -/
inductive Lbl | A | B | C
  deriving DecidableEq, Repr

open Lbl

/-- The split rule `A[x,y] ↝ { B[x,y], C[x,y] }`: replace an `A`-edge by a `B`-edge and a `C`-edge on the
same two attachment nodes. A genuine hyperedge replacement. -/
def splitRule : Hyperedge Lbl Nat → List (Hyperedge Lbl Nat) → Prop :=
  fun e rhs => ∃ x y, e = (A, [x, y]) ∧ rhs = [(B, [x, y]), (C, [x, y])]

/-- The one-step reduction certificate `⟨[A 0 1]⟩ ↝ ⟨[B 0 1, C 0 1]⟩`. -/
def redChain : List (Hypergraph Lbl Nat) :=
  [ ⟨[(A, [0, 1])]⟩, ⟨[(B, [0, 1]), (C, [0, 1])]⟩ ]

/-- The certificate is valid: the single step is a genuine `splitRule` hyperedge replacement. -/
theorem red_cert :
    Cert (Reduces splitRule) ⟨[(A, [0, 1])]⟩ ⟨[(B, [0, 1]), (C, [0, 1])]⟩ redChain := by
  refine ⟨rfl, rfl, ?_, trivial⟩
  have h : Reduces splitRule ⟨[] ++ (A, [0, 1]) :: []⟩ ⟨[] ++ [(B, [0, 1]), (C, [0, 1])] ++ []⟩ :=
    Reduces.replace [] [] (A, [0, 1]) [(B, [0, 1]), (C, [0, 1])] ⟨0, 1, rfl, rfl⟩
  simpa using h

/-- **`red_reduces`** — via the bridge, the certificate proves the genuine reflexive-transitive reduction
`⟨[A 0 1]⟩ ↝* ⟨[B 0 1, C 0 1]⟩`. A concrete arbitrary-hypergraph-reduction proof from a checkable chain. -/
theorem red_reduces :
    Relation.ReflTransGen (Reduces splitRule) ⟨[(A, [0, 1])]⟩ ⟨[(B, [0, 1]), (C, [0, 1])]⟩ :=
  (hypergraph_reduction_bridge splitRule _ _).mp ⟨redChain, red_cert⟩

end Reference

end Dregg2.Crypto.Hypergraph
