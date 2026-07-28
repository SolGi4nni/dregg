/-
# Dregg2.Circuit.Emit.KimchiDag — the DAG SOURCE LANGUAGE, and why `Head` could not be it

## ⚑ THE RUNG THIS IS, AND THE MEASUREMENT THAT FORCED IT

`KimchiRootAirEval` generates `C_i` for two of the root's seven tables end-to-end from extractor
output — `expose_claim` (25 constraints ⇒ 88 packed rows) and `Alu` (92 ⇒ 1,180) — with
`airFold_forces` proving at an arbitrary `CommRing` that any assignment satisfying the emitted rows
puts p3's accumulator `fold_i (acc·α + C_i)` in the output variable. **117 of 901 base
constraints.** Its §7.2 then stopped, for a reason it stated precisely:

> All 901 base constraints are flat-`Head`-expressible — and must not be. `Head` is FLAT; p3's
> constraints are an `Arc`-shared DAG, and flattening destroys the sharing: **2,937 DAG multiplies
> against 1,529,889 flat — 521×** (804× on W24 alone). At ≈31 o1js rows per extension multiply that
> is ≈9.1 × 10⁴ rows sharing-preserving against **≈4.7 × 10⁷ flat — the flat form ALONE exceeds
> §3.14's ≈3.0 × 10⁷ whole-verifier budget.**

This file is that source language. `Node` is a **1:1 image of p3's `SymbolicExpr`** —
`Leaf`/`Add`/`Sub`/`Neg`/`Mul` — with each `Arc` child replaced by the INDEX of the node it became.
Nothing is distributed and nothing is expanded, so the extractor's job drops from an algebraic
rewrite to a re-indexing: a strictly narrower thing to get wrong than `to_head` (§7.1).

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored generation over a machine-checked lowering.** No Kimchi row below is
hand-written: every one is `packGen` output over `dagGens`, and `dagFold_forces` proves what the
emitted rows force. §6's node tables are EXTRACTOR OUTPUT, pasted verbatim.

## The three theorems that carry it

  * **`dagGens_forces`** — the analogue of `lowerHead_sound`, and the load-bearing one. Any
    assignment satisfying the emitted rows makes variable `nv + k` hold node `k`'s denotation, for
    EVERY `k`, at an arbitrary `CommRing`, over the actual emitted list. One `Gen1` per node.
  * **`dagDenote_unfold`** — **SHARING IS SOUND.** Node `k` is lowered to ONE variable `nv + k`,
    read by every parent that names it; this says that variable holds `evalNode` of `k`'s OWN
    children's denotations. So a node used twenty times contributes twenty occurrences of ONE
    value, not twenty independently-forced values a satisfying assignment could pull apart.
    Cheapness and soundness are the same fact here, and it is proved rather than assumed.
  * **`cseGo_denote`** — the frontend, going the other way. A TREE `Expr` compiled through a
    common-subexpression cache keyed on **structural identity** yields a DAG whose root denotes
    exactly `evalExpr` of the tree. So the sharing the cache introduces is value-preserving: the
    thing that turns 1,529,889 multiplies into 2,937 does not change what is computed.

## ⚑ WHAT IS AND IS NOT PROVED — read before citing

`dagWf` (every child index strictly below its parent's) is a **HYPOTHESIS, not a lemma**: an
out-of-order node list reads a child that has not been forced yet, and the soundness theorem is
false for it. It is `decide`-checked on every emitted table below, and the Rust emitter refuses to
print a DAG that fails it.

Nothing here proves the node tables ARE p3's constraints. That is the same seam
`KimchiRootAirEval` §7.1 names — narrowed, not closed (§7.1 below).

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`/`native_decide`.
NEW file; the single import `Dregg2.Circuit.Emit.KimchiRootAirEval` carries `Gen1`, `packGen`,
`rowsHold`, `Head` and the FLAT generator this rung is differentially checked against, through
`KimchiRootAirEval → KimchiLower → KimchiTarget → AirBuilder → DescriptorIR2`.
-/
import Dregg2.Circuit.Emit.KimchiRootAirEval

namespace Dregg2.Circuit.Emit.KimchiDag

open Dregg2.Circuit.Emit.AirBuilder (Head)
open Dregg2.Circuit.Emit.KimchiTarget
open Dregg2.Circuit.Emit.KimchiLower
open Dregg2.Circuit.Emit.KimchiRootAirEval

set_option autoImplicit false
set_option maxRecDepth 100000

/-! ## §1 — the source language.

`Node` mirrors `p3_air::symbolic::SymbolicExpr` constructor for constructor. `var` covers all four
non-constant `BaseLeaf`s (`Variable`, `IsFirstRow`, `IsLastRow`, `IsTransition`) because the
extractor resolves each to a column index through one `VarKey` numbering — the SAME numbering
`to_head` uses, which is what lets a DAG and a `Head` from the same AIR be compared at one
assignment. -/

/-- One SSA node. Children are INDICES into the node list, and `dagWf` requires them strictly below
the node's own index — so the list is topologically sorted and a node is defined before it is
read. -/
inductive Node where
  /-- A column of the opened values: `a c`. -/
  | var (c : Nat)
  /-- A compile-time constant, as a canonical BabyBear representative. -/
  | cst (k : ℤ)
  | add (i j : Nat)
  | sub (i j : Nat)
  | neg (i : Nat)
  | mul (i j : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- A constraint system: one shared node list plus the indices of the constraint ROOTS, in p3's own
order. -/
structure Dag where
  nodes : List Node
  roots : List Nat
  deriving Repr, Inhabited

/-! ### §1.1 — the denotation.

The value store is a plain function `Nat → R` extended one index at a time rather than an array.
That is deliberate: it makes the store DIRECTLY comparable with `fun k => a (nv + k)`, which is
what the soundness theorem has to say, and keeps every step to `if k = i then _ else _`. -/

/-- Extend a value store at one index. -/
def ext {R : Type} [CommRing R] (f : Nat → R) (i : Nat) (x : R) : Nat → R :=
  fun k => if k = i then x else f k

theorem ext_eq {R : Type} [CommRing R] (f : Nat → R) (i : Nat) (x : R) : ext f i x i = x := by
  simp [ext]

theorem ext_ne {R : Type} [CommRing R] (f : Nat → R) (i : Nat) (x : R) (k : Nat) (h : k ≠ i) :
    ext f i x k = f k := by
  simp [ext, h]

/-- One node's value, given the store of the nodes before it. -/
def evalNode {R : Type} [CommRing R] (a : Nat → R) (f : Nat → R) : Node → R
  | .var c => a c
  | .cst k => ((k : ℤ) : R)
  | .add i j => f i + f j
  | .sub i j => f i - f j
  | .neg i => - f i
  | .mul i j => f i * f j

/-- Thread the store through the node list, starting at index `i`. -/
def denoteGo {R : Type} [CommRing R] (a : Nat → R) : (Nat → R) → Nat → List Node → (Nat → R)
  | f, _, [] => f
  | f, i, n :: ns => denoteGo a (ext f i (evalNode a f n)) (i + 1) ns

/-- **THE DENOTATION.** `dagDenote a ns k` is the value of node `k`. -/
def dagDenote {R : Type} [CommRing R] (a : Nat → R) (ns : List Node) : Nat → R :=
  denoteGo a (fun _ => 0) 0 ns

/-! ### §1.2 — well-formedness, which is a HYPOTHESIS and not a lemma. -/

/-- Node `n`, sitting at index `i`, names only children strictly below `i`. -/
def nodeWf (i : Nat) : Node → Bool
  | .var _ => true
  | .cst _ => true
  | .neg x => decide (x < i)
  | .add x y => decide (x < i) && decide (y < i)
  | .sub x y => decide (x < i) && decide (y < i)
  | .mul x y => decide (x < i) && decide (y < i)

def dagWfGo : Nat → List Node → Bool
  | _, [] => true
  | i, n :: ns => nodeWf i n && dagWfGo (i + 1) ns

/-- **The topological-sort invariant.** Decidable, checked on every emitted table below, and
asserted by the Rust emitter, which refuses to print a DAG that fails it. -/
def dagWf (ns : List Node) : Bool := dagWfGo 0 ns

theorem dagWfGo_append : ∀ (xs ys : List Node) (b : Nat),
    dagWfGo b (xs ++ ys) = (dagWfGo b xs && dagWfGo (b + xs.length) ys) := by
  intro xs
  induction xs with
  | nil => intro ys b; simp [dagWfGo]
  | cons x xs ih =>
    intro ys b
    have hb : b + 1 + xs.length = b + (xs.length + 1) := by omega
    simp only [List.cons_append, dagWfGo, ih, List.length_cons, Bool.and_assoc, hb]

theorem dagWfGo_get : ∀ (ns : List Node) (b i : Nat) (h : i < ns.length),
    dagWfGo b ns = true → nodeWf (b + i) ns[i] = true := by
  intro ns
  induction ns with
  | nil => intro b i h; exact absurd h (by simp)
  | cons n ns ih =>
    intro b i h hwf
    simp only [dagWfGo, Bool.and_eq_true] at hwf
    cases i with
    | zero => simpa using hwf.1
    | succ m =>
      have hm : m < ns.length := by
        have : m + 1 < ns.length + 1 := by simpa using h
        omega
      have hb := ih (b + 1) m hm hwf.2
      have heq : b + (m + 1) = b + 1 + m := by omega
      rw [heq]
      simpa only [List.getElem_cons_succ] using hb

/-- Every node of a well-formed DAG names only earlier nodes. -/
theorem dagWf_get (ns : List Node) (i : Nat) (h : i < ns.length) (hwf : dagWf ns = true) :
    nodeWf i ns[i] = true := by
  have hb := dagWfGo_get ns 0 i h hwf
  simpa only [Nat.zero_add] using hb

/-! ## §2 — the lowering: ONE `Gen1` per node.

This is `SymbolicCompiler::compile_base`'s shape (`plonky3-recursion@0a4a554
circuit/src/symbolic/compiler.rs:47-124`) with the `CircuitBuilder` replaced by `Gen1` sub-gates:
node `k` is lowered to the single sub-gate that DEFINES variable `nv + k`, and every parent naming
`k` reads that one variable.

⚑ **The cost, and which sub-gates carry it.** Only `.mul` is a live extension multiply (≈31 o1js
rows, §3.10/§3.15). `.add`/`.sub`/`.neg`/`.var` lower to `Gen1.lin2`/`Gen1.scale` — a scale by a
COMPILE-TIME base coefficient and an add, which `AirEval.ts`'s `extScaleConst` prices as
free-modulo-reduction — and `.cst` is a pin. So `dagMulCount` is the number that prices `C_i`,
exactly as `extMulCount` is for the flat path. -/

/-- The sub-gate defining node `i`'s variable. -/
def nodeGen (nv i : Nat) : Node → Gen1
  | .var c => Gen1.scale c (nv + i) 1
  | .cst k => Gen1.const (nv + i) k
  | .add x y => Gen1.lin2 (nv + x) (nv + y) (nv + i) 1 1
  | .sub x y => Gen1.lin2 (nv + x) (nv + y) (nv + i) 1 (-1)
  | .neg x => Gen1.scale (nv + x) (nv + i) (-1)
  | .mul x y => Gen1.mul (nv + x) (nv + y) (nv + i)

def dagGensGo (nv : Nat) : Nat → List Node → List Gen1
  | _, [] => []
  | i, n :: ns => nodeGen nv i n :: dagGensGo nv (i + 1) ns

/-- **THE EMITTED NODE PROGRAM.** Fresh variables start at `nv`; the AIR's opened values and α
occupy indices below it. -/
def dagGens (ns : List Node) (nv : Nat) : List Gen1 := dagGensGo nv 0 ns

/-! ## §3 — soundness. -/

section Sound

variable {R : Type} [CommRing R]

/-- One node's sub-gate forces its variable to the node's value, given that its children's
variables already hold theirs. This is the whole induction step, and `nodeWf` is where an
out-of-order DAG would break it. -/
theorem nodeGen_forces (a : Nat → R) (f : Nat → R) (nv i : Nat) (n : Node)
    (hwf : nodeWf i n = true)
    (hpre : ∀ k, k < i → a (nv + k) = f k)
    (hg : (nodeGen nv i n).holds a) :
    a (nv + i) = evalNode a f n := by
  cases n with
  | var c =>
    have h := Gen1.scale_forces a c (nv + i) 1 hg
    simp only [evalNode]
    rw [h]; push_cast; ring
  | cst k =>
    have h := Gen1.const_forces a (nv + i) k hg
    simp only [evalNode]
    exact h
  | add x y =>
    simp only [nodeWf, Bool.and_eq_true, decide_eq_true_eq] at hwf
    have h := Gen1.lin2_forces a (nv + x) (nv + y) (nv + i) 1 1 hg
    rw [hpre x hwf.1, hpre y hwf.2] at h
    simp only [evalNode]
    rw [h]; push_cast; ring
  | sub x y =>
    simp only [nodeWf, Bool.and_eq_true, decide_eq_true_eq] at hwf
    have h := Gen1.lin2_forces a (nv + x) (nv + y) (nv + i) 1 (-1) hg
    rw [hpre x hwf.1, hpre y hwf.2] at h
    simp only [evalNode]
    rw [h]; push_cast; ring
  | neg x =>
    simp only [nodeWf, decide_eq_true_eq] at hwf
    have h := Gen1.scale_forces a (nv + x) (nv + i) (-1) hg
    rw [hpre x hwf] at h
    simp only [evalNode]
    rw [h]; push_cast; ring
  | mul x y =>
    simp only [nodeWf, Bool.and_eq_true, decide_eq_true_eq] at hwf
    have h := Gen1.mul_forces a (nv + x) (nv + y) (nv + i) hg
    rw [hpre x hwf.1, hpre y hwf.2] at h
    simp only [evalNode]
    exact h

/-- The generalised forcing statement, threaded over a prefix already forced. -/
theorem dagGensGo_forces (a : Nat → R) :
    ∀ (ns : List Node) (f : Nat → R) (i nv : Nat),
      dagWfGo i ns = true →
      (∀ k, k < i → a (nv + k) = f k) →
      gensHold a (dagGensGo nv i ns) →
      ∀ k, k < i + ns.length → a (nv + k) = denoteGo a f i ns k := by
  intro ns
  induction ns with
  | nil =>
    intro f i nv _ hpre _ k hk
    simp only [List.length_nil, Nat.add_zero] at hk
    simpa only [denoteGo] using hpre k hk
  | cons n ns ih =>
    intro f i nv hwf hpre hg k hk
    simp only [dagWfGo, Bool.and_eq_true] at hwf
    simp only [dagGensGo] at hg
    obtain ⟨hnode, hrest⟩ := gensHold_cons hg
    have hstep : a (nv + i) = evalNode a f n := nodeGen_forces a f nv i n hwf.1 hpre hnode
    have hpre' : ∀ m, m < i + 1 → a (nv + m) = ext f i (evalNode a f n) m := by
      intro m hm
      rcases Nat.lt_or_ge m i with hlt | hge
      · rw [ext_ne _ _ _ _ (by omega)]
        exact hpre m hlt
      · have hmi : m = i := by omega
        subst hmi
        rw [ext_eq]
        exact hstep
    have hk' : k < (i + 1) + ns.length := by
      simp only [List.length_cons] at hk; omega
    have := ih (ext f i (evalNode a f n)) (i + 1) nv hwf.2 hpre' hrest k hk'
    simpa only [denoteGo] using this

/-- **THE RUNG-8 THEOREM.** Any assignment satisfying every sub-gate this compiler emits makes
variable `nv + k` hold node `k`'s denotation — for EVERY node, at an ARBITRARY `CommRing`, over the
list actually handed to the backend. `lowerHead_sound`'s shape, one `Gen1` per DAG node instead of
one per monomial multiplication. -/
theorem dagGens_forces (a : Nat → R) (ns : List Node) (nv : Nat)
    (hwf : dagWf ns = true) (hg : gensHold a (dagGens ns nv)) :
    ∀ k, k < ns.length → a (nv + k) = dagDenote a ns k := by
  intro k hk
  exact dagGensGo_forces a ns (fun _ => 0) 0 nv hwf (by omega) hg k (by omega)

end Sound

/-! ## §4 — SHARING IS SOUND. -/

section Sharing

variable {R : Type} [CommRing R]

/-- `evalNode` reads only the children `nodeWf` bounds, so two stores agreeing below `i` give the
same value for a node sitting at `i`. -/
theorem evalNode_congr (a : Nat → R) (f g : Nat → R) (i : Nat) (n : Node)
    (hwf : nodeWf i n = true) (h : ∀ k, k < i → f k = g k) :
    evalNode a f n = evalNode a g n := by
  cases n with
  | var c => rfl
  | cst k => rfl
  | add x y =>
    simp only [nodeWf, Bool.and_eq_true, decide_eq_true_eq] at hwf
    simp only [evalNode, h x hwf.1, h y hwf.2]
  | sub x y =>
    simp only [nodeWf, Bool.and_eq_true, decide_eq_true_eq] at hwf
    simp only [evalNode, h x hwf.1, h y hwf.2]
  | neg x =>
    simp only [nodeWf, decide_eq_true_eq] at hwf
    simp only [evalNode, h x hwf]
  | mul x y =>
    simp only [nodeWf, Bool.and_eq_true, decide_eq_true_eq] at hwf
    simp only [evalNode, h x hwf.1, h y hwf.2]

/-- Later steps never disturb an index already written: the store is append-only. -/
theorem denoteGo_stable (a : Nat → R) :
    ∀ (ns : List Node) (f : Nat → R) (i k : Nat), k < i → denoteGo a f i ns k = f k := by
  intro ns
  induction ns with
  | nil => intro f i k _; rfl
  | cons n ns ih =>
    intro f i k hk
    simp only [denoteGo]
    rw [ih _ (i + 1) k (by omega), ext_ne _ _ _ _ (by omega)]

theorem denoteGo_append (a : Nat → R) :
    ∀ (ns ms : List Node) (f : Nat → R) (i : Nat),
      denoteGo a f i (ns ++ ms) = denoteGo a (denoteGo a f i ns) (i + ns.length) ms := by
  intro ns
  induction ns with
  | nil => intro ms f i; simp only [List.nil_append, denoteGo, List.length_nil, Nat.add_zero]
  | cons n ns ih =>
    intro ms f i
    simp only [List.cons_append, denoteGo, List.length_cons, ih]
    congr 1
    omega

/-- **Appending nodes never changes what an existing node denotes.** This is what makes a
hash-consing builder safe to grow: the values already proved stay proved. -/
theorem dagDenote_prefix (a : Nat → R) (ns ms : List Node) (k : Nat) (hk : k < ns.length) :
    dagDenote a (ns ++ ms) k = dagDenote a ns k := by
  simp only [dagDenote, denoteGo_append]
  exact denoteGo_stable a ms _ (0 + ns.length) k (by omega)

/-- The last node of a list denotes `evalNode` at the store the earlier nodes built. -/
theorem dagDenote_snoc (a : Nat → R) (ns : List Node) (n : Node) :
    dagDenote a (ns ++ [n]) ns.length = evalNode a (dagDenote a ns) n := by
  simp only [dagDenote, denoteGo_append, Nat.zero_add]
  simp only [denoteGo]
  rw [ext_eq]

/-- **SHARING IS SOUND.** Node `i` is lowered to exactly ONE variable, `nv + i`, and every parent
naming `i` reads that variable. This says the variable holds `evalNode` of `i`'s OWN children's
denotations — so the `m` occurrences of an `m`-times-shared node are `m` reads of one forced value,
never `m` values a satisfying assignment could pull apart. The 521× saving and its soundness are
the same fact. -/
theorem dagDenote_unfold (a : Nat → R) :
    ∀ (ns : List Node), dagWf ns = true → ∀ (i : Nat) (h : i < ns.length),
      dagDenote a ns i = evalNode a (dagDenote a ns) ns[i] := by
  intro ns
  induction ns using List.reverseRecOn with
  | nil => intro _ i h; exact absurd h (by simp)
  | append_singleton pre n ih =>
    intro hwf i h
    have hwfsplit : dagWfGo 0 pre = true ∧ dagWfGo (0 + pre.length) [n] = true := by
      have := hwf
      simp only [dagWf, dagWfGo_append, Bool.and_eq_true] at this
      exact this
    have hwfpre : dagWf pre = true := hwfsplit.1
    have hnwf : nodeWf pre.length n = true := by
      have := hwfsplit.2
      simp only [dagWfGo, Bool.and_eq_true, Nat.zero_add] at this
      exact this.1
    have hagree : ∀ k, k < pre.length → dagDenote a pre k = dagDenote a (pre ++ [n]) k := by
      intro k hk
      exact (dagDenote_prefix a pre [n] k hk).symm
    simp only [List.length_append, List.length_singleton] at h
    rcases Nat.lt_or_ge i pre.length with hlt | hge
    · have hget : (pre ++ [n])[i] = pre[i]'hlt := by
        simp only [List.getElem_append_left hlt]
      rw [hget, dagDenote_prefix a pre [n] i hlt, ih hwfpre i hlt]
      exact evalNode_congr a _ _ i _ (dagWf_get pre i hlt hwfpre)
        (fun k hk => hagree k (by omega))
    · have hi : i = pre.length := by omega
      subst hi
      have hget : (pre ++ [n])[pre.length] = n := by
        simp only [List.getElem_append_right (Nat.le_refl _)]
        simp
      rw [hget, dagDenote_snoc]
      exact evalNode_congr a _ _ pre.length n hnwf hagree

end Sharing

/-! ## §5 — THE CSE FRONTEND: a tree, a cache keyed on structural identity, a DAG.

p3's `SymbolicCompiler::compile_base` keys its cache on the raw `Arc` POINTER, so two structurally
identical but separately allocated subtrees stay separate. This one interns on the STRUCTURAL
identity of the already-numbered node, which is at least as sharing-preserving — and, unlike a
pointer, is a thing Lean can reason about.

The theorem is `cseGo_denote`: the DAG's root denotes exactly `evalExpr` of the source tree. That is
the statement that the sharing a cache introduces is VALUE-PRESERVING, which is the half a cost
argument cannot supply. -/

/-- The TREE source: what an unshared expression looks like. -/
inductive Expr where
  | var (c : Nat)
  | cst (k : ℤ)
  | add (l r : Expr)
  | sub (l r : Expr)
  | neg (e : Expr)
  | mul (l r : Expr)
  deriving Repr, DecidableEq, Inhabited

def evalExpr {R : Type} [CommRing R] (a : Nat → R) : Expr → R
  | .var c => a c
  | .cst k => ((k : ℤ) : R)
  | .add l r => evalExpr a l + evalExpr a r
  | .sub l r => evalExpr a l - evalExpr a r
  | .neg e => - evalExpr a e
  | .mul l r => evalExpr a l * evalExpr a r

/-- The cache lookup: structural identity, written out rather than taken from a `List` API whose
name moves between toolchains. -/
def findNode : List Node → Node → Option Nat
  | [], _ => none
  | m :: ms, n => if m = n then some 0 else (findNode ms n).map (· + 1)

/-- A cache HIT names a node that is really there, and really is the one asked for. -/
theorem findNode_get : ∀ (ns : List Node) (n : Node) (i : Nat), findNode ns n = some i →
    ∃ h : i < ns.length, ns[i] = n := by
  intro ns
  induction ns with
  | nil => intro n i h; exact absurd h (by simp [findNode])
  | cons m ms ih =>
    intro n i h
    simp only [findNode] at h
    by_cases hm : m = n
    · rw [if_pos hm] at h
      have hi : i = 0 := by simpa using h.symm
      subst hi
      exact ⟨by simp, by simpa using hm⟩
    · rw [if_neg hm] at h
      obtain ⟨j, hj, hij⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨hlt, hget⟩ := ih n j hj
      subst hij
      exact ⟨by simp only [List.length_cons]; omega, by simpa using hget⟩

/-- **Intern one node.** A structural hit returns the existing index and grows nothing; a miss
appends. -/
def intern (ns : List Node) (n : Node) : List Node × Nat :=
  match findNode ns n with
  | some i => (ns, i)
  | none => (ns ++ [n], ns.length)

/-- **THE CSE PASS.** Structural recursion on the tree; the node list threads through as the
cache. -/
def cseGo (ns : List Node) : Expr → List Node × Nat
  | .var c => intern ns (.var c)
  | .cst k => intern ns (.cst k)
  | .neg e => let p := cseGo ns e; intern p.1 (.neg p.2)
  | .add l r => let p := cseGo ns l; let q := cseGo p.1 r; intern q.1 (.add p.2 q.2)
  | .sub l r => let p := cseGo ns l; let q := cseGo p.1 r; intern q.1 (.sub p.2 q.2)
  | .mul l r => let p := cseGo ns l; let q := cseGo p.1 r; intern q.1 (.mul p.2 q.2)

/-! The definitional equations, named — `cseGo`'s body binds its recursive calls with `let`, which
`rw` cannot see through, and the `let` is deliberate: writing the calls out inline would recompute
each subtree and make the pass exponential in tree depth. -/

theorem cseGo_neg (ns : List Node) (e : Expr) :
    cseGo ns (.neg e) = intern (cseGo ns e).1 (Node.neg (cseGo ns e).2) := rfl

theorem cseGo_add (ns : List Node) (l r : Expr) :
    cseGo ns (.add l r)
      = intern (cseGo (cseGo ns l).1 r).1
          (Node.add (cseGo ns l).2 (cseGo (cseGo ns l).1 r).2) := rfl

theorem cseGo_sub (ns : List Node) (l r : Expr) :
    cseGo ns (.sub l r)
      = intern (cseGo (cseGo ns l).1 r).1
          (Node.sub (cseGo ns l).2 (cseGo (cseGo ns l).1 r).2) := rfl

theorem cseGo_mul (ns : List Node) (l r : Expr) :
    cseGo ns (.mul l r)
      = intern (cseGo (cseGo ns l).1 r).1
          (Node.mul (cseGo ns l).2 (cseGo (cseGo ns l).1 r).2) := rfl

/-- Compile a whole list of constraint trees against ONE shared cache — p3's `base_cache`, which
is declared outside the constraint loop and is what makes the multiply count a cross-constraint
number. -/
def cse (es : List Expr) : Dag :=
  let go : List Node × List Nat → Expr → List Node × List Nat :=
    fun st e => let p := cseGo st.1 e; (p.1, st.2 ++ [p.2])
  let r := es.foldl go ([], [])
  ⟨r.1, r.2⟩

section Cse

variable {R : Type} [CommRing R]

/-- Interning preserves well-formedness and every existing denotation, and puts `evalNode` of the
interned node at the returned index. -/
theorem intern_spec (a : Nat → R) (ns : List Node) (n : Node)
    (hwf : dagWf ns = true) (hn : nodeWf ns.length n = true) :
    dagWf (intern ns n).1 = true
      ∧ (∃ ms, (intern ns n).1 = ns ++ ms)
      ∧ (intern ns n).2 < (intern ns n).1.length
      ∧ dagDenote a (intern ns n).1 (intern ns n).2 = evalNode a (dagDenote a ns) n := by
  simp only [intern]
  cases hf : findNode ns n with
  | none =>
    refine ⟨?_, ⟨[n], rfl⟩, by simp, ?_⟩
    · simp only [dagWf, dagWfGo_append, Bool.and_eq_true]
      refine ⟨hwf, ?_⟩
      simp only [dagWfGo, Nat.zero_add, hn, Bool.true_and]
    · exact dagDenote_snoc a ns n
  | some i =>
    obtain ⟨hi, hget⟩ := findNode_get ns n i hf
    refine ⟨hwf, ⟨[], by simp⟩, hi, ?_⟩
    have hu := dagDenote_unfold a ns hwf i hi
    rw [hu, hget]

/-- **THE FRONTEND'S SOUNDNESS.** Whatever the cache does — hit or miss, at any depth — the index
`cseGo` returns denotes exactly the tree's value. So collapsing a tree into a DAG changes the cost
and not the meaning. -/
theorem cseGo_denote (a : Nat → R) :
    ∀ (e : Expr) (ns : List Node), dagWf ns = true →
      dagWf (cseGo ns e).1 = true
        ∧ (∃ ms, (cseGo ns e).1 = ns ++ ms)
        ∧ (cseGo ns e).2 < (cseGo ns e).1.length
        ∧ dagDenote a (cseGo ns e).1 (cseGo ns e).2 = evalExpr a e := by
  intro e
  induction e with
  | var c =>
    intro ns hwf
    have h := intern_spec a ns (.var c) hwf rfl
    simpa [cseGo, evalExpr, evalNode] using h
  | cst k =>
    intro ns hwf
    have h := intern_spec a ns (.cst k) hwf rfl
    simpa [cseGo, evalExpr, evalNode] using h
  | neg e ih =>
    intro ns hwf
    rw [cseGo_neg]
    obtain ⟨hwf1, ⟨ms, hms⟩, hlt1, hval1⟩ := ih ns hwf
    have hn : nodeWf (cseGo ns e).1.length (Node.neg (cseGo ns e).2) = true := by
      simpa [nodeWf] using hlt1
    obtain ⟨hwf2, ⟨ms2, hms2⟩, hlt2, hval2⟩ :=
      intern_spec a (cseGo ns e).1 (Node.neg (cseGo ns e).2) hwf1 hn
    refine ⟨hwf2, ⟨ms ++ ms2, by rw [hms2, hms, List.append_assoc]⟩, hlt2, ?_⟩
    rw [hval2]
    simp only [evalNode, evalExpr, hval1]
  | add l r ihl ihr =>
    intro ns hwf
    rw [cseGo_add]
    obtain ⟨hwfL, ⟨msL, hmsL⟩, hltL, hvalL⟩ := ihl ns hwf
    obtain ⟨hwfR, ⟨msR, hmsR⟩, hltR, hvalR⟩ := ihr (cseGo ns l).1 hwfL
    have hLmono : (cseGo ns l).1.length ≤ (cseGo (cseGo ns l).1 r).1.length := by
      rw [hmsR]; simp
    have hn : nodeWf (cseGo (cseGo ns l).1 r).1.length
        (Node.add (cseGo ns l).2 (cseGo (cseGo ns l).1 r).2) = true := by
      simp only [nodeWf, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by omega, hltR⟩
    obtain ⟨hwf2, ⟨ms2, hms2⟩, hlt2, hval2⟩ :=
      intern_spec a (cseGo (cseGo ns l).1 r).1
        (Node.add (cseGo ns l).2 (cseGo (cseGo ns l).1 r).2) hwfR hn
    refine ⟨hwf2, ⟨msL ++ msR ++ ms2, by rw [hms2, hmsR, hmsL]; simp [List.append_assoc]⟩,
      hlt2, ?_⟩
    rw [hval2]
    simp only [evalNode, evalExpr]
    rw [hvalR, ← hvalL, hmsR, dagDenote_prefix a (cseGo ns l).1 msR _ hltL]
  | sub l r ihl ihr =>
    intro ns hwf
    rw [cseGo_sub]
    obtain ⟨hwfL, ⟨msL, hmsL⟩, hltL, hvalL⟩ := ihl ns hwf
    obtain ⟨hwfR, ⟨msR, hmsR⟩, hltR, hvalR⟩ := ihr (cseGo ns l).1 hwfL
    have hLmono : (cseGo ns l).1.length ≤ (cseGo (cseGo ns l).1 r).1.length := by
      rw [hmsR]; simp
    have hn : nodeWf (cseGo (cseGo ns l).1 r).1.length
        (Node.sub (cseGo ns l).2 (cseGo (cseGo ns l).1 r).2) = true := by
      simp only [nodeWf, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by omega, hltR⟩
    obtain ⟨hwf2, ⟨ms2, hms2⟩, hlt2, hval2⟩ :=
      intern_spec a (cseGo (cseGo ns l).1 r).1
        (Node.sub (cseGo ns l).2 (cseGo (cseGo ns l).1 r).2) hwfR hn
    refine ⟨hwf2, ⟨msL ++ msR ++ ms2, by rw [hms2, hmsR, hmsL]; simp [List.append_assoc]⟩,
      hlt2, ?_⟩
    rw [hval2]
    simp only [evalNode, evalExpr]
    rw [hvalR, ← hvalL, hmsR, dagDenote_prefix a (cseGo ns l).1 msR _ hltL]
  | mul l r ihl ihr =>
    intro ns hwf
    rw [cseGo_mul]
    obtain ⟨hwfL, ⟨msL, hmsL⟩, hltL, hvalL⟩ := ihl ns hwf
    obtain ⟨hwfR, ⟨msR, hmsR⟩, hltR, hvalR⟩ := ihr (cseGo ns l).1 hwfL
    have hLmono : (cseGo ns l).1.length ≤ (cseGo (cseGo ns l).1 r).1.length := by
      rw [hmsR]; simp
    have hn : nodeWf (cseGo (cseGo ns l).1 r).1.length
        (Node.mul (cseGo ns l).2 (cseGo (cseGo ns l).1 r).2) = true := by
      simp only [nodeWf, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by omega, hltR⟩
    obtain ⟨hwf2, ⟨ms2, hms2⟩, hlt2, hval2⟩ :=
      intern_spec a (cseGo (cseGo ns l).1 r).1
        (Node.mul (cseGo ns l).2 (cseGo (cseGo ns l).1 r).2) hwfR hn
    refine ⟨hwf2, ⟨msL ++ msR ++ ms2, by rw [hms2, hmsR, hmsL]; simp [List.append_assoc]⟩,
      hlt2, ?_⟩
    rw [hval2]
    simp only [evalNode, evalExpr]
    rw [hvalR, ← hvalL, hmsR, dagDenote_prefix a (cseGo ns l).1 msR _ hltL]

end Cse

/-! ## §6 — the α-fold, which is the verifier's accumulator.

Identical in shape to `KimchiRootAirEval.foldGo` — p3's `VerifierConstraintFolder` starts the
accumulator at ZERO and runs `acc ← acc·α + C` once per constraint — except that the constraint's
value is not computed here: it is already sitting in the root node's variable. -/

/-- The fold over ROOT VARIABLES (absolute indices, already forced by `dagGens`). -/
def foldRootsGo : List Nat → Nat → Nat → Nat → Nat × Nat × List Gen1
  | [], acc, _, nv => (acc, nv, [])
  | r :: rs, acc, al, nv =>
      let rest := foldRootsGo rs (nv + 1) al (nv + 2)
      (rest.1, rest.2.1, Gen1.mul acc al nv :: Gen1.lin2 nv r (nv + 1) 1 1 :: rest.2.2)

/-- **THE EMITTED PROGRAM.** Every node, then a zero accumulator, then one Horner step per root. -/
def dagFoldGens (d : Dag) (al nv : Nat) : List Gen1 :=
  dagGens d.nodes nv
    ++ (Gen1.const (nv + d.nodes.length) 0
        :: (foldRootsGo (d.roots.map (fun r => nv + r)) (nv + d.nodes.length) al
              (nv + d.nodes.length + 1)).2.2)

/-- The variable holding the verifier's accumulator. -/
def dagFoldOut (d : Dag) (al nv : Nat) : Nat :=
  (foldRootsGo (d.roots.map (fun r => nv + r)) (nv + d.nodes.length) al
    (nv + d.nodes.length + 1)).1

/-- **The emitted Kimchi circuit**, packed two sub-gates to a row. -/
def dagFoldRows (d : Dag) (al nv : Nat) : List KRow := packGen (dagFoldGens d al nv)

/-- The Horner value the fold computes, stated independently of the circuit. -/
def dagHorner {R : Type} [CommRing R] (a : Nat → R) (al : Nat) (d : Dag) : R :=
  (d.roots.map (dagDenote a d.nodes)).foldl (fun s c => s * a al + c) 0

section Fold

variable {R : Type} [CommRing R]

theorem map_congr_mem {α β : Type} (l : List α) (f g : α → β) (h : ∀ x ∈ l, f x = g x) :
    l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons]
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

theorem foldRootsGo_forces (a : Nat → R) :
    ∀ (rs : List Nat) (acc al nv : Nat), gensHold a (foldRootsGo rs acc al nv).2.2 →
      a (foldRootsGo rs acc al nv).1
        = (rs.map a).foldl (fun s c => s * a al + c) (a acc) := by
  intro rs
  induction rs with
  | nil => intro acc al nv _; simp [foldRootsGo]
  | cons r rs ih =>
    intro acc al nv hg
    simp only [foldRootsGo] at hg ⊢
    obtain ⟨hmul, hg2⟩ := gensHold_cons hg
    obtain ⟨hlin, hg3⟩ := gensHold_cons hg2
    have hm : a nv = a acc * a al := Gen1.mul_forces a acc al nv hmul
    have hl : a (nv + 1) = (1 : ℤ) * a nv + (1 : ℤ) * a r :=
      Gen1.lin2_forces a nv r (nv + 1) 1 1 hlin
    have hrest := ih (nv + 1) al (nv + 2) hg3
    rw [hrest]
    simp only [List.map_cons, List.foldl_cons]
    congr 1
    rw [hl, hm]
    push_cast
    ring

/-- **THE TOP THEOREM, over the DAG.** Any assignment satisfying every Kimchi row this compiler
emits makes the output variable hold exactly `fold_i (acc·α + C_i)` from zero — the accumulator
`VerifierData::verify_constraints_with_lookups` compares against `quotient(ζ)·Z_H(ζ)`
(`p3-batch-stark/src/verifier/data.rs:96-100`).

Stated over the emitted object itself, over `rowsHold` (whose generic case is welded to the
reality-gated `KimchiVerify.genericGateConstraint`), and at an ARBITRARY `CommRing` — so it holds
over the extension the challenge actually lives in, not only over ℤ.

⚑ **What it does NOT say.** It does not say the `d` is p3's constraint system (§7.1). It does not
close the verifier: the closing equality, the real preamble, mixed-height MMCS openings,
19-queries-not-1 and the undischarged FRI floor all stand. -/
theorem dagFold_forces (a : Nat → R) (d : Dag) (al nv : Nat)
    (hwf : dagWf d.nodes = true)
    (hroots : ∀ r ∈ d.roots, r < d.nodes.length)
    (hr : rowsHold a (dagFoldRows d al nv)) :
    a (dagFoldOut d al nv) = dagHorner a al d := by
  rw [dagFoldRows, packGen_holds_iff] at hr
  simp only [dagFoldGens] at hr
  obtain ⟨hnodes, hfold⟩ := gensHold_append hr
  obtain ⟨hzero, hrest⟩ := gensHold_cons hfold
  have h0 : a (nv + d.nodes.length) = ((0 : ℤ) : R) :=
    Gen1.const_forces a (nv + d.nodes.length) 0 hzero
  have hnode := dagGens_forces a d.nodes nv hwf hnodes
  have hf := foldRootsGo_forces a (d.roots.map (fun r => nv + r)) (nv + d.nodes.length) al
    (nv + d.nodes.length + 1) hrest
  simp only [dagFoldOut, dagHorner]
  rw [hf, h0]
  simp only [List.map_map]
  have : (d.roots.map ((fun x => a x) ∘ fun r => nv + r))
      = d.roots.map (dagDenote a d.nodes) :=
    map_congr_mem d.roots _ _ (fun x hx => hnode x (hroots x hx))
  rw [this]
  norm_num

end Fold

/-! ## §7 — the cost model, as theorems over the emitted list. -/

/-- Is this node a live extension multiply? -/
def isMul : Node → Bool
  | .mul _ _ => true
  | _ => false

/-- **The number that prices `C_i`.** Only `.mul` is a full extension multiply (≈31 o1js rows);
every other node lowers to a scale-by-a-compile-time-constant and an add. -/
def dagMulCount (ns : List Node) : Nat := (ns.filter isMul).length

/-- Extension multiplies for the whole fold: the DAG's own, plus one α-multiply per root. -/
def dagFoldMulCount (d : Dag) : Nat := dagMulCount d.nodes + d.roots.length

/-- Sub-gates the whole program costs: one per node, the zero pin, two per root. -/
def dagFoldGenCount (d : Dag) : Nat := d.nodes.length + 1 + 2 * d.roots.length

theorem dagGensGo_length : ∀ (ns : List Node) (nv i : Nat),
    (dagGensGo nv i ns).length = ns.length := by
  intro ns
  induction ns with
  | nil => intro nv i; rfl
  | cons n ns ih => intro nv i; simp only [dagGensGo, List.length_cons, ih]

theorem dagGens_length (ns : List Node) (nv : Nat) : (dagGens ns nv).length = ns.length :=
  dagGensGo_length ns nv 0

theorem foldRootsGo_length : ∀ (rs : List Nat) (acc al nv : Nat),
    (foldRootsGo rs acc al nv).2.2.length = 2 * rs.length := by
  intro rs
  induction rs with
  | nil => intro acc al nv; rfl
  | cons r rs ih =>
    intro acc al nv
    simp only [foldRootsGo, List.length_cons, ih, List.length_cons]
    omega

theorem dagFoldGens_length (d : Dag) (al nv : Nat) :
    (dagFoldGens d al nv).length = dagFoldGenCount d := by
  simp only [dagFoldGens, dagFoldGenCount, List.length_append, List.length_cons,
    dagGens_length, foldRootsGo_length, List.length_map]
  omega

/-- **The row count is a THEOREM.** After packing, `⌈gens/2⌉` — the same halving `packGen_length`
prices. -/
theorem dagFoldRows_length (d : Dag) (al nv : Nat) :
    (dagFoldRows d al nv).length = (dagFoldGenCount d + 1) / 2 := by
  rw [dagFoldRows, packGen_length, dagFoldGens_length]

/-! ## §8 — anti-vacuity.

A soundness theorem over an emitted circuit is discharged for free if the circuit cannot be
satisfied. The same three obligations `KimchiRootAirEval` §4 meets, met again on the new object —
and one more, because the whole point of this rung is that it must agree with the old one. -/

/-- Every row the fold emits carries a MODELLED gate, so `dagFold_forces` is not discharged by
`KimchiTarget`'s fail-closed `False` on an unmodelled row. -/
theorem dagFoldRows_all_modelled (d : Dag) (al nv : Nat) :
    ∀ r ∈ dagFoldRows d al nv, r.gate.modelled = true :=
  packGen_all_modelled _

/-! ### §8.1 — the satisfying assignment, computed MODULO THE FIELD.

`KimchiRootAirEval`'s `runGens` executes over ℤ. That is fine for a flat `Head`: a monomial is a
product of at most four seeded columns. It is NOT fine for a DAG, where a node's value is a product
of two node values and the bit-length DOUBLES with depth — a 60-deep Poseidon2 DAG over ℤ would
carry `2^60`-bit integers and the check would not terminate in any useful sense.

So the run is done in the field the values actually live in: every push is reduced mod the BabyBear
prime, and acceptance is `body ≡ 0`. `dagFold_forces` holds at an ARBITRARY `CommRing`, so
instantiating the certificate at `ZMod 2013265921` is exactly on-statement rather than a weakening.
⚑ These are `#guard`s — evaluation at elaboration time, not proof terms — and are labelled as such
here rather than described as theorems. -/

/-- The BabyBear prime. -/
def bbP : ℤ := 2013265921

def rdP (x : ℤ) : ℤ := x % bbP

/-- Execute one sub-gate, requiring it to define the NEXT fresh variable. A `none` is an ALIASING
report on the generator, so the evaluator is a freshness audit as well as a witness. -/
def stepGenP (v : Array ℤ) (g : Gen1) : Option (Array ℤ) :=
  let l := v.getD g.l 0
  let r := v.getD g.r 0
  if g.co = -1 then
    if g.o = v.size then some (v.push (rdP (g.cl * l + g.cr * r + g.cm * (l * r) + g.cc)))
    else none
  else
    if g.l = v.size then some (v.push (rdP (-g.cc))) else none

def runGensP (v : Array ℤ) : List Gen1 → Option (Array ℤ)
  | [] => some v
  | g :: gs => match stepGenP v g with
    | none => none
    | some v' => runGensP v' gs

/-- Does every sub-gate hold in the field at this assignment? -/
def gensAcceptP (v : Array ℤ) (gs : List Gen1) : Bool :=
  gs.all fun g =>
    decide (rdP (g.cl * v.getD g.l 0 + g.cr * v.getD g.r 0 + g.co * v.getD g.o 0
      + g.cm * (v.getD g.l 0 * v.getD g.r 0) + g.cc) = 0)

/-- The DAG's own values, evaluated DIRECTLY — the independent oracle the circuit's output variable
is checked against, spanning the whole program rather than one gate. -/
def denoteZ (v : Array ℤ) : List Node → Array ℤ → Array ℤ
  | [], w => w
  | n :: ns, w =>
      let x := match n with
        | .var c => v.getD c 0
        | .cst k => k
        | .add i j => w.getD i 0 + w.getD j 0
        | .sub i j => w.getD i 0 - w.getD j 0
        | .neg i => - w.getD i 0
        | .mul i j => w.getD i 0 * w.getD j 0
      denoteZ v ns (w.push (rdP x))

/-- The Horner accumulator, computed from the DAG directly. -/
def dagHornerZ (v : Array ℤ) (al : Nat) (d : Dag) : ℤ :=
  let w := denoteZ v d.nodes #[]
  (d.roots.map (fun r => w.getD r 0)).foldl (fun s c => rdP (s * v.getD al 0 + c)) 0

/-- Run the emitted program for `d` over `nCols` seeded input columns, with α at column `nCols`.
`seedInputs` is `KimchiRootAirEval`'s — the SAME seeding the flat path uses, which is what makes
the two runs comparable. -/
def runDag (d : Dag) (nCols : Nat) : Option (Array ℤ) :=
  runGensP (seedInputs (nCols + 1)) (dagFoldGens d nCols (nCols + 1))

/-! ### §8.2 — the REGRESSION: the new path must denote what the old one denoted.

A compiler change that silently alters emitted semantics is the worst possible outcome, so the
existing differential IS the regression test. `hornerZ` is `KimchiRootAirEval`'s independent
evaluation of the FLAT heads; `dagHornerZ` is this file's independent evaluation of the SHARED DAG.
At the same seeding they must agree in the field. -/

/-- The flat path's accumulator, reduced into the field so the two evaluators are comparable. -/
def flatHornerP (nCols : Nat) (hs : List Head) : ℤ :=
  rdP (hornerZ (seedInputs (nCols + 1)) nCols hs)

def dagHornerP (d : Dag) (nCols : Nat) : ℤ :=
  rdP (dagHornerZ (seedInputs (nCols + 1)) nCols d)

/-! ## §9 — THE GENERATED TABLES.

⚑ **Nothing below was written by hand.** Every node list is verbatim output of `emit_lean_dag` in
`circuit-prove/tests/root_air_constraint_census.rs`, which walks
`p3_batch_stark::symbolic::get_symbolic_constraints` of the DEPLOYED AIR and replaces each `Arc`
child by the index of the node it became. `to_dag` refuses to print a DAG failing `dag_wf`, and
`dagWf` is `#guard`ed here as well, because a claim on the emitter's side is not a check on this
one.

⚑ **The four tables below are ALL 901 base constraints.** `Const`, `Public` and `recompose` have
ZERO base constraints — they are pure lookup tables — so there is nothing to emit for them and
nothing missing (§10.4).

Coefficients are canonical BabyBear representatives, so `2013265920` is `−1` and `2013265910` is
`−11`. Column numbering is the extractor's canonical order over the leaves the verifier holds at ζ,
and is **the same `VarKey` numbering `to_head` uses** — which is what makes §10.3's differential
against the flat path a comparison at one assignment rather than two.

The node lists are chunked at 512 for the elaborator's benefit; `++` is positional, so the indices
are the emitter's own.
-/

def aluDagC0 : List Node :=
  [  .var 0, .var 1, .var 2, .add 1 2, .var 3, .sub 3 4, .mul 0 5, .var 4, .var 5, .add 7 8, .var 6, .sub 9 10,
    .mul 0 11, .var 7, .var 8, .add 13 14, .var 9, .sub 15 16, .mul 0 17, .var 10, .var 11, .add 19 20,
    .var 12, .sub 21 22, .mul 0 23, .var 13, .neg 25, .var 14, .sub 26 27, .var 15, .sub 28 29, .var 16,
    .sub 30 31, .sub 32 0, .mul 1 2, .cst 11, .mul 7 20, .mul 35 36, .add 34 37, .mul 13 14, .mul 35 39,
    .add 38 40, .mul 19 8, .mul 35 42, .add 41 43, .sub 44 4, .mul 33 45, .mul 1 8, .mul 7 2, .add 47 48,
    .mul 13 20, .mul 35 50, .add 49 51, .mul 19 14, .mul 35 53, .add 52 54, .sub 55 10, .mul 33 56, .mul 1 14,
    .mul 7 8, .add 58 59, .mul 13 2, .add 60 61, .mul 19 20, .mul 35 63, .add 62 64, .sub 65 16, .mul 33 66,
    .mul 1 20, .mul 7 14, .add 68 69, .mul 13 8, .add 70 71, .mul 19 2, .add 72 73, .sub 74 22, .mul 33 75,
    .mul 27 1, .cst 1, .sub 1 78, .mul 77 79, .mul 27 7, .mul 27 13, .mul 27 19, .var 17, .add 44 84, .sub 85 4,
    .mul 29 86, .var 18, .add 55 88, .sub 89 10, .mul 29 90, .var 19, .add 65 92, .sub 93 16, .mul 29 94,
    .var 20, .add 74 96, .sub 97 22, .mul 29 98, .var 21, .var 22, .mul 2 2, .mul 8 20, .mul 35 103, .add 102 104,
    .mul 14 14, .mul 35 106, .add 105 107, .mul 20 8, .mul 35 109, .add 108 110, .sub 101 111, .mul 100 112,
    .var 23, .mul 2 8, .mul 8 2, .add 115 116, .mul 14 20, .mul 35 118, .add 117 119, .mul 20 14, .mul 35 121,
    .add 120 122, .sub 114 123, .mul 100 124, .var 24, .mul 2 14, .mul 8 8, .add 127 128, .mul 14 2, .add 129 130,
    .mul 20 20, .mul 35 132, .add 131 133, .sub 126 134, .mul 100 135, .var 25, .mul 2 20, .mul 8 14, .add 138 139,
    .mul 14 8, .add 140 141, .mul 20 2, .add 142 143, .sub 137 144, .mul 100 145, .var 26, .var 27, .mul 4 148,
    .var 28, .mul 10 150, .mul 35 151, .add 149 152, .var 29, .mul 16 154, .mul 35 155, .add 153 156, .var 30,
    .mul 22 158, .mul 35 159, .add 157 160, .var 31, .var 32, .mul 162 163, .var 33, .var 34, .mul 165 166,
    .mul 35 167, .add 164 168, .var 35, .var 36, .mul 170 171, .mul 35 172, .add 169 173, .var 37, .var 38,
    .mul 175 176, .mul 35 177, .add 174 178, .add 161 179, .var 39, .mul 181 163, .var 40, .mul 183 166,
    .mul 35 184, .add 182 185, .var 41, .mul 187 171, .mul 35 188, .add 186 189, .var 42, .mul 191 176,
    .mul 35 192, .add 190 193, .sub 180 194, .var 43, .add 195 196, .var 44, .sub 197 198, .var 45, .sub 199 200,
    .mul 147 201, .cst 0, .mul 4 158, .mul 10 148, .add 204 205, .mul 16 150, .mul 35 207, .add 206 208,
    .mul 22 154, .mul 35 210, .add 209 211, .mul 162 176, .mul 165 163, .add 213 214, .mul 170 166, .mul 35 216,
    .add 215 217, .mul 175 171, .mul 35 219, .add 218 220, .add 212 221, .mul 181 176, .mul 183 163, .add 223 224,
    .mul 187 166, .mul 35 226, .add 225 227, .mul 191 171, .mul 35 229, .add 228 230, .sub 222 231, .var 46,
    .add 232 233, .var 47, .sub 234 235, .var 48, .sub 236 237, .mul 147 238, .mul 4 154, .mul 10 158,
    .add 240 241, .mul 16 148, .add 242 243, .mul 22 150, .mul 35 245, .add 244 246, .mul 162 171, .mul 165 176,
    .add 248 249, .mul 170 163, .add 250 251, .mul 175 166, .mul 35 253, .add 252 254, .add 247 255, .mul 181 171,
    .mul 183 176, .add 257 258, .mul 187 163, .add 259 260, .mul 191 166, .mul 35 262, .add 261 263, .sub 256 264,
    .var 49, .add 265 266, .var 50, .sub 267 268, .var 51, .sub 269 270, .mul 147 271, .mul 4 150, .mul 10 154,
    .add 273 274, .mul 16 158, .add 275 276, .mul 22 148, .add 277 278, .mul 162 166, .mul 165 171, .add 280 281,
    .mul 170 176, .add 282 283, .mul 175 163, .add 284 285, .add 279 286, .mul 181 166, .mul 183 171, .add 288 289,
    .mul 187 176, .add 290 291, .mul 191 163, .add 292 293, .sub 287 294, .var 52, .add 295 296, .var 53,
    .sub 297 298, .var 54, .sub 299 300, .mul 147 301, .var 55, .sub 303 147, .mul 4 163, .mul 10 166,
    .mul 35 306, .add 305 307, .mul 16 171, .mul 35 309, .add 308 310, .mul 22 176, .mul 35 312, .add 311 313,
    .add 314 162, .sub 315 181, .sub 316 200, .mul 304 317, .mul 4 176, .mul 10 163, .add 319 320, .mul 16 166,
    .mul 35 322, .add 321 323, .mul 22 171, .mul 35 325, .add 324 326, .add 327 165, .sub 328 183, .sub 329 237,
    .mul 304 330, .mul 4 171, .mul 10 176, .add 332 333, .mul 16 163, .add 334 335, .mul 22 166, .mul 35 337,
    .add 336 338, .add 339 170, .sub 340 187, .sub 341 270, .mul 304 342, .mul 4 166, .mul 10 171, .add 344 345,
    .mul 16 176, .add 346 347, .mul 22 163, .add 348 349, .add 350 175, .sub 351 191, .sub 352 300, .mul 304 353,
    .var 56, .var 57, .var 58, .add 356 357, .var 59, .sub 358 359, .mul 355 360, .var 60, .var 61, .add 362 363,
    .var 62, .sub 364 365, .mul 355 366, .var 63, .var 64, .add 368 369, .var 65, .sub 370 371, .mul 355 372,
    .var 66, .var 67, .add 374 375, .var 68, .sub 376 377, .mul 355 378, .var 69, .neg 380, .var 70, .sub 381 382,
    .var 71, .sub 383 384, .var 72, .sub 385 386, .sub 387 355, .mul 356 357, .mul 362 375, .mul 35 390,
    .add 389 391, .mul 368 369, .mul 35 393, .add 392 394, .mul 374 363, .mul 35 396, .add 395 397, .sub 398 359,
    .mul 388 399, .mul 356 363, .mul 362 357, .add 401 402, .mul 368 375, .mul 35 404, .add 403 405, .mul 374 369,
    .mul 35 407, .add 406 408, .sub 409 365, .mul 388 410, .mul 356 369, .mul 362 363, .add 412 413, .mul 368 357,
    .add 414 415, .mul 374 375, .mul 35 417, .add 416 418, .sub 419 371, .mul 388 420, .mul 356 375, .mul 362 369,
    .add 422 423, .mul 368 363, .add 424 425, .mul 374 357, .add 426 427, .sub 428 377, .mul 388 429, .mul 382 356,
    .sub 356 78, .mul 431 432, .mul 382 362, .mul 382 368, .mul 382 374, .var 73, .add 398 437, .sub 438 359,
    .mul 384 439, .var 74, .add 409 441, .sub 442 365, .mul 384 443, .var 75, .add 419 445, .sub 446 371,
    .mul 384 447, .var 76, .add 428 449, .sub 450 377, .mul 384 451, .var 77, .var 78, .mul 359 454, .var 79,
    .mul 365 456, .mul 35 457, .add 455 458, .var 80, .mul 371 460, .mul 35 461, .add 459 462, .var 81,
    .mul 377 464, .mul 35 465, .add 463 466, .var 82, .add 467 468, .var 83, .sub 469 470, .var 84, .sub 471 472,
    .mul 453 473, .mul 359 464, .mul 365 454, .add 475 476, .mul 371 456, .mul 35 478, .add 477 479, .mul 377 460,
    .mul 35 481, .add 480 482, .var 85, .add 483 484, .var 86, .sub 485 486, .var 87, .sub 487 488, .mul 453 489,
    .mul 359 460, .mul 365 464, .add 491 492, .mul 371 454, .add 493 494, .mul 377 456, .mul 35 496, .add 495 497,
    .var 88, .add 498 499, .var 89, .sub 500 501, .var 90, .sub 502 503, .mul 453 504, .mul 359 456, .mul 365 460,
    .add 506 507, .mul 371 464, .add 508 509, .mul 377 454]

def aluDagC1 : List Node :=
  [  .add 510 511, .var 91, .add 512 513, .var 92, .sub 514 515, .var 93, .sub 516 517, .mul 453 518, .var 94,
    .var 95, .var 96, .add 521 522, .var 97, .sub 523 524, .mul 520 525, .var 98, .var 99, .add 527 528,
    .var 100, .sub 529 530, .mul 520 531, .var 101, .var 102, .add 533 534, .var 103, .sub 535 536, .mul 520 537,
    .var 104, .var 105, .add 539 540, .var 106, .sub 541 542, .mul 520 543, .var 107, .neg 545, .var 108,
    .sub 546 547, .var 109, .sub 548 549, .var 110, .sub 550 551, .sub 552 520, .mul 521 522, .mul 527 540,
    .mul 35 555, .add 554 556, .mul 533 534, .mul 35 558, .add 557 559, .mul 539 528, .mul 35 561, .add 560 562,
    .sub 563 524, .mul 553 564, .mul 521 528, .mul 527 522, .add 566 567, .mul 533 540, .mul 35 569, .add 568 570,
    .mul 539 534, .mul 35 572, .add 571 573, .sub 574 530, .mul 553 575, .mul 521 534, .mul 527 528, .add 577 578,
    .mul 533 522, .add 579 580, .mul 539 540, .mul 35 582, .add 581 583, .sub 584 536, .mul 553 585, .mul 521 540,
    .mul 527 534, .add 587 588, .mul 533 528, .add 589 590, .mul 539 522, .add 591 592, .sub 593 542, .mul 553 594,
    .mul 547 521, .sub 521 78, .mul 596 597, .mul 547 527, .mul 547 533, .mul 547 539, .var 111, .add 563 602,
    .sub 603 524, .mul 549 604, .var 112, .add 574 606, .sub 607 530, .mul 549 608, .var 113, .add 584 610,
    .sub 611 536, .mul 549 612, .var 114, .add 593 614, .sub 615 542, .mul 549 616, .var 115, .var 116,
    .mul 524 619, .var 117, .mul 530 621, .mul 35 622, .add 620 623, .var 118, .mul 536 625, .mul 35 626,
    .add 624 627, .var 119, .mul 542 629, .mul 35 630, .add 628 631, .var 120, .add 632 633, .var 121,
    .sub 634 635, .var 122, .sub 636 637, .mul 618 638, .mul 524 629, .mul 530 619, .add 640 641, .mul 536 621,
    .mul 35 643, .add 642 644, .mul 542 625, .mul 35 646, .add 645 647, .var 123, .add 648 649, .var 124,
    .sub 650 651, .var 125, .sub 652 653, .mul 618 654, .mul 524 625, .mul 530 629, .add 656 657, .mul 536 619,
    .add 658 659, .mul 542 621, .mul 35 661, .add 660 662, .var 126, .add 663 664, .var 127, .sub 665 666,
    .var 128, .sub 667 668, .mul 618 669, .mul 524 621, .mul 530 625, .add 671 672, .mul 536 629, .add 673 674,
    .mul 542 619, .add 675 676, .var 129, .add 677 678, .var 130, .sub 679 680, .var 131, .sub 681 682,
    .mul 618 683, .var 132, .var 133, .var 134, .add 686 687, .var 135, .sub 688 689, .mul 685 690, .var 136,
    .var 137, .add 692 693, .var 138, .sub 694 695, .mul 685 696, .var 139, .var 140, .add 698 699, .var 141,
    .sub 700 701, .mul 685 702, .var 142, .var 143, .add 704 705, .var 144, .sub 706 707, .mul 685 708,
    .var 145, .neg 710, .var 146, .sub 711 712, .var 147, .sub 713 714, .var 148, .sub 715 716, .sub 717 685,
    .mul 686 687, .mul 692 705, .mul 35 720, .add 719 721, .mul 698 699, .mul 35 723, .add 722 724, .mul 704 693,
    .mul 35 726, .add 725 727, .sub 728 689, .mul 718 729, .mul 686 693, .mul 692 687, .add 731 732, .mul 698 705,
    .mul 35 734, .add 733 735, .mul 704 699, .mul 35 737, .add 736 738, .sub 739 695, .mul 718 740, .mul 686 699,
    .mul 692 693, .add 742 743, .mul 698 687, .add 744 745, .mul 704 705, .mul 35 747, .add 746 748, .sub 749 701,
    .mul 718 750, .mul 686 705, .mul 692 699, .add 752 753, .mul 698 693, .add 754 755, .mul 704 687, .add 756 757,
    .sub 758 707, .mul 718 759, .mul 712 686, .sub 686 78, .mul 761 762, .mul 712 692, .mul 712 698, .mul 712 704,
    .var 149, .add 728 767, .sub 768 689, .mul 714 769, .var 150, .add 739 771, .sub 772 695, .mul 714 773,
    .var 151, .add 749 775, .sub 776 701, .mul 714 777, .var 152, .add 758 779, .sub 780 707, .mul 714 781,
    .var 153, .var 154, .mul 689 784, .var 155, .mul 695 786, .mul 35 787, .add 785 788, .var 156, .mul 701 790,
    .mul 35 791, .add 789 792, .var 157, .mul 707 794, .mul 35 795, .add 793 796, .var 158, .add 797 798,
    .var 159, .sub 799 800, .var 160, .sub 801 802, .mul 783 803, .mul 689 794, .mul 695 784, .add 805 806,
    .mul 701 786, .mul 35 808, .add 807 809, .mul 707 790, .mul 35 811, .add 810 812, .var 161, .add 813 814,
    .var 162, .sub 815 816, .var 163, .sub 817 818, .mul 783 819, .mul 689 790, .mul 695 794, .add 821 822,
    .mul 701 784, .add 823 824, .mul 707 786, .mul 35 826, .add 825 827, .var 164, .add 828 829, .var 165,
    .sub 830 831, .var 166, .sub 832 833, .mul 783 834, .mul 689 786, .mul 695 790, .add 836 837, .mul 701 794,
    .add 838 839, .mul 707 784, .add 840 841, .var 167, .add 842 843, .var 168, .sub 844 845, .var 169,
    .sub 846 847, .mul 783 848]

def aluDagNodes : List Node :=
  aluDagC0 ++ aluDagC1

def aluDagRoots : List Nat :=
  [  6, 12, 18, 24, 46, 57, 67, 76, 80, 81, 82, 83, 87, 91, 95, 99, 113, 125, 136, 146, 202, 203, 239, 203,
    272, 203, 302, 203, 318, 331, 343, 354, 361, 367, 373, 379, 400, 411, 421, 430, 433, 434, 435, 436,
    440, 444, 448, 452, 474, 490, 505, 519, 526, 532, 538, 544, 565, 576, 586, 595, 598, 599, 600, 601,
    605, 609, 613, 617, 639, 655, 670, 684, 691, 697, 703, 709, 730, 741, 751, 760, 763, 764, 765, 766,
    770, 774, 778, 782, 804, 820, 835, 849]

def aluDag : Dag := ⟨aluDagNodes, aluDagRoots⟩

def aluDagCols : Nat := 170

def exposeClaimDagC0 : List Node :=
  [  .var 0, .neg 0, .var 1, .var 2, .sub 2 3, .mul 1 4, .var 3, .neg 6, .var 4, .var 5, .sub 8 9, .mul 7 10,
    .var 6, .neg 12, .var 7, .var 8, .sub 14 15, .mul 13 16, .var 9, .neg 18, .var 10, .var 11, .sub 20 21,
    .mul 19 22, .var 12, .neg 24, .var 13, .var 14, .sub 26 27, .mul 25 28, .var 15, .neg 30, .var 16,
    .var 17, .sub 32 33, .mul 31 34, .var 18, .neg 36, .var 19, .var 20, .sub 38 39, .mul 37 40, .var 21,
    .neg 42, .var 22, .var 23, .sub 44 45, .mul 43 46, .var 24, .neg 48, .var 25, .var 26, .sub 50 51,
    .mul 49 52, .var 27, .neg 54, .var 28, .var 29, .sub 56 57, .mul 55 58, .var 30, .neg 60, .var 31,
    .var 32, .sub 62 63, .mul 61 64, .var 33, .neg 66, .var 34, .var 35, .sub 68 69, .mul 67 70, .var 36,
    .neg 72, .var 37, .var 38, .sub 74 75, .mul 73 76, .var 39, .neg 78, .var 40, .var 41, .sub 80 81,
    .mul 79 82, .var 42, .neg 84, .var 43, .var 44, .sub 86 87, .mul 85 88, .var 45, .neg 90, .var 46,
    .var 47, .sub 92 93, .mul 91 94, .var 48, .neg 96, .var 49, .var 50, .sub 98 99, .mul 97 100, .var 51,
    .neg 102, .var 52, .var 53, .sub 104 105, .mul 103 106, .var 54, .neg 108, .var 55, .var 56, .sub 110 111,
    .mul 109 112, .var 57, .neg 114, .var 58, .var 59, .sub 116 117, .mul 115 118, .var 60, .neg 120, .var 61,
    .var 62, .sub 122 123, .mul 121 124, .var 63, .neg 126, .var 64, .var 65, .sub 128 129, .mul 127 130,
    .var 66, .neg 132, .var 67, .var 68, .sub 134 135, .mul 133 136, .var 69, .neg 138, .var 70, .var 71,
    .sub 140 141, .mul 139 142, .var 72, .neg 144, .var 73, .var 74, .sub 146 147, .mul 145 148]

def exposeClaimDagNodes : List Node :=
  exposeClaimDagC0

def exposeClaimDagRoots : List Nat :=
  [  5, 11, 17, 23, 29, 35, 41, 47, 53, 59, 65, 71, 77, 83, 89, 95, 101, 107, 113, 119, 125, 131, 137, 143,
    149]

def exposeClaimDag : Dag := ⟨exposeClaimDagNodes, exposeClaimDagRoots⟩

def exposeClaimDagCols : Nat := 75

def p2w16DagC0 : List Node :=
  [  .var 0, .cst 1, .sub 0 1, .mul 0 2, .var 1, .var 2, .var 3, .var 4, .sub 6 7, .mul 5 8, .mul 4 9, .var 5,
    .var 6, .sub 11 12, .mul 5 13, .mul 4 14, .var 7, .var 8, .sub 16 17, .mul 5 18, .mul 4 19, .var 9,
    .var 10, .sub 21 22, .mul 5 23, .mul 4 24, .var 11, .var 12, .var 13, .sub 27 28, .mul 26 29, .mul 4 30,
    .var 14, .var 15, .sub 32 33, .mul 26 34, .mul 4 35, .var 16, .var 17, .sub 37 38, .mul 26 39, .mul 4 40,
    .var 18, .var 19, .sub 42 43, .mul 26 44, .mul 4 45, .var 20, .var 21, .var 22, .sub 48 49, .mul 47 50,
    .mul 4 51, .var 23, .var 24, .sub 53 54, .mul 47 55, .mul 4 56, .var 25, .var 26, .sub 58 59, .mul 47 60,
    .mul 4 61, .var 27, .var 28, .sub 63 64, .mul 47 65, .mul 4 66, .var 29, .var 30, .var 31, .sub 69 70,
    .mul 68 71, .mul 4 72, .var 32, .var 33, .sub 74 75, .mul 68 76, .mul 4 77, .var 34, .var 35, .sub 79 80,
    .mul 68 81, .mul 4 82, .var 36, .var 37, .sub 84 85, .mul 68 86, .mul 4 87, .var 38, .var 39, .sub 1 90,
    .mul 89 91, .mul 92 8, .mul 4 93, .mul 92 13, .mul 4 95, .mul 92 18, .mul 4 97, .mul 92 23, .mul 4 99,
    .var 40, .mul 101 91, .mul 102 29, .mul 4 103, .mul 102 34, .mul 4 105, .mul 102 39, .mul 4 107, .mul 102 44,
    .mul 4 109, .mul 89 90, .sub 48 7, .mul 111 112, .mul 4 113, .sub 53 12, .mul 111 115, .mul 4 116,
    .sub 58 17, .mul 111 118, .mul 4 119, .sub 63 22, .mul 111 121, .mul 4 122, .mul 101 90, .sub 69 28,
    .mul 124 125, .mul 4 126, .sub 74 33, .mul 124 128, .mul 4 129, .sub 79 38, .mul 124 131, .mul 4 132,
    .sub 84 43, .mul 124 134, .mul 4 135, .var 41, .sub 1 137, .var 42, .var 43, .var 44, .cst 2, .mul 141 142,
    .add 143 90, .sub 140 144, .mul 139 145, .mul 138 146, .mul 4 147, .var 45, .var 46, .var 47, .add 150 151,
    .var 48, .var 49, .add 153 154, .add 152 155, .add 156 151, .add 157 152, .var 50, .var 51, .add 159 160,
    .var 52, .var 53, .add 162 163, .add 161 164, .add 165 160, .add 166 161, .add 158 167, .var 54, .var 55,
    .add 169 170, .var 56, .var 57, .add 172 173, .add 171 174, .add 175 170, .add 176 171, .add 168 177,
    .var 58, .var 59, .add 179 180, .var 60, .var 61, .add 182 183, .add 181 184, .add 185 180, .add 186 181,
    .add 178 187, .add 158 188, .cst 1774958255, .add 189 190, .mul 191 191, .mul 192 191, .sub 149 193,
    .var 62, .add 153 153, .add 157 196, .add 162 162, .add 166 198, .add 197 199, .add 172 172, .add 176 201,
    .add 200 202, .add 182 182, .add 186 204, .add 203 205, .add 197 206, .cst 1185780729, .add 207 208,
    .mul 209 209, .mul 210 209, .sub 195 211, .var 63, .add 156 154, .add 214 155, .add 165 163, .add 216 164,
    .add 215 217, .add 175 173, .add 219 174, .add 218 220, .add 185 183, .add 222 184, .add 221 223, .add 215 224,
    .cst 1621102414, .add 225 226, .mul 227 227, .mul 228 227, .sub 213 229, .var 64, .add 150 150, .add 214 232,
    .add 159 159, .add 216 234, .add 233 235, .add 169 169, .add 219 237, .add 236 238, .add 179 179, .add 222 240,
    .add 239 241, .add 233 242, .cst 1796380621, .add 243 244, .mul 245 245, .mul 246 245, .sub 231 247,
    .var 65, .add 167 188, .cst 588815102, .add 250 251, .mul 252 252, .mul 253 252, .sub 249 254, .var 66,
    .add 199 206, .cst 1932426223, .add 257 258, .mul 259 259, .mul 260 259, .sub 256 261, .var 67, .add 217 224,
    .cst 1925334750, .add 264 265, .mul 266 266, .mul 267 266, .sub 263 268, .var 68, .add 235 242, .cst 747903232,
    .add 271 272, .mul 273 273, .mul 274 273, .sub 270 275, .var 69, .add 177 188, .cst 89648862, .add 278 279,
    .mul 280 280, .mul 281 280, .sub 277 282, .var 70, .add 202 206, .cst 360728943, .add 285 286, .mul 287 287,
    .mul 288 287, .sub 284 289, .var 71, .add 220 224, .cst 977184635, .add 292 293, .mul 294 294, .mul 295 294,
    .sub 291 296, .var 72, .add 238 242, .cst 1425273457, .add 299 300, .mul 301 301, .mul 302 301, .sub 298 303,
    .var 73, .add 187 188, .cst 256487465, .add 306 307, .mul 308 308, .mul 309 308, .sub 305 310, .var 74,
    .add 205 206, .cst 1200041953, .add 313 314, .mul 315 315, .mul 316 315, .sub 312 317, .var 75, .add 223 224,
    .cst 572403254, .add 320 321, .mul 322 322, .mul 323 322, .sub 319 324, .var 76, .add 241 242, .cst 448208942,
    .add 327 328, .mul 329 329, .mul 330 329, .sub 326 331, .mul 149 149, .mul 333 191, .mul 195 195, .mul 335 209,
    .add 334 336, .mul 213 213, .mul 338 227, .mul 231 231, .mul 340 245, .add 339 341, .add 337 342, .add 343 336,
    .add 344 337, .mul 249 249, .mul 346 252, .mul 256 256, .mul 348 259, .add 347 349, .mul 263 263, .mul 351 266,
    .mul 270 270, .mul 353 273, .add 352 354, .add 350 355, .add 356 349, .add 357 350, .add 345 358, .mul 277 277,
    .mul 360 280, .mul 284 284, .mul 362 287, .add 361 363, .mul 291 291, .mul 365 294, .mul 298 298, .mul 367 301,
    .add 366 368, .add 364 369, .add 370 363, .add 371 364, .add 359 372, .mul 305 305, .mul 374 308, .mul 312 312,
    .mul 376 315, .add 375 377, .mul 319 319, .mul 379 322, .mul 326 326, .mul 381 329, .add 380 382, .add 378 383,
    .add 384 377, .add 385 378, .add 373 386, .add 345 387, .var 77, .sub 388 389, .add 339 339, .add 344 391,
    .add 352 352, .add 357 393, .add 392 394, .add 366 366, .add 371 396, .add 395 397, .add 380 380, .add 385 399,
    .add 398 400, .add 392 401, .var 78, .sub 402 403, .add 343 341, .add 405 342, .add 356 354, .add 407 355,
    .add 406 408, .add 370 368, .add 410 369, .add 409 411, .add 384 382, .add 413 383, .add 412 414, .add 406 415,
    .var 79, .sub 416 417, .add 334 334, .add 405 419, .add 347 347, .add 407 421, .add 420 422, .add 361 361,
    .add 410 424, .add 423 425, .add 375 375, .add 413 427, .add 426 428, .add 420 429, .var 80, .sub 430 431,
    .add 358 387, .var 81, .sub 433 434, .add 394 401, .var 82, .sub 436 437, .add 408 415, .var 83, .sub 439 440,
    .add 422 429, .var 84, .sub 442 443, .add 372 387, .var 85, .sub 445 446, .add 397 401, .var 86, .sub 448 449,
    .add 411 415, .var 87, .sub 451 452, .add 425 429, .var 88, .sub 454 455, .add 386 387, .var 89, .sub 457 458,
    .add 400 401, .var 90, .sub 460 461, .add 414 415, .var 91, .sub 463 464, .add 428 429, .var 92, .sub 466 467,
    .var 93, .cst 1215789478, .add 389 470, .mul 471 471, .mul 472 471, .sub 469 473, .var 94, .cst 944884184,
    .add 403 476, .mul 477 477, .mul 478 477, .sub 475 479, .var 95, .cst 953948096, .add 417 482, .mul 483 483,
    .mul 484 483, .sub 481 485, .var 96, .cst 547326025, .add 431 488, .mul 489 489, .mul 490 489, .sub 487 491,
    .var 97, .cst 646827752, .add 434 494, .mul 495 495, .mul 496 495, .sub 493 497, .var 98, .cst 889997530,
    .add 437 500, .mul 501 501, .mul 502 501, .sub 499 503, .var 99, .cst 1536873262, .add 440 506, .mul 507 507,
    .mul 508 507, .sub 505 509, .var 100]

def p2w16DagC1 : List Node :=
  [  .cst 86189867, .add 443 512, .mul 513 513, .mul 514 513, .sub 511 515, .var 101, .cst 1065944411, .add 446 518,
    .mul 519 519, .mul 520 519, .sub 517 521, .var 102, .cst 32019634, .add 449 524, .mul 525 525, .mul 526 525,
    .sub 523 527, .var 103, .cst 333311454, .add 452 530, .mul 531 531, .mul 532 531, .sub 529 533, .var 104,
    .cst 456061748, .add 455 536, .mul 537 537, .mul 538 537, .sub 535 539, .var 105, .cst 1963448500,
    .add 458 542, .mul 543 543, .mul 544 543, .sub 541 545, .var 106, .cst 1827584334, .add 461 548, .mul 549 549,
    .mul 550 549, .sub 547 551, .var 107, .cst 1391160226, .add 464 554, .mul 555 555, .mul 556 555, .sub 553 557,
    .var 108, .cst 1348741381, .add 467 560, .mul 561 561, .mul 562 561, .sub 559 563, .mul 469 469, .mul 565 471,
    .mul 475 475, .mul 567 477, .add 566 568, .mul 481 481, .mul 570 483, .mul 487 487, .mul 572 489, .add 571 573,
    .add 569 574, .add 575 568, .add 576 569, .mul 493 493, .mul 578 495, .mul 499 499, .mul 580 501, .add 579 581,
    .mul 505 505, .mul 583 507, .mul 511 511, .mul 585 513, .add 584 586, .add 582 587, .add 588 581, .add 589 582,
    .add 577 590, .mul 517 517, .mul 592 519, .mul 523 523, .mul 594 525, .add 593 595, .mul 529 529, .mul 597 531,
    .mul 535 535, .mul 599 537, .add 598 600, .add 596 601, .add 602 595, .add 603 596, .add 591 604, .mul 541 541,
    .mul 606 543, .mul 547 547, .mul 608 549, .add 607 609, .mul 553 553, .mul 611 555, .mul 559 559, .mul 613 561,
    .add 612 614, .add 610 615, .add 616 609, .add 617 610, .add 605 618, .add 577 619, .var 109, .sub 620 621,
    .add 571 571, .add 576 623, .add 584 584, .add 589 625, .add 624 626, .add 598 598, .add 603 628, .add 627 629,
    .add 612 612, .add 617 631, .add 630 632, .add 624 633, .var 110, .sub 634 635, .add 575 573, .add 637 574,
    .add 588 586, .add 639 587, .add 638 640, .add 602 600, .add 642 601, .add 641 643, .add 616 614, .add 645 615,
    .add 644 646, .add 638 647, .var 111, .sub 648 649, .add 566 566, .add 637 651, .add 579 579, .add 639 653,
    .add 652 654, .add 593 593, .add 642 656, .add 655 657, .add 607 607, .add 645 659, .add 658 660, .add 652 661,
    .var 112, .sub 662 663, .add 590 619, .var 113, .sub 665 666, .add 626 633, .var 114, .sub 668 669,
    .add 640 647, .var 115, .sub 671 672, .add 654 661, .var 116, .sub 674 675, .add 604 619, .var 117,
    .sub 677 678, .add 629 633, .var 118, .sub 680 681, .add 643 647, .var 119, .sub 683 684, .add 657 661,
    .var 120, .sub 686 687, .add 618 619, .var 121, .sub 689 690, .add 632 633, .var 122, .sub 692 693,
    .add 646 647, .var 123, .sub 695 696, .add 660 661, .var 124, .sub 698 699, .var 125, .cst 88424255,
    .add 621 702, .mul 703 703, .mul 704 703, .sub 701 705, .var 126, .cst 104111868, .add 635 708, .mul 709 709,
    .mul 710 709, .sub 707 711, .var 127, .cst 1763866748, .add 649 714, .mul 715 715, .mul 716 715, .sub 713 717,
    .var 128, .cst 79691676, .add 663 720, .mul 721 721, .mul 722 721, .sub 719 723, .var 129, .cst 1988915530,
    .add 666 726, .mul 727 727, .mul 728 727, .sub 725 729, .var 130, .cst 1050669594, .add 669 732, .mul 733 733,
    .mul 734 733, .sub 731 735, .var 131, .cst 359890076, .add 672 738, .mul 739 739, .mul 740 739, .sub 737 741,
    .var 132, .cst 573163527, .add 675 744, .mul 745 745, .mul 746 745, .sub 743 747, .var 133, .cst 222820492,
    .add 678 750, .mul 751 751, .mul 752 751, .sub 749 753, .var 134, .cst 159256268, .add 681 756, .mul 757 757,
    .mul 758 757, .sub 755 759, .var 135, .cst 669703072, .add 684 762, .mul 763 763, .mul 764 763, .sub 761 765,
    .var 136, .cst 763177444, .add 687 768, .mul 769 769, .mul 770 769, .sub 767 771, .var 137, .cst 889367200,
    .add 690 774, .mul 775 775, .mul 776 775, .sub 773 777, .var 138, .cst 256335831, .add 693 780, .mul 781 781,
    .mul 782 781, .sub 779 783, .var 139, .cst 704371273, .add 696 786, .mul 787 787, .mul 788 787, .sub 785 789,
    .var 140, .cst 25886717, .add 699 792, .mul 793 793, .mul 794 793, .sub 791 795, .mul 701 701, .mul 797 703,
    .mul 707 707, .mul 799 709, .add 798 800, .mul 713 713, .mul 802 715, .mul 719 719, .mul 804 721, .add 803 805,
    .add 801 806, .add 807 800, .add 808 801, .mul 725 725, .mul 810 727, .mul 731 731, .mul 812 733, .add 811 813,
    .mul 737 737, .mul 815 739, .mul 743 743, .mul 817 745, .add 816 818, .add 814 819, .add 820 813, .add 821 814,
    .add 809 822, .mul 749 749, .mul 824 751, .mul 755 755, .mul 826 757, .add 825 827, .mul 761 761, .mul 829 763,
    .mul 767 767, .mul 831 769, .add 830 832, .add 828 833, .add 834 827, .add 835 828, .add 823 836, .mul 773 773,
    .mul 838 775, .mul 779 779, .mul 840 781, .add 839 841, .mul 785 785, .mul 843 787, .mul 791 791, .mul 845 793,
    .add 844 846, .add 842 847, .add 848 841, .add 849 842, .add 837 850, .add 809 851, .var 141, .sub 852 853,
    .add 803 803, .add 808 855, .add 816 816, .add 821 857, .add 856 858, .add 830 830, .add 835 860, .add 859 861,
    .add 844 844, .add 849 863, .add 862 864, .add 856 865, .var 142, .sub 866 867, .add 807 805, .add 869 806,
    .add 820 818, .add 871 819, .add 870 872, .add 834 832, .add 874 833, .add 873 875, .add 848 846, .add 877 847,
    .add 876 878, .add 870 879, .var 143, .sub 880 881, .add 798 798, .add 869 883, .add 811 811, .add 871 885,
    .add 884 886, .add 825 825, .add 874 888, .add 887 889, .add 839 839, .add 877 891, .add 890 892, .add 884 893,
    .var 144, .sub 894 895, .add 822 851, .var 145, .sub 897 898, .add 858 865, .var 146, .sub 900 901,
    .add 872 879, .var 147, .sub 903 904, .add 886 893, .var 148, .sub 906 907, .add 836 851, .var 149,
    .sub 909 910, .add 861 865, .var 150, .sub 912 913, .add 875 879, .var 151, .sub 915 916, .add 889 893,
    .var 152, .sub 918 919, .add 850 851, .var 153, .sub 921 922, .add 864 865, .var 154, .sub 924 925,
    .add 878 879, .var 155, .sub 927 928, .add 892 893, .var 156, .sub 930 931, .var 157, .cst 51754520,
    .add 853 934, .mul 935 935, .mul 936 935, .sub 933 937, .var 158, .cst 1833211857, .add 867 940, .mul 941 941,
    .mul 942 941, .sub 939 943, .var 159, .cst 454499742, .add 881 946, .mul 947 947, .mul 948 947, .sub 945 949,
    .var 160, .cst 1384520381, .add 895 952, .mul 953 953, .mul 954 953, .sub 951 955, .var 161, .cst 777848065,
    .add 898 958, .mul 959 959, .mul 960 959, .sub 957 961, .var 162, .cst 1053320300, .add 901 964, .mul 965 965,
    .mul 966 965, .sub 963 967, .var 163, .cst 1851729162, .add 904 970, .mul 971 971, .mul 972 971, .sub 969 973,
    .var 164, .cst 344647910, .add 907 976, .mul 977 977, .mul 978 977, .sub 975 979, .var 165, .cst 401996362,
    .add 910 982, .mul 983 983, .mul 984 983, .sub 981 985, .var 166, .cst 1046925956, .add 913 988, .mul 989 989,
    .mul 990 989, .sub 987 991, .var 167, .cst 5351995, .add 916 994, .mul 995 995, .mul 996 995, .sub 993 997,
    .var 168, .cst 1212119315, .add 919 1000, .mul 1001 1001, .mul 1002 1001, .sub 999 1003, .var 169,
    .cst 754867989, .add 922 1006, .mul 1007 1007, .mul 1008 1007, .sub 1005 1009, .var 170, .cst 36972490,
    .add 925 1012, .mul 1013 1013, .mul 1014 1013, .sub 1011 1015, .var 171, .cst 751272725, .add 928 1018,
    .mul 1019 1019, .mul 1020 1019, .sub 1017 1021, .var 172]

def p2w16DagC2 : List Node :=
  [  .cst 506915399, .add 931 1024, .mul 1025 1025, .mul 1026 1025, .sub 1023 1027, .mul 933 933, .mul 1029 935,
    .mul 939 939, .mul 1031 941, .add 1030 1032, .mul 945 945, .mul 1034 947, .mul 951 951, .mul 1036 953,
    .add 1035 1037, .add 1033 1038, .add 1039 1032, .add 1040 1033, .mul 957 957, .mul 1042 959, .mul 963 963,
    .mul 1044 965, .add 1043 1045, .mul 969 969, .mul 1047 971, .mul 975 975, .mul 1049 977, .add 1048 1050,
    .add 1046 1051, .add 1052 1045, .add 1053 1046, .add 1041 1054, .mul 981 981, .mul 1056 983, .mul 987 987,
    .mul 1058 989, .add 1057 1059, .mul 993 993, .mul 1061 995, .mul 999 999, .mul 1063 1001, .add 1062 1064,
    .add 1060 1065, .add 1066 1059, .add 1067 1060, .add 1055 1068, .mul 1005 1005, .mul 1070 1007, .mul 1011 1011,
    .mul 1072 1013, .add 1071 1073, .mul 1017 1017, .mul 1075 1019, .mul 1023 1023, .mul 1077 1025, .add 1076 1078,
    .add 1074 1079, .add 1080 1073, .add 1081 1074, .add 1069 1082, .add 1041 1083, .var 173, .sub 1084 1085,
    .add 1035 1035, .add 1040 1087, .add 1048 1048, .add 1053 1089, .add 1088 1090, .add 1062 1062, .add 1067 1092,
    .add 1091 1093, .add 1076 1076, .add 1081 1095, .add 1094 1096, .add 1088 1097, .var 174, .sub 1098 1099,
    .add 1039 1037, .add 1101 1038, .add 1052 1050, .add 1103 1051, .add 1102 1104, .add 1066 1064, .add 1106 1065,
    .add 1105 1107, .add 1080 1078, .add 1109 1079, .add 1108 1110, .add 1102 1111, .var 175, .sub 1112 1113,
    .add 1030 1030, .add 1101 1115, .add 1043 1043, .add 1103 1117, .add 1116 1118, .add 1057 1057, .add 1106 1120,
    .add 1119 1121, .add 1071 1071, .add 1109 1123, .add 1122 1124, .add 1116 1125, .var 176, .sub 1126 1127,
    .add 1054 1083, .var 177, .sub 1129 1130, .add 1090 1097, .var 178, .sub 1132 1133, .add 1104 1111,
    .var 179, .sub 1135 1136, .add 1118 1125, .var 180, .sub 1138 1139, .add 1068 1083, .var 181, .sub 1141 1142,
    .add 1093 1097, .var 182, .sub 1144 1145, .add 1107 1111, .var 183, .sub 1147 1148, .add 1121 1125,
    .var 184, .sub 1150 1151, .add 1082 1083, .var 185, .sub 1153 1154, .add 1096 1097, .var 186, .sub 1156 1157,
    .add 1110 1111, .var 187, .sub 1159 1160, .add 1124 1125, .var 188, .sub 1162 1163, .var 189, .cst 1518359488,
    .add 1085 1166, .mul 1167 1167, .mul 1168 1167, .sub 1165 1169, .mul 1165 1165, .mul 1171 1167, .var 190,
    .sub 1172 1173, .var 191, .add 1099 1113, .add 1176 1127, .add 1177 1130, .add 1178 1133, .add 1179 1136,
    .add 1180 1139, .add 1181 1142, .add 1182 1145, .add 1183 1148, .add 1184 1151, .add 1185 1154, .add 1186 1157,
    .add 1187 1160, .add 1188 1163, .sub 1189 1173, .cst 1765533241, .add 1190 1191, .mul 1192 1192, .mul 1193 1192,
    .sub 1175 1194, .mul 1175 1175, .mul 1196 1192, .var 192, .sub 1197 1198, .var 193, .add 1189 1173,
    .add 1099 1201, .add 1113 1113, .add 1203 1201, .add 1202 1204, .cst 1006632961, .mul 1127 1206, .add 1207 1201,
    .add 1205 1208, .add 1130 1130, .add 1201 1210, .add 1211 1130, .add 1209 1212, .add 1133 1133, .add 1214 1214,
    .add 1201 1215, .add 1213 1216, .mul 1136 1206, .sub 1201 1218, .add 1217 1219, .add 1139 1139, .add 1221 1139,
    .sub 1201 1222, .add 1220 1223, .add 1142 1142, .add 1225 1225, .sub 1201 1226, .add 1224 1227, .cst 2005401601,
    .mul 1145 1229, .add 1230 1201, .add 1228 1231, .cst 1509949441, .mul 1148 1233, .add 1234 1201, .add 1232 1235,
    .cst 1761607681, .mul 1151 1237, .add 1238 1201, .add 1236 1239, .cst 2013265906, .mul 1154 1241, .add 1242 1201,
    .add 1240 1243, .mul 1157 1229, .sub 1201 1245, .add 1244 1246, .cst 1887436801, .mul 1160 1248, .sub 1201 1249,
    .add 1247 1250, .mul 1163 1241, .sub 1201 1252, .add 1251 1253, .sub 1254 1198, .cst 945325693, .add 1255 1256,
    .mul 1257 1257, .mul 1258 1257, .sub 1200 1259, .mul 1200 1200, .mul 1261 1257, .var 194, .sub 1262 1263,
    .var 195, .add 1254 1198, .add 1202 1266, .add 1204 1204, .add 1268 1266, .add 1267 1269, .mul 1208 1206,
    .add 1271 1266, .add 1270 1272, .add 1212 1212, .add 1266 1274, .add 1275 1212, .add 1273 1276, .add 1216 1216,
    .add 1278 1278, .add 1266 1279, .add 1277 1280, .mul 1219 1206, .sub 1266 1282, .add 1281 1283, .add 1223 1223,
    .add 1285 1223, .sub 1266 1286, .add 1284 1287, .add 1227 1227, .add 1289 1289, .sub 1266 1290, .add 1288 1291,
    .mul 1231 1229, .add 1293 1266, .add 1292 1294, .mul 1235 1233, .add 1296 1266, .add 1295 1297, .mul 1239 1237,
    .add 1299 1266, .add 1298 1300, .mul 1243 1241, .add 1302 1266, .add 1301 1303, .mul 1246 1229, .sub 1266 1305,
    .add 1304 1306, .mul 1250 1248, .sub 1266 1308, .add 1307 1309, .mul 1253 1241, .sub 1266 1311, .add 1310 1312,
    .sub 1313 1263, .cst 422793067, .add 1314 1315, .mul 1316 1316, .mul 1317 1316, .sub 1265 1318, .mul 1265 1265,
    .mul 1320 1316, .var 196, .sub 1321 1322, .var 197, .add 1313 1263, .add 1267 1325, .add 1269 1269,
    .add 1327 1325, .add 1326 1328, .mul 1272 1206, .add 1330 1325, .add 1329 1331, .add 1276 1276, .add 1325 1333,
    .add 1334 1276, .add 1332 1335, .add 1280 1280, .add 1337 1337, .add 1325 1338, .add 1336 1339, .mul 1283 1206,
    .sub 1325 1341, .add 1340 1342, .add 1287 1287, .add 1344 1287, .sub 1325 1345, .add 1343 1346, .add 1291 1291,
    .add 1348 1348, .sub 1325 1349, .add 1347 1350, .mul 1294 1229, .add 1352 1325, .add 1351 1353, .mul 1297 1233,
    .add 1355 1325, .add 1354 1356, .mul 1300 1237, .add 1358 1325, .add 1357 1359, .mul 1303 1241, .add 1361 1325,
    .add 1360 1362, .mul 1306 1229, .sub 1325 1364, .add 1363 1365, .mul 1309 1248, .sub 1325 1367, .add 1366 1368,
    .mul 1312 1241, .sub 1325 1370, .add 1369 1371, .sub 1372 1322, .cst 311365592, .add 1373 1374, .mul 1375 1375,
    .mul 1376 1375, .sub 1324 1377, .mul 1324 1324, .mul 1379 1375, .var 198, .sub 1380 1381, .var 199,
    .add 1372 1322, .add 1326 1384, .add 1328 1328, .add 1386 1384, .add 1385 1387, .mul 1331 1206, .add 1389 1384,
    .add 1388 1390, .add 1335 1335, .add 1384 1392, .add 1393 1335, .add 1391 1394, .add 1339 1339, .add 1396 1396,
    .add 1384 1397, .add 1395 1398, .mul 1342 1206, .sub 1384 1400, .add 1399 1401, .add 1346 1346, .add 1403 1346,
    .sub 1384 1404, .add 1402 1405, .add 1350 1350, .add 1407 1407, .sub 1384 1408, .add 1406 1409, .mul 1353 1229,
    .add 1411 1384, .add 1410 1412, .mul 1356 1233, .add 1414 1384, .add 1413 1415, .mul 1359 1237, .add 1417 1384,
    .add 1416 1418, .mul 1362 1241, .add 1420 1384, .add 1419 1421, .mul 1365 1229, .sub 1384 1423, .add 1422 1424,
    .mul 1368 1248, .sub 1384 1426, .add 1425 1427, .mul 1371 1241, .sub 1384 1429, .add 1428 1430, .sub 1431 1381,
    .cst 1311448267, .add 1432 1433, .mul 1434 1434, .mul 1435 1434, .sub 1383 1436, .mul 1383 1383, .mul 1438 1434,
    .var 200, .sub 1439 1440, .var 201, .add 1431 1381, .add 1385 1443, .add 1387 1387, .add 1445 1443,
    .add 1444 1446, .mul 1390 1206, .add 1448 1443, .add 1447 1449, .add 1394 1394, .add 1443 1451, .add 1452 1394,
    .add 1450 1453, .add 1398 1398, .add 1455 1455, .add 1443 1456, .add 1454 1457, .mul 1401 1206, .sub 1443 1459,
    .add 1458 1460, .add 1405 1405, .add 1462 1405, .sub 1443 1463, .add 1461 1464, .add 1409 1409, .add 1466 1466,
    .sub 1443 1467, .add 1465 1468, .mul 1412 1229, .add 1470 1443, .add 1469 1471, .mul 1415 1233, .add 1473 1443,
    .add 1472 1474, .mul 1418 1237, .add 1476 1443, .add 1475 1477, .mul 1421 1241, .add 1479 1443, .add 1478 1480,
    .mul 1424 1229, .sub 1443 1482, .add 1481 1483, .mul 1427 1248, .sub 1443 1485, .add 1484 1486, .mul 1430 1241,
    .sub 1443 1488, .add 1487 1489, .sub 1490 1440, .cst 1629555936, .add 1491 1492, .mul 1493 1493, .mul 1494 1493,
    .sub 1442 1495, .mul 1442 1442, .mul 1497 1493, .var 202, .sub 1498 1499, .var 203, .add 1490 1440,
    .add 1444 1502, .add 1446 1446, .add 1504 1502, .add 1503 1505, .mul 1449 1206, .add 1507 1502, .add 1506 1508,
    .add 1453 1453, .add 1502 1510, .add 1511 1453, .add 1509 1512, .add 1457 1457, .add 1514 1514, .add 1502 1515,
    .add 1513 1516, .mul 1460 1206, .sub 1502 1518, .add 1517 1519, .add 1464 1464, .add 1521 1464, .sub 1502 1522,
    .add 1520 1523, .add 1468 1468, .add 1525 1525, .sub 1502 1526, .add 1524 1527, .mul 1471 1229, .add 1529 1502,
    .add 1528 1530, .mul 1474 1233, .add 1532 1502, .add 1531 1533, .mul 1477 1237]

def p2w16DagC3 : List Node :=
  [  .add 1535 1502, .add 1534 1536, .mul 1480 1241, .add 1538 1502, .add 1537 1539, .mul 1483 1229, .sub 1502 1541,
    .add 1540 1542, .mul 1486 1248, .sub 1502 1544, .add 1543 1545, .mul 1489 1241, .sub 1502 1547, .add 1546 1548,
    .sub 1549 1499, .cst 1009879353, .add 1550 1551, .mul 1552 1552, .mul 1553 1552, .sub 1501 1554, .mul 1501 1501,
    .mul 1556 1552, .var 204, .sub 1557 1558, .var 205, .add 1549 1499, .add 1503 1561, .add 1505 1505,
    .add 1563 1561, .add 1562 1564, .mul 1508 1206, .add 1566 1561, .add 1565 1567, .add 1512 1512, .add 1561 1569,
    .add 1570 1512, .add 1568 1571, .add 1516 1516, .add 1573 1573, .add 1561 1574, .add 1572 1575, .mul 1519 1206,
    .sub 1561 1577, .add 1576 1578, .add 1523 1523, .add 1580 1523, .sub 1561 1581, .add 1579 1582, .add 1527 1527,
    .add 1584 1584, .sub 1561 1585, .add 1583 1586, .mul 1530 1229, .add 1588 1561, .add 1587 1589, .mul 1533 1233,
    .add 1591 1561, .add 1590 1592, .mul 1536 1237, .add 1594 1561, .add 1593 1595, .mul 1539 1241, .add 1597 1561,
    .add 1596 1598, .mul 1542 1229, .sub 1561 1600, .add 1599 1601, .mul 1545 1248, .sub 1561 1603, .add 1602 1604,
    .mul 1548 1241, .sub 1561 1606, .add 1605 1607, .sub 1608 1558, .cst 190525218, .add 1609 1610, .mul 1611 1611,
    .mul 1612 1611, .sub 1560 1613, .mul 1560 1560, .mul 1615 1611, .var 206, .sub 1616 1617, .var 207,
    .add 1608 1558, .add 1562 1620, .add 1564 1564, .add 1622 1620, .add 1621 1623, .mul 1567 1206, .add 1625 1620,
    .add 1624 1626, .add 1571 1571, .add 1620 1628, .add 1629 1571, .add 1627 1630, .add 1575 1575, .add 1632 1632,
    .add 1620 1633, .add 1631 1634, .mul 1578 1206, .sub 1620 1636, .add 1635 1637, .add 1582 1582, .add 1639 1582,
    .sub 1620 1640, .add 1638 1641, .add 1586 1586, .add 1643 1643, .sub 1620 1644, .add 1642 1645, .mul 1589 1229,
    .add 1647 1620, .add 1646 1648, .mul 1592 1233, .add 1650 1620, .add 1649 1651, .mul 1595 1237, .add 1653 1620,
    .add 1652 1654, .mul 1598 1241, .add 1656 1620, .add 1655 1657, .mul 1601 1229, .sub 1620 1659, .add 1658 1660,
    .mul 1604 1248, .sub 1620 1662, .add 1661 1663, .mul 1607 1241, .sub 1620 1665, .add 1664 1666, .sub 1667 1617,
    .cst 786108885, .add 1668 1669, .mul 1670 1670, .mul 1671 1670, .sub 1619 1672, .mul 1619 1619, .mul 1674 1670,
    .var 208, .sub 1675 1676, .var 209, .add 1667 1617, .add 1621 1679, .add 1623 1623, .add 1681 1679,
    .add 1680 1682, .mul 1626 1206, .add 1684 1679, .add 1683 1685, .add 1630 1630, .add 1679 1687, .add 1688 1630,
    .add 1686 1689, .add 1634 1634, .add 1691 1691, .add 1679 1692, .add 1690 1693, .mul 1637 1206, .sub 1679 1695,
    .add 1694 1696, .add 1641 1641, .add 1698 1641, .sub 1679 1699, .add 1697 1700, .add 1645 1645, .add 1702 1702,
    .sub 1679 1703, .add 1701 1704, .mul 1648 1229, .add 1706 1679, .add 1705 1707, .mul 1651 1233, .add 1709 1679,
    .add 1708 1710, .mul 1654 1237, .add 1712 1679, .add 1711 1713, .mul 1657 1241, .add 1715 1679, .add 1714 1716,
    .mul 1660 1229, .sub 1679 1718, .add 1717 1719, .mul 1663 1248, .sub 1679 1721, .add 1720 1722, .mul 1666 1241,
    .sub 1679 1724, .add 1723 1725, .sub 1726 1676, .cst 557776863, .add 1727 1728, .mul 1729 1729, .mul 1730 1729,
    .sub 1678 1731, .mul 1678 1678, .mul 1733 1729, .var 210, .sub 1734 1735, .var 211, .add 1726 1676,
    .add 1680 1738, .add 1682 1682, .add 1740 1738, .add 1739 1741, .mul 1685 1206, .add 1743 1738, .add 1742 1744,
    .add 1689 1689, .add 1738 1746, .add 1747 1689, .add 1745 1748, .add 1693 1693, .add 1750 1750, .add 1738 1751,
    .add 1749 1752, .mul 1696 1206, .sub 1738 1754, .add 1753 1755, .add 1700 1700, .add 1757 1700, .sub 1738 1758,
    .add 1756 1759, .add 1704 1704, .add 1761 1761, .sub 1738 1762, .add 1760 1763, .mul 1707 1229, .add 1765 1738,
    .add 1764 1766, .mul 1710 1233, .add 1768 1738, .add 1767 1769, .mul 1713 1237, .add 1771 1738, .add 1770 1772,
    .mul 1716 1241, .add 1774 1738, .add 1773 1775, .mul 1719 1229, .sub 1738 1777, .add 1776 1778, .mul 1722 1248,
    .sub 1738 1780, .add 1779 1781, .mul 1725 1241, .sub 1738 1783, .add 1782 1784, .sub 1785 1735, .cst 212616710,
    .add 1786 1787, .mul 1788 1788, .mul 1789 1788, .sub 1737 1790, .mul 1737 1737, .mul 1792 1788, .var 212,
    .sub 1793 1794, .var 213, .add 1785 1735, .add 1739 1797, .add 1741 1741, .add 1799 1797, .add 1798 1800,
    .mul 1744 1206, .add 1802 1797, .add 1801 1803, .add 1748 1748, .add 1797 1805, .add 1806 1748, .add 1804 1807,
    .add 1752 1752, .add 1809 1809, .add 1797 1810, .add 1808 1811, .mul 1755 1206, .sub 1797 1813, .add 1812 1814,
    .add 1759 1759, .add 1816 1759, .sub 1797 1817, .add 1815 1818, .add 1763 1763, .add 1820 1820, .sub 1797 1821,
    .add 1819 1822, .mul 1766 1229, .add 1824 1797, .add 1823 1825, .mul 1769 1233, .add 1827 1797, .add 1826 1828,
    .mul 1772 1237, .add 1830 1797, .add 1829 1831, .mul 1775 1241, .add 1833 1797, .add 1832 1834, .mul 1778 1229,
    .sub 1797 1836, .add 1835 1837, .mul 1781 1248, .sub 1797 1839, .add 1838 1840, .mul 1784 1241, .sub 1797 1842,
    .add 1841 1843, .sub 1844 1794, .cst 605745517, .add 1845 1846, .mul 1847 1847, .mul 1848 1847, .sub 1796 1849,
    .mul 1796 1796, .mul 1851 1847, .var 214, .sub 1852 1853, .var 215, .add 1844 1794, .add 1798 1856,
    .add 1800 1800, .add 1858 1856, .add 1857 1859, .mul 1803 1206, .add 1861 1856, .add 1860 1862, .add 1807 1807,
    .add 1856 1864, .add 1865 1807, .add 1863 1866, .add 1811 1811, .add 1868 1868, .add 1856 1869, .add 1867 1870,
    .mul 1814 1206, .sub 1856 1872, .add 1871 1873, .add 1818 1818, .add 1875 1818, .sub 1856 1876, .add 1874 1877,
    .add 1822 1822, .add 1879 1879, .sub 1856 1880, .add 1878 1881, .mul 1825 1229, .add 1883 1856, .add 1882 1884,
    .mul 1828 1233, .add 1886 1856, .add 1885 1887, .mul 1831 1237, .add 1889 1856, .add 1888 1890, .mul 1834 1241,
    .add 1892 1856, .add 1891 1893, .mul 1837 1229, .sub 1856 1895, .add 1894 1896, .mul 1840 1248, .sub 1856 1898,
    .add 1897 1899, .mul 1843 1241, .sub 1856 1901, .add 1900 1902, .sub 1903 1853, .cst 1922082829, .add 1904 1905,
    .mul 1906 1906, .mul 1907 1906, .sub 1855 1908, .var 216, .add 1903 1853, .add 1857 1911, .cst 1870549801,
    .add 1912 1913, .mul 1914 1914, .mul 1915 1914, .sub 1910 1916, .var 217, .add 1859 1859, .add 1919 1911,
    .cst 1502529704, .add 1920 1921, .mul 1922 1922, .mul 1923 1922, .sub 1918 1924, .var 218, .mul 1862 1206,
    .add 1927 1911, .cst 1990744480, .add 1928 1929, .mul 1930 1930, .mul 1931 1930, .sub 1926 1932, .var 219,
    .add 1866 1866, .add 1911 1935, .add 1936 1866, .cst 1700391016, .add 1937 1938, .mul 1939 1939, .mul 1940 1939,
    .sub 1934 1941, .var 220, .add 1870 1870, .add 1944 1944, .add 1911 1945, .cst 1702593455, .add 1946 1947,
    .mul 1948 1948, .mul 1949 1948, .sub 1943 1950, .var 221, .mul 1873 1206, .sub 1911 1953, .cst 321330495,
    .add 1954 1955, .mul 1956 1956, .mul 1957 1956, .sub 1952 1958, .var 222, .add 1877 1877, .add 1961 1877,
    .sub 1911 1962, .cst 528965731, .add 1963 1964, .mul 1965 1965, .mul 1966 1965, .sub 1960 1967, .var 223,
    .add 1881 1881, .add 1970 1970, .sub 1911 1971, .cst 183414327, .add 1972 1973, .mul 1974 1974, .mul 1975 1974,
    .sub 1969 1976, .var 224, .mul 1884 1229, .add 1979 1911, .cst 1886297254, .add 1980 1981, .mul 1982 1982,
    .mul 1983 1982, .sub 1978 1984, .var 225, .mul 1887 1233, .add 1987 1911, .cst 1178602734, .add 1988 1989,
    .mul 1990 1990, .mul 1991 1990, .sub 1986 1992, .var 226, .mul 1890 1237, .add 1995 1911, .cst 1923111974,
    .add 1996 1997, .mul 1998 1998, .mul 1999 1998, .sub 1994 2000, .var 227, .mul 1893 1241, .add 2003 1911,
    .cst 744004766, .add 2004 2005, .mul 2006 2006, .mul 2007 2006, .sub 2002 2008, .var 228, .mul 1896 1229,
    .sub 1911 2011, .cst 549271463, .add 2012 2013, .mul 2014 2014, .mul 2015 2014, .sub 2010 2016, .var 229,
    .mul 1899 1248, .sub 1911 2019, .cst 1781349648, .add 2020 2021, .mul 2022 2022, .mul 2023 2022, .sub 2018 2024,
    .var 230, .mul 1902 1241, .sub 1911 2027, .cst 542259047, .add 2028 2029, .mul 2030 2030, .mul 2031 2030,
    .sub 2026 2032, .mul 1855 1855, .mul 2034 1906, .mul 1910 1910, .mul 2036 1914, .add 2035 2037, .mul 1918 1918,
    .mul 2039 1922, .mul 1926 1926, .mul 2041 1930, .add 2040 2042, .add 2038 2043, .add 2044 2037, .add 2045 2038,
    .mul 1934 1934]

def p2w16DagC4 : List Node :=
  [  .mul 2047 1939, .mul 1943 1943, .mul 2049 1948, .add 2048 2050, .mul 1952 1952, .mul 2052 1956, .mul 1960 1960,
    .mul 2054 1965, .add 2053 2055, .add 2051 2056, .add 2057 2050, .add 2058 2051, .add 2046 2059, .mul 1969 1969,
    .mul 2061 1974, .mul 1978 1978, .mul 2063 1982, .add 2062 2064, .mul 1986 1986, .mul 2066 1990, .mul 1994 1994,
    .mul 2068 1998, .add 2067 2069, .add 2065 2070, .add 2071 2064, .add 2072 2065, .add 2060 2073, .mul 2002 2002,
    .mul 2075 2006, .mul 2010 2010, .mul 2077 2014, .add 2076 2078, .mul 2018 2018, .mul 2080 2022, .mul 2026 2026,
    .mul 2082 2030, .add 2081 2083, .add 2079 2084, .add 2085 2078, .add 2086 2079, .add 2074 2087, .add 2046 2088,
    .var 231, .sub 2089 2090, .add 2040 2040, .add 2045 2092, .add 2053 2053, .add 2058 2094, .add 2093 2095,
    .add 2067 2067, .add 2072 2097, .add 2096 2098, .add 2081 2081, .add 2086 2100, .add 2099 2101, .add 2093 2102,
    .var 232, .sub 2103 2104, .add 2044 2042, .add 2106 2043, .add 2057 2055, .add 2108 2056, .add 2107 2109,
    .add 2071 2069, .add 2111 2070, .add 2110 2112, .add 2085 2083, .add 2114 2084, .add 2113 2115, .add 2107 2116,
    .var 233, .sub 2117 2118, .add 2035 2035, .add 2106 2120, .add 2048 2048, .add 2108 2122, .add 2121 2123,
    .add 2062 2062, .add 2111 2125, .add 2124 2126, .add 2076 2076, .add 2114 2128, .add 2127 2129, .add 2121 2130,
    .var 234, .sub 2131 2132, .add 2059 2088, .var 235, .sub 2134 2135, .add 2095 2102, .var 236, .sub 2137 2138,
    .add 2109 2116, .var 237, .sub 2140 2141, .add 2123 2130, .var 238, .sub 2143 2144, .add 2073 2088,
    .var 239, .sub 2146 2147, .add 2098 2102, .var 240, .sub 2149 2150, .add 2112 2116, .var 241, .sub 2152 2153,
    .add 2126 2130, .var 242, .sub 2155 2156, .add 2087 2088, .var 243, .sub 2158 2159, .add 2101 2102,
    .var 244, .sub 2161 2162, .add 2115 2116, .var 245, .sub 2164 2165, .add 2129 2130, .var 246, .sub 2167 2168,
    .var 247, .cst 1536158148, .add 2090 2171, .mul 2172 2172, .mul 2173 2172, .sub 2170 2174, .var 248,
    .cst 715456982, .add 2104 2177, .mul 2178 2178, .mul 2179 2178, .sub 2176 2180, .var 249, .cst 503426110,
    .add 2118 2183, .mul 2184 2184, .mul 2185 2184, .sub 2182 2186, .var 250, .cst 340311124, .add 2132 2189,
    .mul 2190 2190, .mul 2191 2190, .sub 2188 2192, .var 251, .cst 1558555932, .add 2135 2195, .mul 2196 2196,
    .mul 2197 2196, .sub 2194 2198, .var 252, .cst 1226350925, .add 2138 2201, .mul 2202 2202, .mul 2203 2202,
    .sub 2200 2204, .var 253, .cst 742828095, .add 2141 2207, .mul 2208 2208, .mul 2209 2208, .sub 2206 2210,
    .var 254, .cst 1338992758, .add 2144 2213, .mul 2214 2214, .mul 2215 2214, .sub 2212 2216, .var 255,
    .cst 1641600456, .add 2147 2219, .mul 2220 2220, .mul 2221 2220, .sub 2218 2222, .var 256, .cst 1843351545,
    .add 2150 2225, .mul 2226 2226, .mul 2227 2226, .sub 2224 2228, .var 257, .cst 301835475, .add 2153 2231,
    .mul 2232 2232, .mul 2233 2232, .sub 2230 2234, .var 258, .cst 43203215, .add 2156 2237, .mul 2238 2238,
    .mul 2239 2238, .sub 2236 2240, .var 259, .cst 386838401, .add 2159 2243, .mul 2244 2244, .mul 2245 2244,
    .sub 2242 2246, .var 260, .cst 1520185679, .add 2162 2249, .mul 2250 2250, .mul 2251 2250, .sub 2248 2252,
    .var 261, .cst 1235297680, .add 2165 2255, .mul 2256 2256, .mul 2257 2256, .sub 2254 2258, .var 262,
    .cst 904680097, .add 2168 2261, .mul 2262 2262, .mul 2263 2262, .sub 2260 2264, .mul 2170 2170, .mul 2266 2172,
    .mul 2176 2176, .mul 2268 2178, .add 2267 2269, .mul 2182 2182, .mul 2271 2184, .mul 2188 2188, .mul 2273 2190,
    .add 2272 2274, .add 2270 2275, .add 2276 2269, .add 2277 2270, .mul 2194 2194, .mul 2279 2196, .mul 2200 2200,
    .mul 2281 2202, .add 2280 2282, .mul 2206 2206, .mul 2284 2208, .mul 2212 2212, .mul 2286 2214, .add 2285 2287,
    .add 2283 2288, .add 2289 2282, .add 2290 2283, .add 2278 2291, .mul 2218 2218, .mul 2293 2220, .mul 2224 2224,
    .mul 2295 2226, .add 2294 2296, .mul 2230 2230, .mul 2298 2232, .mul 2236 2236, .mul 2300 2238, .add 2299 2301,
    .add 2297 2302, .add 2303 2296, .add 2304 2297, .add 2292 2305, .mul 2242 2242, .mul 2307 2244, .mul 2248 2248,
    .mul 2309 2250, .add 2308 2310, .mul 2254 2254, .mul 2312 2256, .mul 2260 2260, .mul 2314 2262, .add 2313 2315,
    .add 2311 2316, .add 2317 2310, .add 2318 2311, .add 2306 2319, .add 2278 2320, .var 263, .sub 2321 2322,
    .add 2272 2272, .add 2277 2324, .add 2285 2285, .add 2290 2326, .add 2325 2327, .add 2299 2299, .add 2304 2329,
    .add 2328 2330, .add 2313 2313, .add 2318 2332, .add 2331 2333, .add 2325 2334, .var 264, .sub 2335 2336,
    .add 2276 2274, .add 2338 2275, .add 2289 2287, .add 2340 2288, .add 2339 2341, .add 2303 2301, .add 2343 2302,
    .add 2342 2344, .add 2317 2315, .add 2346 2316, .add 2345 2347, .add 2339 2348, .var 265, .sub 2349 2350,
    .add 2267 2267, .add 2338 2352, .add 2280 2280, .add 2340 2354, .add 2353 2355, .add 2294 2294, .add 2343 2357,
    .add 2356 2358, .add 2308 2308, .add 2346 2360, .add 2359 2361, .add 2353 2362, .var 266, .sub 2363 2364,
    .add 2291 2320, .var 267, .sub 2366 2367, .add 2327 2334, .var 268, .sub 2369 2370, .add 2341 2348,
    .var 269, .sub 2372 2373, .add 2355 2362, .var 270, .sub 2375 2376, .add 2305 2320, .var 271, .sub 2378 2379,
    .add 2330 2334, .var 272, .sub 2381 2382, .add 2344 2348, .var 273, .sub 2384 2385, .add 2358 2362,
    .var 274, .sub 2387 2388, .add 2319 2320, .var 275, .sub 2390 2391, .add 2333 2334, .var 276, .sub 2393 2394,
    .add 2347 2348, .var 277, .sub 2396 2397, .add 2361 2362, .var 278, .sub 2399 2400, .var 279, .cst 1491801617,
    .add 2322 2403, .mul 2404 2404, .mul 2405 2404, .sub 2402 2406, .var 280, .cst 1581784677, .add 2336 2409,
    .mul 2410 2410, .mul 2411 2410, .sub 2408 2412, .var 281, .cst 913384905, .add 2350 2415, .mul 2416 2416,
    .mul 2417 2416, .sub 2414 2418, .var 282, .cst 247083962, .add 2364 2421, .mul 2422 2422, .mul 2423 2422,
    .sub 2420 2424, .var 283, .cst 532844013, .add 2367 2427, .mul 2428 2428, .mul 2429 2428, .sub 2426 2430,
    .var 284, .cst 107190701, .add 2370 2433, .mul 2434 2434, .mul 2435 2434, .sub 2432 2436, .var 285,
    .cst 213827818, .add 2373 2439, .mul 2440 2440, .mul 2441 2440, .sub 2438 2442, .var 286, .cst 1979521776,
    .add 2376 2445, .mul 2446 2446, .mul 2447 2446, .sub 2444 2448, .var 287, .cst 1358282574, .add 2379 2451,
    .mul 2452 2452, .mul 2453 2452, .sub 2450 2454, .var 288, .cst 1681743681, .add 2382 2457, .mul 2458 2458,
    .mul 2459 2458, .sub 2456 2460, .var 289, .cst 1867507480, .add 2385 2463, .mul 2464 2464, .mul 2465 2464,
    .sub 2462 2466, .var 290, .cst 1530706910, .add 2388 2469, .mul 2470 2470, .mul 2471 2470, .sub 2468 2472,
    .var 291, .cst 507181886, .add 2391 2475, .mul 2476 2476, .mul 2477 2476, .sub 2474 2478, .var 292,
    .cst 695185447, .add 2394 2481, .mul 2482 2482, .mul 2483 2482, .sub 2480 2484, .var 293, .cst 1172395131,
    .add 2397 2487, .mul 2488 2488, .mul 2489 2488, .sub 2486 2490, .var 294, .cst 1250800299, .add 2400 2493,
    .mul 2494 2494, .mul 2495 2494, .sub 2492 2496, .mul 2402 2402, .mul 2498 2404, .mul 2408 2408, .mul 2500 2410,
    .add 2499 2501, .mul 2414 2414, .mul 2503 2416, .mul 2420 2420, .mul 2505 2422, .add 2504 2506, .add 2502 2507,
    .add 2508 2501, .add 2509 2502, .mul 2426 2426, .mul 2511 2428, .mul 2432 2432, .mul 2513 2434, .add 2512 2514,
    .mul 2438 2438, .mul 2516 2440, .mul 2444 2444, .mul 2518 2446, .add 2517 2519, .add 2515 2520, .add 2521 2514,
    .add 2522 2515, .add 2510 2523, .mul 2450 2450, .mul 2525 2452, .mul 2456 2456, .mul 2527 2458, .add 2526 2528,
    .mul 2462 2462, .mul 2530 2464, .mul 2468 2468, .mul 2532 2470, .add 2531 2533, .add 2529 2534, .add 2535 2528,
    .add 2536 2529, .add 2524 2537, .mul 2474 2474, .mul 2539 2476, .mul 2480 2480, .mul 2541 2482, .add 2540 2542,
    .mul 2486 2486, .mul 2544 2488, .mul 2492 2492, .mul 2546 2494, .add 2545 2547, .add 2543 2548, .add 2549 2542,
    .add 2550 2543, .add 2538 2551, .add 2510 2552, .var 295, .sub 2553 2554, .add 2504 2504, .add 2509 2556,
    .add 2517 2517, .add 2522 2558]

def p2w16DagC5 : List Node :=
  [  .add 2557 2559, .add 2531 2531, .add 2536 2561, .add 2560 2562, .add 2545 2545, .add 2550 2564, .add 2563 2565,
    .add 2557 2566, .var 296, .sub 2567 2568, .add 2508 2506, .add 2570 2507, .add 2521 2519, .add 2572 2520,
    .add 2571 2573, .add 2535 2533, .add 2575 2534, .add 2574 2576, .add 2549 2547, .add 2578 2548, .add 2577 2579,
    .add 2571 2580, .var 297, .sub 2581 2582, .add 2499 2499, .add 2570 2584, .add 2512 2512, .add 2572 2586,
    .add 2585 2587, .add 2526 2526, .add 2575 2589, .add 2588 2590, .add 2540 2540, .add 2578 2592, .add 2591 2593,
    .add 2585 2594, .var 298, .sub 2595 2596, .add 2523 2552, .var 299, .sub 2598 2599, .add 2559 2566,
    .var 300, .sub 2601 2602, .add 2573 2580, .var 301, .sub 2604 2605, .add 2587 2594, .var 302, .sub 2607 2608,
    .add 2537 2552, .var 303, .sub 2610 2611, .add 2562 2566, .var 304, .sub 2613 2614, .add 2576 2580,
    .var 305, .sub 2616 2617, .add 2590 2594, .var 306, .sub 2619 2620, .add 2551 2552, .var 307, .sub 2622 2623,
    .add 2565 2566, .var 308, .sub 2625 2626, .add 2579 2580, .var 309, .sub 2628 2629, .add 2593 2594,
    .var 310, .sub 2631 2632, .var 311, .cst 1503161625, .add 2554 2635, .mul 2636 2636, .mul 2637 2636,
    .sub 2634 2638, .var 312, .cst 817684387, .add 2568 2641, .mul 2642 2642, .mul 2643 2642, .sub 2640 2644,
    .var 313, .cst 498481458, .add 2582 2647, .mul 2648 2648, .mul 2649 2648, .sub 2646 2650, .var 314,
    .cst 494676004, .add 2596 2653, .mul 2654 2654, .mul 2655 2654, .sub 2652 2656, .var 315, .cst 1404253825,
    .add 2599 2659, .mul 2660 2660, .mul 2661 2660, .sub 2658 2662, .var 316, .cst 108246855, .add 2602 2665,
    .mul 2666 2666, .mul 2667 2666, .sub 2664 2668, .var 317, .cst 59414691, .add 2605 2671, .mul 2672 2672,
    .mul 2673 2672, .sub 2670 2674, .var 318, .cst 744214112, .add 2608 2677, .mul 2678 2678, .mul 2679 2678,
    .sub 2676 2680, .var 319, .cst 890862029, .add 2611 2683, .mul 2684 2684, .mul 2685 2684, .sub 2682 2686,
    .var 320, .cst 1342765939, .add 2614 2689, .mul 2690 2690, .mul 2691 2690, .sub 2688 2692, .var 321,
    .cst 1417398904, .add 2617 2695, .mul 2696 2696, .mul 2697 2696, .sub 2694 2698, .var 322, .cst 1897591937,
    .add 2620 2701, .mul 2702 2702, .mul 2703 2702, .sub 2700 2704, .var 323, .cst 1066647396, .add 2623 2707,
    .mul 2708 2708, .mul 2709 2708, .sub 2706 2710, .var 324, .cst 1682806907, .add 2626 2713, .mul 2714 2714,
    .mul 2715 2714, .sub 2712 2716, .var 325, .cst 1015795079, .add 2629 2719, .mul 2720 2720, .mul 2721 2720,
    .sub 2718 2722, .var 326, .cst 1619482808, .add 2632 2725, .mul 2726 2726, .mul 2727 2726, .sub 2724 2728,
    .mul 2634 2634, .mul 2730 2636, .mul 2640 2640, .mul 2732 2642, .add 2731 2733, .mul 2646 2646, .mul 2735 2648,
    .mul 2652 2652, .mul 2737 2654, .add 2736 2738, .add 2734 2739, .add 2740 2733, .add 2741 2734, .mul 2658 2658,
    .mul 2743 2660, .mul 2664 2664, .mul 2745 2666, .add 2744 2746, .mul 2670 2670, .mul 2748 2672, .mul 2676 2676,
    .mul 2750 2678, .add 2749 2751, .add 2747 2752, .add 2753 2746, .add 2754 2747, .add 2742 2755, .mul 2682 2682,
    .mul 2757 2684, .mul 2688 2688, .mul 2759 2690, .add 2758 2760, .mul 2694 2694, .mul 2762 2696, .mul 2700 2700,
    .mul 2764 2702, .add 2763 2765, .add 2761 2766, .add 2767 2760, .add 2768 2761, .add 2756 2769, .mul 2706 2706,
    .mul 2771 2708, .mul 2712 2712, .mul 2773 2714, .add 2772 2774, .mul 2718 2718, .mul 2776 2720, .mul 2724 2724,
    .mul 2778 2726, .add 2777 2779, .add 2775 2780, .add 2781 2774, .add 2782 2775, .add 2770 2783, .add 2742 2784,
    .sub 2785 7, .add 2736 2736, .add 2741 2787, .add 2749 2749, .add 2754 2789, .add 2788 2790, .add 2763 2763,
    .add 2768 2792, .add 2791 2793, .add 2777 2777, .add 2782 2795, .add 2794 2796, .add 2788 2797, .sub 2798 12,
    .add 2740 2738, .add 2800 2739, .add 2753 2751, .add 2802 2752, .add 2801 2803, .add 2767 2765, .add 2805 2766,
    .add 2804 2806, .add 2781 2779, .add 2808 2780, .add 2807 2809, .add 2801 2810, .sub 2811 17, .add 2731 2731,
    .add 2800 2813, .add 2744 2744, .add 2802 2815, .add 2814 2816, .add 2758 2758, .add 2805 2818, .add 2817 2819,
    .add 2772 2772, .add 2808 2821, .add 2820 2822, .add 2814 2823, .sub 2824 22, .add 2755 2784, .sub 2826 28,
    .add 2790 2797, .sub 2828 33, .add 2803 2810, .sub 2830 38, .add 2816 2823, .sub 2832 43, .add 2769 2784,
    .sub 2834 49, .add 2793 2797, .sub 2836 54, .add 2806 2810, .sub 2838 59, .add 2819 2823, .sub 2840 64,
    .add 2783 2784, .sub 2842 70, .add 2796 2797, .sub 2844 75, .add 2809 2810, .sub 2846 80, .add 2822 2823,
    .sub 2848 85]

def p2w16DagNodes : List Node :=
  p2w16DagC0 ++ p2w16DagC1 ++ p2w16DagC2 ++ p2w16DagC3 ++ p2w16DagC4 ++ p2w16DagC5

def p2w16DagRoots : List Nat :=
  [  3, 10, 15, 20, 25, 31, 36, 41, 46, 52, 57, 62, 67, 73, 78, 83, 88, 94, 96, 98, 100, 104, 106, 108,
    110, 114, 117, 120, 123, 127, 130, 133, 136, 148, 194, 212, 230, 248, 255, 262, 269, 276, 283, 290,
    297, 304, 311, 318, 325, 332, 390, 404, 418, 432, 435, 438, 441, 444, 447, 450, 453, 456, 459, 462,
    465, 468, 474, 480, 486, 492, 498, 504, 510, 516, 522, 528, 534, 540, 546, 552, 558, 564, 622, 636,
    650, 664, 667, 670, 673, 676, 679, 682, 685, 688, 691, 694, 697, 700, 706, 712, 718, 724, 730, 736,
    742, 748, 754, 760, 766, 772, 778, 784, 790, 796, 854, 868, 882, 896, 899, 902, 905, 908, 911, 914,
    917, 920, 923, 926, 929, 932, 938, 944, 950, 956, 962, 968, 974, 980, 986, 992, 998, 1004, 1010, 1016,
    1022, 1028, 1086, 1100, 1114, 1128, 1131, 1134, 1137, 1140, 1143, 1146, 1149, 1152, 1155, 1158, 1161,
    1164, 1170, 1174, 1195, 1199, 1260, 1264, 1319, 1323, 1378, 1382, 1437, 1441, 1496, 1500, 1555, 1559,
    1614, 1618, 1673, 1677, 1732, 1736, 1791, 1795, 1850, 1854, 1909, 1917, 1925, 1933, 1942, 1951, 1959,
    1968, 1977, 1985, 1993, 2001, 2009, 2017, 2025, 2033, 2091, 2105, 2119, 2133, 2136, 2139, 2142, 2145,
    2148, 2151, 2154, 2157, 2160, 2163, 2166, 2169, 2175, 2181, 2187, 2193, 2199, 2205, 2211, 2217, 2223,
    2229, 2235, 2241, 2247, 2253, 2259, 2265, 2323, 2337, 2351, 2365, 2368, 2371, 2374, 2377, 2380, 2383,
    2386, 2389, 2392, 2395, 2398, 2401, 2407, 2413, 2419, 2425, 2431, 2437, 2443, 2449, 2455, 2461, 2467,
    2473, 2479, 2485, 2491, 2497, 2555, 2569, 2583, 2597, 2600, 2603, 2606, 2609, 2612, 2615, 2618, 2621,
    2624, 2627, 2630, 2633, 2639, 2645, 2651, 2657, 2663, 2669, 2675, 2681, 2687, 2693, 2699, 2705, 2711,
    2717, 2723, 2729, 2786, 2799, 2812, 2825, 2827, 2829, 2831, 2833, 2835, 2837, 2839, 2841, 2843, 2845,
    2847, 2849]

def p2w16Dag : Dag := ⟨p2w16DagNodes, p2w16DagRoots⟩

def p2w16DagCols : Nat := 327

def p2w24DagC0 : List Node :=
  [  .var 0, .cst 1, .sub 0 1, .mul 0 2, .var 1, .var 2, .var 3, .var 4, .sub 6 7, .mul 5 8, .mul 4 9, .var 5,
    .var 6, .sub 11 12, .mul 5 13, .mul 4 14, .var 7, .var 8, .sub 16 17, .mul 5 18, .mul 4 19, .var 9,
    .var 10, .sub 21 22, .mul 5 23, .mul 4 24, .var 11, .var 12, .var 13, .sub 27 28, .mul 26 29, .mul 4 30,
    .var 14, .var 15, .sub 32 33, .mul 26 34, .mul 4 35, .var 16, .var 17, .sub 37 38, .mul 26 39, .mul 4 40,
    .var 18, .var 19, .sub 42 43, .mul 26 44, .mul 4 45, .var 20, .var 21, .var 22, .sub 48 49, .mul 47 50,
    .mul 4 51, .var 23, .var 24, .sub 53 54, .mul 47 55, .mul 4 56, .var 25, .var 26, .sub 58 59, .mul 47 60,
    .mul 4 61, .var 27, .var 28, .sub 63 64, .mul 47 65, .mul 4 66, .var 29, .var 30, .var 31, .sub 69 70,
    .mul 68 71, .mul 4 72, .var 32, .var 33, .sub 74 75, .mul 68 76, .mul 4 77, .var 34, .var 35, .sub 79 80,
    .mul 68 81, .mul 4 82, .var 36, .var 37, .sub 84 85, .mul 68 86, .mul 4 87, .var 38, .var 39, .var 40,
    .sub 90 91, .mul 89 92, .mul 4 93, .var 41, .var 42, .sub 95 96, .mul 89 97, .mul 4 98, .var 43, .var 44,
    .sub 100 101, .mul 89 102, .mul 4 103, .var 45, .var 46, .sub 105 106, .mul 89 107, .mul 4 108, .var 47,
    .var 48, .var 49, .sub 111 112, .mul 110 113, .mul 4 114, .var 50, .var 51, .sub 116 117, .mul 110 118,
    .mul 4 119, .var 52, .var 53, .sub 121 122, .mul 110 123, .mul 4 124, .var 54, .var 55, .sub 126 127,
    .mul 110 128, .mul 4 129, .var 56, .var 57, .sub 1 132, .mul 131 133, .mul 134 8, .mul 4 135, .mul 134 13,
    .mul 4 137, .mul 134 18, .mul 4 139, .mul 134 23, .mul 4 141, .var 58, .mul 143 133, .mul 144 29, .mul 4 145,
    .mul 144 34, .mul 4 147, .mul 144 39, .mul 4 149, .mul 144 44, .mul 4 151, .var 59, .mul 153 133, .mul 154 50,
    .mul 4 155, .mul 154 55, .mul 4 157, .mul 154 60, .mul 4 159, .mul 154 65, .mul 4 161, .var 60, .mul 163 133,
    .mul 164 71, .mul 4 165, .mul 164 76, .mul 4 167, .mul 164 81, .mul 4 169, .mul 164 86, .mul 4 171,
    .var 61, .sub 1 173, .var 62, .var 63, .var 64, .cst 2, .mul 177 178, .add 179 132, .sub 176 180, .mul 175 181,
    .mul 174 182, .mul 4 183, .var 65, .var 66, .var 67, .add 186 187, .var 68, .var 69, .add 189 190,
    .add 188 191, .add 192 187, .add 193 188, .var 70, .var 71, .add 195 196, .var 72, .var 73, .add 198 199,
    .add 197 200, .add 201 196, .add 202 197, .add 194 203, .var 74, .var 75, .add 205 206, .var 76, .var 77,
    .add 208 209, .add 207 210, .add 211 206, .add 212 207, .add 204 213, .var 78, .var 79, .add 215 216,
    .var 80, .var 81, .add 218 219, .add 217 220, .add 221 216, .add 222 217, .add 214 223, .var 82, .var 83,
    .add 225 226, .var 84, .var 85, .add 228 229, .add 227 230, .add 231 226, .add 232 227, .add 224 233,
    .var 86, .var 87, .add 235 236, .var 88, .var 89, .add 238 239, .add 237 240, .add 241 236, .add 242 237,
    .add 234 243, .add 194 244, .cst 262278199, .add 245 246, .mul 247 247, .mul 248 247, .sub 185 249,
    .var 90, .add 189 189, .add 193 252, .add 198 198, .add 202 254, .add 253 255, .add 208 208, .add 212 257,
    .add 256 258, .add 218 218, .add 222 260, .add 259 261, .add 228 228, .add 232 263, .add 262 264, .add 238 238,
    .add 242 266, .add 265 267, .add 253 268, .cst 127253399, .add 269 270, .mul 271 271, .mul 272 271,
    .sub 251 273, .var 91, .add 192 190, .add 276 191, .add 201 199, .add 278 200, .add 277 279, .add 211 209,
    .add 281 210, .add 280 282, .add 221 219, .add 284 220, .add 283 285, .add 231 229, .add 287 230, .add 286 288,
    .add 241 239, .add 290 240, .add 289 291, .add 277 292, .cst 314968988, .add 293 294, .mul 295 295,
    .mul 296 295, .sub 275 297, .var 92, .add 186 186, .add 276 300, .add 195 195, .add 278 302, .add 301 303,
    .add 205 205, .add 281 305, .add 304 306, .add 215 215, .add 284 308, .add 307 309, .add 225 225, .add 287 311,
    .add 310 312, .add 235 235, .add 290 314, .add 313 315, .add 301 316, .cst 246143118, .add 317 318,
    .mul 319 319, .mul 320 319, .sub 299 321, .var 93, .add 203 244, .cst 157582794, .add 324 325, .mul 326 326,
    .mul 327 326, .sub 323 328, .var 94, .add 255 268, .cst 118043943, .add 331 332, .mul 333 333, .mul 334 333,
    .sub 330 335, .var 95, .add 279 292, .cst 454905424, .add 338 339, .mul 340 340, .mul 341 340, .sub 337 342,
    .var 96, .add 303 316, .cst 815798990, .add 345 346, .mul 347 347, .mul 348 347, .sub 344 349, .var 97,
    .add 213 244, .cst 1004040026, .add 352 353, .mul 354 354, .mul 355 354, .sub 351 356, .var 98, .add 258 268,
    .cst 1773108264, .add 359 360, .mul 361 361, .mul 362 361, .sub 358 363, .var 99, .add 282 292, .cst 1066694495,
    .add 366 367, .mul 368 368, .mul 369 368, .sub 365 370, .var 100, .add 306 316, .cst 1930780904, .add 373 374,
    .mul 375 375, .mul 376 375, .sub 372 377, .var 101, .add 223 244, .cst 1180307149, .add 380 381, .mul 382 382,
    .mul 383 382, .sub 379 384, .var 102, .add 261 268, .cst 1464793095, .add 387 388, .mul 389 389, .mul 390 389,
    .sub 386 391, .var 103, .add 285 292, .cst 1660766320, .add 394 395, .mul 396 396, .mul 397 396, .sub 393 398,
    .var 104, .add 309 316, .cst 1389166148, .add 401 402, .mul 403 403, .mul 404 403, .sub 400 405, .var 105,
    .add 233 244, .cst 343354132, .add 408 409, .mul 410 410, .mul 411 410, .sub 407 412, .var 106, .add 264 268,
    .cst 1307439985, .add 415 416, .mul 417 417, .mul 418 417, .sub 414 419, .var 107, .add 288 292, .cst 638242172,
    .add 422 423, .mul 424 424, .mul 425 424, .sub 421 426, .var 108, .add 312 316, .cst 525458520, .add 429 430,
    .mul 431 431, .mul 432 431, .sub 428 433, .var 109, .add 243 244, .cst 1964135730, .add 436 437, .mul 438 438,
    .mul 439 438, .sub 435 440, .var 110, .add 267 268, .cst 1751797115, .add 443 444, .mul 445 445, .mul 446 445,
    .sub 442 447, .var 111, .add 291 292, .cst 1421525369, .add 450 451, .mul 452 452, .mul 453 452, .sub 449 454,
    .var 112, .add 315 316, .cst 831813382, .add 457 458, .mul 459 459, .mul 460 459, .sub 456 461, .mul 185 185,
    .mul 463 247, .mul 251 251, .mul 465 271, .add 464 466, .mul 275 275, .mul 468 295, .mul 299 299, .mul 470 319,
    .add 469 471, .add 467 472, .add 473 466, .add 474 467, .mul 323 323, .mul 476 326, .mul 330 330, .mul 478 333,
    .add 477 479, .mul 337 337, .mul 481 340, .mul 344 344, .mul 483 347, .add 482 484, .add 480 485, .add 486 479,
    .add 487 480, .add 475 488, .mul 351 351, .mul 490 354, .mul 358 358, .mul 492 361, .add 491 493, .mul 365 365,
    .mul 495 368, .mul 372 372, .mul 497 375, .add 496 498, .add 494 499, .add 500 493, .add 501 494, .add 489 502,
    .mul 379 379, .mul 504 382, .mul 386 386, .mul 506 389, .add 505 507, .mul 393 393, .mul 509 396, .mul 400 400]

def p2w24DagC1 : List Node :=
  [  .mul 511 403, .add 510 512, .add 508 513, .add 514 507, .add 515 508, .add 503 516, .mul 407 407, .mul 518 410,
    .mul 414 414, .mul 520 417, .add 519 521, .mul 421 421, .mul 523 424, .mul 428 428, .mul 525 431, .add 524 526,
    .add 522 527, .add 528 521, .add 529 522, .add 517 530, .mul 435 435, .mul 532 438, .mul 442 442, .mul 534 445,
    .add 533 535, .mul 449 449, .mul 537 452, .mul 456 456, .mul 539 459, .add 538 540, .add 536 541, .add 542 535,
    .add 543 536, .add 531 544, .add 475 545, .var 113, .sub 546 547, .add 469 469, .add 474 549, .add 482 482,
    .add 487 551, .add 550 552, .add 496 496, .add 501 554, .add 553 555, .add 510 510, .add 515 557, .add 556 558,
    .add 524 524, .add 529 560, .add 559 561, .add 538 538, .add 543 563, .add 562 564, .add 550 565, .var 114,
    .sub 566 567, .add 473 471, .add 569 472, .add 486 484, .add 571 485, .add 570 572, .add 500 498, .add 574 499,
    .add 573 575, .add 514 512, .add 577 513, .add 576 578, .add 528 526, .add 580 527, .add 579 581, .add 542 540,
    .add 583 541, .add 582 584, .add 570 585, .var 115, .sub 586 587, .add 464 464, .add 569 589, .add 477 477,
    .add 571 591, .add 590 592, .add 491 491, .add 574 594, .add 593 595, .add 505 505, .add 577 597, .add 596 598,
    .add 519 519, .add 580 600, .add 599 601, .add 533 533, .add 583 603, .add 602 604, .add 590 605, .var 116,
    .sub 606 607, .add 488 545, .var 117, .sub 609 610, .add 552 565, .var 118, .sub 612 613, .add 572 585,
    .var 119, .sub 615 616, .add 592 605, .var 120, .sub 618 619, .add 502 545, .var 121, .sub 621 622,
    .add 555 565, .var 122, .sub 624 625, .add 575 585, .var 123, .sub 627 628, .add 595 605, .var 124,
    .sub 630 631, .add 516 545, .var 125, .sub 633 634, .add 558 565, .var 126, .sub 636 637, .add 578 585,
    .var 127, .sub 639 640, .add 598 605, .var 128, .sub 642 643, .add 530 545, .var 129, .sub 645 646,
    .add 561 565, .var 130, .sub 648 649, .add 581 585, .var 131, .sub 651 652, .add 601 605, .var 132,
    .sub 654 655, .add 544 545, .var 133, .sub 657 658, .add 564 565, .var 134, .sub 660 661, .add 584 585,
    .var 135, .sub 663 664, .add 604 605, .var 136, .sub 666 667, .var 137, .cst 695835963, .add 547 670,
    .mul 671 671, .mul 672 671, .sub 669 673, .var 138, .cst 1845603984, .add 567 676, .mul 677 677, .mul 678 677,
    .sub 675 679, .var 139, .cst 540703332, .add 587 682, .mul 683 683, .mul 684 683, .sub 681 685, .var 140,
    .cst 1333667262, .add 607 688, .mul 689 689, .mul 690 689, .sub 687 691, .var 141, .cst 1917861751,
    .add 610 694, .mul 695 695, .mul 696 695, .sub 693 697, .var 142, .cst 1170029417, .add 613 700, .mul 701 701,
    .mul 702 701, .sub 699 703, .var 143, .cst 1989924532, .add 616 706, .mul 707 707, .mul 708 707, .sub 705 709,
    .var 144, .cst 1518763784, .add 619 712, .mul 713 713, .mul 714 713, .sub 711 715, .var 145, .cst 1339793538,
    .add 622 718, .mul 719 719, .mul 720 719, .sub 717 721, .var 146, .cst 622609176, .add 625 724, .mul 725 725,
    .mul 726 725, .sub 723 727, .var 147, .cst 686842369, .add 628 730, .mul 731 731, .mul 732 731, .sub 729 733,
    .var 148, .cst 1737016378, .add 631 736, .mul 737 737, .mul 738 737, .sub 735 739, .var 149, .cst 1282239129,
    .add 634 742, .mul 743 743, .mul 744 743, .sub 741 745, .var 150, .cst 897025192, .add 637 748, .mul 749 749,
    .mul 750 749, .sub 747 751, .var 151, .cst 716894289, .add 640 754, .mul 755 755, .mul 756 755, .sub 753 757,
    .var 152, .cst 1997503974, .add 643 760, .mul 761 761, .mul 762 761, .sub 759 763, .var 153, .cst 395622276,
    .add 646 766, .mul 767 767, .mul 768 767, .sub 765 769, .var 154, .cst 1201063290, .add 649 772, .mul 773 773,
    .mul 774 773, .sub 771 775, .var 155, .cst 1917549072, .add 652 778, .mul 779 779, .mul 780 779, .sub 777 781,
    .var 156, .cst 1150912935, .add 655 784, .mul 785 785, .mul 786 785, .sub 783 787, .var 157, .cst 1687379185,
    .add 658 790, .mul 791 791, .mul 792 791, .sub 789 793, .var 158, .cst 1507936940, .add 661 796, .mul 797 797,
    .mul 798 797, .sub 795 799, .var 159, .cst 241306552, .add 664 802, .mul 803 803, .mul 804 803, .sub 801 805,
    .var 160, .cst 989176635, .add 667 808, .mul 809 809, .mul 810 809, .sub 807 811, .mul 669 669, .mul 813 671,
    .mul 675 675, .mul 815 677, .add 814 816, .mul 681 681, .mul 818 683, .mul 687 687, .mul 820 689, .add 819 821,
    .add 817 822, .add 823 816, .add 824 817, .mul 693 693, .mul 826 695, .mul 699 699, .mul 828 701, .add 827 829,
    .mul 705 705, .mul 831 707, .mul 711 711, .mul 833 713, .add 832 834, .add 830 835, .add 836 829, .add 837 830,
    .add 825 838, .mul 717 717, .mul 840 719, .mul 723 723, .mul 842 725, .add 841 843, .mul 729 729, .mul 845 731,
    .mul 735 735, .mul 847 737, .add 846 848, .add 844 849, .add 850 843, .add 851 844, .add 839 852, .mul 741 741,
    .mul 854 743, .mul 747 747, .mul 856 749, .add 855 857, .mul 753 753, .mul 859 755, .mul 759 759, .mul 861 761,
    .add 860 862, .add 858 863, .add 864 857, .add 865 858, .add 853 866, .mul 765 765, .mul 868 767, .mul 771 771,
    .mul 870 773, .add 869 871, .mul 777 777, .mul 873 779, .mul 783 783, .mul 875 785, .add 874 876, .add 872 877,
    .add 878 871, .add 879 872, .add 867 880, .mul 789 789, .mul 882 791, .mul 795 795, .mul 884 797, .add 883 885,
    .mul 801 801, .mul 887 803, .mul 807 807, .mul 889 809, .add 888 890, .add 886 891, .add 892 885, .add 893 886,
    .add 881 894, .add 825 895, .var 161, .sub 896 897, .add 819 819, .add 824 899, .add 832 832, .add 837 901,
    .add 900 902, .add 846 846, .add 851 904, .add 903 905, .add 860 860, .add 865 907, .add 906 908, .add 874 874,
    .add 879 910, .add 909 911, .add 888 888, .add 893 913, .add 912 914, .add 900 915, .var 162, .sub 916 917,
    .add 823 821, .add 919 822, .add 836 834, .add 921 835, .add 920 922, .add 850 848, .add 924 849, .add 923 925,
    .add 864 862, .add 927 863, .add 926 928, .add 878 876, .add 930 877, .add 929 931, .add 892 890, .add 933 891,
    .add 932 934, .add 920 935, .var 163, .sub 936 937, .add 814 814, .add 919 939, .add 827 827, .add 921 941,
    .add 940 942, .add 841 841, .add 924 944, .add 943 945, .add 855 855, .add 927 947, .add 946 948, .add 869 869,
    .add 930 950, .add 949 951, .add 883 883, .add 933 953, .add 952 954, .add 940 955, .var 164, .sub 956 957,
    .add 838 895, .var 165, .sub 959 960, .add 902 915, .var 166, .sub 962 963, .add 922 935, .var 167,
    .sub 965 966, .add 942 955, .var 168, .sub 968 969, .add 852 895, .var 169, .sub 971 972, .add 905 915,
    .var 170, .sub 974 975, .add 925 935, .var 171, .sub 977 978, .add 945 955, .var 172, .sub 980 981,
    .add 866 895, .var 173, .sub 983 984, .add 908 915, .var 174, .sub 986 987, .add 928 935, .var 175,
    .sub 989 990, .add 948 955, .var 176, .sub 992 993, .add 880 895, .var 177, .sub 995 996, .add 911 915,
    .var 178, .sub 998 999, .add 931 935, .var 179, .sub 1001 1002, .add 951 955, .var 180, .sub 1004 1005,
    .add 894 895, .var 181, .sub 1007 1008, .add 914 915, .var 182, .sub 1010 1011, .add 934 935, .var 183,
    .sub 1013 1014, .add 954 955, .var 184, .sub 1016 1017, .var 185, .cst 1147522062, .add 897 1020, .mul 1021 1021,
    .mul 1022 1021]

def p2w24DagC2 : List Node :=
  [  .sub 1019 1023, .var 186, .cst 27129487, .add 917 1026, .mul 1027 1027, .mul 1028 1027, .sub 1025 1029,
    .var 187, .cst 1257820264, .add 937 1032, .mul 1033 1033, .mul 1034 1033, .sub 1031 1035, .var 188,
    .cst 142102402, .add 957 1038, .mul 1039 1039, .mul 1040 1039, .sub 1037 1041, .var 189, .cst 217046702,
    .add 960 1044, .mul 1045 1045, .mul 1046 1045, .sub 1043 1047, .var 190, .cst 1664590951, .add 963 1050,
    .mul 1051 1051, .mul 1052 1051, .sub 1049 1053, .var 191, .cst 855276054, .add 966 1056, .mul 1057 1057,
    .mul 1058 1057, .sub 1055 1059, .var 192, .cst 1215259350, .add 969 1062, .mul 1063 1063, .mul 1064 1063,
    .sub 1061 1065, .var 193, .cst 946500736, .add 972 1068, .mul 1069 1069, .mul 1070 1069, .sub 1067 1071,
    .var 194, .cst 552696906, .add 975 1074, .mul 1075 1075, .mul 1076 1075, .sub 1073 1077, .var 195,
    .cst 1424297384, .add 978 1080, .mul 1081 1081, .mul 1082 1081, .sub 1079 1083, .var 196, .cst 538103555,
    .add 981 1086, .mul 1087 1087, .mul 1088 1087, .sub 1085 1089, .var 197, .cst 1608853840, .add 984 1092,
    .mul 1093 1093, .mul 1094 1093, .sub 1091 1095, .var 198, .cst 162510541, .add 987 1098, .mul 1099 1099,
    .mul 1100 1099, .sub 1097 1101, .var 199, .cst 623051854, .add 990 1104, .mul 1105 1105, .mul 1106 1105,
    .sub 1103 1107, .var 200, .cst 1549062383, .add 993 1110, .mul 1111 1111, .mul 1112 1111, .sub 1109 1113,
    .var 201, .cst 1908416316, .add 996 1116, .mul 1117 1117, .mul 1118 1117, .sub 1115 1119, .var 202,
    .cst 1622328571, .add 999 1122, .mul 1123 1123, .mul 1124 1123, .sub 1121 1125, .var 203, .cst 1079030649,
    .add 1002 1128, .mul 1129 1129, .mul 1130 1129, .sub 1127 1131, .var 204, .cst 1584033957, .add 1005 1134,
    .mul 1135 1135, .mul 1136 1135, .sub 1133 1137, .var 205, .cst 1099252725, .add 1008 1140, .mul 1141 1141,
    .mul 1142 1141, .sub 1139 1143, .var 206, .cst 1910423126, .add 1011 1146, .mul 1147 1147, .mul 1148 1147,
    .sub 1145 1149, .var 207, .cst 447555988, .add 1014 1152, .mul 1153 1153, .mul 1154 1153, .sub 1151 1155,
    .var 208, .cst 862495875, .add 1017 1158, .mul 1159 1159, .mul 1160 1159, .sub 1157 1161, .mul 1019 1019,
    .mul 1163 1021, .mul 1025 1025, .mul 1165 1027, .add 1164 1166, .mul 1031 1031, .mul 1168 1033, .mul 1037 1037,
    .mul 1170 1039, .add 1169 1171, .add 1167 1172, .add 1173 1166, .add 1174 1167, .mul 1043 1043, .mul 1176 1045,
    .mul 1049 1049, .mul 1178 1051, .add 1177 1179, .mul 1055 1055, .mul 1181 1057, .mul 1061 1061, .mul 1183 1063,
    .add 1182 1184, .add 1180 1185, .add 1186 1179, .add 1187 1180, .add 1175 1188, .mul 1067 1067, .mul 1190 1069,
    .mul 1073 1073, .mul 1192 1075, .add 1191 1193, .mul 1079 1079, .mul 1195 1081, .mul 1085 1085, .mul 1197 1087,
    .add 1196 1198, .add 1194 1199, .add 1200 1193, .add 1201 1194, .add 1189 1202, .mul 1091 1091, .mul 1204 1093,
    .mul 1097 1097, .mul 1206 1099, .add 1205 1207, .mul 1103 1103, .mul 1209 1105, .mul 1109 1109, .mul 1211 1111,
    .add 1210 1212, .add 1208 1213, .add 1214 1207, .add 1215 1208, .add 1203 1216, .mul 1115 1115, .mul 1218 1117,
    .mul 1121 1121, .mul 1220 1123, .add 1219 1221, .mul 1127 1127, .mul 1223 1129, .mul 1133 1133, .mul 1225 1135,
    .add 1224 1226, .add 1222 1227, .add 1228 1221, .add 1229 1222, .add 1217 1230, .mul 1139 1139, .mul 1232 1141,
    .mul 1145 1145, .mul 1234 1147, .add 1233 1235, .mul 1151 1151, .mul 1237 1153, .mul 1157 1157, .mul 1239 1159,
    .add 1238 1240, .add 1236 1241, .add 1242 1235, .add 1243 1236, .add 1231 1244, .add 1175 1245, .var 209,
    .sub 1246 1247, .add 1169 1169, .add 1174 1249, .add 1182 1182, .add 1187 1251, .add 1250 1252, .add 1196 1196,
    .add 1201 1254, .add 1253 1255, .add 1210 1210, .add 1215 1257, .add 1256 1258, .add 1224 1224, .add 1229 1260,
    .add 1259 1261, .add 1238 1238, .add 1243 1263, .add 1262 1264, .add 1250 1265, .var 210, .sub 1266 1267,
    .add 1173 1171, .add 1269 1172, .add 1186 1184, .add 1271 1185, .add 1270 1272, .add 1200 1198, .add 1274 1199,
    .add 1273 1275, .add 1214 1212, .add 1277 1213, .add 1276 1278, .add 1228 1226, .add 1280 1227, .add 1279 1281,
    .add 1242 1240, .add 1283 1241, .add 1282 1284, .add 1270 1285, .var 211, .sub 1286 1287, .add 1164 1164,
    .add 1269 1289, .add 1177 1177, .add 1271 1291, .add 1290 1292, .add 1191 1191, .add 1274 1294, .add 1293 1295,
    .add 1205 1205, .add 1277 1297, .add 1296 1298, .add 1219 1219, .add 1280 1300, .add 1299 1301, .add 1233 1233,
    .add 1283 1303, .add 1302 1304, .add 1290 1305, .var 212, .sub 1306 1307, .add 1188 1245, .var 213,
    .sub 1309 1310, .add 1252 1265, .var 214, .sub 1312 1313, .add 1272 1285, .var 215, .sub 1315 1316,
    .add 1292 1305, .var 216, .sub 1318 1319, .add 1202 1245, .var 217, .sub 1321 1322, .add 1255 1265,
    .var 218, .sub 1324 1325, .add 1275 1285, .var 219, .sub 1327 1328, .add 1295 1305, .var 220, .sub 1330 1331,
    .add 1216 1245, .var 221, .sub 1333 1334, .add 1258 1265, .var 222, .sub 1336 1337, .add 1278 1285,
    .var 223, .sub 1339 1340, .add 1298 1305, .var 224, .sub 1342 1343, .add 1230 1245, .var 225, .sub 1345 1346,
    .add 1261 1265, .var 226, .sub 1348 1349, .add 1281 1285, .var 227, .sub 1351 1352, .add 1301 1305,
    .var 228, .sub 1354 1355, .add 1244 1245, .var 229, .sub 1357 1358, .add 1264 1265, .var 230, .sub 1360 1361,
    .add 1284 1285, .var 231, .sub 1363 1364, .add 1304 1305, .var 232, .sub 1366 1367, .var 233, .cst 128479034,
    .add 1247 1370, .mul 1371 1371, .mul 1372 1371, .sub 1369 1373, .var 234, .cst 1587822577, .add 1267 1376,
    .mul 1377 1377, .mul 1378 1377, .sub 1375 1379, .var 235, .cst 608401422, .add 1287 1382, .mul 1383 1383,
    .mul 1384 1383, .sub 1381 1385, .var 236, .cst 1290028279, .add 1307 1388, .mul 1389 1389, .mul 1390 1389,
    .sub 1387 1391, .var 237, .cst 342857858, .add 1310 1394, .mul 1395 1395, .mul 1396 1395, .sub 1393 1397,
    .var 238, .cst 825405577, .add 1313 1400, .mul 1401 1401, .mul 1402 1401, .sub 1399 1403, .var 239,
    .cst 427731030, .add 1316 1406, .mul 1407 1407, .mul 1408 1407, .sub 1405 1409, .var 240, .cst 1718628547,
    .add 1319 1412, .mul 1413 1413, .mul 1414 1413, .sub 1411 1415, .var 241, .cst 588764636, .add 1322 1418,
    .mul 1419 1419, .mul 1420 1419, .sub 1417 1421, .var 242, .cst 204228775, .add 1325 1424, .mul 1425 1425,
    .mul 1426 1425, .sub 1423 1427, .var 243, .cst 1454563174, .add 1328 1430, .mul 1431 1431, .mul 1432 1431,
    .sub 1429 1433, .var 244, .cst 1740472809, .add 1331 1436, .mul 1437 1437, .mul 1438 1437, .sub 1435 1439,
    .var 245, .cst 1338899225, .add 1334 1442, .mul 1443 1443, .mul 1444 1443, .sub 1441 1445, .var 246,
    .cst 1269493554, .add 1337 1448, .mul 1449 1449, .mul 1450 1449, .sub 1447 1451, .var 247, .cst 53007114,
    .add 1340 1454, .mul 1455 1455, .mul 1456 1455, .sub 1453 1457, .var 248, .cst 1647670797, .add 1343 1460,
    .mul 1461 1461, .mul 1462 1461, .sub 1459 1463, .var 249, .cst 306391314, .add 1346 1466, .mul 1467 1467,
    .mul 1468 1467, .sub 1465 1469, .var 250, .cst 172614232, .add 1349 1472, .mul 1473 1473, .mul 1474 1473,
    .sub 1471 1475, .var 251, .cst 51256176, .add 1352 1478, .mul 1479 1479, .mul 1480 1479, .sub 1477 1481,
    .var 252, .cst 1221257987, .add 1355 1484, .mul 1485 1485, .mul 1486 1485, .sub 1483 1487, .var 253,
    .cst 1239734761, .add 1358 1490, .mul 1491 1491, .mul 1492 1491, .sub 1489 1493, .var 254, .cst 273790406,
    .add 1361 1496, .mul 1497 1497, .mul 1498 1497, .sub 1495 1499, .var 255, .cst 1781980094, .add 1364 1502,
    .mul 1503 1503, .mul 1504 1503, .sub 1501 1505, .var 256, .cst 1291790245, .add 1367 1508, .mul 1509 1509,
    .mul 1510 1509, .sub 1507 1511, .mul 1369 1369, .mul 1513 1371, .mul 1375 1375, .mul 1515 1377, .add 1514 1516,
    .mul 1381 1381, .mul 1518 1383, .mul 1387 1387, .mul 1520 1389, .add 1519 1521, .add 1517 1522, .add 1523 1516,
    .add 1524 1517, .mul 1393 1393, .mul 1526 1395, .mul 1399 1399, .mul 1528 1401, .add 1527 1529, .mul 1405 1405,
    .mul 1531 1407, .mul 1411 1411, .mul 1533 1413, .add 1532 1534]

def p2w24DagC3 : List Node :=
  [  .add 1530 1535, .add 1536 1529, .add 1537 1530, .add 1525 1538, .mul 1417 1417, .mul 1540 1419, .mul 1423 1423,
    .mul 1542 1425, .add 1541 1543, .mul 1429 1429, .mul 1545 1431, .mul 1435 1435, .mul 1547 1437, .add 1546 1548,
    .add 1544 1549, .add 1550 1543, .add 1551 1544, .add 1539 1552, .mul 1441 1441, .mul 1554 1443, .mul 1447 1447,
    .mul 1556 1449, .add 1555 1557, .mul 1453 1453, .mul 1559 1455, .mul 1459 1459, .mul 1561 1461, .add 1560 1562,
    .add 1558 1563, .add 1564 1557, .add 1565 1558, .add 1553 1566, .mul 1465 1465, .mul 1568 1467, .mul 1471 1471,
    .mul 1570 1473, .add 1569 1571, .mul 1477 1477, .mul 1573 1479, .mul 1483 1483, .mul 1575 1485, .add 1574 1576,
    .add 1572 1577, .add 1578 1571, .add 1579 1572, .add 1567 1580, .mul 1489 1489, .mul 1582 1491, .mul 1495 1495,
    .mul 1584 1497, .add 1583 1585, .mul 1501 1501, .mul 1587 1503, .mul 1507 1507, .mul 1589 1509, .add 1588 1590,
    .add 1586 1591, .add 1592 1585, .add 1593 1586, .add 1581 1594, .add 1525 1595, .var 257, .sub 1596 1597,
    .add 1519 1519, .add 1524 1599, .add 1532 1532, .add 1537 1601, .add 1600 1602, .add 1546 1546, .add 1551 1604,
    .add 1603 1605, .add 1560 1560, .add 1565 1607, .add 1606 1608, .add 1574 1574, .add 1579 1610, .add 1609 1611,
    .add 1588 1588, .add 1593 1613, .add 1612 1614, .add 1600 1615, .var 258, .sub 1616 1617, .add 1523 1521,
    .add 1619 1522, .add 1536 1534, .add 1621 1535, .add 1620 1622, .add 1550 1548, .add 1624 1549, .add 1623 1625,
    .add 1564 1562, .add 1627 1563, .add 1626 1628, .add 1578 1576, .add 1630 1577, .add 1629 1631, .add 1592 1590,
    .add 1633 1591, .add 1632 1634, .add 1620 1635, .var 259, .sub 1636 1637, .add 1514 1514, .add 1619 1639,
    .add 1527 1527, .add 1621 1641, .add 1640 1642, .add 1541 1541, .add 1624 1644, .add 1643 1645, .add 1555 1555,
    .add 1627 1647, .add 1646 1648, .add 1569 1569, .add 1630 1650, .add 1649 1651, .add 1583 1583, .add 1633 1653,
    .add 1652 1654, .add 1640 1655, .var 260, .sub 1656 1657, .add 1538 1595, .var 261, .sub 1659 1660,
    .add 1602 1615, .var 262, .sub 1662 1663, .add 1622 1635, .var 263, .sub 1665 1666, .add 1642 1655,
    .var 264, .sub 1668 1669, .add 1552 1595, .var 265, .sub 1671 1672, .add 1605 1615, .var 266, .sub 1674 1675,
    .add 1625 1635, .var 267, .sub 1677 1678, .add 1645 1655, .var 268, .sub 1680 1681, .add 1566 1595,
    .var 269, .sub 1683 1684, .add 1608 1615, .var 270, .sub 1686 1687, .add 1628 1635, .var 271, .sub 1689 1690,
    .add 1648 1655, .var 272, .sub 1692 1693, .add 1580 1595, .var 273, .sub 1695 1696, .add 1611 1615,
    .var 274, .sub 1698 1699, .add 1631 1635, .var 275, .sub 1701 1702, .add 1651 1655, .var 276, .sub 1704 1705,
    .add 1594 1595, .var 277, .sub 1707 1708, .add 1614 1615, .var 278, .sub 1710 1711, .add 1634 1635,
    .var 279, .sub 1713 1714, .add 1654 1655, .var 280, .sub 1716 1717, .var 281, .cst 497520322, .add 1597 1720,
    .mul 1721 1721, .mul 1722 1721, .sub 1719 1723, .mul 1719 1719, .mul 1725 1721, .var 282, .sub 1726 1727,
    .var 283, .add 1617 1637, .add 1730 1657, .add 1731 1660, .add 1732 1663, .add 1733 1666, .add 1734 1669,
    .add 1735 1672, .add 1736 1675, .add 1737 1678, .add 1738 1681, .add 1739 1684, .add 1740 1687, .add 1741 1690,
    .add 1742 1693, .add 1743 1696, .add 1744 1699, .add 1745 1702, .add 1746 1705, .add 1747 1708, .add 1748 1711,
    .add 1749 1714, .add 1750 1717, .sub 1751 1727, .cst 1930103076, .add 1752 1753, .mul 1754 1754, .mul 1755 1754,
    .sub 1729 1756, .mul 1729 1729, .mul 1758 1754, .var 284, .sub 1759 1760, .var 285, .add 1751 1727,
    .add 1617 1763, .add 1637 1637, .add 1765 1763, .add 1764 1766, .cst 1006632961, .mul 1657 1768, .add 1769 1763,
    .add 1767 1770, .add 1660 1660, .add 1763 1772, .add 1773 1660, .add 1771 1774, .add 1663 1663, .add 1776 1776,
    .add 1763 1777, .add 1775 1778, .mul 1666 1768, .sub 1763 1780, .add 1779 1781, .add 1669 1669, .add 1783 1669,
    .sub 1763 1784, .add 1782 1785, .add 1672 1672, .add 1787 1787, .sub 1763 1788, .add 1786 1789, .cst 2005401601,
    .mul 1675 1791, .add 1792 1763, .add 1790 1793, .cst 1509949441, .mul 1678 1795, .add 1796 1763, .add 1794 1797,
    .cst 1761607681, .mul 1681 1799, .add 1800 1763, .add 1798 1801, .cst 1887436801, .mul 1684 1803, .add 1804 1763,
    .add 1802 1805, .cst 1997537281, .mul 1687 1807, .add 1808 1763, .add 1806 1809, .cst 2009333761, .mul 1690 1811,
    .add 1812 1763, .add 1810 1813, .cst 2013265906, .mul 1693 1815, .add 1816 1763, .add 1814 1817, .mul 1696 1791,
    .sub 1763 1819, .add 1818 1820, .mul 1699 1795, .sub 1763 1822, .add 1821 1823, .mul 1702 1799, .sub 1763 1825,
    .add 1824 1826, .mul 1705 1803, .sub 1763 1828, .add 1827 1829, .cst 1950351361, .mul 1708 1831, .sub 1763 1832,
    .add 1830 1833, .cst 1981808641, .mul 1711 1835, .sub 1763 1836, .add 1834 1837, .mul 1714 1807, .sub 1763 1839,
    .add 1838 1840, .mul 1717 1815, .sub 1763 1842, .add 1841 1843, .sub 1844 1760, .cst 1052077299, .add 1845 1846,
    .mul 1847 1847, .mul 1848 1847, .sub 1762 1849, .mul 1762 1762, .mul 1851 1847, .var 286, .sub 1852 1853,
    .var 287, .add 1844 1760, .add 1764 1856, .add 1766 1766, .add 1858 1856, .add 1857 1859, .mul 1770 1768,
    .add 1861 1856, .add 1860 1862, .add 1774 1774, .add 1856 1864, .add 1865 1774, .add 1863 1866, .add 1778 1778,
    .add 1868 1868, .add 1856 1869, .add 1867 1870, .mul 1781 1768, .sub 1856 1872, .add 1871 1873, .add 1785 1785,
    .add 1875 1785, .sub 1856 1876, .add 1874 1877, .add 1789 1789, .add 1879 1879, .sub 1856 1880, .add 1878 1881,
    .mul 1793 1791, .add 1883 1856, .add 1882 1884, .mul 1797 1795, .add 1886 1856, .add 1885 1887, .mul 1801 1799,
    .add 1889 1856, .add 1888 1890, .mul 1805 1803, .add 1892 1856, .add 1891 1893, .mul 1809 1807, .add 1895 1856,
    .add 1894 1896, .mul 1813 1811, .add 1898 1856, .add 1897 1899, .mul 1817 1815, .add 1901 1856, .add 1900 1902,
    .mul 1820 1791, .sub 1856 1904, .add 1903 1905, .mul 1823 1795, .sub 1856 1907, .add 1906 1908, .mul 1826 1799,
    .sub 1856 1910, .add 1909 1911, .mul 1829 1803, .sub 1856 1913, .add 1912 1914, .mul 1833 1831, .sub 1856 1916,
    .add 1915 1917, .mul 1837 1835, .sub 1856 1919, .add 1918 1920, .mul 1840 1807, .sub 1856 1922, .add 1921 1923,
    .mul 1843 1815, .sub 1856 1925, .add 1924 1926, .sub 1927 1853, .cst 1540960371, .add 1928 1929, .mul 1930 1930,
    .mul 1931 1930, .sub 1855 1932, .mul 1855 1855, .mul 1934 1930, .var 288, .sub 1935 1936, .var 289,
    .add 1927 1853, .add 1857 1939, .add 1859 1859, .add 1941 1939, .add 1940 1942, .mul 1862 1768, .add 1944 1939,
    .add 1943 1945, .add 1866 1866, .add 1939 1947, .add 1948 1866, .add 1946 1949, .add 1870 1870, .add 1951 1951,
    .add 1939 1952, .add 1950 1953, .mul 1873 1768, .sub 1939 1955, .add 1954 1956, .add 1877 1877, .add 1958 1877,
    .sub 1939 1959, .add 1957 1960, .add 1881 1881, .add 1962 1962, .sub 1939 1963, .add 1961 1964, .mul 1884 1791,
    .add 1966 1939, .add 1965 1967, .mul 1887 1795, .add 1969 1939, .add 1968 1970, .mul 1890 1799, .add 1972 1939,
    .add 1971 1973, .mul 1893 1803, .add 1975 1939, .add 1974 1976, .mul 1896 1807, .add 1978 1939, .add 1977 1979,
    .mul 1899 1811, .add 1981 1939, .add 1980 1982, .mul 1902 1815, .add 1984 1939, .add 1983 1985, .mul 1905 1791,
    .sub 1939 1987, .add 1986 1988, .mul 1908 1795, .sub 1939 1990, .add 1989 1991, .mul 1911 1799, .sub 1939 1993,
    .add 1992 1994, .mul 1914 1803, .sub 1939 1996, .add 1995 1997, .mul 1917 1831, .sub 1939 1999, .add 1998 2000,
    .mul 1920 1835, .sub 1939 2002, .add 2001 2003, .mul 1923 1807, .sub 1939 2005, .add 2004 2006, .mul 1926 1815,
    .sub 1939 2008, .add 2007 2009, .sub 2010 1936, .cst 924863639, .add 2011 2012, .mul 2013 2013, .mul 2014 2013,
    .sub 1938 2015, .mul 1938 1938, .mul 2017 2013, .var 290, .sub 2018 2019, .var 291, .add 2010 1936,
    .add 1940 2022, .add 1942 1942, .add 2024 2022, .add 2023 2025, .mul 1945 1768, .add 2027 2022, .add 2026 2028,
    .add 1949 1949, .add 2022 2030, .add 2031 1949, .add 2029 2032, .add 1953 1953, .add 2034 2034, .add 2022 2035,
    .add 2033 2036, .mul 1956 1768, .sub 2022 2038, .add 2037 2039, .add 1960 1960, .add 2041 1960, .sub 2022 2042,
    .add 2040 2043, .add 1964 1964, .add 2045 2045, .sub 2022 2046]

def p2w24DagC4 : List Node :=
  [  .add 2044 2047, .mul 1967 1791, .add 2049 2022, .add 2048 2050, .mul 1970 1795, .add 2052 2022, .add 2051 2053,
    .mul 1973 1799, .add 2055 2022, .add 2054 2056, .mul 1976 1803, .add 2058 2022, .add 2057 2059, .mul 1979 1807,
    .add 2061 2022, .add 2060 2062, .mul 1982 1811, .add 2064 2022, .add 2063 2065, .mul 1985 1815, .add 2067 2022,
    .add 2066 2068, .mul 1988 1791, .sub 2022 2070, .add 2069 2071, .mul 1991 1795, .sub 2022 2073, .add 2072 2074,
    .mul 1994 1799, .sub 2022 2076, .add 2075 2077, .mul 1997 1803, .sub 2022 2079, .add 2078 2080, .mul 2000 1831,
    .sub 2022 2082, .add 2081 2083, .mul 2003 1835, .sub 2022 2085, .add 2084 2086, .mul 2006 1807, .sub 2022 2088,
    .add 2087 2089, .mul 2009 1815, .sub 2022 2091, .add 2090 2092, .sub 2093 2019, .cst 1365519753, .add 2094 2095,
    .mul 2096 2096, .mul 2097 2096, .sub 2021 2098, .mul 2021 2021, .mul 2100 2096, .var 292, .sub 2101 2102,
    .var 293, .add 2093 2019, .add 2023 2105, .add 2025 2025, .add 2107 2105, .add 2106 2108, .mul 2028 1768,
    .add 2110 2105, .add 2109 2111, .add 2032 2032, .add 2105 2113, .add 2114 2032, .add 2112 2115, .add 2036 2036,
    .add 2117 2117, .add 2105 2118, .add 2116 2119, .mul 2039 1768, .sub 2105 2121, .add 2120 2122, .add 2043 2043,
    .add 2124 2043, .sub 2105 2125, .add 2123 2126, .add 2047 2047, .add 2128 2128, .sub 2105 2129, .add 2127 2130,
    .mul 2050 1791, .add 2132 2105, .add 2131 2133, .mul 2053 1795, .add 2135 2105, .add 2134 2136, .mul 2056 1799,
    .add 2138 2105, .add 2137 2139, .mul 2059 1803, .add 2141 2105, .add 2140 2142, .mul 2062 1807, .add 2144 2105,
    .add 2143 2145, .mul 2065 1811, .add 2147 2105, .add 2146 2148, .mul 2068 1815, .add 2150 2105, .add 2149 2151,
    .mul 2071 1791, .sub 2105 2153, .add 2152 2154, .mul 2074 1795, .sub 2105 2156, .add 2155 2157, .mul 2077 1799,
    .sub 2105 2159, .add 2158 2160, .mul 2080 1803, .sub 2105 2162, .add 2161 2163, .mul 2083 1831, .sub 2105 2165,
    .add 2164 2166, .mul 2086 1835, .sub 2105 2168, .add 2167 2169, .mul 2089 1807, .sub 2105 2171, .add 2170 2172,
    .mul 2092 1815, .sub 2105 2174, .add 2173 2175, .sub 2176 2102, .cst 1726563304, .add 2177 2178, .mul 2179 2179,
    .mul 2180 2179, .sub 2104 2181, .mul 2104 2104, .mul 2183 2179, .var 294, .sub 2184 2185, .var 295,
    .add 2176 2102, .add 2106 2188, .add 2108 2108, .add 2190 2188, .add 2189 2191, .mul 2111 1768, .add 2193 2188,
    .add 2192 2194, .add 2115 2115, .add 2188 2196, .add 2197 2115, .add 2195 2198, .add 2119 2119, .add 2200 2200,
    .add 2188 2201, .add 2199 2202, .mul 2122 1768, .sub 2188 2204, .add 2203 2205, .add 2126 2126, .add 2207 2126,
    .sub 2188 2208, .add 2206 2209, .add 2130 2130, .add 2211 2211, .sub 2188 2212, .add 2210 2213, .mul 2133 1791,
    .add 2215 2188, .add 2214 2216, .mul 2136 1795, .add 2218 2188, .add 2217 2219, .mul 2139 1799, .add 2221 2188,
    .add 2220 2222, .mul 2142 1803, .add 2224 2188, .add 2223 2225, .mul 2145 1807, .add 2227 2188, .add 2226 2228,
    .mul 2148 1811, .add 2230 2188, .add 2229 2231, .mul 2151 1815, .add 2233 2188, .add 2232 2234, .mul 2154 1791,
    .sub 2188 2236, .add 2235 2237, .mul 2157 1795, .sub 2188 2239, .add 2238 2240, .mul 2160 1799, .sub 2188 2242,
    .add 2241 2243, .mul 2163 1803, .sub 2188 2245, .add 2244 2246, .mul 2166 1831, .sub 2188 2248, .add 2247 2249,
    .mul 2169 1835, .sub 2188 2251, .add 2250 2252, .mul 2172 1807, .sub 2188 2254, .add 2253 2255, .mul 2175 1815,
    .sub 2188 2257, .add 2256 2258, .sub 2259 2185, .cst 440300254, .add 2260 2261, .mul 2262 2262, .mul 2263 2262,
    .sub 2187 2264, .mul 2187 2187, .mul 2266 2262, .var 296, .sub 2267 2268, .var 297, .add 2259 2185,
    .add 2189 2271, .add 2191 2191, .add 2273 2271, .add 2272 2274, .mul 2194 1768, .add 2276 2271, .add 2275 2277,
    .add 2198 2198, .add 2271 2279, .add 2280 2198, .add 2278 2281, .add 2202 2202, .add 2283 2283, .add 2271 2284,
    .add 2282 2285, .mul 2205 1768, .sub 2271 2287, .add 2286 2288, .add 2209 2209, .add 2290 2209, .sub 2271 2291,
    .add 2289 2292, .add 2213 2213, .add 2294 2294, .sub 2271 2295, .add 2293 2296, .mul 2216 1791, .add 2298 2271,
    .add 2297 2299, .mul 2219 1795, .add 2301 2271, .add 2300 2302, .mul 2222 1799, .add 2304 2271, .add 2303 2305,
    .mul 2225 1803, .add 2307 2271, .add 2306 2308, .mul 2228 1807, .add 2310 2271, .add 2309 2311, .mul 2231 1811,
    .add 2313 2271, .add 2312 2314, .mul 2234 1815, .add 2316 2271, .add 2315 2317, .mul 2237 1791, .sub 2271 2319,
    .add 2318 2320, .mul 2240 1795, .sub 2271 2322, .add 2321 2323, .mul 2243 1799, .sub 2271 2325, .add 2324 2326,
    .mul 2246 1803, .sub 2271 2328, .add 2327 2329, .mul 2249 1831, .sub 2271 2331, .add 2330 2332, .mul 2252 1835,
    .sub 2271 2334, .add 2333 2335, .mul 2255 1807, .sub 2271 2337, .add 2336 2338, .mul 2258 1815, .sub 2271 2340,
    .add 2339 2341, .sub 2342 2268, .cst 1891545577, .add 2343 2344, .mul 2345 2345, .mul 2346 2345, .sub 2270 2347,
    .mul 2270 2270, .mul 2349 2345, .var 298, .sub 2350 2351, .var 299, .add 2342 2268, .add 2272 2354,
    .add 2274 2274, .add 2356 2354, .add 2355 2357, .mul 2277 1768, .add 2359 2354, .add 2358 2360, .add 2281 2281,
    .add 2354 2362, .add 2363 2281, .add 2361 2364, .add 2285 2285, .add 2366 2366, .add 2354 2367, .add 2365 2368,
    .mul 2288 1768, .sub 2354 2370, .add 2369 2371, .add 2292 2292, .add 2373 2292, .sub 2354 2374, .add 2372 2375,
    .add 2296 2296, .add 2377 2377, .sub 2354 2378, .add 2376 2379, .mul 2299 1791, .add 2381 2354, .add 2380 2382,
    .mul 2302 1795, .add 2384 2354, .add 2383 2385, .mul 2305 1799, .add 2387 2354, .add 2386 2388, .mul 2308 1803,
    .add 2390 2354, .add 2389 2391, .mul 2311 1807, .add 2393 2354, .add 2392 2394, .mul 2314 1811, .add 2396 2354,
    .add 2395 2397, .mul 2317 1815, .add 2399 2354, .add 2398 2400, .mul 2320 1791, .sub 2354 2402, .add 2401 2403,
    .mul 2323 1795, .sub 2354 2405, .add 2404 2406, .mul 2326 1799, .sub 2354 2408, .add 2407 2409, .mul 2329 1803,
    .sub 2354 2411, .add 2410 2412, .mul 2332 1831, .sub 2354 2414, .add 2413 2415, .mul 2335 1835, .sub 2354 2417,
    .add 2416 2418, .mul 2338 1807, .sub 2354 2420, .add 2419 2421, .mul 2341 1815, .sub 2354 2423, .add 2422 2424,
    .sub 2425 2351, .cst 822033215, .add 2426 2427, .mul 2428 2428, .mul 2429 2428, .sub 2353 2430, .mul 2353 2353,
    .mul 2432 2428, .var 300, .sub 2433 2434, .var 301, .add 2425 2351, .add 2355 2437, .add 2357 2357,
    .add 2439 2437, .add 2438 2440, .mul 2360 1768, .add 2442 2437, .add 2441 2443, .add 2364 2364, .add 2437 2445,
    .add 2446 2364, .add 2444 2447, .add 2368 2368, .add 2449 2449, .add 2437 2450, .add 2448 2451, .mul 2371 1768,
    .sub 2437 2453, .add 2452 2454, .add 2375 2375, .add 2456 2375, .sub 2437 2457, .add 2455 2458, .add 2379 2379,
    .add 2460 2460, .sub 2437 2461, .add 2459 2462, .mul 2382 1791, .add 2464 2437, .add 2463 2465, .mul 2385 1795,
    .add 2467 2437, .add 2466 2468, .mul 2388 1799, .add 2470 2437, .add 2469 2471, .mul 2391 1803, .add 2473 2437,
    .add 2472 2474, .mul 2394 1807, .add 2476 2437, .add 2475 2477, .mul 2397 1811, .add 2479 2437, .add 2478 2480,
    .mul 2400 1815, .add 2482 2437, .add 2481 2483, .mul 2403 1791, .sub 2437 2485, .add 2484 2486, .mul 2406 1795,
    .sub 2437 2488, .add 2487 2489, .mul 2409 1799, .sub 2437 2491, .add 2490 2492, .mul 2412 1803, .sub 2437 2494,
    .add 2493 2495, .mul 2415 1831, .sub 2437 2497, .add 2496 2498, .mul 2418 1835, .sub 2437 2500, .add 2499 2501,
    .mul 2421 1807, .sub 2437 2503, .add 2502 2504, .mul 2424 1815, .sub 2437 2506, .add 2505 2507, .sub 2508 2434,
    .cst 1111544260, .add 2509 2510, .mul 2511 2511, .mul 2512 2511, .sub 2436 2513, .mul 2436 2436, .mul 2515 2511,
    .var 302, .sub 2516 2517, .var 303, .add 2508 2434, .add 2438 2520, .add 2440 2440, .add 2522 2520,
    .add 2521 2523, .mul 2443 1768, .add 2525 2520, .add 2524 2526, .add 2447 2447, .add 2520 2528, .add 2529 2447,
    .add 2527 2530, .add 2451 2451, .add 2532 2532, .add 2520 2533, .add 2531 2534, .mul 2454 1768, .sub 2520 2536,
    .add 2535 2537, .add 2458 2458, .add 2539 2458, .sub 2520 2540, .add 2538 2541, .add 2462 2462, .add 2543 2543,
    .sub 2520 2544, .add 2542 2545, .mul 2465 1791, .add 2547 2520, .add 2546 2548, .mul 2468 1795, .add 2550 2520,
    .add 2549 2551, .mul 2471 1799, .add 2553 2520, .add 2552 2554, .mul 2474 1803, .add 2556 2520, .add 2555 2557,
    .mul 2477 1807]

def p2w24DagC5 : List Node :=
  [  .add 2559 2520, .add 2558 2560, .mul 2480 1811, .add 2562 2520, .add 2561 2563, .mul 2483 1815, .add 2565 2520,
    .add 2564 2566, .mul 2486 1791, .sub 2520 2568, .add 2567 2569, .mul 2489 1795, .sub 2520 2571, .add 2570 2572,
    .mul 2492 1799, .sub 2520 2574, .add 2573 2575, .mul 2495 1803, .sub 2520 2577, .add 2576 2578, .mul 2498 1831,
    .sub 2520 2580, .add 2579 2581, .mul 2501 1835, .sub 2520 2583, .add 2582 2584, .mul 2504 1807, .sub 2520 2586,
    .add 2585 2587, .mul 2507 1815, .sub 2520 2589, .add 2588 2590, .sub 2591 2517, .cst 308575117, .add 2592 2593,
    .mul 2594 2594, .mul 2595 2594, .sub 2519 2596, .mul 2519 2519, .mul 2598 2594, .var 304, .sub 2599 2600,
    .var 305, .add 2591 2517, .add 2521 2603, .add 2523 2523, .add 2605 2603, .add 2604 2606, .mul 2526 1768,
    .add 2608 2603, .add 2607 2609, .add 2530 2530, .add 2603 2611, .add 2612 2530, .add 2610 2613, .add 2534 2534,
    .add 2615 2615, .add 2603 2616, .add 2614 2617, .mul 2537 1768, .sub 2603 2619, .add 2618 2620, .add 2541 2541,
    .add 2622 2541, .sub 2603 2623, .add 2621 2624, .add 2545 2545, .add 2626 2626, .sub 2603 2627, .add 2625 2628,
    .mul 2548 1791, .add 2630 2603, .add 2629 2631, .mul 2551 1795, .add 2633 2603, .add 2632 2634, .mul 2554 1799,
    .add 2636 2603, .add 2635 2637, .mul 2557 1803, .add 2639 2603, .add 2638 2640, .mul 2560 1807, .add 2642 2603,
    .add 2641 2643, .mul 2563 1811, .add 2645 2603, .add 2644 2646, .mul 2566 1815, .add 2648 2603, .add 2647 2649,
    .mul 2569 1791, .sub 2603 2651, .add 2650 2652, .mul 2572 1795, .sub 2603 2654, .add 2653 2655, .mul 2575 1799,
    .sub 2603 2657, .add 2656 2658, .mul 2578 1803, .sub 2603 2660, .add 2659 2661, .mul 2581 1831, .sub 2603 2663,
    .add 2662 2664, .mul 2584 1835, .sub 2603 2666, .add 2665 2667, .mul 2587 1807, .sub 2603 2669, .add 2668 2670,
    .mul 2590 1815, .sub 2603 2672, .add 2671 2673, .sub 2674 2600, .cst 1708681573, .add 2675 2676, .mul 2677 2677,
    .mul 2678 2677, .sub 2602 2679, .mul 2602 2602, .mul 2681 2677, .var 306, .sub 2682 2683, .var 307,
    .add 2674 2600, .add 2604 2686, .add 2606 2606, .add 2688 2686, .add 2687 2689, .mul 2609 1768, .add 2691 2686,
    .add 2690 2692, .add 2613 2613, .add 2686 2694, .add 2695 2613, .add 2693 2696, .add 2617 2617, .add 2698 2698,
    .add 2686 2699, .add 2697 2700, .mul 2620 1768, .sub 2686 2702, .add 2701 2703, .add 2624 2624, .add 2705 2624,
    .sub 2686 2706, .add 2704 2707, .add 2628 2628, .add 2709 2709, .sub 2686 2710, .add 2708 2711, .mul 2631 1791,
    .add 2713 2686, .add 2712 2714, .mul 2634 1795, .add 2716 2686, .add 2715 2717, .mul 2637 1799, .add 2719 2686,
    .add 2718 2720, .mul 2640 1803, .add 2722 2686, .add 2721 2723, .mul 2643 1807, .add 2725 2686, .add 2724 2726,
    .mul 2646 1811, .add 2728 2686, .add 2727 2729, .mul 2649 1815, .add 2731 2686, .add 2730 2732, .mul 2652 1791,
    .sub 2686 2734, .add 2733 2735, .mul 2655 1795, .sub 2686 2737, .add 2736 2738, .mul 2658 1799, .sub 2686 2740,
    .add 2739 2741, .mul 2661 1803, .sub 2686 2743, .add 2742 2744, .mul 2664 1831, .sub 2686 2746, .add 2745 2747,
    .mul 2667 1835, .sub 2686 2749, .add 2748 2750, .mul 2670 1807, .sub 2686 2752, .add 2751 2753, .mul 2673 1815,
    .sub 2686 2755, .add 2754 2756, .sub 2757 2683, .cst 1240419708, .add 2758 2759, .mul 2760 2760, .mul 2761 2760,
    .sub 2685 2762, .mul 2685 2685, .mul 2764 2760, .var 308, .sub 2765 2766, .var 309, .add 2757 2683,
    .add 2687 2769, .add 2689 2689, .add 2771 2769, .add 2770 2772, .mul 2692 1768, .add 2774 2769, .add 2773 2775,
    .add 2696 2696, .add 2769 2777, .add 2778 2696, .add 2776 2779, .add 2700 2700, .add 2781 2781, .add 2769 2782,
    .add 2780 2783, .mul 2703 1768, .sub 2769 2785, .add 2784 2786, .add 2707 2707, .add 2788 2707, .sub 2769 2789,
    .add 2787 2790, .add 2711 2711, .add 2792 2792, .sub 2769 2793, .add 2791 2794, .mul 2714 1791, .add 2796 2769,
    .add 2795 2797, .mul 2717 1795, .add 2799 2769, .add 2798 2800, .mul 2720 1799, .add 2802 2769, .add 2801 2803,
    .mul 2723 1803, .add 2805 2769, .add 2804 2806, .mul 2726 1807, .add 2808 2769, .add 2807 2809, .mul 2729 1811,
    .add 2811 2769, .add 2810 2812, .mul 2732 1815, .add 2814 2769, .add 2813 2815, .mul 2735 1791, .sub 2769 2817,
    .add 2816 2818, .mul 2738 1795, .sub 2769 2820, .add 2819 2821, .mul 2741 1799, .sub 2769 2823, .add 2822 2824,
    .mul 2744 1803, .sub 2769 2826, .add 2825 2827, .mul 2747 1831, .sub 2769 2829, .add 2828 2830, .mul 2750 1835,
    .sub 2769 2832, .add 2831 2833, .mul 2753 1807, .sub 2769 2835, .add 2834 2836, .mul 2756 1815, .sub 2769 2838,
    .add 2837 2839, .sub 2840 2766, .cst 1199068823, .add 2841 2842, .mul 2843 2843, .mul 2844 2843, .sub 2768 2845,
    .mul 2768 2768, .mul 2847 2843, .var 310, .sub 2848 2849, .var 311, .add 2840 2766, .add 2770 2852,
    .add 2772 2772, .add 2854 2852, .add 2853 2855, .mul 2775 1768, .add 2857 2852, .add 2856 2858, .add 2779 2779,
    .add 2852 2860, .add 2861 2779, .add 2859 2862, .add 2783 2783, .add 2864 2864, .add 2852 2865, .add 2863 2866,
    .mul 2786 1768, .sub 2852 2868, .add 2867 2869, .add 2790 2790, .add 2871 2790, .sub 2852 2872, .add 2870 2873,
    .add 2794 2794, .add 2875 2875, .sub 2852 2876, .add 2874 2877, .mul 2797 1791, .add 2879 2852, .add 2878 2880,
    .mul 2800 1795, .add 2882 2852, .add 2881 2883, .mul 2803 1799, .add 2885 2852, .add 2884 2886, .mul 2806 1803,
    .add 2888 2852, .add 2887 2889, .mul 2809 1807, .add 2891 2852, .add 2890 2892, .mul 2812 1811, .add 2894 2852,
    .add 2893 2895, .mul 2815 1815, .add 2897 2852, .add 2896 2898, .mul 2818 1791, .sub 2852 2900, .add 2899 2901,
    .mul 2821 1795, .sub 2852 2903, .add 2902 2904, .mul 2824 1799, .sub 2852 2906, .add 2905 2907, .mul 2827 1803,
    .sub 2852 2909, .add 2908 2910, .mul 2830 1831, .sub 2852 2912, .add 2911 2913, .mul 2833 1835, .sub 2852 2915,
    .add 2914 2916, .mul 2836 1807, .sub 2852 2918, .add 2917 2919, .mul 2839 1815, .sub 2852 2921, .add 2920 2922,
    .sub 2923 2849, .cst 1186174623, .add 2924 2925, .mul 2926 2926, .mul 2927 2926, .sub 2851 2928, .mul 2851 2851,
    .mul 2930 2926, .var 312, .sub 2931 2932, .var 313, .add 2923 2849, .add 2853 2935, .add 2855 2855,
    .add 2937 2935, .add 2936 2938, .mul 2858 1768, .add 2940 2935, .add 2939 2941, .add 2862 2862, .add 2935 2943,
    .add 2944 2862, .add 2942 2945, .add 2866 2866, .add 2947 2947, .add 2935 2948, .add 2946 2949, .mul 2869 1768,
    .sub 2935 2951, .add 2950 2952, .add 2873 2873, .add 2954 2873, .sub 2935 2955, .add 2953 2956, .add 2877 2877,
    .add 2958 2958, .sub 2935 2959, .add 2957 2960, .mul 2880 1791, .add 2962 2935, .add 2961 2963, .mul 2883 1795,
    .add 2965 2935, .add 2964 2966, .mul 2886 1799, .add 2968 2935, .add 2967 2969, .mul 2889 1803, .add 2971 2935,
    .add 2970 2972, .mul 2892 1807, .add 2974 2935, .add 2973 2975, .mul 2895 1811, .add 2977 2935, .add 2976 2978,
    .mul 2898 1815, .add 2980 2935, .add 2979 2981, .mul 2901 1791, .sub 2935 2983, .add 2982 2984, .mul 2904 1795,
    .sub 2935 2986, .add 2985 2987, .mul 2907 1799, .sub 2935 2989, .add 2988 2990, .mul 2910 1803, .sub 2935 2992,
    .add 2991 2993, .mul 2913 1831, .sub 2935 2995, .add 2994 2996, .mul 2916 1835, .sub 2935 2998, .add 2997 2999,
    .mul 2919 1807, .sub 2935 3001, .add 3000 3002, .mul 2922 1815, .sub 2935 3004, .add 3003 3005, .sub 3006 2932,
    .cst 1551596046, .add 3007 3008, .mul 3009 3009, .mul 3010 3009, .sub 2934 3011, .mul 2934 2934, .mul 3013 3009,
    .var 314, .sub 3014 3015, .var 315, .add 3006 2932, .add 2936 3018, .add 2938 2938, .add 3020 3018,
    .add 3019 3021, .mul 2941 1768, .add 3023 3018, .add 3022 3024, .add 2945 2945, .add 3018 3026, .add 3027 2945,
    .add 3025 3028, .add 2949 2949, .add 3030 3030, .add 3018 3031, .add 3029 3032, .mul 2952 1768, .sub 3018 3034,
    .add 3033 3035, .add 2956 2956, .add 3037 2956, .sub 3018 3038, .add 3036 3039, .add 2960 2960, .add 3041 3041,
    .sub 3018 3042, .add 3040 3043, .mul 2963 1791, .add 3045 3018, .add 3044 3046, .mul 2966 1795, .add 3048 3018,
    .add 3047 3049, .mul 2969 1799, .add 3051 3018, .add 3050 3052, .mul 2972 1803, .add 3054 3018, .add 3053 3055,
    .mul 2975 1807, .add 3057 3018, .add 3056 3058, .mul 2978 1811, .add 3060 3018, .add 3059 3061, .mul 2981 1815,
    .add 3063 3018, .add 3062 3064, .mul 2984 1791, .sub 3018 3066, .add 3065 3067, .mul 2987 1795, .sub 3018 3069,
    .add 3068 3070]

def p2w24DagC6 : List Node :=
  [  .mul 2990 1799, .sub 3018 3072, .add 3071 3073, .mul 2993 1803, .sub 3018 3075, .add 3074 3076, .mul 2996 1831,
    .sub 3018 3078, .add 3077 3079, .mul 2999 1835, .sub 3018 3081, .add 3080 3082, .mul 3002 1807, .sub 3018 3084,
    .add 3083 3085, .mul 3005 1815, .sub 3018 3087, .add 3086 3088, .sub 3089 3015, .cst 1886977120, .add 3090 3091,
    .mul 3092 3092, .mul 3093 3092, .sub 3017 3094, .mul 3017 3017, .mul 3096 3092, .var 316, .sub 3097 3098,
    .var 317, .add 3089 3015, .add 3019 3101, .add 3021 3021, .add 3103 3101, .add 3102 3104, .mul 3024 1768,
    .add 3106 3101, .add 3105 3107, .add 3028 3028, .add 3101 3109, .add 3110 3028, .add 3108 3111, .add 3032 3032,
    .add 3113 3113, .add 3101 3114, .add 3112 3115, .mul 3035 1768, .sub 3101 3117, .add 3116 3118, .add 3039 3039,
    .add 3120 3039, .sub 3101 3121, .add 3119 3122, .add 3043 3043, .add 3124 3124, .sub 3101 3125, .add 3123 3126,
    .mul 3046 1791, .add 3128 3101, .add 3127 3129, .mul 3049 1795, .add 3131 3101, .add 3130 3132, .mul 3052 1799,
    .add 3134 3101, .add 3133 3135, .mul 3055 1803, .add 3137 3101, .add 3136 3138, .mul 3058 1807, .add 3140 3101,
    .add 3139 3141, .mul 3061 1811, .add 3143 3101, .add 3142 3144, .mul 3064 1815, .add 3146 3101, .add 3145 3147,
    .mul 3067 1791, .sub 3101 3149, .add 3148 3150, .mul 3070 1795, .sub 3101 3152, .add 3151 3153, .mul 3073 1799,
    .sub 3101 3155, .add 3154 3156, .mul 3076 1803, .sub 3101 3158, .add 3157 3159, .mul 3079 1831, .sub 3101 3161,
    .add 3160 3162, .mul 3082 1835, .sub 3101 3164, .add 3163 3165, .mul 3085 1807, .sub 3101 3167, .add 3166 3168,
    .mul 3088 1815, .sub 3101 3170, .add 3169 3171, .sub 3172 3098, .cst 1327682690, .add 3173 3174, .mul 3175 3175,
    .mul 3176 3175, .sub 3100 3177, .mul 3100 3100, .mul 3179 3175, .var 318, .sub 3180 3181, .var 319,
    .add 3172 3098, .add 3102 3184, .add 3104 3104, .add 3186 3184, .add 3185 3187, .mul 3107 1768, .add 3189 3184,
    .add 3188 3190, .add 3111 3111, .add 3184 3192, .add 3193 3111, .add 3191 3194, .add 3115 3115, .add 3196 3196,
    .add 3184 3197, .add 3195 3198, .mul 3118 1768, .sub 3184 3200, .add 3199 3201, .add 3122 3122, .add 3203 3122,
    .sub 3184 3204, .add 3202 3205, .add 3126 3126, .add 3207 3207, .sub 3184 3208, .add 3206 3209, .mul 3129 1791,
    .add 3211 3184, .add 3210 3212, .mul 3132 1795, .add 3214 3184, .add 3213 3215, .mul 3135 1799, .add 3217 3184,
    .add 3216 3218, .mul 3138 1803, .add 3220 3184, .add 3219 3221, .mul 3141 1807, .add 3223 3184, .add 3222 3224,
    .mul 3144 1811, .add 3226 3184, .add 3225 3227, .mul 3147 1815, .add 3229 3184, .add 3228 3230, .mul 3150 1791,
    .sub 3184 3232, .add 3231 3233, .mul 3153 1795, .sub 3184 3235, .add 3234 3236, .mul 3156 1799, .sub 3184 3238,
    .add 3237 3239, .mul 3159 1803, .sub 3184 3241, .add 3240 3242, .mul 3162 1831, .sub 3184 3244, .add 3243 3245,
    .mul 3165 1835, .sub 3184 3247, .add 3246 3248, .mul 3168 1807, .sub 3184 3250, .add 3249 3251, .mul 3171 1815,
    .sub 3184 3253, .add 3252 3254, .sub 3255 3181, .cst 1210751726, .add 3256 3257, .mul 3258 3258, .mul 3259 3258,
    .sub 3183 3260, .mul 3183 3183, .mul 3262 3258, .var 320, .sub 3263 3264, .var 321, .add 3255 3181,
    .add 3185 3267, .add 3187 3187, .add 3269 3267, .add 3268 3270, .mul 3190 1768, .add 3272 3267, .add 3271 3273,
    .add 3194 3194, .add 3267 3275, .add 3276 3194, .add 3274 3277, .add 3198 3198, .add 3279 3279, .add 3267 3280,
    .add 3278 3281, .mul 3201 1768, .sub 3267 3283, .add 3282 3284, .add 3205 3205, .add 3286 3205, .sub 3267 3287,
    .add 3285 3288, .add 3209 3209, .add 3290 3290, .sub 3267 3291, .add 3289 3292, .mul 3212 1791, .add 3294 3267,
    .add 3293 3295, .mul 3215 1795, .add 3297 3267, .add 3296 3298, .mul 3218 1799, .add 3300 3267, .add 3299 3301,
    .mul 3221 1803, .add 3303 3267, .add 3302 3304, .mul 3224 1807, .add 3306 3267, .add 3305 3307, .mul 3227 1811,
    .add 3309 3267, .add 3308 3310, .mul 3230 1815, .add 3312 3267, .add 3311 3313, .mul 3233 1791, .sub 3267 3315,
    .add 3314 3316, .mul 3236 1795, .sub 3267 3318, .add 3317 3319, .mul 3239 1799, .sub 3267 3321, .add 3320 3322,
    .mul 3242 1803, .sub 3267 3324, .add 3323 3325, .mul 3245 1831, .sub 3267 3327, .add 3326 3328, .mul 3248 1835,
    .sub 3267 3330, .add 3329 3331, .mul 3251 1807, .sub 3267 3333, .add 3332 3334, .mul 3254 1815, .sub 3267 3336,
    .add 3335 3337, .sub 3338 3264, .cst 1810596765, .add 3339 3340, .mul 3341 3341, .mul 3342 3341, .sub 3266 3343,
    .mul 3266 3266, .mul 3345 3341, .var 322, .sub 3346 3347, .var 323, .add 3338 3264, .add 3268 3350,
    .add 3270 3270, .add 3352 3350, .add 3351 3353, .mul 3273 1768, .add 3355 3350, .add 3354 3356, .add 3277 3277,
    .add 3350 3358, .add 3359 3277, .add 3357 3360, .add 3281 3281, .add 3362 3362, .add 3350 3363, .add 3361 3364,
    .mul 3284 1768, .sub 3350 3366, .add 3365 3367, .add 3288 3288, .add 3369 3288, .sub 3350 3370, .add 3368 3371,
    .add 3292 3292, .add 3373 3373, .sub 3350 3374, .add 3372 3375, .mul 3295 1791, .add 3377 3350, .add 3376 3378,
    .mul 3298 1795, .add 3380 3350, .add 3379 3381, .mul 3301 1799, .add 3383 3350, .add 3382 3384, .mul 3304 1803,
    .add 3386 3350, .add 3385 3387, .mul 3307 1807, .add 3389 3350, .add 3388 3390, .mul 3310 1811, .add 3392 3350,
    .add 3391 3393, .mul 3313 1815, .add 3395 3350, .add 3394 3396, .mul 3316 1791, .sub 3350 3398, .add 3397 3399,
    .mul 3319 1795, .sub 3350 3401, .add 3400 3402, .mul 3322 1799, .sub 3350 3404, .add 3403 3405, .mul 3325 1803,
    .sub 3350 3407, .add 3406 3408, .mul 3328 1831, .sub 3350 3410, .add 3409 3411, .mul 3331 1835, .sub 3350 3413,
    .add 3412 3414, .mul 3334 1807, .sub 3350 3416, .add 3415 3417, .mul 3337 1815, .sub 3350 3419, .add 3418 3420,
    .sub 3421 3347, .cst 53041581, .add 3422 3423, .mul 3424 3424, .mul 3425 3424, .sub 3349 3426, .var 324,
    .add 3421 3347, .add 3351 3429, .cst 723038058, .add 3430 3431, .mul 3432 3432, .mul 3433 3432, .sub 3428 3434,
    .var 325, .add 3353 3353, .add 3437 3429, .cst 1439947916, .add 3438 3439, .mul 3440 3440, .mul 3441 3440,
    .sub 3436 3442, .var 326, .mul 3356 1768, .add 3445 3429, .cst 1136469704, .add 3446 3447, .mul 3448 3448,
    .mul 3449 3448, .sub 3444 3450, .var 327, .add 3360 3360, .add 3429 3453, .add 3454 3360, .cst 205609311,
    .add 3455 3456, .mul 3457 3457, .mul 3458 3457, .sub 3452 3459, .var 328, .add 3364 3364, .add 3462 3462,
    .add 3429 3463, .cst 1883820770, .add 3464 3465, .mul 3466 3466, .mul 3467 3466, .sub 3461 3468, .var 329,
    .mul 3367 1768, .sub 3429 3471, .cst 14387587, .add 3472 3473, .mul 3474 3474, .mul 3475 3474, .sub 3470 3476,
    .var 330, .add 3371 3371, .add 3479 3371, .sub 3429 3480, .cst 720724951, .add 3481 3482, .mul 3483 3483,
    .mul 3484 3483, .sub 3478 3485, .var 331, .add 3375 3375, .add 3488 3488, .sub 3429 3489, .cst 1854174607,
    .add 3490 3491, .mul 3492 3492, .mul 3493 3492, .sub 3487 3494, .var 332, .mul 3378 1791, .add 3497 3429,
    .cst 1629316321, .add 3498 3499, .mul 3500 3500, .mul 3501 3500, .sub 3496 3502, .var 333, .mul 3381 1795,
    .add 3505 3429, .cst 530151394, .add 3506 3507, .mul 3508 3508, .mul 3509 3508, .sub 3504 3510, .var 334,
    .mul 3384 1799, .add 3513 3429, .cst 1679178250, .add 3514 3515, .mul 3516 3516, .mul 3517 3516, .sub 3512 3518,
    .var 335, .mul 3387 1803, .add 3521 3429, .cst 1549779579, .add 3522 3523, .mul 3524 3524, .mul 3525 3524,
    .sub 3520 3526, .var 336, .mul 3390 1807, .add 3529 3429, .cst 48375137, .add 3530 3531, .mul 3532 3532,
    .mul 3533 3532, .sub 3528 3534, .var 337, .mul 3393 1811, .add 3537 3429, .cst 976057819, .add 3538 3539,
    .mul 3540 3540, .mul 3541 3540, .sub 3536 3542, .var 338, .mul 3396 1815, .add 3545 3429, .cst 463976218,
    .add 3546 3547, .mul 3548 3548, .mul 3549 3548, .sub 3544 3550, .var 339, .mul 3399 1791, .sub 3429 3553,
    .cst 875839332, .add 3554 3555, .mul 3556 3556, .mul 3557 3556, .sub 3552 3558, .var 340, .mul 3402 1795,
    .sub 3429 3561, .cst 1946596189, .add 3562 3563, .mul 3564 3564, .mul 3565 3564, .sub 3560 3566, .var 341,
    .mul 3405 1799, .sub 3429 3569, .cst 434078361, .add 3570 3571, .mul 3572 3572, .mul 3573 3572, .sub 3568 3574,
    .var 342, .mul 3408 1803, .sub 3429 3577, .cst 1878280202, .add 3578 3579, .mul 3580 3580, .mul 3581 3580,
    .sub 3576 3582]

def p2w24DagC7 : List Node :=
  [  .var 343, .mul 3411 1831, .sub 3429 3585, .cst 1363837384, .add 3586 3587, .mul 3588 3588, .mul 3589 3588,
    .sub 3584 3590, .var 344, .mul 3414 1835, .sub 3429 3593, .cst 1470845646, .add 3594 3595, .mul 3596 3596,
    .mul 3597 3596, .sub 3592 3598, .var 345, .mul 3417 1807, .sub 3429 3601, .cst 1792450386, .add 3602 3603,
    .mul 3604 3604, .mul 3605 3604, .sub 3600 3606, .var 346, .mul 3420 1815, .sub 3429 3609, .cst 1040977421,
    .add 3610 3611, .mul 3612 3612, .mul 3613 3612, .sub 3608 3614, .mul 3349 3349, .mul 3616 3424, .mul 3428 3428,
    .mul 3618 3432, .add 3617 3619, .mul 3436 3436, .mul 3621 3440, .mul 3444 3444, .mul 3623 3448, .add 3622 3624,
    .add 3620 3625, .add 3626 3619, .add 3627 3620, .mul 3452 3452, .mul 3629 3457, .mul 3461 3461, .mul 3631 3466,
    .add 3630 3632, .mul 3470 3470, .mul 3634 3474, .mul 3478 3478, .mul 3636 3483, .add 3635 3637, .add 3633 3638,
    .add 3639 3632, .add 3640 3633, .add 3628 3641, .mul 3487 3487, .mul 3643 3492, .mul 3496 3496, .mul 3645 3500,
    .add 3644 3646, .mul 3504 3504, .mul 3648 3508, .mul 3512 3512, .mul 3650 3516, .add 3649 3651, .add 3647 3652,
    .add 3653 3646, .add 3654 3647, .add 3642 3655, .mul 3520 3520, .mul 3657 3524, .mul 3528 3528, .mul 3659 3532,
    .add 3658 3660, .mul 3536 3536, .mul 3662 3540, .mul 3544 3544, .mul 3664 3548, .add 3663 3665, .add 3661 3666,
    .add 3667 3660, .add 3668 3661, .add 3656 3669, .mul 3552 3552, .mul 3671 3556, .mul 3560 3560, .mul 3673 3564,
    .add 3672 3674, .mul 3568 3568, .mul 3676 3572, .mul 3576 3576, .mul 3678 3580, .add 3677 3679, .add 3675 3680,
    .add 3681 3674, .add 3682 3675, .add 3670 3683, .mul 3584 3584, .mul 3685 3588, .mul 3592 3592, .mul 3687 3596,
    .add 3686 3688, .mul 3600 3600, .mul 3690 3604, .mul 3608 3608, .mul 3692 3612, .add 3691 3693, .add 3689 3694,
    .add 3695 3688, .add 3696 3689, .add 3684 3697, .add 3628 3698, .var 347, .sub 3699 3700, .add 3622 3622,
    .add 3627 3702, .add 3635 3635, .add 3640 3704, .add 3703 3705, .add 3649 3649, .add 3654 3707, .add 3706 3708,
    .add 3663 3663, .add 3668 3710, .add 3709 3711, .add 3677 3677, .add 3682 3713, .add 3712 3714, .add 3691 3691,
    .add 3696 3716, .add 3715 3717, .add 3703 3718, .var 348, .sub 3719 3720, .add 3626 3624, .add 3722 3625,
    .add 3639 3637, .add 3724 3638, .add 3723 3725, .add 3653 3651, .add 3727 3652, .add 3726 3728, .add 3667 3665,
    .add 3730 3666, .add 3729 3731, .add 3681 3679, .add 3733 3680, .add 3732 3734, .add 3695 3693, .add 3736 3694,
    .add 3735 3737, .add 3723 3738, .var 349, .sub 3739 3740, .add 3617 3617, .add 3722 3742, .add 3630 3630,
    .add 3724 3744, .add 3743 3745, .add 3644 3644, .add 3727 3747, .add 3746 3748, .add 3658 3658, .add 3730 3750,
    .add 3749 3751, .add 3672 3672, .add 3733 3753, .add 3752 3754, .add 3686 3686, .add 3736 3756, .add 3755 3757,
    .add 3743 3758, .var 350, .sub 3759 3760, .add 3641 3698, .var 351, .sub 3762 3763, .add 3705 3718,
    .var 352, .sub 3765 3766, .add 3725 3738, .var 353, .sub 3768 3769, .add 3745 3758, .var 354, .sub 3771 3772,
    .add 3655 3698, .var 355, .sub 3774 3775, .add 3708 3718, .var 356, .sub 3777 3778, .add 3728 3738,
    .var 357, .sub 3780 3781, .add 3748 3758, .var 358, .sub 3783 3784, .add 3669 3698, .var 359, .sub 3786 3787,
    .add 3711 3718, .var 360, .sub 3789 3790, .add 3731 3738, .var 361, .sub 3792 3793, .add 3751 3758,
    .var 362, .sub 3795 3796, .add 3683 3698, .var 363, .sub 3798 3799, .add 3714 3718, .var 364, .sub 3801 3802,
    .add 3734 3738, .var 365, .sub 3804 3805, .add 3754 3758, .var 366, .sub 3807 3808, .add 3697 3698,
    .var 367, .sub 3810 3811, .add 3717 3718, .var 368, .sub 3813 3814, .add 3737 3738, .var 369, .sub 3816 3817,
    .add 3757 3758, .var 370, .sub 3819 3820, .var 371, .cst 1209164052, .add 3700 3823, .mul 3824 3824,
    .mul 3825 3824, .sub 3822 3826, .var 372, .cst 714957516, .add 3720 3829, .mul 3830 3830, .mul 3831 3830,
    .sub 3828 3832, .var 373, .cst 390340387, .add 3740 3835, .mul 3836 3836, .mul 3837 3836, .sub 3834 3838,
    .var 374, .cst 1213686459, .add 3760 3841, .mul 3842 3842, .mul 3843 3842, .sub 3840 3844, .var 375,
    .cst 790726260, .add 3763 3847, .mul 3848 3848, .mul 3849 3848, .sub 3846 3850, .var 376, .cst 117294666,
    .add 3766 3853, .mul 3854 3854, .mul 3855 3854, .sub 3852 3856, .var 377, .cst 140621810, .add 3769 3859,
    .mul 3860 3860, .mul 3861 3860, .sub 3858 3862, .var 378, .cst 993455846, .add 3772 3865, .mul 3866 3866,
    .mul 3867 3866, .sub 3864 3868, .var 379, .cst 1889603648, .add 3775 3871, .mul 3872 3872, .mul 3873 3872,
    .sub 3870 3874, .var 380, .cst 78845751, .add 3778 3877, .mul 3878 3878, .mul 3879 3878, .sub 3876 3880,
    .var 381, .cst 925018226, .add 3781 3883, .mul 3884 3884, .mul 3885 3884, .sub 3882 3886, .var 382,
    .cst 708123747, .add 3784 3889, .mul 3890 3890, .mul 3891 3890, .sub 3888 3892, .var 383, .cst 1647665372,
    .add 3787 3895, .mul 3896 3896, .mul 3897 3896, .sub 3894 3898, .var 384, .cst 1649953458, .add 3790 3901,
    .mul 3902 3902, .mul 3903 3902, .sub 3900 3904, .var 385, .cst 942439428, .add 3793 3907, .mul 3908 3908,
    .mul 3909 3908, .sub 3906 3910, .var 386, .cst 1006235079, .add 3796 3913, .mul 3914 3914, .mul 3915 3914,
    .sub 3912 3916, .var 387, .cst 238616145, .add 3799 3919, .mul 3920 3920, .mul 3921 3920, .sub 3918 3922,
    .var 388, .cst 930036496, .add 3802 3925, .mul 3926 3926, .mul 3927 3926, .sub 3924 3928, .var 389,
    .cst 1401020792, .add 3805 3931, .mul 3932 3932, .mul 3933 3932, .sub 3930 3934, .var 390, .cst 989618631,
    .add 3808 3937, .mul 3938 3938, .mul 3939 3938, .sub 3936 3940, .var 391, .cst 1545325389, .add 3811 3943,
    .mul 3944 3944, .mul 3945 3944, .sub 3942 3946, .var 392, .cst 1715719711, .add 3814 3949, .mul 3950 3950,
    .mul 3951 3950, .sub 3948 3952, .var 393, .cst 755691969, .add 3817 3955, .mul 3956 3956, .mul 3957 3956,
    .sub 3954 3958, .var 394, .cst 150307788, .add 3820 3961, .mul 3962 3962, .mul 3963 3962, .sub 3960 3964,
    .mul 3822 3822, .mul 3966 3824, .mul 3828 3828, .mul 3968 3830, .add 3967 3969, .mul 3834 3834, .mul 3971 3836,
    .mul 3840 3840, .mul 3973 3842, .add 3972 3974, .add 3970 3975, .add 3976 3969, .add 3977 3970, .mul 3846 3846,
    .mul 3979 3848, .mul 3852 3852, .mul 3981 3854, .add 3980 3982, .mul 3858 3858, .mul 3984 3860, .mul 3864 3864,
    .mul 3986 3866, .add 3985 3987, .add 3983 3988, .add 3989 3982, .add 3990 3983, .add 3978 3991, .mul 3870 3870,
    .mul 3993 3872, .mul 3876 3876, .mul 3995 3878, .add 3994 3996, .mul 3882 3882, .mul 3998 3884, .mul 3888 3888,
    .mul 4000 3890, .add 3999 4001, .add 3997 4002, .add 4003 3996, .add 4004 3997, .add 3992 4005, .mul 3894 3894,
    .mul 4007 3896, .mul 3900 3900, .mul 4009 3902, .add 4008 4010, .mul 3906 3906, .mul 4012 3908, .mul 3912 3912,
    .mul 4014 3914, .add 4013 4015, .add 4011 4016, .add 4017 4010, .add 4018 4011, .add 4006 4019, .mul 3918 3918,
    .mul 4021 3920, .mul 3924 3924, .mul 4023 3926, .add 4022 4024, .mul 3930 3930, .mul 4026 3932, .mul 3936 3936,
    .mul 4028 3938, .add 4027 4029, .add 4025 4030, .add 4031 4024, .add 4032 4025, .add 4020 4033, .mul 3942 3942,
    .mul 4035 3944, .mul 3948 3948, .mul 4037 3950, .add 4036 4038, .mul 3954 3954, .mul 4040 3956, .mul 3960 3960,
    .mul 4042 3962, .add 4041 4043, .add 4039 4044, .add 4045 4038, .add 4046 4039, .add 4034 4047, .add 3978 4048,
    .var 395, .sub 4049 4050, .add 3972 3972, .add 3977 4052, .add 3985 3985, .add 3990 4054, .add 4053 4055,
    .add 3999 3999, .add 4004 4057, .add 4056 4058, .add 4013 4013, .add 4018 4060, .add 4059 4061, .add 4027 4027,
    .add 4032 4063, .add 4062 4064, .add 4041 4041, .add 4046 4066, .add 4065 4067, .add 4053 4068, .var 396,
    .sub 4069 4070, .add 3976 3974, .add 4072 3975, .add 3989 3987, .add 4074 3988, .add 4073 4075, .add 4003 4001,
    .add 4077 4002, .add 4076 4078, .add 4017 4015, .add 4080 4016, .add 4079 4081, .add 4031 4029, .add 4083 4030,
    .add 4082 4084, .add 4045 4043, .add 4086 4044, .add 4085 4087, .add 4073 4088, .var 397, .sub 4089 4090,
    .add 3967 3967, .add 4072 4092, .add 3980 3980, .add 4074 4094]

def p2w24DagC8 : List Node :=
  [  .add 4093 4095, .add 3994 3994, .add 4077 4097, .add 4096 4098, .add 4008 4008, .add 4080 4100, .add 4099 4101,
    .add 4022 4022, .add 4083 4103, .add 4102 4104, .add 4036 4036, .add 4086 4106, .add 4105 4107, .add 4093 4108,
    .var 398, .sub 4109 4110, .add 3991 4048, .var 399, .sub 4112 4113, .add 4055 4068, .var 400, .sub 4115 4116,
    .add 4075 4088, .var 401, .sub 4118 4119, .add 4095 4108, .var 402, .sub 4121 4122, .add 4005 4048,
    .var 403, .sub 4124 4125, .add 4058 4068, .var 404, .sub 4127 4128, .add 4078 4088, .var 405, .sub 4130 4131,
    .add 4098 4108, .var 406, .sub 4133 4134, .add 4019 4048, .var 407, .sub 4136 4137, .add 4061 4068,
    .var 408, .sub 4139 4140, .add 4081 4088, .var 409, .sub 4142 4143, .add 4101 4108, .var 410, .sub 4145 4146,
    .add 4033 4048, .var 411, .sub 4148 4149, .add 4064 4068, .var 412, .sub 4151 4152, .add 4084 4088,
    .var 413, .sub 4154 4155, .add 4104 4108, .var 414, .sub 4157 4158, .add 4047 4048, .var 415, .sub 4160 4161,
    .add 4067 4068, .var 416, .sub 4163 4164, .add 4087 4088, .var 417, .sub 4166 4167, .add 4107 4108,
    .var 418, .sub 4169 4170, .var 419, .cst 1567618575, .add 4050 4173, .mul 4174 4174, .mul 4175 4174,
    .sub 4172 4176, .var 420, .cst 1663353317, .add 4070 4179, .mul 4180 4180, .mul 4181 4180, .sub 4178 4182,
    .var 421, .cst 1950429111, .add 4090 4185, .mul 4186 4186, .mul 4187 4186, .sub 4184 4188, .var 422,
    .cst 1891637550, .add 4110 4191, .mul 4192 4192, .mul 4193 4192, .sub 4190 4194, .var 423, .cst 192082241,
    .add 4113 4197, .mul 4198 4198, .mul 4199 4198, .sub 4196 4200, .var 424, .cst 1080533265, .add 4116 4203,
    .mul 4204 4204, .mul 4205 4204, .sub 4202 4206, .var 425, .cst 1463323727, .add 4119 4209, .mul 4210 4210,
    .mul 4211 4210, .sub 4208 4212, .var 426, .cst 890243564, .add 4122 4215, .mul 4216 4216, .mul 4217 4216,
    .sub 4214 4218, .var 427, .cst 158646617, .add 4125 4221, .mul 4222 4222, .mul 4223 4222, .sub 4220 4224,
    .var 428, .cst 1402624179, .add 4128 4227, .mul 4228 4228, .mul 4229 4228, .sub 4226 4230, .var 429,
    .cst 59510015, .add 4131 4233, .mul 4234 4234, .mul 4235 4234, .sub 4232 4236, .var 430, .cst 1198261138,
    .add 4134 4239, .mul 4240 4240, .mul 4241 4240, .sub 4238 4242, .var 431, .cst 1065075039, .add 4137 4245,
    .mul 4246 4246, .mul 4247 4246, .sub 4244 4248, .var 432, .cst 1150410028, .add 4140 4251, .mul 4252 4252,
    .mul 4253 4252, .sub 4250 4254, .var 433, .cst 1293938517, .add 4143 4257, .mul 4258 4258, .mul 4259 4258,
    .sub 4256 4260, .var 434, .cst 76770019, .add 4146 4263, .mul 4264 4264, .mul 4265 4264, .sub 4262 4266,
    .var 435, .cst 1478577620, .add 4149 4269, .mul 4270 4270, .mul 4271 4270, .sub 4268 4272, .var 436,
    .cst 1748789933, .add 4152 4275, .mul 4276 4276, .mul 4277 4276, .sub 4274 4278, .var 437, .cst 457372011,
    .add 4155 4281, .mul 4282 4282, .mul 4283 4282, .sub 4280 4284, .var 438, .cst 1841795381, .add 4158 4287,
    .mul 4288 4288, .mul 4289 4288, .sub 4286 4290, .var 439, .cst 760115692, .add 4161 4293, .mul 4294 4294,
    .mul 4295 4294, .sub 4292 4296, .var 440, .cst 1042892522, .add 4164 4299, .mul 4300 4300, .mul 4301 4300,
    .sub 4298 4302, .var 441, .cst 1507649755, .add 4167 4305, .mul 4306 4306, .mul 4307 4306, .sub 4304 4308,
    .var 442, .cst 1827572010, .add 4170 4311, .mul 4312 4312, .mul 4313 4312, .sub 4310 4314, .mul 4172 4172,
    .mul 4316 4174, .mul 4178 4178, .mul 4318 4180, .add 4317 4319, .mul 4184 4184, .mul 4321 4186, .mul 4190 4190,
    .mul 4323 4192, .add 4322 4324, .add 4320 4325, .add 4326 4319, .add 4327 4320, .mul 4196 4196, .mul 4329 4198,
    .mul 4202 4202, .mul 4331 4204, .add 4330 4332, .mul 4208 4208, .mul 4334 4210, .mul 4214 4214, .mul 4336 4216,
    .add 4335 4337, .add 4333 4338, .add 4339 4332, .add 4340 4333, .add 4328 4341, .mul 4220 4220, .mul 4343 4222,
    .mul 4226 4226, .mul 4345 4228, .add 4344 4346, .mul 4232 4232, .mul 4348 4234, .mul 4238 4238, .mul 4350 4240,
    .add 4349 4351, .add 4347 4352, .add 4353 4346, .add 4354 4347, .add 4342 4355, .mul 4244 4244, .mul 4357 4246,
    .mul 4250 4250, .mul 4359 4252, .add 4358 4360, .mul 4256 4256, .mul 4362 4258, .mul 4262 4262, .mul 4364 4264,
    .add 4363 4365, .add 4361 4366, .add 4367 4360, .add 4368 4361, .add 4356 4369, .mul 4268 4268, .mul 4371 4270,
    .mul 4274 4274, .mul 4373 4276, .add 4372 4374, .mul 4280 4280, .mul 4376 4282, .mul 4286 4286, .mul 4378 4288,
    .add 4377 4379, .add 4375 4380, .add 4381 4374, .add 4382 4375, .add 4370 4383, .mul 4292 4292, .mul 4385 4294,
    .mul 4298 4298, .mul 4387 4300, .add 4386 4388, .mul 4304 4304, .mul 4390 4306, .mul 4310 4310, .mul 4392 4312,
    .add 4391 4393, .add 4389 4394, .add 4395 4388, .add 4396 4389, .add 4384 4397, .add 4328 4398, .var 443,
    .sub 4399 4400, .add 4322 4322, .add 4327 4402, .add 4335 4335, .add 4340 4404, .add 4403 4405, .add 4349 4349,
    .add 4354 4407, .add 4406 4408, .add 4363 4363, .add 4368 4410, .add 4409 4411, .add 4377 4377, .add 4382 4413,
    .add 4412 4414, .add 4391 4391, .add 4396 4416, .add 4415 4417, .add 4403 4418, .var 444, .sub 4419 4420,
    .add 4326 4324, .add 4422 4325, .add 4339 4337, .add 4424 4338, .add 4423 4425, .add 4353 4351, .add 4427 4352,
    .add 4426 4428, .add 4367 4365, .add 4430 4366, .add 4429 4431, .add 4381 4379, .add 4433 4380, .add 4432 4434,
    .add 4395 4393, .add 4436 4394, .add 4435 4437, .add 4423 4438, .var 445, .sub 4439 4440, .add 4317 4317,
    .add 4422 4442, .add 4330 4330, .add 4424 4444, .add 4443 4445, .add 4344 4344, .add 4427 4447, .add 4446 4448,
    .add 4358 4358, .add 4430 4450, .add 4449 4451, .add 4372 4372, .add 4433 4453, .add 4452 4454, .add 4386 4386,
    .add 4436 4456, .add 4455 4457, .add 4443 4458, .var 446, .sub 4459 4460, .add 4341 4398, .var 447,
    .sub 4462 4463, .add 4405 4418, .var 448, .sub 4465 4466, .add 4425 4438, .var 449, .sub 4468 4469,
    .add 4445 4458, .var 450, .sub 4471 4472, .add 4355 4398, .var 451, .sub 4474 4475, .add 4408 4418,
    .var 452, .sub 4477 4478, .add 4428 4438, .var 453, .sub 4480 4481, .add 4448 4458, .var 454, .sub 4483 4484,
    .add 4369 4398, .var 455, .sub 4486 4487, .add 4411 4418, .var 456, .sub 4489 4490, .add 4431 4438,
    .var 457, .sub 4492 4493, .add 4451 4458, .var 458, .sub 4495 4496, .add 4383 4398, .var 459, .sub 4498 4499,
    .add 4414 4418, .var 460, .sub 4501 4502, .add 4434 4438, .var 461, .sub 4504 4505, .add 4454 4458,
    .var 462, .sub 4507 4508, .add 4397 4398, .var 463, .sub 4510 4511, .add 4417 4418, .var 464, .sub 4513 4514,
    .add 4437 4438, .var 465, .sub 4516 4517, .add 4457 4458, .var 466, .sub 4519 4520, .var 467, .cst 1206940496,
    .add 4400 4523, .mul 4524 4524, .mul 4525 4524, .sub 4522 4526, .var 468, .cst 1896271507, .add 4420 4529,
    .mul 4530 4530, .mul 4531 4530, .sub 4528 4532, .var 469, .cst 1003792297, .add 4440 4535, .mul 4536 4536,
    .mul 4537 4536, .sub 4534 4538, .var 470, .cst 738091882, .add 4460 4541, .mul 4542 4542, .mul 4543 4542,
    .sub 4540 4544, .var 471, .cst 1124078057, .add 4463 4547, .mul 4548 4548, .mul 4549 4548, .sub 4546 4550,
    .var 472, .cst 1889898, .add 4466 4553, .mul 4554 4554, .mul 4555 4554, .sub 4552 4556, .var 473, .cst 813674331,
    .add 4469 4559, .mul 4560 4560, .mul 4561 4560, .sub 4558 4562, .var 474, .cst 228520958, .add 4472 4565,
    .mul 4566 4566, .mul 4567 4566, .sub 4564 4568, .var 475, .cst 1832911930, .add 4475 4571, .mul 4572 4572,
    .mul 4573 4572, .sub 4570 4574, .var 476, .cst 781141772, .add 4478 4577, .mul 4578 4578, .mul 4579 4578,
    .sub 4576 4580, .var 477, .cst 459826664, .add 4481 4583, .mul 4584 4584, .mul 4585 4584, .sub 4582 4586,
    .var 478, .cst 202271745, .add 4484 4589, .mul 4590 4590, .mul 4591 4590, .sub 4588 4592, .var 479,
    .cst 1296144415, .add 4487 4595, .mul 4596 4596, .mul 4597 4596, .sub 4594 4598, .var 480, .cst 1111203133,
    .add 4490 4601, .mul 4602 4602, .mul 4603 4602, .sub 4600 4604, .var 481, .cst 1090783436]

def p2w24DagC9 : List Node :=
  [  .add 4493 4607, .mul 4608 4608, .mul 4609 4608, .sub 4606 4610, .var 482, .cst 641665156, .add 4496 4613,
    .mul 4614 4614, .mul 4615 4614, .sub 4612 4616, .var 483, .cst 1393671120, .add 4499 4619, .mul 4620 4620,
    .mul 4621 4620, .sub 4618 4622, .var 484, .cst 1303271640, .add 4502 4625, .mul 4626 4626, .mul 4627 4626,
    .sub 4624 4628, .var 485, .cst 809508074, .add 4505 4631, .mul 4632 4632, .mul 4633 4632, .sub 4630 4634,
    .var 486, .cst 162506101, .add 4508 4637, .mul 4638 4638, .mul 4639 4638, .sub 4636 4640, .var 487,
    .cst 1262312258, .add 4511 4643, .mul 4644 4644, .mul 4645 4644, .sub 4642 4646, .var 488, .cst 1672219447,
    .add 4514 4649, .mul 4650 4650, .mul 4651 4650, .sub 4648 4652, .var 489, .cst 1608891156, .add 4517 4655,
    .mul 4656 4656, .mul 4657 4656, .sub 4654 4658, .var 490, .cst 1380248020, .add 4520 4661, .mul 4662 4662,
    .mul 4663 4662, .sub 4660 4664, .mul 4522 4522, .mul 4666 4524, .mul 4528 4528, .mul 4668 4530, .add 4667 4669,
    .mul 4534 4534, .mul 4671 4536, .mul 4540 4540, .mul 4673 4542, .add 4672 4674, .add 4670 4675, .add 4676 4669,
    .add 4677 4670, .mul 4546 4546, .mul 4679 4548, .mul 4552 4552, .mul 4681 4554, .add 4680 4682, .mul 4558 4558,
    .mul 4684 4560, .mul 4564 4564, .mul 4686 4566, .add 4685 4687, .add 4683 4688, .add 4689 4682, .add 4690 4683,
    .add 4678 4691, .mul 4570 4570, .mul 4693 4572, .mul 4576 4576, .mul 4695 4578, .add 4694 4696, .mul 4582 4582,
    .mul 4698 4584, .mul 4588 4588, .mul 4700 4590, .add 4699 4701, .add 4697 4702, .add 4703 4696, .add 4704 4697,
    .add 4692 4705, .mul 4594 4594, .mul 4707 4596, .mul 4600 4600, .mul 4709 4602, .add 4708 4710, .mul 4606 4606,
    .mul 4712 4608, .mul 4612 4612, .mul 4714 4614, .add 4713 4715, .add 4711 4716, .add 4717 4710, .add 4718 4711,
    .add 4706 4719, .mul 4618 4618, .mul 4721 4620, .mul 4624 4624, .mul 4723 4626, .add 4722 4724, .mul 4630 4630,
    .mul 4726 4632, .mul 4636 4636, .mul 4728 4638, .add 4727 4729, .add 4725 4730, .add 4731 4724, .add 4732 4725,
    .add 4720 4733, .mul 4642 4642, .mul 4735 4644, .mul 4648 4648, .mul 4737 4650, .add 4736 4738, .mul 4654 4654,
    .mul 4740 4656, .mul 4660 4660, .mul 4742 4662, .add 4741 4743, .add 4739 4744, .add 4745 4738, .add 4746 4739,
    .add 4734 4747, .add 4678 4748, .sub 4749 7, .add 4672 4672, .add 4677 4751, .add 4685 4685, .add 4690 4753,
    .add 4752 4754, .add 4699 4699, .add 4704 4756, .add 4755 4757, .add 4713 4713, .add 4718 4759, .add 4758 4760,
    .add 4727 4727, .add 4732 4762, .add 4761 4763, .add 4741 4741, .add 4746 4765, .add 4764 4766, .add 4752 4767,
    .sub 4768 12, .add 4676 4674, .add 4770 4675, .add 4689 4687, .add 4772 4688, .add 4771 4773, .add 4703 4701,
    .add 4775 4702, .add 4774 4776, .add 4717 4715, .add 4778 4716, .add 4777 4779, .add 4731 4729, .add 4781 4730,
    .add 4780 4782, .add 4745 4743, .add 4784 4744, .add 4783 4785, .add 4771 4786, .sub 4787 17, .add 4667 4667,
    .add 4770 4789, .add 4680 4680, .add 4772 4791, .add 4790 4792, .add 4694 4694, .add 4775 4794, .add 4793 4795,
    .add 4708 4708, .add 4778 4797, .add 4796 4798, .add 4722 4722, .add 4781 4800, .add 4799 4801, .add 4736 4736,
    .add 4784 4803, .add 4802 4804, .add 4790 4805, .sub 4806 22, .add 4691 4748, .sub 4808 28, .add 4754 4767,
    .sub 4810 33, .add 4773 4786, .sub 4812 38, .add 4792 4805, .sub 4814 43, .add 4705 4748, .sub 4816 49,
    .add 4757 4767, .sub 4818 54, .add 4776 4786, .sub 4820 59, .add 4795 4805, .sub 4822 64, .add 4719 4748,
    .sub 4824 70, .add 4760 4767, .sub 4826 75, .add 4779 4786, .sub 4828 80, .add 4798 4805, .sub 4830 85,
    .add 4733 4748, .sub 4832 91, .add 4763 4767, .sub 4834 96, .add 4782 4786, .sub 4836 101, .add 4801 4805,
    .sub 4838 106, .add 4747 4748, .sub 4840 112, .add 4766 4767, .sub 4842 117, .add 4785 4786, .sub 4844 122,
    .add 4804 4805, .sub 4846 127]

def p2w24DagNodes : List Node :=
  p2w24DagC0 ++ p2w24DagC1 ++ p2w24DagC2 ++ p2w24DagC3 ++ p2w24DagC4 ++ p2w24DagC5 ++ p2w24DagC6 ++ p2w24DagC7 ++ p2w24DagC8 ++ p2w24DagC9

def p2w24DagRoots : List Nat :=
  [  3, 10, 15, 20, 25, 31, 36, 41, 46, 52, 57, 62, 67, 73, 78, 83, 88, 94, 99, 104, 109, 115, 120, 125,
    130, 136, 138, 140, 142, 146, 148, 150, 152, 156, 158, 160, 162, 166, 168, 170, 172, 184, 250, 274,
    298, 322, 329, 336, 343, 350, 357, 364, 371, 378, 385, 392, 399, 406, 413, 420, 427, 434, 441, 448,
    455, 462, 548, 568, 588, 608, 611, 614, 617, 620, 623, 626, 629, 632, 635, 638, 641, 644, 647, 650,
    653, 656, 659, 662, 665, 668, 674, 680, 686, 692, 698, 704, 710, 716, 722, 728, 734, 740, 746, 752,
    758, 764, 770, 776, 782, 788, 794, 800, 806, 812, 898, 918, 938, 958, 961, 964, 967, 970, 973, 976,
    979, 982, 985, 988, 991, 994, 997, 1000, 1003, 1006, 1009, 1012, 1015, 1018, 1024, 1030, 1036, 1042,
    1048, 1054, 1060, 1066, 1072, 1078, 1084, 1090, 1096, 1102, 1108, 1114, 1120, 1126, 1132, 1138, 1144,
    1150, 1156, 1162, 1248, 1268, 1288, 1308, 1311, 1314, 1317, 1320, 1323, 1326, 1329, 1332, 1335, 1338,
    1341, 1344, 1347, 1350, 1353, 1356, 1359, 1362, 1365, 1368, 1374, 1380, 1386, 1392, 1398, 1404, 1410,
    1416, 1422, 1428, 1434, 1440, 1446, 1452, 1458, 1464, 1470, 1476, 1482, 1488, 1494, 1500, 1506, 1512,
    1598, 1618, 1638, 1658, 1661, 1664, 1667, 1670, 1673, 1676, 1679, 1682, 1685, 1688, 1691, 1694, 1697,
    1700, 1703, 1706, 1709, 1712, 1715, 1718, 1724, 1728, 1757, 1761, 1850, 1854, 1933, 1937, 2016, 2020,
    2099, 2103, 2182, 2186, 2265, 2269, 2348, 2352, 2431, 2435, 2514, 2518, 2597, 2601, 2680, 2684, 2763,
    2767, 2846, 2850, 2929, 2933, 3012, 3016, 3095, 3099, 3178, 3182, 3261, 3265, 3344, 3348, 3427, 3435,
    3443, 3451, 3460, 3469, 3477, 3486, 3495, 3503, 3511, 3519, 3527, 3535, 3543, 3551, 3559, 3567, 3575,
    3583, 3591, 3599, 3607, 3615, 3701, 3721, 3741, 3761, 3764, 3767, 3770, 3773, 3776, 3779, 3782, 3785,
    3788, 3791, 3794, 3797, 3800, 3803, 3806, 3809, 3812, 3815, 3818, 3821, 3827, 3833, 3839, 3845, 3851,
    3857, 3863, 3869, 3875, 3881, 3887, 3893, 3899, 3905, 3911, 3917, 3923, 3929, 3935, 3941, 3947, 3953,
    3959, 3965, 4051, 4071, 4091, 4111, 4114, 4117, 4120, 4123, 4126, 4129, 4132, 4135, 4138, 4141, 4144,
    4147, 4150, 4153, 4156, 4159, 4162, 4165, 4168, 4171, 4177, 4183, 4189, 4195, 4201, 4207, 4213, 4219,
    4225, 4231, 4237, 4243, 4249, 4255, 4261, 4267, 4273, 4279, 4285, 4291, 4297, 4303, 4309, 4315, 4401,
    4421, 4441, 4461, 4464, 4467, 4470, 4473, 4476, 4479, 4482, 4485, 4488, 4491, 4494, 4497, 4500, 4503,
    4506, 4509, 4512, 4515, 4518, 4521, 4527, 4533, 4539, 4545, 4551, 4557, 4563, 4569, 4575, 4581, 4587,
    4593, 4599, 4605, 4611, 4617, 4623, 4629, 4635, 4641, 4647, 4653, 4659, 4665, 4750, 4769, 4788, 4807,
    4809, 4811, 4813, 4815, 4817, 4819, 4821, 4823, 4825, 4827, 4829, 4831, 4833, 4835, 4837, 4839, 4841,
    4843, 4845, 4847]

def p2w24Dag : Dag := ⟨p2w24DagNodes, p2w24DagRoots⟩

def p2w24DagCols : Nat := 491

/-! ## §10 — THE MEASUREMENTS, on the actual emitted objects.

`dagFoldRows_length` is a theorem, so the row `#guard`s are its instances rather than independent
readings — but they are the numbers that go into the price, and a `#guard` is what stops the price
and the compiler from drifting apart. -/

/-! ### §10.1 — the topological invariant, which every soundness theorem below takes as a
hypothesis. Without these four lines `dagFold_forces` would be a true statement about a
hypothesis nothing discharges. -/

#guard dagWf aluDagNodes
#guard dagWf exposeClaimDagNodes
#guard dagWf p2w16DagNodes
#guard dagWf p2w24DagNodes

/-! The roots are in range — the other hypothesis of `dagFold_forces`. -/

#guard aluDagRoots.all (· < aluDagNodes.length)
#guard exposeClaimDagRoots.all (· < exposeClaimDagNodes.length)
#guard p2w16DagRoots.all (· < p2w16DagNodes.length)
#guard p2w24DagRoots.all (· < p2w24DagNodes.length)

/-! ### §10.2 — the shape and the price.

`Alu`: 92 constraints ⇒ 850 nodes, of which **356 are multiplies** — p3's own count for this table
(`dag_sharing_versus_flat_monomials`). 1,035 sub-gates ⇒ 518 packed rows, 448 extension multiplies
(356 nodes + 92 α-folds). The FLAT path pays 1,396.
-/

#guard aluDagRoots.length = 92
#guard aluDagNodes.length = 850
#guard dagMulCount aluDagNodes = 356
#guard dagFoldGenCount aluDag = 1035
#guard (dagFoldRows aluDag aluDagCols (aluDagCols + 1)).length = 518
#guard dagFoldMulCount aluDag = 448

/-! `expose_claim`: 25 constraints ⇒ 150 nodes, 25 multiplies, 201 sub-gates, 101 packed rows, 50
extension multiplies. ⚑ The FLAT path pays 88 rows here against 101 — **the DAG language is not
uniformly cheaper in ROWS**, because it materialises a copy node per column read. It is uniformly
cheaper in MULTIPLIES (50 against 75), which is what prices the emission, and §11.2 names the
elision that would remove the row regression too. -/

#guard exposeClaimDagRoots.length = 25
#guard exposeClaimDagNodes.length = 150
#guard dagMulCount exposeClaimDagNodes = 25
#guard dagFoldGenCount exposeClaimDag = 201
#guard (dagFoldRows exposeClaimDag exposeClaimDagCols (exposeClaimDagCols + 1)).length = 101
#guard dagFoldMulCount exposeClaimDag = 50

/-! `poseidon2-w16`: 316 constraints ⇒ 2,850 nodes, **754 multiplies against the flat form's
243,849 — 323×**. 3,483 sub-gates ⇒ 1,742 packed rows, 1,070 extension multiplies. This is a table
the flat compiler could express and could not afford. -/

#guard p2w16DagRoots.length = 316
#guard p2w16DagNodes.length = 2850
#guard dagMulCount p2w16DagNodes = 754
#guard dagFoldGenCount p2w16Dag = 3483
#guard (dagFoldRows p2w16Dag p2w16DagCols (p2w16DagCols + 1)).length = 1742
#guard dagFoldMulCount p2w16Dag = 1070

/-! `poseidon2-w24`: 468 constraints ⇒ 4,848 nodes, **1,298 multiplies against the flat form's
1,284,686 — 990×**. 5,785 sub-gates ⇒ 2,893 packed rows, 1,766 extension multiplies. -/

#guard p2w24DagRoots.length = 468
#guard p2w24DagNodes.length = 4848
#guard dagMulCount p2w24DagNodes = 1298
#guard dagFoldGenCount p2w24Dag = 5785
#guard (dagFoldRows p2w24Dag p2w24DagCols (p2w24DagCols + 1)).length = 2893
#guard dagFoldMulCount p2w24Dag = 1766

/-! **THE WHOLE ROOT'S BASE CONSTRAINT SYSTEM.** 901 roots, 8,698 nodes, **2,433 multiplies** —
against the flat form's 1,529,889, a factor of **629**. (p3's own pointer-keyed cache reaches 2,937;
the structural cache here merges what separately-allocated identical subtrees leave separate, and
that is where the extra 504 go.) With one α-multiply per constraint the emission costs **3,334
extension multiplies** for the root's entire AIR evaluation. -/

#guard aluDagRoots.length + exposeClaimDagRoots.length + p2w16DagRoots.length
    + p2w24DagRoots.length = 901
#guard aluDagNodes.length + exposeClaimDagNodes.length + p2w16DagNodes.length
    + p2w24DagNodes.length = 8698
#guard dagMulCount aluDagNodes + dagMulCount exposeClaimDagNodes + dagMulCount p2w16DagNodes
    + dagMulCount p2w24DagNodes = 2433
#guard dagFoldMulCount aluDag + dagFoldMulCount exposeClaimDag + dagFoldMulCount p2w16Dag
    + dagFoldMulCount p2w24Dag = 3334
#guard dagFoldGenCount aluDag + dagFoldGenCount exposeClaimDag + dagFoldGenCount p2w16Dag
    + dagFoldGenCount p2w24Dag = 10504

/-! ### §10.3 — the anti-vacuity run, and THE REGRESSION.

`runDag` executes the emitted straight-line program under the discipline the generator claims to
obey — **every sub-gate defines the NEXT fresh variable** — so a `none` would be an ALIASING report
on the generator rather than a failed check, and the evaluator is a freshness audit as well as a
satisfiability certificate. The inputs are seeded with distinct non-zero values
(`KimchiRootAirEval.seedInputs`): running at all-zero would certify satisfiability at a degenerate
point where every product vanishes and an aliased variable is indistinguishable from a fresh one.

⚑ These are `#guard`s — evaluation at elaboration time, not proof terms — and the arithmetic is in
`ZMod 2013265921` rather than ℤ, because a DAG's bit-length DOUBLES with depth and a 60-deep
Poseidon2 program over ℤ carries `2^60`-bit integers. `dagFold_forces` holds at an arbitrary
`CommRing`, so the field is on-statement.
-/

/-! The emitted program is a genuine straight-line program on fresh variables. -/
#guard (runDag aluDag aluDagCols).isSome
#guard (runDag exposeClaimDag exposeClaimDagCols).isSome
#guard (runDag p2w16Dag p2w16DagCols).isSome
#guard (runDag p2w24Dag p2w24DagCols).isSome

/-! **A SATISFYING ASSIGNMENT EXISTS** for each emitted circuit, at a non-degenerate seeding.
Without this, `dagFold_forces` would be a true statement about the empty set. -/

#guard match runDag aluDag aluDagCols with
  | none => false
  | some v => gensAcceptP v (dagFoldGens aluDag aluDagCols (aluDagCols + 1))

#guard match runDag exposeClaimDag exposeClaimDagCols with
  | none => false
  | some v => gensAcceptP v (dagFoldGens exposeClaimDag exposeClaimDagCols (exposeClaimDagCols + 1))

#guard match runDag p2w16Dag p2w16DagCols with
  | none => false
  | some v => gensAcceptP v (dagFoldGens p2w16Dag p2w16DagCols (p2w16DagCols + 1))

#guard match runDag p2w24Dag p2w24DagCols with
  | none => false
  | some v => gensAcceptP v (dagFoldGens p2w24Dag p2w24DagCols (p2w24DagCols + 1))

/-! **AND THE OUTPUT IS p3's ACCUMULATOR**, checked against `dagHornerZ` — an evaluation of the same
DAG that never touches the circuit. This is `dagFold_forces` instantiated at a concrete witness: the
theorem's conclusion observed, not merely implied, and spanning the whole 5,785-gate fold rather
than one gate of it. -/

#guard match runDag aluDag aluDagCols with
  | none => false
  | some v => v.getD (dagFoldOut aluDag aluDagCols (aluDagCols + 1)) 0
      = dagHornerZ (seedInputs (aluDagCols + 1)) aluDagCols aluDag

#guard match runDag exposeClaimDag exposeClaimDagCols with
  | none => false
  | some v => v.getD (dagFoldOut exposeClaimDag exposeClaimDagCols (exposeClaimDagCols + 1)) 0
      = dagHornerZ (seedInputs (exposeClaimDagCols + 1)) exposeClaimDagCols exposeClaimDag

#guard match runDag p2w16Dag p2w16DagCols with
  | none => false
  | some v => v.getD (dagFoldOut p2w16Dag p2w16DagCols (p2w16DagCols + 1)) 0
      = dagHornerZ (seedInputs (p2w16DagCols + 1)) p2w16DagCols p2w16Dag

#guard match runDag p2w24Dag p2w24DagCols with
  | none => false
  | some v => v.getD (dagFoldOut p2w24Dag p2w24DagCols (p2w24DagCols + 1)) 0
      = dagHornerZ (seedInputs (p2w24DagCols + 1)) p2w24DagCols p2w24Dag

/-! ⚑⚑ **THE REGRESSION — the two paths must DENOTE THE SAME THING.**

A compiler change that silently alters emitted semantics is the worst possible outcome, so the
existing differential IS the regression test. For the two tables `KimchiRootAirEval` already
generated, the SHARED DAG and the FLAT `Head` list are evaluated independently — `dagHornerZ` walks
nodes, `hornerZ` walks monomials — at the SAME `seedInputs` over the SAME column numbering, and the
accumulators must agree in the field.

This is the check that would have caught a CSE merging two subtrees that are not equal. On the Rust
side the same comparison runs at 8 pseudorandom assignments over every constraint of both tables
(`dag_and_head_denote_the_same_constraints`, 936 agreements) and against p3's own evaluation over
all 901 constraints of all seven tables (`dag_extractor_agrees_with_p3_evaluation`, 7,208
agreements). Both are differentials, and a differential is a confession, not a mitigation.
-/

#guard dagHornerP aluDag aluDagCols = flatHornerP aluDagCols aluHeads
#guard dagHornerP exposeClaimDag exposeClaimDagCols = flatHornerP exposeClaimDagCols exposeClaimHeads

/-! ### §10.4 — what the compiler now covers, stated as a count.

901 of the root's 901 BASE constraints are compiler output: `Alu` 92, `poseidon2-w16` 316,
`poseidon2-w24` 468, `expose_claim` 25, and `Const`/`Public`/`recompose` 0-of-0. That is
**901 of 1,093 total `N`**; the remaining 192 are the LogUp permutation constraints (§11.3).
-/

/-! ## §11 — THE RESIDUALS, at the resolution they are actually at.

**§11.1 — the extraction is still a SEAM, but a NARROWER one.** Nothing here proves §9's nodes are
p3's constraints. They are `to_dag` output, checked by `dag_extractor_agrees_with_p3_evaluation` — a
DIFFERENTIAL at pseudorandom assignments over all 901 base constraints of all seven tables. What
changed is what the extractor DOES: `to_head` flattened an expression tree into monomials, an
algebraic rewrite with its own arithmetic; `to_dag` renumbers, and its node kinds are 1:1 with
`SymbolicExpr`'s constructors. The seam is narrower and it is not closed. Closing it needs a Lean
model of `SymbolicExpr` and a refinement of the numbering — which, unlike a refinement of the
flattening, is now a structural statement rather than a polynomial identity.

**§11.2 — ⚑ THE COPY-NODE ELISION, named and NOT done.** 1,063 of the 8,698 nodes are `.var` — a
sub-gate whose whole content is `o = 1·c`, copying a column the verifier already holds into a fresh
variable. A lowering that mapped a `.var c` node to column `c` itself, rather than to `nv + k`,
would delete all 1,063 (≈2.0 × 10⁴ rows at the measured 19 rows/extension-scale) and is why
`expose_claim` costs 101 rows here against the flat path's 88. It is NOT landed: it makes
`nodeVar` depend on the node list, so `dagGens_forces` no longer reads `a (nv + k)` uniformly, and
an optimisation whose forcing lemma is not re-proved is exactly the thing this file exists to not
do. The same applies to the 377 `.cst` pins, which `Gen1.lin2c`'s constant slot could absorb.

**§11.3 — the LOOKUP constraints are still outside this vocabulary, and the extension it needs has
a name.** 192 of the root's 1,093 are LogUp permutation constraints, and they are
`SymbolicExpressionExt`, not `SymbolicExpression`: their leaves include `ExtLeaf::Challenge` (the
LogUp challenges β, γ) and `ExtLeaf::Base` (a lifted base expression), and their values live in the
challenge extension rather than the base field. `Node` has no constructor for either. The extension
is precisely: a second leaf kind `chal (i : Nat)` for a permutation challenge, a `perm (o i : Nat)`
leaf for a permutation-trace column at a row offset, and a `lift` node embedding a base-DAG index —
which is exactly `SymbolicCompiler::compile_ext`'s shape, taking BOTH caches and delegating
`ExtLeaf::Base` back into `compile_base` with the shared `base_cache`. The lowering is unchanged
(`Gen1` is already at arbitrary `CommRing`); what is missing is the leaf vocabulary and a second
extractor. Three of the seven tables — `Const`, `Public`, `recompose` — have ZERO base constraints,
so for them this rung still covers nothing at all.

**§11.4 — the closing equality is not this file's.** `dagFold_forces` produces the accumulator;
multiplying by `inv_vanishing(ζ)` and comparing against the recomposed quotient is `AirEval.ts`'s
`assertQuotientConsistency`. The two halves are NOT welded: one is a Lean theorem, the other a
TypeScript circuit, and nothing states they compose.

**§11.5 — the lane currency.** Everything above rides `packGen`, whose `packGen_holds_iff` is
proved, and is stated at an arbitrary `CommRing` — i.e. in EXTENSION-element operations. The
lowering of one extension element to Pasta lanes is `KimchiPoseidon2`'s `BB` layer, which
interleaves `RangeCheck0` rows, and for THAT backend the needed lemma is `KimchiLower`'s
named-and-unproved `renderOps_gens_sound`. So this rung is proved in the extension currency and NOT
in the lane currency.

**§11.6 — this does not make the verifier sound.** P10 stands. So do the real preamble, the
mixed-height MMCS openings, 19-queries-not-1, and the undischarged FRI/STARK floor.
-/

#assert_axioms nodeGen_forces
#assert_axioms dagGensGo_forces
#assert_axioms dagGens_forces
#assert_axioms dagDenote_unfold
#assert_axioms dagDenote_prefix
#assert_axioms cseGo_denote
#assert_axioms intern_spec
#assert_axioms foldRootsGo_forces
#assert_axioms dagFold_forces
#assert_axioms dagFoldRows_length
#assert_axioms dagFoldGens_length
#assert_axioms dagFoldRows_all_modelled

end Dregg2.Circuit.Emit.KimchiDag
