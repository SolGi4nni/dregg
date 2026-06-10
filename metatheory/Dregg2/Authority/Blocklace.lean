/-
# Dregg2.Authority.Blocklace — the concrete byzantine-repelling DAG.

`Authority.CDT` gives the abstract capability-derivation order (CDT ≡ strand-log ≡ biscuit-graph):
the same append-only partial order seen three ways. The blocklace is the concrete strand-log face —
mirroring dregg1's `blocklace/` crate (`finality.rs`, `ordering.rs`, `dissemination.rs`) — and is the
face that carries the byzantine-repelling guarantee: a Byzantine author who forks (equivocates) is caught.

Literature anchor: Almog–Lewis–Naor–Shapiro, *"The Blocklace: A Byzantine-repelling and Universal CRDT"*
(arXiv 2402.08068, `pdfs/blocklace-byzantine-repelling-universal-2402.08068.pdf`). We formalize:

* **Def 2.x (observation / `≺`).** `≺` is the transitive closure of the direct predecessor/ack relation `←`.
  `a ≺ b` reads "`b` observes `a`" — `a` is in `b`'s causal past. (`finality.rs::causal_past` / `is_predecessor`.)
* **Def 4.2 (Equivocation).** An equivocation by node `p` is a pair of different `p`-blocks `a, b ∈ B`
  incomparable under `≺` (`a ∥ b ≡ a ⊀ b ∧ b ⊀ a`). The pair's presence is the `EquivocationProof` (`finality.rs:181`).
* **§5 (Byzantine-repelling).** The incomparable pair is witnessed: any observer who has gossiped both
  branches holds the proof (`finality.rs::detect_equivocation`, `ordering.rs::has_equivocation_in_past`).

§8 boundary (crypto seam — NOT proved here): hash-injectivity and signature-unforgeability are §8
obligations discharged by the circuit + Rust cascade, never Lean theorems (same status as `CDT.CapHash`).
Every theorem below is a semantic DAG/order fact that does not depend on any property of hashing or signing.

Pure, computable, `#eval`-able.
-/
import Dregg2.Authority.CDT
import Dregg2.Finality
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.Finset.Basic

namespace Dregg2.Authority.Blocklace

open Dregg2.Authority

/-! ## 1. Blocks and the append-only DAG (`finality.rs::Block` / `Blocklace`). -/

/-- **`BlockId`** — the opaque content-address of a block (`finality.rs::BlockId([u8;32])`).
Modelled as a `Nat` for concreteness and `#eval`-ability, but treated abstractly: no theorem
here depends on any property of the id (hash-injectivity is a §8 obligation, same as `CDT.CapHash`). -/
abbrev BlockId := Nat

/-- **`AuthorId`** — the public key of a block's creator (`finality.rs::Block.creator`,
`[u8;32]`). Modelled as a `Nat`. -/
abbrev AuthorId := Nat

/-- **A `Block`** — one node of the blocklace (`finality.rs:130`). It is `signed` by its
`creator` over `(creator, seq, payload, predecessors)`; `seq` is the position in the
creator's *virtual chain*; `preds` are the content-address pointers (acks) to the blocks this
block **observes directly**.

* `id` — the opaque content-address (a §8 seam; here a field so blocks are concrete).
* `creator` — the signing author (`node(b)` in the paper).
* `seq` — the creator's virtual-chain index.
* `preds` — the direct predecessor / ack set (the paper's `←`).
* `signed` — a **`Bool`-carrier** for the (uninterpreted) signature check (`§8`); the actual
  Ed25519 verification is a Rust/circuit obligation, never Lean-proved crypto. -/
structure Block where
  id      : BlockId
  creator : AuthorId
  seq     : Nat
  preds   : List BlockId
  signed  : Bool := true
  deriving DecidableEq, Inhabited

/-- **The blocklace** — an append-only collection of blocks (`finality.rs::Blocklace.blocks`,
a `HashMap<BlockId, Block>`). Modelled as a `List Block`; `lookup` resolves a content-address.
The set grows monotonically (CRDT join), mirroring `World.recv_mono`. -/
abbrev Lace := List Block

/-- Resolve a `BlockId` to its block (the content-address dereference,
`finality.rs::Blocklace.get`). -/
def Lace.lookup (B : Lace) (h : BlockId) : Option Block :=
  B.find? (fun b => b.id = h)

/-- A block is **in** the lace (membership by content-address). -/
def Lace.has (B : Lace) (h : BlockId) : Bool := (B.lookup h).isSome

/-- **`Canonical B`** — the content-addressing invariant: the `id` *determines* the block, so
no two distinct blocks in `B` share an `id`. This is what "content-address" *means*
(`finality.rs` keys its `HashMap` by `BlockId`); the §8 collision-resistance obligation is
precisely what makes this hold in the wire format, but here it is an explicit structural
hypothesis (NOT a crypto axiom): the keyed map cannot hold two values at one key. -/
def Lace.Canonical (B : Lace) : Prop :=
  ∀ a ∈ B, ∀ b ∈ B, a.id = b.id → a = b

/-- **`lookup_of_mem`** — in a canonical lace, a present block resolves to itself:
`lookup` of `n.id` returns `n`. Proved by induction on `B`; the distinctness invariant forces
the first `id`-match to be `n` itself. -/
theorem lookup_of_mem {B : Lace} (hcanon : B.Canonical) {n : Block} (hmem : n ∈ B) :
    B.lookup n.id = some n := by
  induction B with
  | nil => simp at hmem
  | cons h t ih =>
    simp only [Lace.lookup, List.find?_cons]
    by_cases hh : h.id = n.id
    · have hhn : h = n := hcanon h (by simp) n (by simp [hmem]) hh
      simp [hhn]
    · simp only [hh, decide_false, if_false]
      rcases List.mem_cons.mp hmem with rfl | htl
      · exact absurd rfl hh
      · exact ih (fun a ha b hb => hcanon a (by simp [ha]) b (by simp [hb])) htl

/-! ## 2. The pointed (`←`) and observe (`≺`) relations (paper §2; `causal_past`). -/

/-- **`pointed B a b`** — `a ← b`: block `b` *directly* points to (acks) `a`; `a` is one of
`b`'s predecessors and both resolve in `B`. The paper's `←`; the edge of `causal_past`'s BFS
(`finality.rs:830`). -/
def pointed (B : Lace) (a b : Block) : Prop :=
  a.id ∈ b.preds ∧ B.lookup a.id = some a ∧ B.lookup b.id = some b

/-- **`precedes B a b`** — `a ≺ b`: the transitive closure of `pointed` (paper: `≺ = ←⁺`).
`a ≺ b` reads "`b` **observes** `a`" — `a` is in `b`'s **causal past**
(`finality.rs::is_predecessor`). Defined inductively as the transitive closure so it is a
genuine `Prop` order (no fuel bound). -/
inductive precedes (B : Lace) : Block → Block → Prop where
  /-- A direct ack edge `a ← b` gives `a ≺ b`. -/
  | base {a b : Block} (h : pointed B a b) : precedes B a b
  /-- Transitivity: `a ≺ m` and `m ≺ b` give `a ≺ b`. -/
  | trans {a m b : Block} (hab : precedes B a m) (hbc : precedes B m b) : precedes B a b

/-- **`observes B b a`** — `b` observes `a` (`a ≺ b`), the reader-friendly direction. -/
def observes (B : Lace) (b a : Block) : Prop := precedes B a b

/-- **`comparable`** — `a  b ∨ b  a` in the paper's `` (`≺ or =`). The negation is the
paper's `∥` (incomparable). -/
def comparable (B : Lace) (a b : Block) : Prop :=
  a = b ∨ precedes B a b ∨ precedes B b a

/-- **`incomparable B a b`** — the paper's `a ∥ b ≡ a ⊀ b ∧ b ⊀ a` (and `a ≠ b`). Neither
block observes the other: they are *concurrent*. This is the heart of equivocation. -/
def incomparable (B : Lace) (a b : Block) : Prop :=
  a ≠ b ∧ ¬ precedes B a b ∧ ¬ precedes B b a

/-! ## 3. Equivocation (paper Def 4.2; `finality.rs::EquivocationProof`). -/

/-- **`Equivocation B p a b` (paper Def 4.2 — EQUIV).** An equivocation by author `p` in
lace `B`: a pair of *different* `p`-blocks `a, b ∈ B` that are **incomparable** under `≺`:
`node(a) = node(b) = p ∧ a ∥ b`. The two blocks are a **fork** in `p`'s virtual chain — `p`
told different stories to different peers. The pair *is* the `EquivocationProof`
(`finality.rs:181`). -/
structure Equivocation (B : Lace) (p : AuthorId) (a b : Block) : Prop where
  a_mem      : B.lookup a.id = some a
  b_mem      : B.lookup b.id = some b
  a_author   : a.creator = p
  b_author   : b.creator = p
  incomp     : incomparable B a b

/-- **`Equivocator B p`** — `p ∈ eqvc(B)`: there *exists* an incomparable `p`-pair in `B`
(paper: "the existence of a pair of incomparable `p`-blocks in `B` is enough", even if no
block observes it). The set `eqvc(B)` (`finality.rs::Blocklace.equivocators`). -/
def Equivocator (B : Lace) (p : AuthorId) : Prop :=
  ∃ a b, Equivocation B p a b

/-! ## 4. THE DEFINING THEOREM — equivocation is detectable (byzantine-repelling).

The §5 byzantine-repelling guarantee in its *witnessed* form: the fork is not a hidden state
of the network — it is **present in `B` as a checkable pair**. `finality.rs::detect_equivocation`
scans for two same-creator/same-seq blocks of different content; the paper's stronger,
content-independent witness is the **incomparable pair** itself. We give the observer's-eye
form (`approved_by` / `has_equivocation_in_past`): if an observer's causal past contains both
forked blocks, the observer holds the proof. -/

/-- The observer-side detector: `seesBoth B o a b` — observer block `o` **observes** both `a`
and `b` (`a ≺ o ∧ b ≺ o`), i.e. both forked blocks are in `o`'s causal past. This is exactly
the condition `finality.rs::approved_by` / `ordering.rs::has_equivocation_in_past` test, made
into a `Prop`. -/
def seesBoth (B : Lace) (o a b : Block) : Prop :=
  precedes B a o ∧ precedes B b o

/-- **`equivocation_detectable`** — the byzantine-repelling theorem (paper §5, Def 4.2).
If author `p` equivocates in `B` with forked pair `a, b`, the equivocation is witnessed
constructively by the pair itself: `Equivocator B p` holds with witness `(a, b)`. The fork
cannot be hidden — its evidence is two concrete in-lace blocks. No quorum, no synchrony,
no signature-forgery assumption: purely a semantic order fact (the §8 seam is untouched). -/
theorem equivocation_detectable {B : Lace} {p : AuthorId} {a b : Block}
    (e : Equivocation B p a b) :
    Equivocator B p ∧ a ≠ b ∧ ¬ precedes B a b ∧ ¬ precedes B b a :=
  ⟨⟨a, b, e⟩, e.incomp⟩

/-- **`observer_detects`** — the observer's-eye form (`approved_by`). An observer block `o`
whose causal past contains both forked blocks holds the proof: any honest node that has
gossiped both branches detects the equivocator. The witness pair `(a, b)` is the payload
`finality.rs` inserts into `EquivocationProof` and what `ordering.rs::has_equivocation_in_past`
returns `true` on, repelling leader ratification. -/
theorem observer_detects {B : Lace} {p : AuthorId} {a b o : Block}
    (e : Equivocation B p a b) (hsee : seesBoth B o a b) :
    Equivocation B p a b ∧ precedes B a o ∧ precedes B b o :=
  ⟨e, hsee.1, hsee.2⟩

/-! ## 5. Honest authors never equivocate (paper §5.1; `add_block` virtual chain).

`finality.rs::add_block` makes each new block point at the creator's current `tip`, so an
honest author's blocks form a single ack-chain — each block observes its predecessor. We model
"honest" as this total-order discipline and prove honest `p`-blocks are `≺`-totally-ordered,
hence never incomparable, hence `p ∉ eqvc(B)`. -/

/-- **`HonestChain B p`** — author `p` follows the honest virtual-chain discipline
(`add_block`): `p`'s blocks are *totally ordered* by `≺`. Any two distinct `p`-blocks in `B`
are comparable — one observes the other (because each new `p`-block acks `p`'s previous tip,
so later blocks transitively observe all earlier ones). This is the §8-free semantic content
of "always ack your own latest block". -/
def HonestChain (B : Lace) (p : AuthorId) : Prop :=
  ∀ a b, B.lookup a.id = some a → B.lookup b.id = some b →
    a.creator = p → b.creator = p → a ≠ b →
    precedes B a b ∨ precedes B b a

/-- **`honest_no_equivocation`** — paper §5.1. An author following the honest virtual-chain
discipline (`HonestChain`) is never an equivocator: `¬ Equivocator B p`. An equivocation
requires an incomparable `p`-pair, but under `HonestChain` every `p`-pair is comparable.
The fork is structurally impossible for an author that always extends its own latest block. -/
theorem honest_no_equivocation {B : Lace} {p : AuthorId}
    (hon : HonestChain B p) :
    ¬ Equivocator B p := by
  rintro ⟨a, b, e⟩
  obtain ⟨hne, hnab, hnba⟩ := e.incomp
  rcases hon a b e.a_mem e.b_mem e.a_author e.b_author hne with hab | hba
  · exact hnab hab
  · exact hnba hba

/-- **`honest_chain_implies_comparable`** — under the honest discipline, any two distinct
`p`-blocks are comparable (one observes the other). The ack-chain is a total order —
the positive dual of `honest_no_equivocation`. -/
theorem honest_chain_implies_comparable {B : Lace} {p : AuthorId}
    (hon : HonestChain B p) {a b : Block}
    (ha : B.lookup a.id = some a) (hb : B.lookup b.id = some b)
    (hpa : a.creator = p) (hpb : b.creator = p) :
    comparable B a b := by
  by_cases h : a = b
  · exact Or.inl h
  · exact Or.inr (hon a b ha hb hpa hpb h)

/-! ## 6. The bridge: the CDT derivation order IS the blocklace causal order.

`Authority.CDT` carries the attenuation order; the blocklace carries the causal (ack) order.
`cdt_is_blocklace` exhibits the structural correspondence: a CDT `(child → parent)` edge IS
a blocklace pointed/ack edge, and a `DerivationPath` IS a `≺`-chain. So `CDT.path_attenuates`
(authority shrinks down a derivation chain) transports to the concrete log: authority shrinks
down the causal/ack order. -/

/-- **The faithful translation `cdtNodeToBlock`.** A CDT `CapNode` becomes a `Block` whose
ack set is exactly its (singleton or empty) parent pointer: `self ↦ id`, `parent ↦ preds`,
`authority` dropped (the causal face forgets rights — the two faces of the same order
disagree only on the *label*, never the *shape*). The `creator` is carried as the node's own
`self` (one strand per derivation node in the content-addressed CDT). -/
def cdtNodeToBlock (n : CDT.CapNode) : Block where
  id      := n.self
  creator := n.self
  seq     := 0
  preds   := match n.parent with | none => [] | some p => [p]
  signed  := true

@[simp] theorem cdtNodeToBlock_id (n : CDT.CapNode) : (cdtNodeToBlock n).id = n.self := rfl

/-- The translated lace of a CDT tree (the blocklace face of the derivation DAG). -/
def cdtToLace (g : CDT.Tree) : Lace := g.map cdtNodeToBlock

/-- Membership transports across the translation: a CDT node `n ∈ g` gives its block
`cdtNodeToBlock n ∈ cdtToLace g`. -/
theorem cdtNodeToBlock_mem {g : CDT.Tree} {n : CDT.CapNode} (h : n ∈ g) :
    cdtNodeToBlock n ∈ cdtToLace g :=
  List.mem_map_of_mem h

/-- **The translated lace is canonical** — given the CDT's `self`-injectivity (which the
content-addressing of the CDT supplies, exactly as `CDT.CapHash` is an opaque content id).
Two translated blocks share an `id` only if their source nodes share a `self`, which
injectivity collapses to equality. -/
theorem cdtToLace_canonical {g : CDT.Tree}
    (hinj : ∀ m ∈ g, ∀ m' ∈ g, m.self = m'.self → m = m') :
    (cdtToLace g).Canonical := by
  intro a ha b hb hid
  simp only [cdtToLace, List.mem_map] at ha hb
  obtain ⟨na, hna, rfl⟩ := ha
  obtain ⟨nb, hnb, rfl⟩ := hb
  -- ids equal ⇒ selfs equal ⇒ (by injectivity) nodes equal ⇒ blocks equal.
  have : na.self = nb.self := by simpa [cdtNodeToBlock] using hid
  rw [hinj na hna nb hnb this]

/-- **`cdt_edge_is_pointed`** — the structural heart of the bridge: a CDT
`(child → parent)` present edge IS a blocklace `pointed` (ack) edge `parent ← child`. The
derivation edge and the causal-ack edge are the same edge, on the translated lace. -/
theorem cdt_edge_is_pointed {g : CDT.Tree} {child parent : CDT.CapNode}
    (hedge : child.parent = some parent.self)
    (hchild : child ∈ g) (hparent : parent ∈ g)
    (hinj : ∀ m ∈ g, ∀ m' ∈ g, m.self = m'.self → m = m') :
    pointed (cdtToLace g) (cdtNodeToBlock parent) (cdtNodeToBlock child) := by
  have hcanon := cdtToLace_canonical hinj
  refine ⟨?_, ?_, ?_⟩
  · -- parent.self ∈ child's preds: the translation makes child's preds = [parent.self].
    simp only [cdtNodeToBlock, hedge, List.mem_cons, List.not_mem_nil, or_false]
  · exact lookup_of_mem hcanon (cdtNodeToBlock_mem hparent)
  · exact lookup_of_mem hcanon (cdtNodeToBlock_mem hchild)

/-- **`cdt_is_blocklace`** — a CDT `DerivationPath g leaf root` IS a blocklace `≺`-chain: `leaf`
causally observes `root` in the translated lace. The abstract derivation order and the concrete
causal order coincide; the strand-log face of the CDT is the blocklace.

Proved by induction on the path: each `child → mid` edge becomes a `precedes.base` step,
chained by `precedes.trans`. The `refl` case is vacuous for non-trivial paths. Consequence:
`CDT.path_attenuates` ("authority only shrinks down a derivation chain") reads on the concrete
log as "authority only shrinks down the causal/ack order." -/
theorem cdt_is_blocklace {g : CDT.Tree} {leaf root : CDT.CapNode}
    (hinj : ∀ m ∈ g, ∀ m' ∈ g, m.self = m'.self → m = m')
    (path : CDT.DerivationPath g leaf root) (hleaf : leaf ∈ g) (hne : leaf ≠ root) :
    precedes (cdtToLace g) (cdtNodeToBlock root) (cdtNodeToBlock leaf) := by
  induction path with
  | refl n => exact absurd rfl hne
  | @step child mid root hedge hpresent rest ih =>
      -- `child → mid` is a present edge; `mid` resolves to itself, so `mid ∈ g`.
      have hmidmem : mid ∈ g := List.mem_of_find?_eq_some hpresent
      -- the head edge `mid ← child` as a `precedes` step.
      have hstep : precedes (cdtToLace g) (cdtNodeToBlock mid) (cdtNodeToBlock child) :=
        .base (cdt_edge_is_pointed hedge hleaf hmidmem hinj)
      by_cases hmr : mid = root
      · -- the tail is the trivial path: the single head edge already reaches the root.
        subst hmr; exact hstep
      · -- chain the head edge with the (inductive) tail `root ≺ mid`.
        exact .trans (ih hmidmem hmr) hstep

/-! ## 7. A finality bridge: a block is final when a quorum acks it (`Finality`).

`finality.rs::FinalityTracker` advances a block to `Attested` once a quorum (2f+1) of
distinct creators ack it. We connect the ack-count to `Finality.Config.threshold` (the
`½(n+f)` threshold), giving the tier-2 ack-threshold predicate as a pure count — the same
shape `World.committedByQuorum` uses, here over the blocklace's own ack edges. -/

/-- The set of distinct authors whose blocks in `B` ack (directly point to) `target`
(`finality.rs::FinalityTracker.ack_counts`, counted by unique creator). -/
def ackers (B : Lace) (target : BlockId) : List AuthorId :=
  (B.filter (fun b => target ∈ b.preds)).map (·.creator) |>.dedup

/-- **`attested B cfg target`** — the tier-2/3 finality predicate: a quorum (`cfg.threshold`,
the lifted `½(n+f)`) of distinct authors ack `target`. The `Finality.Committed` instance for
the blocklace ack face (`finality.rs::FinalityLevel.Attested`). -/
def attested (B : Lace) (cfg : Finality.Config) (target : BlockId) : Prop :=
  cfg.threshold ≤ (ackers B target).length

/-- **`attested_mono`** — finality never regresses. Appending blocks (CRDT growth) can only
add ackers, so an attested block stays attested: `attested B cfg t → attested (b :: B) cfg t`.
The "once Attested, stays Attested" guarantee (`finality.rs:166`), as a count monotonicity. -/
theorem attested_mono {B : Lace} {cfg : Finality.Config} {target : BlockId} {b : Block}
    (h : attested B cfg target) : attested (b :: B) cfg target := by
  refine le_trans h ?_
  -- ackers can only grow: the old acker list (Nodup, from dedup) is a subset of the new one,
  -- so its length is ≤ (Nodup.subperm.length_le).
  have hsub : ackers B target ⊆ ackers (b :: B) target := by
    intro x hx
    -- x ∈ dedup(map creator (filter …)) over B ⟹ over (b::B): the filtered list grows.
    have hxB : x ∈ (B.filter (fun bl => target ∈ bl.preds)).map (·.creator) :=
      List.dedup_subset _ hx
    apply List.subset_dedup
    exact List.map_subset _
      (List.filter_subset _ (List.subset_cons_self b B)) hxB
  exact (List.nodup_dedup _).subperm hsub |>.length_le

/-! ## 8. Non-vacuity — a concrete blocklace with a DETECTED fork and an HONEST chain.

A four-block lace over two authors. Author `7` is honest: a base block `g0` (seq 0) and a
successor `g1` (seq 1) that **acks** `g0` — a single ack-chain (totally ordered). Author `9`
is Byzantine: two blocks `f1, f2` (both seq 1) that each ack the genesis but **NOT each
other** — an incomparable pair, a fork. -/

/-- Genesis of the honest author `7` (seq 0, no predecessors). -/
def g0 : Block := { id := 0, creator := 7, seq := 0, preds := [] }
/-- Honest successor (seq 1) — **acks** `g0`: extends the virtual chain (so `g0 ≺ g1`). -/
def g1 : Block := { id := 1, creator := 7, seq := 1, preds := [0] }
/-- Byzantine fork branch A (author `9`, seq 1) — acks genesis `g0` only. -/
def f1 : Block := { id := 2, creator := 9, seq := 1, preds := [0] }
/-- Byzantine fork branch B (author `9`, seq 1) — acks genesis `g0` only; NOT `f1`. -/
def f2 : Block := { id := 3, creator := 9, seq := 1, preds := [0] }

/-- The demo lace: honest chain `g0 ← g1` plus the Byzantine fork `f1 ∥ f2`. -/
def demoLace : Lace := [g0, g1, f1, f2]

-- The honest ack edge resolves (g0 is in g1's preds) and both blocks are present.
#guard (demoLace.lookup 0).isSome && (demoLace.lookup 1).isSome   -- both present
#guard decide (g0.id ∈ g1.preds)                                  -- g1 acks g0
-- The fork blocks share author 9 and seq 1 but neither acks the other.
#guard decide (f1.creator = f2.creator ∧ f1.seq = f2.seq)         -- same strand+seq
#guard decide (f1.id ∈ f2.preds ∨ f2.id ∈ f1.preds) == false      -- neither acks other

/-- The honest ack edge `g0 ← g1` is a `pointed` edge in `demoLace` (`decide`). -/
theorem demo_honest_edge : pointed demoLace g0 g1 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **`demo_honest_precedes`** — in the demo lace the honest successor observes its genesis:
`g0 ≺ g1`. Witnesses that the honest chain is a real, non-trivial `≺`-order. -/
theorem demo_honest_precedes : precedes demoLace g0 g1 := .base demo_honest_edge

/-- The fork blocks `f1, f2` are NOT directly pointed at each other (neither in the other's
preds) — the structural fact underlying their incomparability. PROVED by `decide`. -/
theorem demo_fork_not_pointed :
    ¬ pointed demoLace f1 f2 ∧ ¬ pointed demoLace f2 f1 := by
  constructor <;> · rintro ⟨hmem, _, _⟩; revert hmem; decide

/-- **`demo_precedes_left_g0`** — in `demoLace`, the leftmost block of ANY `≺`-chain
is genesis `g0`: `precedes demoLace x y → x = g0`. Because every `pointed` edge in `demoLace`
acks genesis (all nonempty `preds` are `[0]`, the id of `g0`), so the source of any base edge
is the block looked up at id `0`, which is `g0`; transitivity preserves the leftmost. This is
the acyclicity / single-genesis structure of the demo DAG (paper Prop 2.5). -/
theorem demo_precedes_left_g0 {x y : Block} (h : precedes demoLace x y) : x = g0 := by
  -- The key per-edge fact: a `pointed` edge's source resolves at an id in the target's preds,
  -- and in `demoLace` every member's nonempty preds is `[0]`, whose lookup is `g0`.
  have edge : ∀ a b, pointed demoLace a b → a = g0 := by
    rintro a b ⟨hmem, hla, hlb⟩
    -- b ∈ demoLace (it resolves), so its preds is one of [], [0]; hmem ⇒ a.id = 0.
    have hbmem : b ∈ demoLace := List.mem_of_find?_eq_some hlb
    have ha0 : a.id = 0 := by
      simp only [demoLace, List.mem_cons, List.not_mem_nil, or_false] at hbmem
      rcases hbmem with rfl | rfl | rfl | rfl <;>
        · revert hmem; simp [g0, g1, f1, f2]
    -- lookup demoLace 0 = some g0, and hla says it is some a, so a = g0.
    rw [ha0] at hla
    have : demoLace.lookup 0 = some g0 := by decide
    rw [this] at hla; exact (Option.some.injEq _ _ ▸ hla).symm
  induction h with
  | @base a b hp => exact edge a b hp
  | @trans a m b _ _ iha _ => exact iha

/-- The two non-precedence facts the equivocation needs: nothing reaches a fork block except
via genesis, and a fork block is not genesis. From `demo_precedes_left_g0`: a `≺`-edge from
`f1`/`f2` would force `f1 = g0`/`f2 = g0`, which `decide` refutes. -/
theorem demo_no_fork_precedes :
    ¬ precedes demoLace f1 f2 ∧ ¬ precedes demoLace f2 f1 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have : f1 = g0 := demo_precedes_left_g0 h
    revert this; decide
  · have : f2 = g0 := demo_precedes_left_g0 h
    revert this; decide

/-- **`demo_equivocation`** — author `9` equivocates in `demoLace`: `f1` and `f2` are two
distinct seq-1 `9`-blocks, both present, neither observing the other. Incomparability is
discharged by `demo_no_fork_precedes` (every `≺`-chain in the tiny lace starts at genesis
`g0`, a different author). -/
theorem demo_equivocation : Equivocation demoLace 9 f1 f2 := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  exact ⟨by decide, demo_no_fork_precedes.1, demo_no_fork_precedes.2⟩

/-- **`demo_detect`** — the byzantine-repelling theorem on the concrete fork: author `9` is an
equivocator and the witnessing incomparable pair is `(f1, f2)`. -/
theorem demo_detect :
    Equivocator demoLace 9 ∧ f1 ≠ f2 ∧ ¬ precedes demoLace f1 f2 ∧ ¬ precedes demoLace f2 f1 :=
  equivocation_detectable demo_equivocation

/-! ### Keystones — `#assert_axioms`-clean. -/
#print axioms equivocation_detectable
#print axioms honest_no_equivocation
#print axioms cdt_is_blocklace
#print axioms demo_equivocation
#print axioms attested_mono

end Dregg2.Authority.Blocklace
