/-
# Dregg2.Distributed.ExclusionByPast — equivocator exclusion as a predicate over committed structure.

THE CONSENSUS RULE, AUTHORED HERE (flag day 2026-08-08, exclusion-by-past). The node used to
"exclude" an equivocator by a node-local live mutation: `constitution.auto_evict(proof)` on gossip
arrival retained a participant out of the τ set and recomputed the threshold — so the participant
set was a function of local ARRIVAL ORDER (a node holding both fork halves ran at `n−1` while a
peer holding one ran at `n`, and `wave_leader = participants[wave % n]` elected different leaders
for the same wave: a silent fork), and the verdict REVERTED on restart (never a block, absent from
`committee_replay`'s fold). Neither source paper does this. The blocklace's own paper (Almeida &
Shapiro, arXiv:2402.08068 §4.3) excludes via

    `polog(B) = ({b ∈ B | wf(b) ∧ valid(b) ∧ node(b) ∉ byz(⌊b⌋)}, ≺)`

— **a predicate over the block's own causal closure** — and Cordial Miners' `approves`
(Alg. 1:17) is its anchor-relative twin. `Π` never changes.

This module authors that predicate over the stable DAG substrate
(`Dregg2.Authority.Blocklace`: `precedes`/`incomparable`/`Equivocation`, the same shapes
`blocklace/src/finality.rs::detect_equivocation`/`approved_by` implement) and proves the three
poles the deployment needs, as NAMED theorems (never `#guard`s):

* **Locality / convergence** (`excluded_agrees`, `excluded_agrees_across_nodes`): the verdict is a
  function of the block's closure alone — any two laces that both contain a closed core holding
  the block agree exactly. Two honest nodes that hold `⌊b⌋` compute the SAME exclusion, no matter
  their arrival orders; there is nothing left for a live mutation to decide.
* **Restart durability / no retraction** (`excluded_recomputed_after_restart`,
  `excluded_never_retracted`): the same theorem read along the persistence path — a restart that
  reloads the committed blocks recomputes the identical verdict, and lace growth never retracts a
  verdict.
* **Partial view / evidence-before-verdict** (`honest_not_excluded`,
  `prefork_blocks_keep_status` on the concrete lace): no incomparable pair in the closure ⇒ no
  exclusion. A node holding one fork half excludes nobody its peers keep; a block authored BEFORE
  the fork keeps its status forever (§4.3: the predicate reads each block's OWN past).

Plus the weld to the Rust mechanism that makes the predicate REACHABLE: the two-tips evidence
floor (CM Alg. 1:5, `finality.rs::CreatorTips::Pair`). `carrier_excludes_later_author_block`:
a block pointing at BOTH halves of a detected incomparable pair puts the pair into the closure of
everything after it, so every later block by the equivocator is excluded and every observer holds
the proof (`carried_pair_reaches_observer`). One tip per creator — the old shape — made every
theorem in this file vacuous on the deployed DAG: the second half existed and was unreachable.

CONSUMPTION. The τ pipeline's own Lean model (`BlocklaceFinality.hasEquivInPast`/`approves`, the
verified order the node calls by FFI) is the anchor-relative evaluator of exactly this predicate;
the τ re-authoring should discharge its exclusion guard against `ExcludedByPast` (its current
round-equality pair test is a strict subset of incomparability — same class as the old
`(creator, seq)` heuristic `detect_equivocation` shed). Deliberately NO `@[export]` here: the live
Lean entry point for ordering is `BlocklaceFinality`'s, and an export nothing calls is a vestigial
weld.

Pure order-theory; the §8 crypto seam (hash injectivity, signature unforgeability) is untouched.
-/
import Dregg2.Authority.Blocklace

namespace Dregg2.Distributed.ExclusionByPast

open Dregg2.Authority.Blocklace

/-! ## 1. The predicate — `node(b) ∉ byz(⌊b⌋)` (blocklace paper §4.3). -/

/-- `x ∈ ⌊b⌋`: `x` is in `b`'s INCLUSIVE causal closure (`x = b` or `x ≺ b`).
CM Def. 19's `[b]`; `ordering.rs::causal_past_inclusive`. -/
def inClosure (B : Lace) (x b : Block) : Prop :=
  x = b ∨ precedes B x b

/-- `q ∈ byz(⌊b⌋)` with `byz = eqvc` (paper §4.2/§4.3): author `q` has an incomparable
pair of blocks BOTH inside `b`'s own closure. Reuses `Authority.Blocklace.Equivocation`
verbatim — the pair IS the `EquivocationProof` the Rust ingest pins as
`CreatorTips::Pair`. -/
def ByzInClosure (B : Lace) (q : AuthorId) (b : Block) : Prop :=
  ∃ x y, Equivocation B q x y ∧ inClosure B x b ∧ inClosure B y b

/-- **THE EXCLUSION PREDICATE** — `node(b) ∈ byz(⌊b⌋)`: block `b` is excluded from the
PO-Log iff its own creator equivocates INSIDE `b`'s own closure. Deterministic in
`(B restricted to ⌊b⌋)`, so it needs no message, no vote, no membership mutation, and no
agreement about when anyone learned anything — the properties proved below. -/
def ExcludedByPast (B : Lace) (b : Block) : Prop :=
  ByzInClosure B b.creator b

/-- An excluded block's creator is a plain `Equivocator` of the lace (the global set
`eqvc(B)`, `finality.rs::equivocators`): exclusion never fires without a real fork. -/
theorem excluded_equivocator {B : Lace} {b : Block} (h : ExcludedByPast B b) :
    Equivocator B b.creator := by
  obtain ⟨x, y, he, -, -⟩ := h
  exact ⟨x, y, he⟩

/-! ## 2. The partial-view pole — no pair in the closure, no verdict.

The brief's test: *a live read may decide WHETHER you emit, never WHAT you emit — and the
mutation must be asserted present before the verdict.* Here the "mutation" is the incomparable
pair itself, and the verdict cannot exist without it: an honest author is never excluded, on any
view, partial or not. A node that has received only ONE half of a fork holds a lace in which the
equivocator's blocks still satisfy `HonestChain`-style comparability — so it keeps everyone its
peers keep, and converges to exclusion only when (and where) the pair itself arrives. -/

/-- **`honest_not_excluded`** — an author following the honest virtual-chain discipline is
never excluded, in any lace: the verdict requires the pair, and an honest chain has none.
(The general form of the partial-view pole.) -/
theorem honest_not_excluded {B : Lace} {b : Block} (hon : HonestChain B b.creator) :
    ¬ ExcludedByPast B b :=
  fun h => honest_no_equivocation hon (excluded_equivocator h)

/-! ## 3. Locality: the verdict is a function of the closure alone.

`Closed` is exactly the ingest invariant `finality.rs::insert_checked` enforces (every present
block's predecessors are present), and `Canonical` is content-addressing. The confinement lemma
is the heart: a `≺`-path into a block of a closed sub-lace cannot leave that sub-lace — walking
backward from the target, every step resolves inside it. Hence the predicate evaluated on ANY
canonical superset equals the predicate evaluated on the closed core: arrival order, gossip
timing, and everything else a node's live view adds are provably irrelevant. -/

/-- A lace is (pred-)closed: every present block's predecessors resolve. The
`insert_checked` closure gate, as a `Prop`. -/
def Closed (B : Lace) : Prop :=
  ∀ c ∈ B, ∀ p ∈ c.preds, (B.lookup p).isSome

/-- A resolved block carries the id it was looked up by. -/
theorem lookup_id {B : Lace} {h : BlockId} {d : Block} (hl : B.lookup h = some d) :
    d.id = h := by
  have := List.find?_some hl
  simpa using this

/-- A `pointed` edge lifts along lace growth (canonical superset). -/
theorem pointed_mono {B₁ B₂ : Lace} (hsub : ∀ z ∈ B₁, z ∈ B₂)
    (hcanon₂ : B₂.Canonical) {a b : Block} (hp : pointed B₁ a b) : pointed B₂ a b := by
  obtain ⟨hmem, hla, hlb⟩ := hp
  exact ⟨hmem,
    lookup_of_mem hcanon₂ (hsub _ (List.mem_of_find?_eq_some hla)),
    lookup_of_mem hcanon₂ (hsub _ (List.mem_of_find?_eq_some hlb))⟩

/-- `≺` lifts along lace growth: CRDT growth never destroys an observation. -/
theorem precedes_mono {B₁ B₂ : Lace} (hsub : ∀ z ∈ B₁, z ∈ B₂)
    (hcanon₂ : B₂.Canonical) {x y : Block} (h : precedes B₁ x y) : precedes B₂ x y := by
  induction h with
  | base hp => exact .base (pointed_mono hsub hcanon₂ hp)
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-- **`precedes_confined`** — path confinement, the load-bearing lemma. A `≺`-path in a
canonical superset `B₂` INTO a block of a closed canonical core `B₁` lies entirely inside
`B₁`: walking back from the target, each edge's source resolves in `B₁` (closedness) to the
same block it is in `B₂` (canonicity). Growth can add new blocks and new edges OUT of them,
but never a new path into old structure — a block's past is fixed by its own signed pointers. -/
theorem precedes_confined {B₁ B₂ : Lace} (hclosed : Closed B₁)
    (hcanon₁ : B₁.Canonical) (hcanon₂ : B₂.Canonical)
    (hsub : ∀ z ∈ B₁, z ∈ B₂) {x b : Block}
    (h : precedes B₂ x b) :
    b ∈ B₁ → x ∈ B₁ ∧ precedes B₁ x b := by
  induction h with
  | @base a c hp =>
      intro hb
      obtain ⟨hmem, hla, _hlc⟩ := hp
      have hsome : (B₁.lookup a.id).isSome := hclosed c hb a.id hmem
      obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hsome
      have hdmem : d ∈ B₁ := List.mem_of_find?_eq_some hd
      have hdid : d.id = a.id := lookup_id hd
      have hamem₂ : a ∈ B₂ := List.mem_of_find?_eq_some hla
      have hda : d = a := hcanon₂ d (hsub d hdmem) a hamem₂ hdid
      subst hda
      exact ⟨hdmem, .base ⟨hmem, hd, lookup_of_mem hcanon₁ hb⟩⟩
  | @trans a m c _hab _hmc ih₁ ih₂ =>
      intro hb
      obtain ⟨hm₁, hmc₁⟩ := ih₂ hb
      obtain ⟨ha₁, ham₁⟩ := ih₁ hm₁
      exact ⟨ha₁, .trans ham₁ hmc₁⟩

/-- Closure membership is confined with the path. -/
theorem inClosure_confined {B₁ B₂ : Lace} (hclosed : Closed B₁)
    (hcanon₁ : B₁.Canonical) (hcanon₂ : B₂.Canonical)
    (hsub : ∀ z ∈ B₁, z ∈ B₂) {x b : Block}
    (hx : inClosure B₂ x b) (hb : b ∈ B₁) : x ∈ B₁ ∧ inClosure B₁ x b := by
  rcases hx with rfl | hp
  · exact ⟨hb, Or.inl rfl⟩
  · obtain ⟨hx₁, hp₁⟩ := precedes_confined hclosed hcanon₁ hcanon₂ hsub hp hb
    exact ⟨hx₁, Or.inr hp₁⟩

/-! ## 4. THE AGREEMENT THEOREM — both remaining poles at once. -/

/-- **`excluded_agrees`** — the verdict computed on any canonical superset `B₂` equals the
verdict computed on a closed canonical core `B₁` containing the block. Forward: the pair and
its closure paths lift by monotonicity, and incomparability survives because a comparison
path in `B₂` between closure members would be confined back into `B₁`. Backward: the pair,
its paths, and incomparability are all confined into the core.

This is the paper's design goal as a theorem: `node(b) ∉ byz(⌊b⌋)` is a function of
committed structure — of the closure a block's own signed pointers fix — and NOTHING else. -/
theorem excluded_agrees {B₁ B₂ : Lace} (hclosed : Closed B₁)
    (hcanon₁ : B₁.Canonical) (hcanon₂ : B₂.Canonical)
    (hsub : ∀ z ∈ B₁, z ∈ B₂) {b : Block} (hb : b ∈ B₁) :
    (ExcludedByPast B₁ b ↔ ExcludedByPast B₂ b) := by
  constructor
  · rintro ⟨x, y, he, hxcl, hycl⟩
    have hymem₁ : y ∈ B₁ := List.mem_of_find?_eq_some he.b_mem
    have hxmem₁ : x ∈ B₁ := List.mem_of_find?_eq_some he.a_mem
    refine ⟨x, y, ⟨lookup_of_mem hcanon₂ (hsub x hxmem₁),
                   lookup_of_mem hcanon₂ (hsub y hymem₁),
                   he.a_author, he.b_author, ?_⟩, ?_, ?_⟩
    · -- incomparability survives growth: a new comparison path would confine back.
      obtain ⟨hne, hnxy, hnyx⟩ := he.incomp
      refine ⟨hne, fun h₂ => ?_, fun h₂ => ?_⟩
      · exact hnxy (precedes_confined hclosed hcanon₁ hcanon₂ hsub h₂ hymem₁).2
      · exact hnyx (precedes_confined hclosed hcanon₁ hcanon₂ hsub h₂ hxmem₁).2
    · rcases hxcl with rfl | hp
      · exact Or.inl rfl
      · exact Or.inr (precedes_mono hsub hcanon₂ hp)
    · rcases hycl with rfl | hp
      · exact Or.inl rfl
      · exact Or.inr (precedes_mono hsub hcanon₂ hp)
  · rintro ⟨x, y, he, hxcl, hycl⟩
    obtain ⟨hxmem₁, hxcl₁⟩ := inClosure_confined hclosed hcanon₁ hcanon₂ hsub hxcl hb
    obtain ⟨hymem₁, hycl₁⟩ := inClosure_confined hclosed hcanon₁ hcanon₂ hsub hycl hb
    refine ⟨x, y, ⟨lookup_of_mem hcanon₁ hxmem₁, lookup_of_mem hcanon₁ hymem₁,
                   he.a_author, he.b_author, ?_⟩, hxcl₁, hycl₁⟩
    obtain ⟨hne, hnxy, hnyx⟩ := he.incomp
    exact ⟨hne, fun h₁ => hnxy (precedes_mono hsub hcanon₂ h₁),
                fun h₁ => hnyx (precedes_mono hsub hcanon₂ h₁)⟩

/-- **The cross-node pole.** Two honest nodes' laces `B₂, B₃` — different arrival orders,
different extra blocks — each contain a closed canonical core `B₁` holding `b` (any node
that admitted `b` holds `⌊b⌋`: ingest enforces closure). Their verdicts are IDENTICAL.
This is what `auto_evict` could never provide: it keyed on which fork half arrived where. -/
theorem excluded_agrees_across_nodes {B₁ B₂ B₃ : Lace} (hclosed : Closed B₁)
    (hcanon₁ : B₁.Canonical) (hcanon₂ : B₂.Canonical) (hcanon₃ : B₃.Canonical)
    (hsub₂ : ∀ z ∈ B₁, z ∈ B₂) (hsub₃ : ∀ z ∈ B₁, z ∈ B₃) {b : Block} (hb : b ∈ B₁) :
    (ExcludedByPast B₂ b ↔ ExcludedByPast B₃ b) :=
  (excluded_agrees hclosed hcanon₁ hcanon₂ hsub₂ hb).symm.trans
    (excluded_agrees hclosed hcanon₁ hcanon₃ hsub₃ hb)

/-- **The restart pole.** A restart reloads the committed blocks (the persisted lace `B₁` —
`from_checkpoint` re-derives everything from exactly these) and recomputes the SAME verdict
any pre-restart superset view computed: the special case `B₃ = B₁` of agreement. The old
mutation failed precisely here — `n` and the threshold reverted because the eviction was
never a function of these blocks. -/
theorem excluded_recomputed_after_restart {B₁ B₂ : Lace} (hclosed : Closed B₁)
    (hcanon₁ : B₁.Canonical) (hcanon₂ : B₂.Canonical)
    (hsub : ∀ z ∈ B₁, z ∈ B₂) {b : Block} (hb : b ∈ B₁) :
    (ExcludedByPast B₂ b ↔ ExcludedByPast B₁ b) :=
  (excluded_agrees hclosed hcanon₁ hcanon₂ hsub hb).symm

/-- **No verdict is ever retracted** (the brief's second clause): once excluded on the
committed core, excluded on every canonical growth of it. Monotone, like the `equivocators`
set that mirrors it in `finality.rs` (inserted, never removed; checkpoint restore folds it
as a lower bound). -/
theorem excluded_never_retracted {B₁ B₂ : Lace} (hclosed : Closed B₁)
    (hcanon₁ : B₁.Canonical) (hcanon₂ : B₂.Canonical)
    (hsub : ∀ z ∈ B₁, z ∈ B₂) {b : Block} (hb : b ∈ B₁)
    (h : ExcludedByPast B₁ b) : ExcludedByPast B₂ b :=
  (excluded_agrees hclosed hcanon₁ hcanon₂ hsub hb).mp h

/-! ## 5. The weld to the Rust floor — carrying the pair makes the predicate fire.

`finality.rs` pins a detected incomparable pair as `CreatorTips::Pair(a, b)`; the next
locally-authored block (and the round-driven producer's next cohort) points at BOTH halves.
These two theorems are what that buys: every observer of the carrier holds the proof, and
every later block by the equivocator is excluded. Without the floor, both are vacuous on the
deployed DAG — the second half was retained but pointed at by nothing. -/

/-- A block `w` pointing at both halves of an incomparable pair broadcasts the proof: every
block at-or-after `w` sees both halves (`seesBoth`, the `approved_by` test's premise). -/
theorem carried_pair_reaches_observer {B : Lace} {x y w o : Block}
    (hxw : pointed B x w) (hyw : pointed B y w)
    (how : w = o ∨ precedes B w o) : seesBoth B o x y := by
  refine ⟨?_, ?_⟩
  · rcases how with rfl | hwo
    · exact .base hxw
    · exact .trans (.base hxw) hwo
  · rcases how with rfl | hwo
    · exact .base hyw
    · exact .trans (.base hyw) hwo

/-- **`carrier_excludes_later_author_block`** — once one carrier block links the pair, every
later block by the equivocator is `ExcludedByPast`: the fork is in its closure forever. The
transient two-tips floor (pin → carry once → weld through our own chain) suffices. -/
theorem carrier_excludes_later_author_block {B : Lace} {x y w b : Block}
    (he : Equivocation B b.creator x y) (hxw : pointed B x w) (hyw : pointed B y w)
    (hwb : w = b ∨ precedes B w b) : ExcludedByPast B b := by
  obtain ⟨hxo, hyo⟩ := carried_pair_reaches_observer hxw hyw hwb
  exact ⟨x, y, he, Or.inr hxo, Or.inr hyo⟩

/-! ## 6. Non-vacuity — the deployed shape, concretely.

`Authority.Blocklace.demoLace` has the fork (`f1 ∥ f2`, author 9) with NO carrier — exactly
the old deployment: `demoLace` cannot exclude anything (the pair reaches no closure). Extend
it with the two blocks the new floor produces: `w` (an honest block pointing at BOTH halves —
what the pinned `CreatorTips::Pair` makes the next authored block do) and `f3` (the
equivocator continuing after the fork). Then: `f3` is excluded; the pre-fork `f1` keeps its
status; and a half-view lace holding one branch excludes nobody. -/

/-- The carrier: an honest block pointing at both fork halves (`preds = [f1.id, f2.id]`) —
the block the two-tips floor makes us author. -/
def w : Block := { id := 4, creator := 7, seq := 2, preds := [2, 3] }

/-- The equivocator's post-fork block, pointing at the carrier: the block the predicate
must exclude. -/
def f3 : Block := { id := 5, creator := 9, seq := 3, preds := [4] }

/-- The demo lace with the evidence CARRIED: `demoLace` + carrier + post-fork block. -/
def demoLace3 : Lace := [g0, g1, f1, f2, w, f3]

/-- Nothing precedes genesis: `g0` has an empty pred set, in `demoLace3` too. -/
theorem demo3_nothing_precedes_g0 {x y : Block} (h : precedes demoLace3 x y) : y ≠ g0 := by
  induction h with
  | @base a c hp =>
      rintro rfl
      obtain ⟨hmem, -, -⟩ := hp
      simp [g0] at hmem
  | @trans a m c _hab _hmc _ih₁ ih₂ => exact ih₂

/-- Every `≺`-path into `f1` starts at genesis (its only pred is `g0`). -/
theorem demo3_into_f1 {x y : Block} (h : precedes demoLace3 x y) : y = f1 → x = g0 := by
  induction h with
  | @base a c hp =>
      rintro rfl
      obtain ⟨hmem, hla, -⟩ := hp
      have ha0 : a.id = 0 := by simpa [f1] using hmem
      have hg : demoLace3.lookup 0 = some g0 := by decide
      rw [ha0, hg] at hla
      exact (Option.some.injEq _ _ ▸ hla).symm
  | @trans a m c hab _hmc _ih₁ ih₂ =>
      rintro rfl
      exact absurd (ih₂ rfl) (demo3_nothing_precedes_g0 hab)

/-- Every `≺`-path into `f2` starts at genesis (its only pred is `g0`). -/
theorem demo3_into_f2 {x y : Block} (h : precedes demoLace3 x y) : y = f2 → x = g0 := by
  induction h with
  | @base a c hp =>
      rintro rfl
      obtain ⟨hmem, hla, -⟩ := hp
      have ha0 : a.id = 0 := by simpa [f2] using hmem
      have hg : demoLace3.lookup 0 = some g0 := by decide
      rw [ha0, hg] at hla
      exact (Option.some.injEq _ _ ▸ hla).symm
  | @trans a m c hab _hmc _ih₁ ih₂ =>
      rintro rfl
      exact absurd (ih₂ rfl) (demo3_nothing_precedes_g0 hab)

/-- Author 9's fork survives the extension: `f1 ∥ f2` in `demoLace3` (a path either way
would have to start at genesis, which is neither fork block). -/
theorem demo3_equivocation : Equivocation demoLace3 9 f1 f2 := by
  refine ⟨by decide, by decide, by decide, by decide, ⟨by decide, ?_, ?_⟩⟩
  · exact fun h => absurd (demo3_into_f2 h rfl) (by decide)
  · exact fun h => absurd (demo3_into_f1 h rfl) (by decide)

/-- The carrier points at fork half `f1` (`f1.id = 2 ∈ w.preds`). -/
theorem demo3_f1_pointed_w : pointed demoLace3 f1 w := ⟨by decide, by decide, by decide⟩
/-- The carrier points at fork half `f2` (`f2.id = 3 ∈ w.preds`). -/
theorem demo3_f2_pointed_w : pointed demoLace3 f2 w := ⟨by decide, by decide, by decide⟩
/-- The post-fork block points at the carrier (`w.id = 4 ∈ f3.preds`). -/
theorem demo3_w_pointed_f3 : pointed demoLace3 w f3 := ⟨by decide, by decide, by decide⟩

/-- **The floor pays off** — the equivocator's post-fork block is excluded: the carrier put
the pair into `f3`'s closure, and `ExcludedByPast` fires. On `demoLace` (no carrier) this
statement was unprovable for EVERY block: the deployed one-tip shape in one theorem. -/
theorem demo3_postfork_excluded : ExcludedByPast demoLace3 f3 :=
  carrier_excludes_later_author_block demo3_equivocation demo3_f1_pointed_w
    demo3_f2_pointed_w (Or.inr (.base demo3_w_pointed_f3))

/-- **Pre-fork blocks keep their status** (paper §4.3: the predicate reads each block's OWN
past). `f1` — authored before the fork completed — is NOT excluded even in the full lace
that knows everything: its closure is `{g0, f1}`, which holds no pair. Retroactive global
exclusion (what `auto_evict` did to the leader schedule of every wave) is exactly what the
per-closure predicate refuses to express. -/
theorem demo3_prefork_keeps_status : ¬ ExcludedByPast demoLace3 f1 := by
  rintro ⟨x, y, he, hxcl, hycl⟩
  -- Any creator-9 block in f1's closure IS f1: closure = {f1, g0}, and g0 is author 7.
  have hx : x = f1 := by
    rcases hxcl with rfl | hp
    · rfl
    · have hx0 : x = g0 := demo3_into_f1 hp rfl
      have := he.a_author
      rw [hx0] at this
      exact absurd this (by decide)
  have hy : y = f1 := by
    rcases hycl with rfl | hp
    · rfl
    · have hy0 : y = g0 := demo3_into_f1 hp rfl
      have := he.b_author
      rw [hy0] at this
      exact absurd this (by decide)
  obtain ⟨hne, -, -⟩ := he.incomp
  exact hne (hx.trans hy.symm)

/-- **The partial-view pole, concretely.** A node that received only ONE branch of the fork
(`[g0, g1, f1]` — `f2` never arrived) excludes nobody: author 9 satisfies the honest-chain
discipline on this view, so `honest_not_excluded` applies to every 9-block in it. Exclusion
becomes expressible exactly when the pair itself is present and carried — never earlier. -/
def demoLaceHalf : Lace := [g0, g1, f1]

theorem demo_half_view_keeps_f1 : ¬ ExcludedByPast demoLaceHalf f1 := by
  rintro ⟨x, y, he, -, -⟩
  -- The only author-9 block in the half lace is f1 itself: the pair collapses.
  have hx : x = f1 := by
    have hmem := List.mem_of_find?_eq_some he.a_mem
    have ha := he.a_author
    simp only [demoLaceHalf, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact absurd ha (by decide)
    · exact absurd ha (by decide)
    · rfl
  have hy : y = f1 := by
    have hmem := List.mem_of_find?_eq_some he.b_mem
    have hb := he.b_author
    simp only [demoLaceHalf, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact absurd hb (by decide)
    · exact absurd hb (by decide)
    · rfl
  obtain ⟨hne, -, -⟩ := he.incomp
  exact hne (hx.trans hy.symm)

/-! ### Keystones — `#print axioms`-clean (no `native_decide`, no `sorry`). -/
#print axioms excluded_agrees
#print axioms excluded_agrees_across_nodes
#print axioms excluded_recomputed_after_restart
#print axioms excluded_never_retracted
#print axioms honest_not_excluded
#print axioms carrier_excludes_later_author_block
#print axioms demo3_postfork_excluded
#print axioms demo3_prefork_keeps_status
#print axioms demo_half_view_keeps_f1

end Dregg2.Distributed.ExclusionByPast
