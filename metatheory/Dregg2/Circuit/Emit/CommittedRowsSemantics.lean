/-
# Dregg2.Circuit.Emit.CommittedRowsSemantics — SCOPING the named IR gap
`RowSemantics.committedRows (root : EmittedExpr)`, prototyped ADDITIVELY.

**This is Lean-authored AIR metatheory.** It authors no descriptor and adds NO constructor to the
shared `DescriptorIR2.RowSemantics`: the whole denotational content of `committedRows` is carried
here as a SHADOW declaration (`CommittedRowsDecl`) plus a faithfulness leg (`CommittedContents`),
so the shared IR keystone is untouched and no downstream file can go red. That is itself the
finding this file exists to establish (see §7): on the LEAN side the change is additive, because a
table whose `RowSemantics` is not `exactPublicRows` ALREADY has prover-supplied contents in
`Satisfied2` — `TableDef.publicContentsFaithful` is `True` there. What `committedRows` adds is a
LEG, not a change to any existing obligation.

## The gap, restated

`AttestedAutomatonEmit` §7 names it: a `lookup` targets a `TableDef`, and the only
content-committing row semantics is `exactPublicRows`, whose contents ARE the descriptor's own
bytes. So a lookup-shaped "the run's edges are edges of the committed automaton" must declare every
edge (`O(|Q|·|Σ|)` bytes) AND inherits the unit-capacity exact-multiset receive (the Eulerian
obstruction). There is NO row semantics whose contents are committed by a ROOT.

## What is built here

  * `CommittedContents hash cd R t` (§2) — the table `cd.id` carries the GRAPH of some sorted,
    `2^cd.depth`-leaf heap whose deployed binary-Merkle `mapRoot` is `R`. Contents become a
    WITNESS pinned by a root, rather than a transcription of descriptor bytes.
  * `committed_lookup_opens` (§3) — THE LEVER: a lookup hit on such a table IS an `opensTo`
    opening under `R`. This is the exact primitive `MapOp.holdsAt` supplies per-row, obtained
    instead from table membership.
  * `lookup_replaces_mapOp` (§3) — the payoff, machine-checked: the conclusion
    `AttestedAutomatonEmit.att_row_reads` gets from a `MapOp` (`next = d.step current symbol`
    against the COMMITTED automaton) is derived from a `Lookup` plus `CommittedContents`, under
    the same `Poseidon2SpongeCR` floor and nothing more.
  * `committedRoot_binds_contents` (§4) — the attestation: one root, one table content.
  * §5 — non-vacuity: `CommittedContents` is INHABITED (any sorted `2^d`-leaf heap realizes it),
    and inhabited at the automaton commitment `autoHeap`/`autoRoot` specifically.
  * §6 — the cost law, as ARITHMETIC over the deployed AIR's permutation counts. ⚠ These are NOT
    measurements of a proven object: they are counts read off `circuit/src/descriptor_ir2.rs`'s
    `Ir2Air::MapOps` arm. Every `#guard` is compiled evaluation of a closed `Bool` and proves NO
    `Prop`. The only WITNESSED descriptor costs in this area are `AttestedAutomatonEmit` §7's,
    which stand behind `attWit_satisfies`.

## The felt-width wound is INHERITED, not repaired

Everything here that consumes `Poseidon2SpongeCR hash` for `hash : List ℤ → ℤ` inherits
`AttestedAutomatonEmit`'s stated wound verbatim: at the DEPLOYED BabyBear codomain
(p ≈ 2^31) that hypothesis is FALSE (~2^15.5 birthday work). A `committedRows` root would be the
SAME kind of felt and would need the SAME 8-felt weld. This file does not improve that and does
not claim to.

## Axiom hygiene

`#assert_all_clean` on every theorem (§8). NEW file; imports are read-only; deliberately NOT
registered in `Dregg2.lean` (a design/scoping leaf, like `DfaRoutingSubsetTableCost`).
-/
import Dregg2.Circuit.Emit.AttestedAutomatonEmit

namespace Dregg2.Circuit.Emit.CommittedRowsSemantics

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Substrate
open Dregg2.Crypto.DfaAcceptanceAir (TableDfa)
open Dregg2.Circuit.Emit.AttestedAutomatonEmit

set_option autoImplicit false

/-! ## §1 — heap ⇄ table: the row encoding, and the uniqueness a sorted spine buys. -/

/-- The arity-2 table view of a sorted map: one row `[key, value]` per entry, in key order. This
is the shape a `committedRows` table would carry for a `(key, value)` commitment; a wider arity
would pack the value block, which changes nothing below. -/
def rowsOfHeap (h : Heap.FeltHeap) : Table := h.map (fun e => [e.1, e.2])

/-- A table row of a heap view IS an entry of the heap. -/
theorem mem_rowsOfHeap {h : Heap.FeltHeap} {k v : ℤ} (hm : [k, v] ∈ rowsOfHeap h) :
    (k, v) ∈ h := by
  simp only [rowsOfHeap, List.mem_map] at hm
  obtain ⟨⟨a, b⟩, he, heq⟩ := hm
  simp only [List.cons.injEq, and_true] at heq
  obtain ⟨rfl, rfl⟩ := heq
  exact he

/-- On a SORTED map, membership determines the lookup: the first match is the only match. (The
`Heap` API has `get_eq_none_iff` and `ext_get` but not this direction; it is the one lemma the
committed-contents lever needs.) -/
theorem get_of_mem_sorted : ∀ (h : Heap.FeltHeap) (k v : ℤ),
    Heap.SortedKeys h → (k, v) ∈ h → Heap.get h k = some v := by
  intro h
  induction h with
  | nil => intro k v _ hm; cases hm
  | cons e t ih =>
    intro k v hs hm
    obtain ⟨k', v'⟩ := e
    rcases List.mem_cons.mp hm with he | ht
    · have h1 : k = k' ∧ v = v' := by simpa [Prod.mk.injEq] using he
      obtain ⟨rfl, rfl⟩ := h1
      simp [Heap.get]
    · have hk : k ∈ Heap.keys t := by
        simp only [Heap.keys, List.mem_map]
        exact ⟨(k, v), ht, rfl⟩
      have hkne : k ≠ k' := by
        intro hEq
        subst hEq
        exact Heap.head_key_not_mem hs hk
      rw [Heap.get_cons_ne v' t hkne]
      exact ih k v (Heap.sortedKeys_tail hs) ht

/-! ## §2 — WHAT `RowSemantics.committedRows` WOULD MEAN.

The shadow declaration carries exactly the data the enum constructor would: the table id, its
column arity, the COLUMN EXPRESSION carrying the commitment (`root`, the analog of a `MapOp`'s
root group), and the committed tree depth. The `depth` field is NOT decoration — §6 shows the
whole economics turns on whether the commitment is over the table's own PACKED row count or over
the deployed `MAP_TREE_DEPTH = 16` leaf domain. -/

/-- The shadow of `RowSemantics.committedRows` — the declaration a `TableDef` would carry. -/
structure CommittedRowsDecl where
  /-- The declared table's wire id. -/
  id    : TableId
  /-- Column arity (2 for a `(key, value)` commitment). -/
  arity : Nat
  /-- The column expression carrying the commitment root (evaluated on the main row). -/
  root  : EmittedExpr
  /-- The committed binary-Merkle depth (the leaf domain is `2 ^ depth`). -/
  depth : Nat

/-- **THE FAITHFULNESS LEG** that replaces `TableDef.publicContentsFaithful` for a committed
table: the table's contents are not the descriptor's bytes but the graph of SOME sorted,
`2^depth`-leaf heap whose deployed binary-Merkle root is `R`. Contents are a WITNESS; the root
pins them. -/
def CommittedContents (hash : List ℤ → ℤ) (cd : CommittedRowsDecl) (R : ℤ) (t : VmTrace) : Prop :=
  ∃ h : Heap.FeltHeap, Heap.SortedKeys h ∧ h.length = 2 ^ cd.depth
    ∧ MapMerkleRoot.mapRoot hash cd.depth h = R ∧ t.tf cd.id = rowsOfHeap h

/-- **The acceptance predicate a `committedRows` descriptor would denote**: `Satisfied2` plus the
committed-contents leg plus the root pin (the root column carries the public commitment on every
row — the analog of `attRootConst` + `attB3`). It is ADDITIVE over `Satisfied2` exactly as
`Satisfied2Public` / `Satisfied2U` / `Satisfied2Custom` are. -/
structure Satisfied2Committed (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (cd : CommittedRowsDecl) (R : ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace) : Prop
    extends Satisfied2 hash d minit mfin maddrs t where
  /-- The table's contents are committed by `R`. -/
  committedContents : CommittedContents hash cd R t
  /-- The root column carries `R` on every main row. -/
  rootPinned : ∀ i < t.rows.length, cd.root.eval (envAt t i).loc = R

/-! ## §3 — ⚑ THE LEVER: a lookup hit on a committed table IS a root opening. -/

/-- **`committed_lookup_opens`** — the table-membership face of a root opening. If the table's
contents are committed by `R`, then any row `[k, v]` of it is a genuine `opensToMerkle` opening of
`R` at `k`. This is the primitive `MapOp.holdsAt` supplies PER ROW, obtained here from ONE table
membership — the whole point of the extension. -/
theorem committed_lookup_opens (hash : List ℤ → ℤ) (cd : CommittedRowsDecl) (R : ℤ) (t : VmTrace)
    (hc : CommittedContents hash cd R t) {k v : ℤ} (hmem : [k, v] ∈ t.tf cd.id) :
    MapMerkleRoot.opensToMerkle hash cd.depth R k (some v) := by
  obtain ⟨h, hs, hlen, hroot, htf⟩ := hc
  rw [htf] at hmem
  exact ⟨h, hs, hlen, hroot, get_of_mem_sorted h k v hs (mem_rowsOfHeap hmem)⟩

/-- At the DEPLOYED depth the opening is literally `DescriptorIR2.opensTo` — the same relation the
map-ops table realizes, so the two routes are interchangeable at the soundness interface. -/
theorem committed_lookup_opensTo (hash : List ℤ → ℤ) (cd : CommittedRowsDecl)
    (hd : cd.depth = MAP_TREE_DEPTH) (R : ℤ) (t : VmTrace)
    (hc : CommittedContents hash cd R t) {k v : ℤ} (hmem : [k, v] ∈ t.tf cd.id) :
    opensTo hash R k (some v) := by
  have h := committed_lookup_opens hash cd R t hc hmem
  rw [hd] at h
  exact h

/-- ⚑ **`lookup_replaces_mapOp` — THE PAYOFF, machine-checked.** The conclusion
`AttestedAutomatonEmit.att_row_reads` extracts from a per-row `MapOp` — the row's `next` IS the
COMMITTED automaton's step, not merely some declared edge — is derived here from a `Lookup`
against a `committedRows` table, under the SAME `Poseidon2SpongeCR` floor and no extra hypothesis.
So the attestation the map-op route buys is available in lookup shape; §6 is where the two prices
differ. -/
theorem lookup_replaces_mapOp (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (cd : CommittedRowsDecl) (hd : cd.depth = MAP_TREE_DEPTH) (R : ℤ)
    (d : TableDfa Nat Nat) (hcommit : CommitsAutomaton hash R d)
    (t : VmTrace) (hc : CommittedContents hash cd R t)
    (env : VmRowEnv) (kx nx : EmittedExpr) (s y : Nat) (hs : s < ASTATES) (hy : y < ASYM)
    (hkey : kx.eval env.loc = ((keyOf s y : Nat) : ℤ))
    (hlk : Lookup.holdsAt t.tf env ⟨cd.id, [kx, nx]⟩) :
    nx.eval env.loc = ((d.step s y : Nat) : ℤ) := by
  have hmem : [kx.eval env.loc, nx.eval env.loc] ∈ t.tf cd.id := by
    simpa [Lookup.holdsAt] using hlk
  rw [hkey] at hmem
  have hopen := committed_lookup_opensTo hash cd hd R t hc hmem
  have hstep := hcommit s y hs hy
  have hval := opensTo_functional hash hCR hopen hstep
  simpa using hval

/-! ## §4 — ⚑ THE ATTESTATION: one root, one table content. -/

/-- **`committedRoot_binds_contents`** — the analog of `root_binds_automaton` at the table level.
Two committed tables published under the SAME root agree at every key they both carry: a root
determines the table's contents. This is precisely what `exactPublicRows` gets from the descriptor
bytes, obtained instead from ONE felt. (Inherits the felt-width wound: at the deployed BabyBear
codomain the CR hypothesis is false.) -/
theorem committedRoot_binds_contents (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (cd₁ cd₂ : CommittedRowsDecl) (hdep : cd₂.depth = cd₁.depth) (R : ℤ) (t₁ t₂ : VmTrace)
    (h₁ : CommittedContents hash cd₁ R t₁) (h₂ : CommittedContents hash cd₂ R t₂)
    {k v₁ v₂ : ℤ} (m₁ : [k, v₁] ∈ t₁.tf cd₁.id) (m₂ : [k, v₂] ∈ t₂.tf cd₂.id) :
    v₁ = v₂ := by
  have o₁ := committed_lookup_opens hash cd₁ R t₁ h₁ m₁
  have o₂ := committed_lookup_opens hash cd₂ R t₂ h₂ m₂
  rw [hdep] at o₂
  have := MapMerkleRoot.opensToMerkle_functional hash hCR cd₁.depth o₁ o₂
  simpa using this

/-! ## §5 — NON-VACUITY: the predicate is inhabited, and inhabited AT the automaton commitment. -/

/-- The single-table witness family: the declared table carries the heap's graph, every other
table empty. -/
def committedTrace (tid : TableId) (h : Heap.FeltHeap) : VmTrace :=
  { rows := [], pub := zeroAsg, tf := fun id => if id = tid then rowsOfHeap h else [] }

/-- ⚑ **`CommittedContents` is INHABITED for EVERY sorted `2^d`-leaf heap** — the predicate is a
construction, not a wish (the same discipline `autoRoot_commits` holds `CommitsAutomaton` to). -/
theorem committedContents_inhabited (hash : List ℤ → ℤ) (tid : TableId) (dep : Nat)
    (rootE : EmittedExpr) (h : Heap.FeltHeap)
    (hs : Heap.SortedKeys h) (hlen : h.length = 2 ^ dep) :
    CommittedContents hash ⟨tid, 2, rootE, dep⟩
      (MapMerkleRoot.mapRoot hash dep h) (committedTrace tid h) :=
  ⟨h, hs, hlen, rfl, by simp [committedTrace]⟩

/-- ⚑ **Inhabited AT the automaton commitment.** The very heap `AttestedAutomatonEmit` commits
(`autoHeap d`, total over the deployed `2^16` leaves) realizes `CommittedContents` at the deployed
depth — so the committed-rows route and the map-op route commit the SAME object. -/
theorem committedContents_automaton (hash : List ℤ → ℤ) (d : TableDfa Nat Nat) (tid : TableId)
    (rootE : EmittedExpr) :
    CommittedContents hash ⟨tid, 2, rootE, MAP_TREE_DEPTH⟩
      (MapMerkleRoot.mapRoot hash MAP_TREE_DEPTH (autoHeap d))
      (committedTrace tid (autoHeap d)) :=
  committedContents_inhabited hash tid MAP_TREE_DEPTH rootE (autoHeap d)
    (autoHeap_sorted d) (autoHeap_length d)

/-- The automaton commitment `autoRoot` IS the root of `autoHeap` (the `irreducible` barrier hides
the body from elaboration but the equation lemma survives — nothing here ever unfolds a `2^16`-leaf
heap). -/
theorem autoRoot_eq (hash : List ℤ → ℤ) (d : TableDfa Nat Nat) :
    autoRoot hash d = MapMerkleRoot.mapRoot hash MAP_TREE_DEPTH (autoHeap d) := by
  unfold autoRoot
  rfl

/-- ⚑ **THE COMBINED NON-VACUITY**: at ONE root — the automaton's own `autoRoot` — the committed
table exists AND commits the automaton. So `lookup_replaces_mapOp`'s two hypotheses are
SIMULTANEOUSLY satisfiable, which is what keeps §3 from being a statement about an empty set. -/
theorem committed_and_commits_automaton (hash : List ℤ → ℤ) (d : TableDfa Nat Nat)
    (tid : TableId) (rootE : EmittedExpr) :
    CommittedContents hash ⟨tid, 2, rootE, MAP_TREE_DEPTH⟩ (autoRoot hash d)
        (committedTrace tid (autoHeap d))
      ∧ CommitsAutomaton hash (autoRoot hash d) d := by
  refine ⟨?_, autoRoot_commits hash d⟩
  rw [autoRoot_eq hash d]
  exact committedContents_automaton hash d tid rootE

/-- ⚑ **THE WHOLE ROUTE, FIRED END-TO-END.** Against the automaton's own commitment, a lookup hit
`[2s + y, n]` on the committed table forces `n = d.step s y`. Every hypothesis of §3 is discharged
concretely (the contents by construction, the commitment by `autoRoot_commits`); only the standing
CR floor remains. -/
theorem committed_lookup_reads_step (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (d : TableDfa Nat Nat) (tid : TableId) (rootE : EmittedExpr)
    (env : VmRowEnv) (kx nx : EmittedExpr) (s y : Nat) (hs : s < ASTATES) (hy : y < ASYM)
    (hkey : kx.eval env.loc = ((keyOf s y : Nat) : ℤ))
    (hlk : Lookup.holdsAt (committedTrace tid (autoHeap d)).tf env ⟨tid, [kx, nx]⟩) :
    nx.eval env.loc = ((d.step s y : Nat) : ℤ) := by
  obtain ⟨hc, hcom⟩ := committed_and_commits_automaton hash d tid rootE
  exact lookup_replaces_mapOp hash hCR ⟨tid, 2, rootE, MAP_TREE_DEPTH⟩ rfl (autoRoot hash d)
    d hcom (committedTrace tid (autoHeap d)) hc env kx nx s y hs hy hkey hlk

/-! ## §6 — THE COST LAW.

⚠ EVERY `#guard` below is COMPILED EVALUATION of a closed `Bool`; it proves NO `Prop`. And the
per-row permutation counts are NOT measurements of a proven object — they are counts READ OFF the
deployed AIR (`circuit/src/descriptor_ir2.rs`, `Ir2Air::MapOps` arm, `HEAP_TREE_DEPTH` loop). The
only WITNESSED descriptor costs in this area are `AttestedAutomatonEmit` §7's, standing behind
`attWit_satisfies`. -/

/-- Chip PERMUTATIONS a deployed `MapOps` READ row consumes, after the chip table's
unique-permutation dedup (`descriptor_ir2.rs` builds `chip_hist` keyed by the tuple, one row per
unique permutation with a multiplicity column): ONE leaf absorb + `MAP_TREE_DEPTH` `node8`
compressions. The AIR issues TWICE that many BUS LOOKUPS (an old-leaf and a new-leaf absorb, an
old-chain and a new-chain `node8` per level); on a READ row `old_value = value` and
`new_root = root`, so each pair is the SAME tuple and dedups to one chip row of multiplicity 2. -/
def mapOpPermsPerRow : Nat := MAP_TREE_DEPTH + 1

/-- Chip bus LOOKUPS a deployed `MapOps` read row issues (pre-dedup). -/
def mapOpLookupsPerRow : Nat := 2 * (MAP_TREE_DEPTH + 1)

-- The `AttestedAutomatonEmit` §7 headline states `MAP_TREE_DEPTH · |w|` chip rows. Read against
-- the deployed arm that is an UNDERCOUNT BY ONE PER ROW: the leaf absorb is a permutation too.
#guard mapOpPermsPerRow == 17
#guard mapOpLookupsPerRow == 34

/-- The map-op route's chip-permutation bill at word length `w` (upper bound: it ignores the
cross-row sharing of upper path nodes, which only helps this route). -/
def mapOpPerms (w : Nat) : Nat := mapOpPermsPerRow * w

/-- The committed-rows route's chip-permutation bill: the table AIR recomputes the commitment over
its OWN `E` rows ONCE — `E` leaf absorbs + `E - 1` internal nodes for a packed depth-`⌈log₂ E⌉`
tree — and each lookup is then ONE bus send, no permutation. INDEPENDENT of `w`. -/
def committedPermsPacked (E : Nat) : Nat := 2 * E - 1

/-- The same route if the commitment is kept at the DEPLOYED `MAP_TREE_DEPTH` leaf domain rather
than packed to the table's own size: `2^16` leaves recomputed in-circuit. This is the design
decision the `depth` field of `CommittedRowsDecl` carries, and it is the difference between a
5-22x win and a catastrophe. -/
def committedPermsDeployedDepth : Nat := 2 * NKEYS - 1

#guard committedPermsDeployedDepth == 131071

-- ⚑ THE CROSSOVER, at the tiny-automata sizes `TinyAutomataSatisfiable` measures. `E` is the
-- committed edge count `|Q|·|Σ|`; the reachable product spaces are 2, 6, 12, 25 at k = 1..4, so
-- E = 4, 12, 24, 50. The map-op route costs 17 permutations PER SYMBOL; the packed committed-rows
-- route costs 2E-1 ONCE.
#guard (List.map (fun E => 2 * E - 1) [4, 12, 24, 50]) == [7, 23, 47, 99]
-- word length at which the two routes tie, per k (ceil((2E-1)/17)):
#guard (List.map (fun E => (2 * E - 1 + 16) / 17) [4, 12, 24, 50]) == [1, 2, 3, 6]
-- and the ratio at the measured probe lengths, k = 4 (E = 50): map-op perms vs 99.
#guard (List.map (fun w => (mapOpPerms w, committedPermsPacked 50)) [8, 32, 60, 128])
  == [(136, 99), (544, 99), (1020, 99), (2176, 99)]

-- ⚠ AND THE OTHER POLARITY, stated so the win is not laundered: at the DEPLOYED 2^16 leaf domain
-- the committed-rows recompute is 131071 permutations and does not pay until |w| = 7711.
#guard (131071 + 16) / 17 == 7711

/-! ## §7 — WHAT BREAKS (the enumeration this file's SHAPE establishes).

That this whole denotation compiles WITHOUT touching `DescriptorIR2` is the evidence for the
Lean-side verdict: `Satisfied2` already lets a non-`exactPublicRows` table carry prover-supplied
contents (`TableDef.publicContentsFaithful` is `True` there, `PublicLookupBalanced` likewise), so
`committedRows` adds a LEG and changes no existing obligation. The enum constructor is needed only
for the WIRE TAG and the Rust dispatch. The full break list is in
`docs/DESIGN-committed-rows-semantics.md`. -/

/-! ## §8 — axiom tripwires. -/

#assert_all_clean [mem_rowsOfHeap, get_of_mem_sorted,
  committed_lookup_opens, committed_lookup_opensTo, lookup_replaces_mapOp,
  committedRoot_binds_contents, committedContents_inhabited, committedContents_automaton,
  autoRoot_eq, committed_and_commits_automaton, committed_lookup_reads_step]

end Dregg2.Circuit.Emit.CommittedRowsSemantics
