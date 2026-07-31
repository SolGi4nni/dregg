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

  * `CommittedContents hash cd R t` (§2) — the table `cd.id` carries the GRAPH of some admissible
    heap whose DEPLOYED indexed-Merkle root (`padImtRoot`, arity-3 leaves, sparse zero-padded
    occupancy) is `R`. Contents become a WITNESS pinned by a root, rather than a transcription of
    descriptor bytes.
  * `committed_lookup_opens` (§3) — THE LEVER: a lookup hit on such a table IS an `opensTo`
    opening under `R`. This is the exact primitive `MapOp.holdsAt` supplies per-row, obtained
    instead from table membership.
  * `lookup_replaces_mapOp_or_collides` (§3) — the payoff, machine-checked: the conclusion
    `AttestedAutomatonEmit.att_row_reads` gets from a `MapOp` (`next = d.step current symbol`
    against the COMMITTED automaton) is derived from a `Lookup` plus `CommittedContents`,
    consuming NO crypto floor.
  * `committedRoot_binds_contents_or_collides` (§4) — the attestation: one root, one table
    content, or a NAMED `mapRoot` collision at the pair the hypotheses hand over.
  * §5 — non-vacuity: `CommittedContents` is INHABITED (any admissible heap of at most `2^d`
    entries realizes it), and inhabited at the automaton commitment `autoHeap`/`autoRoot`
    specifically.
  * §6 — the cost law, as ARITHMETIC over the deployed AIR's permutation counts. ⚠ These are NOT
    measurements of a proven object: they are counts read off `circuit/src/descriptor_ir2.rs`'s
    `Ir2Air::MapOps` arm. Every `#guard` is compiled evaluation of a closed `Bool` and proves NO
    `Prop`. The only WITNESSED descriptor costs in this area are `AttestedAutomatonEmit` §7's,
    which stand behind `attWit_satisfies`.

## ⛑ REBOUND ONTO THE DEPLOYED COMMITMENT, 2026-07-30

Every root in this file used to be `MapMerkleRoot.mapRoot` — the arity-2 DENSE binary-Merkle fold
that `circuit/src/heap_root.rs` STOPPED COMPUTING on 2026-07-12 (`919b2b0b8d`). `DescriptorIR2`'s
`opensTo`/`writesTo` were moved onto `DeployedMapDenotation.padImtSchema MAP_SENTINEL` — arity-3
IMT leaves `hash[addr, value, next_addr]`, the `relink_next_addrs` pointers with the terminal one
pinned to `SENTINEL_MAX = 2013265920`, sparse occupancy `length ≤ 2 ^ depth`, zero padding — so
`committed_lookup_opensTo`'s claim ("a lookup hit on a committed table IS the same relation the
map-ops table realizes") became UNPROVABLE, and with it §3's whole premise. It is now literally
true again because `CommittedContents` commits the object the prover commits.

Three hypothesis shapes changed with it, and each names a deployed fact rather than a proof
convenience:

  * `h.length = 2 ^ depth` became `≤` — the deployed tree is SPARSE (`CanonicalHeapTree::new`
    commits one live leaf in a `2^16` tree). This ADMITS MORE heaps, so §5's non-vacuity got
    stronger, not narrower.
  * a new `∀ x ∈ Heap.keys h, x < MAP_SENTINEL` conjunct — the terminal-sentinel bound
    `relink_next_addrs` refuses to violate; it is the other half of the deployed schema's `HeapOk`.
  * the table view stays `[key, value]` at arity 2 even though the committed LEAF is arity 3.
    That is sound rather than sloppy: `imtChainOf` is a FUNCTION of the sorted heap, so the
    pointer column carries no committed datum the `(key, value)` graph does not already determine.

## The felt-width wound is INHERITED, not repaired — but it is no longer LAUNDERED

⚑ NOTHING HERE CONSUMES A CRYPTO FLOOR (2026-07-25, and still true after the rebinding). The three
binding results shipped with `Poseidon2SpongeCR hash` binders, which this tree PROVES FALSE at the
deployed BabyBear codomain (p ≈ 2^31, ~2^15.5 birthday work) — so at deployed parameters they were
VACUOUS: true, and saying nothing about anything that ships. They are stated in the `…_or_collides`
idiom (§2b): the binding half is UNCONDITIONAL and the residual is a NAMED root collision at the
pair the hypotheses themselves supply.

⚠ **AND THE CANARY GOT HONESTLY WEAKER, 2026-07-30.** `mapRootColl1_refutes_sponge` used to say
that exhibiting the residual REFUTES `Poseidon2SpongeCR` outright. At the deployed commitment that
is FALSE, and it is not a Lean defect: the padding constant is the literal `BabyBear::ZERO`, so
`PadGhost3` — a live arity-3 leaf digest equal to that literal — is a FIXED-TARGET PREIMAGE, which
collision-resistance does not exclude. Two distinct heaps can therefore share a `padImtRoot` under
a perfectly injective hash. `padImtRootColl_refutes_injective_and_padFree` says exactly what is
true: exhibiting the residual refutes `Function.Injective hash ∧ PadFree3 hash` — which IS
`mapTeeth.Good`, the deployed schema's own anti-laundering predicate. Closing the gap between the
two is a change to `heap_root.rs` (pad with a domain-separated digest), not to this file.

The WOUND is unchanged and is now visible in the statements rather than hidden in a false
hypothesis: at 1 felt the residual costs ~2^15.5, so "binds" honestly reads "binds unless the
prover pays ~2^15.5". A `committedRows` root would be the SAME kind of felt and would need the
SAME 8-felt weld `AttestedAutomatonWeld8` applies to the attestation root. This file does not
improve that and does not claim to.

⚠ AND THE LARGER SCOPE LIMIT, stated where it cannot be missed: `committedRows` is NOT a
`RowSemantics` constructor. The whole denotation here rides a SHADOW declaration, so no descriptor
can emit it and none of this binds anything deployed today. It is a design/scoping result about
what the constructor WOULD buy and what it WOULD cost (§6, §7) — not a property of the shipping
system. Removing the false floor makes the design argument non-vacuous; it does not make it
deployed.

## Axiom hygiene

`#assert_all_clean` on every theorem (§8). NEW file; imports are read-only.

⚠ **CORRECTED 2026-07-25.** This paragraph used to say the module was "deliberately NOT registered
in `Dregg2.lean` (a design/scoping leaf, like `DfaRoutingSubsetTableCost`)". That was FALSE in the
very commit that wrote it: `915437862f` rooted this module at `Dregg2.lean:1523` (and
`AttestedAutomatonWeld8` at :1522). The distinction is not bookkeeping — a rooted module is IN the
accrual gate's environment, so this file's three `Poseidon2SpongeCR` carriers failed
`#floor_ratchet` and turned `lake build Dregg2` RED FOR EVERY LANE until they were ported. A leaf
that is actually rooted is a leaf whose vacuity is everyone's build error. If you re-scope this
file, change the import list and this line TOGETHER.
-/
import Dregg2.Circuit.Emit.AttestedAutomatonEmit

namespace Dregg2.Circuit.Emit.CommittedRowsSemantics

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.DeployedMapDenotation (padImtRoot padImtSchema opensToMerkleS PadFree3)
open Dregg2.Substrate
open Dregg2.Crypto.DfaAcceptanceAir (TableDfa)
open Dregg2.Circuit.Emit.AttestedAutomatonEmit

set_option autoImplicit false

/-! ## §1 — heap ⇄ table: the row encoding, and the uniqueness a sorted spine buys. -/

/-- The arity-2 table view of a sorted map: one row `[key, value]` per entry, in key order. This
is the shape a `committedRows` table would carry for a `(key, value)` commitment; a wider arity
would pack the value block, which changes nothing below.

⚑ It stays arity 2 even though the DEPLOYED committed leaf is arity 3
(`hash[addr, value, next_addr]`): `DeployedMapDenotation.imtChainOf` derives every `next_addr` from
the sorted heap, so the pointer is a FUNCTION of this table and declaring it would commit nothing
new. -/
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
  /-- The committed indexed-Merkle depth (the leaf domain is `2 ^ depth`; occupancy is SPARSE). -/
  depth : Nat

/-- **THE FAITHFULNESS LEG** that replaces `TableDef.publicContentsFaithful` for a committed
table: the table's contents are not the descriptor's bytes but the graph of SOME heap admissible
under the DEPLOYED schema (sorted, all keys below the terminal sentinel, at most `2^depth`
entries) whose deployed indexed-Merkle root `padImtRoot` is `R`. Contents are a WITNESS; the root
pins them.

⛑ REBOUND 2026-07-30 off `MapMerkleRoot.mapRoot` (arity-2, dense) onto the commitment
`heap_root.rs` actually computes — see the header. -/
def CommittedContents (hash : List ℤ → ℤ) (cd : CommittedRowsDecl) (R : ℤ) (t : VmTrace) : Prop :=
  ∃ h : Heap.FeltHeap, Heap.SortedKeys h ∧ (∀ x ∈ Heap.keys h, x < MAP_SENTINEL)
    ∧ h.length ≤ 2 ^ cd.depth
    ∧ padImtRoot MAP_SENTINEL hash cd.depth h = R ∧ t.tf cd.id = rowsOfHeap h

/-! ## §2b — ⚑ THE WITNESS-EXPLICIT FORMS AND THE NAMED RESIDUAL.

The binding results below (§3, §4) used to consume `Poseidon2SpongeCR hash`, which this tree PROVES
FALSE at the deployed BabyBear codomain — so at deployed parameters they said nothing. They are now
stated in the `…_or_collides` idiom `MapMerkleRoot` §5b exports and `AttestedAutomatonWeld8` §2 uses:
BIND, or exhibit a collision at a pair the hypotheses THEMSELVES name. No crypto hypothesis is
consumed anywhere in this file.

⚑ **WHY THE WITNESS IS EXPLICIT.** Exactly the reason `AttestedAutomatonWeld8.CommitsAutomaton8By`
gives, and the same reason `DeployedMapDenotation` §6 hoists the residual to `Exists.choose` rather
than quantifying: the residual must be about the SPECIFIC heaps the openings supply. Restating it
existentially — `∃ a b, a ≠ b ∧ padImtRoot a = padImtRoot b` — would be a FREE PASS, because at
deployed parameters that existential is simply TRUE by pigeonhole (`2^16` felt-valued leaves into one
BabyBear felt), so the disjunction would discharge itself through the right branch and prove nothing.
That is the trap `MapMerkleRoot` §5b.E refuses and `DeployedMapDenotation` §6's own ⚠ names. -/

/-- **`CommittedContentsBy hash cd R t m`** — `CommittedContents` with the witnessing heap NAMED:
`m` IS the table's contents and IS the heap behind the root `R`. -/
def CommittedContentsBy (hash : List ℤ → ℤ) (cd : CommittedRowsDecl) (R : ℤ) (t : VmTrace)
    (m : Heap.FeltHeap) : Prop :=
  Heap.SortedKeys m ∧ (∀ x ∈ Heap.keys m, x < MAP_SENTINEL)
    ∧ m.length ≤ 2 ^ cd.depth
    ∧ padImtRoot MAP_SENTINEL hash cd.depth m = R ∧ t.tf cd.id = rowsOfHeap m

/-- The existential form, for consumers that never see the heap (e.g. `Satisfied2Committed`). -/
theorem CommittedContentsBy.contents {hash : List ℤ → ℤ} {cd : CommittedRowsDecl} {R : ℤ}
    {t : VmTrace} {m : Heap.FeltHeap} (h : CommittedContentsBy hash cd R t m) :
    CommittedContents hash cd R t :=
  ⟨m, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- …and back: the two forms carry the same information, so nothing downstream is narrowed. -/
theorem CommittedContents.exists_by {hash : List ℤ → ℤ} {cd : CommittedRowsDecl} {R : ℤ}
    {t : VmTrace} (h : CommittedContents hash cd R t) :
    ∃ m : Heap.FeltHeap, CommittedContentsBy hash cd R t m := h

/-- **`PadImtRootColl hash d m₁ m₂`** — the residual, at the 1-felt DEPLOYED indexed-Merkle root
this prototype commits with: the two heaps the hypotheses hand over are DISTINCT yet publish the
SAME depth-`d` `padImtRoot`. It is about THAT pair — the extractor is the hypotheses' own witnesses,
hence total — and it is a genuine equivocation of the deployed commitment, not a pigeonhole free
pass.

⛑ REBOUND 2026-07-30 from `MapRootColl1`, which named a collision of the retired arity-2 dense fold
`heap_root.rs` no longer computes. -/
def PadImtRootColl (hash : List ℤ → ℤ) (d : Nat) (m₁ m₂ : Heap.FeltHeap) : Prop :=
  m₁ ≠ m₂ ∧ padImtRoot MAP_SENTINEL hash d m₁ = padImtRoot MAP_SENTINEL hash d m₂

/-- ⚑ **THE RESIDUAL IS NOT A FREE PASS — TAKING IT REFUTES THE DEPLOYED SCHEMA'S `Good`.**

This is the canary, and deliberately in the STRONGER of the two available spellings. The usual
`…_refutable_of_injective` form ASSUMES injectivity to empty the disjunct, which makes it a carrier
of a hypothesis BabyBear refutes. This instead says: a prover who exhibits the collides branch has
thereby produced a COUNTEREXAMPLE to `mapTeeth.Good` — the exact predicate
`DeployedMapDenotation.padImtTeeth` requires its residual to vanish at. It assumes no floor and
concludes a floor's negation, so it is anti-floor content; the accrual gate exempts it by
construction rather than by grandfathering.

⚠ **THIS IS WEAKER THAN THE `mapRootColl1_refutes_sponge` IT REPLACES, AND THAT IS THE TRUTH
RATHER THAN A GREEN.** That statement concluded `¬ Poseidon2SpongeCR hash` — collision-resistance
ALONE. At the deployed commitment it would be FALSE: `heap_root.rs` pads with the literal
`BabyBear::ZERO`, so a live arity-3 leaf digesting to that literal (`PadGhost3`) makes two distinct
heaps share a root under a perfectly injective hash. Pad-freeness is a FIXED-TARGET PREIMAGE
property that no amount of collision-resistance supplies, so the honest conclusion is the
conjunction. Getting back to the one-conjunct form is a `heap_root.rs` change (domain-separated
padding), not a Lean one.

Contrapositively it still delivers everything the `_of_injective` bridge did: at a `Good` hash the
residual is impossible, so every disjunction below collapses to its binding half. ⚑ That direction
is DELIBERATELY NOT given a name here. A `theorem … (hgood : mapTeeth.Good hash) : ¬ PadImtRootColl …`
would be a new declaration whose BINDER is `Function.Injective hash ∧ PadFree3 hash` — a fresh
carrier of the refuted floor, which is what `#floor_ratchet` exists to red on and what the
"migrate the vacuity to a new address" failure looks like. The contrapositive is one `fun hc => …`
at the use site and needs no export. -/
theorem padImtRootColl_refutes_injective_and_padFree (hash : List ℤ → ℤ) (d : Nat)
    {m₁ m₂ : Heap.FeltHeap} (hlen₁ : m₁.length ≤ 2 ^ d) (hlen₂ : m₂.length ≤ 2 ^ d)
    (hc : PadImtRootColl hash d m₁ m₂) :
    ¬ (Function.Injective hash ∧ PadFree3 hash) := by
  rintro ⟨hinj, hpf⟩
  rcases DeployedMapDenotation.padImtRoot_binds_or_ghost_or_collides MAP_SENTINEL hash d
      hlen₁ hlen₂ hc.2 with heq | hg₁ | hg₂ | hcc
  · exact hc.1 heq
  · exact DeployedMapDenotation.padGhost3_refuted hpf MAP_SENTINEL m₁ hg₁
  · exact DeployedMapDenotation.padGhost3_refuted hpf MAP_SENTINEL m₂ hg₂
  · exact hcc.1 (hinj hcc.2)

/-- **`CommitsAutomatonBy hash m R d`** — the witness-explicit twin of
`AttestedAutomatonEmit.CommitsAutomaton`, for the same reason: the residual names the heaps. -/
def CommitsAutomatonBy (hash : List ℤ → ℤ) (m : Heap.FeltHeap) (R : ℤ)
    (d : TableDfa Nat Nat) : Prop :=
  Heap.SortedKeys m ∧ (∀ x ∈ Heap.keys m, x < MAP_SENTINEL)
    ∧ m.length ≤ 2 ^ MAP_TREE_DEPTH
    ∧ padImtRoot MAP_SENTINEL hash MAP_TREE_DEPTH m = R
    ∧ ∀ s y : Nat, s < ASTATES → y < ASYM →
        Heap.get m ((keyOf s y : Nat) : ℤ) = some ((d.step s y : Nat) : ℤ)

/-- The opening-level form, for consumers that never see the heap.

⚠ TRANSPORT, never an anonymous constructor. The old body `⟨m, h.1, …⟩` built the opening AT the
deployed depth, which whnf's the goal into `perfectRoot hash 16 _`, splits the symbolic leaf vector
and dies at the heartbeat limit. `AttestedAutomatonEmit.opensToPadImt` discharges the constructor at
a GENERIC depth; this only APPLIES it. -/
theorem CommitsAutomatonBy.commits {hash : List ℤ → ℤ} {m : Heap.FeltHeap} {R : ℤ}
    {d : TableDfa Nat Nat} (h : CommitsAutomatonBy hash m R d) : CommitsAutomaton hash R d :=
  fun s y hs hy =>
    opensToPadImt MAP_SENTINEL hash MAP_TREE_DEPTH m h.1 h.2.1 h.2.2.1 h.2.2.2.1
      (h.2.2.2.2 s y hs hy)

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
contents are committed by `R`, then any row `[k, v]` of it is a genuine DEPLOYED indexed-Merkle
opening of `R` at `k`. This is the primitive `MapOp.holdsAt` supplies PER ROW, obtained here from
ONE table membership — the whole point of the extension.

⚠ Stated at the DECLARED depth `cd.depth`, which is a variable — see `committed_lookup_opensTo` for
the transport to the deployed 16. -/
theorem committed_lookup_opens (hash : List ℤ → ℤ) (cd : CommittedRowsDecl) (R : ℤ) (t : VmTrace)
    (hc : CommittedContents hash cd R t) {k v : ℤ} (hmem : [k, v] ∈ t.tf cd.id) :
    opensToMerkleS (padImtSchema MAP_SENTINEL) hash cd.depth R k (some v) := by
  obtain ⟨h, hs, hb, hlen, hroot, htf⟩ := hc
  rw [htf] at hmem
  exact opensToPadImt MAP_SENTINEL hash cd.depth h hs hb hlen hroot
    (get_of_mem_sorted h k v hs (mem_rowsOfHeap hmem))

/-- At the DEPLOYED depth the opening is literally `DescriptorIR2.opensTo` — the same relation the
map-ops table realizes, so the two routes are interchangeable at the soundness interface. -/
theorem committed_lookup_opensTo (hash : List ℤ → ℤ) (cd : CommittedRowsDecl)
    (hd : cd.depth = MAP_TREE_DEPTH) (R : ℤ) (t : VmTrace)
    (hc : CommittedContents hash cd R t) {k v : ℤ} (hmem : [k, v] ∈ t.tf cd.id) :
    opensTo hash R k (some v) := by
  have h := committed_lookup_opens hash cd R t hc hmem
  rw [hd] at h
  exact h

/-- The lever in witness-explicit form: a row of a committed table is an entry of the WITNESSING
heap. No existential is opened, so the heap stays nameable in a residual. -/
theorem committed_lookup_getBy (hash : List ℤ → ℤ) (cd : CommittedRowsDecl) (R : ℤ) (t : VmTrace)
    {m : Heap.FeltHeap} (hc : CommittedContentsBy hash cd R t m) {k v : ℤ}
    (hmem : [k, v] ∈ t.tf cd.id) : Heap.get m k = some v := by
  rw [hc.2.2.2.2] at hmem
  exact get_of_mem_sorted m k v hc.1 (mem_rowsOfHeap hmem)

/-- ⚑ **`lookup_replaces_mapOp_or_collides` — THE PAYOFF, machine-checked, UNCONDITIONAL.** The
conclusion `AttestedAutomatonEmit.att_row_reads` extracts from a per-row `MapOp` — the row's `next`
IS the COMMITTED automaton's step, not merely some declared edge — is derived here from a `Lookup`
against a `committedRows` table, consuming NO crypto hypothesis: either the lookup reads the
committed step, or the committed table and the committed automaton are behind ONE root while being
DIFFERENT heaps, which `padImtRootColl_refutes_injective_and_padFree` shows refutes the deployed
schema's `Good`. So the attestation the map-op route buys is available in lookup shape; §6 is where
the prices differ.

(Replaces the `Poseidon2SpongeCR`-consuming `lookup_replaces_mapOp`, which was VACUOUS at deployed
BabyBear parameters. The old statement is the good-hash special case, recovered in one line from
this one plus the canary — see §4's note.) -/
theorem lookup_replaces_mapOp_or_collides (hash : List ℤ → ℤ)
    (cd : CommittedRowsDecl) (hd : cd.depth = MAP_TREE_DEPTH) (R : ℤ)
    (d : TableDfa Nat Nat) {mc ma : Heap.FeltHeap} (hcommit : CommitsAutomatonBy hash ma R d)
    (t : VmTrace) (hc : CommittedContentsBy hash cd R t mc)
    (env : VmRowEnv) (kx nx : EmittedExpr) (s y : Nat) (hs : s < ASTATES) (hy : y < ASYM)
    (hkey : kx.eval env.loc = ((keyOf s y : Nat) : ℤ))
    (hlk : Lookup.holdsAt t.tf env ⟨cd.id, [kx, nx]⟩) :
    nx.eval env.loc = ((d.step s y : Nat) : ℤ) ∨ PadImtRootColl hash MAP_TREE_DEPTH mc ma := by
  have hmem : [kx.eval env.loc, nx.eval env.loc] ∈ t.tf cd.id := by
    simpa [Lookup.holdsAt] using hlk
  rw [hkey] at hmem
  by_cases hne : mc = ma
  · subst hne
    refine Or.inl ?_
    have g₁ := committed_lookup_getBy hash cd R t hc hmem
    have g₂ := hcommit.2.2.2.2 s y hs hy
    rw [g₁] at g₂
    simpa using g₂
  · refine Or.inr ⟨hne, ?_⟩
    rw [← hd, hc.2.2.2.1, hd, hcommit.2.2.2.1]

/-! ## §4 — ⚑ THE ATTESTATION: one root, one table content. -/

/-- **`committedRoot_binds_contents_or_collides`** — the analog of `root_binds_automaton` at the
table level, UNCONDITIONAL. Two committed tables published under the SAME root agree at every key
they both carry, OR the two witnessing heaps are distinct behind one root — a named `padImtRoot`
equivocation, which `padImtRootColl_refutes_injective_and_padFree` turns into a refutation of the
deployed schema's `Good`. A root determines the table's contents: precisely what `exactPublicRows`
gets from the descriptor bytes, obtained instead from ONE felt.

⚠ THE FELT WIDTH IS STILL THE WOUND, and the disjunction is where it now shows. At the deployed
BabyBear codomain a root collision costs ~2^15.5 work, so the right disjunct is REACHABLE for a
real adversary — the honest reading is "binds, unless the prover pays ~2^15.5", not "binds". That
is the same ~31-bit scalar `AttestedAutomatonWeld8` welds to 8 felts, and a real `committedRows`
root would need the SAME weld. What changed is that the price is now VISIBLE in the statement
instead of hidden inside a hypothesis that is false.

⚠ AND THE OTHER HALF OF THE PRICE, since 2026-07-30: the right disjunct is also reachable with NO
work at all if a live arity-3 leaf digests to the literal zero the deployed tree pads with
(`PadGhost3`). That is a `heap_root.rs` property, not a hash-strength one.

(Replaces the `Poseidon2SpongeCR`-consuming `committedRoot_binds_contents`.) -/
theorem committedRoot_binds_contents_or_collides (hash : List ℤ → ℤ)
    (cd₁ cd₂ : CommittedRowsDecl) (hdep : cd₂.depth = cd₁.depth) (R : ℤ) (t₁ t₂ : VmTrace)
    {m₁ m₂ : Heap.FeltHeap}
    (h₁ : CommittedContentsBy hash cd₁ R t₁ m₁) (h₂ : CommittedContentsBy hash cd₂ R t₂ m₂)
    {k v₁ v₂ : ℤ} (mem₁ : [k, v₁] ∈ t₁.tf cd₁.id) (mem₂ : [k, v₂] ∈ t₂.tf cd₂.id) :
    v₁ = v₂ ∨ PadImtRootColl hash cd₁.depth m₁ m₂ := by
  by_cases hne : m₁ = m₂
  · subst hne
    refine Or.inl ?_
    have g₁ := committed_lookup_getBy hash cd₁ R t₁ h₁ mem₁
    have g₂ := committed_lookup_getBy hash cd₂ R t₂ h₂ mem₂
    rw [g₁] at g₂
    simpa using g₂
  · refine Or.inr ⟨hne, ?_⟩
    rw [h₁.2.2.2.1, ← hdep, h₂.2.2.2.1]

/-! ## §5 — NON-VACUITY: the predicate is inhabited, and inhabited AT the automaton commitment. -/

/-- The single-table witness family: the declared table carries the heap's graph, every other
table empty. -/
def committedTrace (tid : TableId) (h : Heap.FeltHeap) : VmTrace :=
  { rows := [], pub := zeroAsg, tf := fun id => if id = tid then rowsOfHeap h else [] }

/-- ⚑ **`CommittedContents` is INHABITED for EVERY admissible heap of at most `2^dep` entries** —
the predicate is a construction, not a wish (the same discipline `autoRoot_commits` holds
`CommitsAutomaton` to). The occupancy hypothesis is `≤`, matching the deployed sparse tree, so this
admits STRICTLY MORE witnesses than the dense `= 2 ^ dep` form it replaces.

⚠ GENERIC `dep`: the deployed instances below TRANSPORT this by application. -/
theorem committedContents_inhabited (hash : List ℤ → ℤ) (tid : TableId) (dep : Nat)
    (rootE : EmittedExpr) (h : Heap.FeltHeap)
    (hs : Heap.SortedKeys h) (hb : ∀ x ∈ Heap.keys h, x < MAP_SENTINEL)
    (hlen : h.length ≤ 2 ^ dep) :
    CommittedContents hash ⟨tid, 2, rootE, dep⟩
      (padImtRoot MAP_SENTINEL hash dep h) (committedTrace tid h) :=
  ⟨h, hs, hb, hlen, rfl, by simp [committedTrace]⟩

/-- ⚑ **Inhabited AT the automaton commitment.** The very heap `AttestedAutomatonEmit` commits
(`autoHeap d`, total over the deployed `2^16` leaves) realizes `CommittedContents` at the deployed
depth — so the committed-rows route and the map-op route commit the SAME object. -/
theorem committedContents_automaton (hash : List ℤ → ℤ) (d : TableDfa Nat Nat) (tid : TableId)
    (rootE : EmittedExpr) :
    CommittedContents hash ⟨tid, 2, rootE, MAP_TREE_DEPTH⟩
      (padImtRoot MAP_SENTINEL hash MAP_TREE_DEPTH (autoHeap d))
      (committedTrace tid (autoHeap d)) :=
  committedContents_inhabited hash tid MAP_TREE_DEPTH rootE (autoHeap d)
    (autoHeap_sorted d) (autoHeap_keys_lt d) (le_of_eq (autoHeap_length d))

/-- The automaton commitment `autoRoot` IS the DEPLOYED padded arity-3 root of `autoHeap` (the
`irreducible` barrier hides the body from elaboration but the equation lemma survives — nothing here
ever unfolds a `2^16`-leaf heap). -/
theorem autoRoot_eq (hash : List ℤ → ℤ) (d : TableDfa Nat Nat) :
    autoRoot hash d = padImtRoot MAP_SENTINEL hash MAP_TREE_DEPTH (autoHeap d) := by
  unfold autoRoot
  exact rfl

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

/-- The declared-key reads of the committed heap, standalone (the fact `autoRoot_commits` proves
inline). Needed to give the automaton commitment its witness-explicit form. -/
theorem autoHeap_get (d : TableDfa Nat Nat) (s y : Nat) (hs : s < ASTATES) (hy : y < ASYM) :
    Heap.get (autoHeap d) ((keyOf s y : Nat) : ℤ) = some ((d.step s y : Nat) : ℤ) := by
  have hy2 : y < 2 := by simpa [ASYM] using hy
  have hk : keyOf s y < 0 + NKEYS := by
    have h1 : s < 32768 := by simpa [ASTATES] using hs
    show keyOf s y < 0 + 65536
    unfold keyOf
    omega
  have hget := kvRows_get (fun j => ((d.step (j / 2) (j % 2) : Nat) : ℤ)) NKEYS 0 (keyOf s y)
    (Nat.zero_le _) hk
  unfold autoHeap
  rw [hget]
  have hdiv : keyOf s y / 2 = s := by unfold keyOf; omega
  have hmod : keyOf s y % 2 = y := by unfold keyOf; omega
  show some ((d.step (keyOf s y / 2) (keyOf s y % 2) : Nat) : ℤ) = some ((d.step s y : Nat) : ℤ)
  rw [hdiv, hmod]

/-- ⚑ **The automaton commitment, WITNESS-EXPLICIT** — `autoRoot` is a commitment of `d` and
`autoHeap d` is the heap that realizes it. CONSTRUCTED; consumes no crypto hypothesis. -/
theorem autoRoot_commitsBy (hash : List ℤ → ℤ) (d : TableDfa Nat Nat) :
    CommitsAutomatonBy hash (autoHeap d) (autoRoot hash d) d :=
  ⟨autoHeap_sorted d, autoHeap_keys_lt d, le_of_eq (autoHeap_length d),
    (autoRoot_eq hash d).symm, autoHeap_get d⟩

/-- The committed table, witness-explicit, at the automaton's own heap. -/
theorem committedContents_automatonBy (hash : List ℤ → ℤ) (d : TableDfa Nat Nat) (tid : TableId)
    (rootE : EmittedExpr) :
    CommittedContentsBy hash ⟨tid, 2, rootE, MAP_TREE_DEPTH⟩ (autoRoot hash d)
      (committedTrace tid (autoHeap d)) (autoHeap d) :=
  ⟨autoHeap_sorted d, autoHeap_keys_lt d, le_of_eq (autoHeap_length d),
    (autoRoot_eq hash d).symm, by simp [committedTrace]⟩

/-- ⚑ **THE WHOLE ROUTE, FIRED END-TO-END — UNCONDITIONALLY, AND WITH NO RESIDUAL AT ALL.**
Against the automaton's own commitment, a lookup hit `[2s + y, n]` on the committed table forces
`n = d.step s y`. Every hypothesis of §3 is discharged concretely, and the collision disjunct is
not merely refutable here but IMPOSSIBLE BY CONSTRUCTION: the committed table and the committed
automaton are the SAME heap `autoHeap d`, so `PadImtRootColl` would assert `autoHeap d ≠ autoHeap d`.

⚑ Note what this does and does not say. It is a statement about the route — the lookup shape
carries the same conclusion the `MapOp` shape carries — proven with NO crypto floor, so it is not
vacuous at deployed parameters the way its `Poseidon2SpongeCR`-consuming predecessor was. It is
still a statement about a SHADOW declaration: `committedRows` is not a `RowSemantics` constructor,
so no descriptor emits it and this binds nothing that ships today. §7 is the honest scope. -/
theorem committed_lookup_reads_step_unconditional (hash : List ℤ → ℤ)
    (d : TableDfa Nat Nat) (tid : TableId) (rootE : EmittedExpr)
    (env : VmRowEnv) (kx nx : EmittedExpr) (s y : Nat) (hs : s < ASTATES) (hy : y < ASYM)
    (hkey : kx.eval env.loc = ((keyOf s y : Nat) : ℤ))
    (hlk : Lookup.holdsAt (committedTrace tid (autoHeap d)).tf env ⟨tid, [kx, nx]⟩) :
    nx.eval env.loc = ((d.step s y : Nat) : ℤ) := by
  rcases lookup_replaces_mapOp_or_collides hash ⟨tid, 2, rootE, MAP_TREE_DEPTH⟩ rfl
      (autoRoot hash d) d (autoRoot_commitsBy hash d) (committedTrace tid (autoHeap d))
      (committedContents_automatonBy hash d tid rootE) env kx nx s y hs hy hkey hlk with h | hcoll
  · exact h
  · exact absurd rfl hcoll.1

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
tree — and each lookup is then ONE bus send, no permutation. INDEPENDENT of `w`.

(The arity-3 rebinding does not move this count: the leaf absorb is one permutation whether the
preimage is `[key, value]` or `[addr, value, next_addr]`, and the deployed relink derives the third
felt from the sorted table rather than committing a column for it.) -/
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
  committed_lookup_opens, committed_lookup_opensTo, committed_lookup_getBy,
  lookup_replaces_mapOp_or_collides, committedRoot_binds_contents_or_collides,
  padImtRootColl_refutes_injective_and_padFree,
  CommittedContentsBy.contents, CommitsAutomatonBy.commits,
  committedContents_inhabited, committedContents_automaton, committedContents_automatonBy,
  autoRoot_eq, autoHeap_get, autoRoot_commitsBy, committed_and_commits_automaton,
  committed_lookup_reads_step_unconditional]

end Dregg2.Circuit.Emit.CommittedRowsSemantics
