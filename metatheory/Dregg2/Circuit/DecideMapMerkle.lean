/-
# Dregg2.Circuit.DecideMapMerkle — the CONCRETE map-op decider, at the DEPLOYED map commitment.

`DecideSatisfied2.decideSatisfied2` parameterizes the `mapOp` leg by a `mapDec : VmRowEnv → MapOp →
Bool` together with a faithfulness HYPOTHESIS `hmapDec : ∀ env m, mapDec env m = true ↔ m.holdsAt hash
env`. That hypothesis was the LAST assumed-faithful parameter in the Lean half of the faithfulness
bridge — the spike flagged the `mapOp` arm as the only non-`Decidable` leg of `Satisfied2`, because
`MapOp.holdsAt` denotes an EXISTENTIAL opening of a heap (`opensTo`/`writesTo` — `∃ h : FeltHeap, …`),
and an unbounded existential is not decidable in general.

## ⚑ WHAT THIS FILE NOW DECIDES (2026-07-30 — the denotation moved under it)

Until 2026-07-30 every check below was against `MapMerkleRoot.mapRoot` — the DENSE fold of **arity-2**
`Heap.leafOf` leaves at occupancy `h.length = 2 ^ d`. `heap_root.rs` stopped computing that root on
2026-07-12 (`919b2b0b8d`), so this decider decided an object the prover never commits. It now checks
the DEPLOYED commitment, `DescriptorIR2.mapSchema = DeployedMapDenotation.padImtSchema MAP_SENTINEL`:

  * `HeapOk h` — `h` is sorted AND every key is `< MAP_SENTINEL` (the terminal `next_addr`
    `relink_next_addrs` pins the largest live leaf to, `heap_root.rs::SENTINEL_MAX`);
  * `SizeOk d h` — `h.length ≤ 2 ^ MAP_TREE_DEPTH`. ⚑ **`≤`, not `=`.** The deployed tree is SPARSE:
    `CanonicalHeapTree::new` commits a live PREFIX inside a `2^16`-leaf tree and zero-pads above it;
  * `commit hash d h` — `padImtRoot MAP_SENTINEL`: the deployed relink, the arity-3 leaf digest
    `hash [addr, value, next_addr]` (`HeapLeaf::preimage`, `HEAP_LEAF_ARITY = 3`), folded over the
    zero-padded `2^16` vector.

Every one of those is still decidable (`SortedKeys` = `Pairwise (· < ·)` over ℤ; the key bound is a
`List.decidableBAll`; `length`, `padImtRoot`, `Heap.get`/`Heap.set` are computable; `Option ℤ` has
`DecidableEq`), so a concrete `mapDecMerkle` still exists — the shape of the check changed, not its
decidability.

⚑ **The depth-16 whnf discipline.** `MAP_TREE_DEPTH` reduces to `16`, and any tactic that whnf's a
goal containing `padImtRoot … MAP_TREE_DEPTH …` dives into `perfectRoot hash 16 _` and splits the
symbolic leaf vector until the heartbeat limit. So every introduction / elimination / binding step is
proved ONCE at a GENERIC depth `d` (§2) and TRANSPORTED to `MAP_TREE_DEPTH` by application. Same
discipline as `DeployedMapDenotation.padImt_opens_none_of_gap`. Do not "fix" a heartbeat here by
raising `maxHeartbeats`.

## The two directions of faithfulness, and what each costs now

  * **soundness** (`mapDecMerkle = true → holdsAt`): UNCONDITIONAL, as before — the SUPPLIED heap
    WITNESSES the existential, because the checked conjuncts ARE the body of
    `opensToMerkleS`/`writesToMerkleS` at the deployed schema. No floor, no residual, no supply
    well-formedness.
  * **completeness** (`holdsAt → mapDecMerkle = true`): the supply must be a genuine opening of the
    column root (`WitnessOpens`, decidable, the prover published it), AND the two heaps — the
    supplied one and the one the denotation's existential carries — must be forced equal by their
    shared root.

⚑ **THE BINDING STEP LOST ITS FLOOR AND GAINED A NAMED RESIDUAL, AND THAT IS AN IMPROVEMENT.** The
old proof used `mapRoot_injective` under `hCR : Poseidon2SpongeCR hash` — a hypothesis this tree
PROVES FALSE at deployed BabyBear parameters
(`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`; `Poseidon2SpongeCR f` is definitionally
`Function.Injective f`). `mapDecMerkle_complete`, `mapDecMerkle_faithful`,
`decideSatisfied2'_iff_Satisfied2` and `instDecidableSatisfied2'` were therefore VACUOUS, and all four
are carried in `Verify/FloorRatchetBaseline` as grandfathered refuted-floor carriers.

They no longer take that floor, or any hypothesis on `hash`. The deployed schema's binding
(`padImtRoot_binds_or_ghost_or_collides`) is floor-free with a NAMED per-instance residual, so
completeness is stated against `SupplyResid` — "some admissible heap of the SAME committed root
carries the schema's residual against the supplied one", i.e. a live arity-3 leaf digest equal to the
padding constant (`PadGhost3`, a DEPLOYED wound: the padding is the literal `BabyBear::ZERO`), or a
genuine sponge collision at the ONE pair `padImtRootFind` returns. `SupplyResid` is:

  * REFUTABLE, at an inhabited instance and with no floor binder anywhere in the statement —
    `supplyResid_refuted_at_oddSponge`; and
  * REACHABLE, so it is not accidentally empty — `mapResid_reachable`.

## What remains (the precise residual, named honestly)

`WitnessOpens` is the prover's OBLIGATION about openings it published — a decidable well-formedness
fact, not a free oracle and not an axiom. `SupplyResid` is a per-instance, per-commitment residual,
refutable and reachable, and NOT a floor. Neither is a hypothesis on `hash`, so
`decideSatisfied2'_iff_Satisfied2` is discharged on the Lean side with **no refuted floor**, which is
strictly more than it said before this file was repointed.

⚠ Not claimed here: that the deployed AIR's map-op gates FORCE these openings. The `.insert` (op=3)
pre-root and the `.aafiInsert` post layout are deployed-side obstructions proved in
`MapKindImtGates` (`insertImtGates_cannot_force_the_write_denotation`,
`no_schema_commits_the_append_order_layout`). This file decides the DENOTATION, not the gates.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. No `sorry`, no `native_decide`, and no
`decide` evaluated over any depth-16 spine — `decide` appears only inside `Bool`-valued definitions
whose kernel evaluation is never demanded by a proof here.
-/
import Dregg2.Circuit.DecideSatisfied2
import Dregg2.Circuit.MapMerkleRoot

namespace Dregg2.Circuit.DecideMapMerkle

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.DeployedMapDenotation (padImtRoot padImtSchema padImtTeeth opensToMerkleS
  writesToMerkleS padImtRoot_binds_or_ghost_or_collides PadGhost3 PadHit padDigest imtChainOf
  imtChainOf_length imtLeafHash oddSponge oddSponge_injective oddSponge_padFree3)
open Dregg2.Substrate
open Dregg2.Circuit.DecideSatisfied2

set_option autoImplicit false

/-! ## §1 — the decidability instances the `decide` legs read. -/

/-- `Heap.SortedKeys` over a concrete `FeltHeap` is decidable: it is definitionally `(keys h).Pairwise
(· < ·)`, and `<` on ℤ is decidable, so `List.Pairwise` is. -/
instance instDecidableSortedKeys (h : Heap.FeltHeap) : Decidable (Heap.SortedKeys h) := by
  unfold Heap.SortedKeys; infer_instance

/-! ## §2 — ⚑ THE GENERIC-DEPTH TRANSPORT LAYER.

Every structural step against the deployed schema is proved HERE at a variable `d`, then applied at
`MAP_TREE_DEPTH`. Stating them at `16` directly makes the elaborator descend into
`perfectRoot hash 16 _` and split the symbolic leaf vector; the four heartbeat failures this file hit
on the denotation move were exactly that. Application does not reduce, so the transport is free. -/

private theorem opensToS_intro (sent : ℤ) (hash : List ℤ → ℤ) (d : Nat)
    {h : Heap.FeltHeap} {r k : ℤ} {o : Option ℤ}
    (hs : Heap.SortedKeys h) (hb : ∀ x ∈ Heap.keys h, x < sent)
    (hlen : h.length ≤ 2 ^ d) (hr : padImtRoot sent hash d h = r) (hg : Heap.get h k = o) :
    opensToMerkleS (padImtSchema sent) hash d r k o :=
  ⟨h, ⟨hs, hb⟩, hlen, hr, hg⟩

private theorem opensToS_elim (sent : ℤ) (hash : List ℤ → ℤ) (d : Nat) {r k : ℤ} {o : Option ℤ}
    (ho : opensToMerkleS (padImtSchema sent) hash d r k o) :
    ∃ h : Heap.FeltHeap, Heap.SortedKeys h ∧ (∀ x ∈ Heap.keys h, x < sent)
      ∧ h.length ≤ 2 ^ d ∧ padImtRoot sent hash d h = r ∧ Heap.get h k = o := by
  obtain ⟨h, ⟨hs, hb⟩, hz, hr, hg⟩ := ho
  exact ⟨h, hs, hb, hz, hr, hg⟩

private theorem writesToS_intro (sent : ℤ) (hash : List ℤ → ℤ) (d : Nat)
    {h : Heap.FeltHeap} {r k v r' : ℤ}
    (hs : Heap.SortedKeys h) (hb : ∀ x ∈ Heap.keys h, x < sent)
    (hlen : h.length ≤ 2 ^ d) (hlen' : (Heap.set h k v).length ≤ 2 ^ d)
    (hr : padImtRoot sent hash d h = r)
    (hr' : r' = padImtRoot sent hash d (Heap.set h k v)) :
    writesToMerkleS (padImtSchema sent) hash d r k v r' :=
  ⟨h, ⟨hs, hb⟩, hlen, hlen', hr, hr'⟩

private theorem writesToS_elim (sent : ℤ) (hash : List ℤ → ℤ) (d : Nat) {r k v r' : ℤ}
    (hw : writesToMerkleS (padImtSchema sent) hash d r k v r') :
    ∃ h : Heap.FeltHeap, Heap.SortedKeys h ∧ (∀ x ∈ Heap.keys h, x < sent)
      ∧ h.length ≤ 2 ^ d ∧ (Heap.set h k v).length ≤ 2 ^ d
      ∧ padImtRoot sent hash d h = r ∧ r' = padImtRoot sent hash d (Heap.set h k v) := by
  obtain ⟨h, ⟨hs, hb⟩, hz, hz', hr, hr'⟩ := hw
  exact ⟨h, hs, hb, hz, hz', hr, hr'⟩

/-- The deployed schema's binding, at a generic depth: two admissible heaps with the SAME padded
arity-3 root are equal, or the schema's NAMED residual holds at that pair. **No hypothesis on
`hash`** — this is `padImtRoot_binds_or_ghost_or_collides`, not an injectivity floor. -/
private theorem heapS_eq_or_resid (sent : ℤ) (hash : List ℤ → ℤ) (d : Nat)
    {h₁ h₂ : Heap.FeltHeap} (hz₁ : h₁.length ≤ 2 ^ d) (hz₂ : h₂.length ≤ 2 ^ d)
    (he : padImtRoot sent hash d h₁ = padImtRoot sent hash d h₂) :
    h₁ = h₂ ∨ (padImtTeeth sent).Resid hash d h₁ h₂ :=
  padImtRoot_binds_or_ghost_or_collides sent hash d hz₁ hz₂ he

/-- The residual is REACHABLE at a generic depth (the `PadGhost3` disjunct at the degenerate
all-zero hash), so `SupplyResid` below is not accidentally empty. -/
private theorem residS_reachable (sent : ℤ) (d : Nat) {h : Heap.FeltHeap} (hne : h ≠ []) :
    (padImtTeeth sent).Resid (fun _ => 0) d h h := by
  refine Or.inl ?_
  show padDigest ∈ (imtChainOf sent h).map (imtLeafHash (fun _ => 0))
  have hlen : (imtChainOf sent h).length = h.length := imtChainOf_length sent h
  rcases hc : imtChainOf sent h with _ | ⟨l, ls⟩
  · rw [hc] at hlen
    exact absurd (List.eq_nil_of_length_eq_zero hlen.symm) hne
  · rw [List.mem_map]
    exact ⟨l, List.mem_cons_self, rfl⟩

/-! ### §2a — the same four steps, TRANSPORTED to the deployed instance. -/

private theorem opensTo_intro (hash : List ℤ → ℤ) {h : Heap.FeltHeap} {r k : ℤ} {o : Option ℤ}
    (hs : Heap.SortedKeys h) (hb : ∀ x ∈ Heap.keys h, x < MAP_SENTINEL)
    (hlen : h.length ≤ 2 ^ MAP_TREE_DEPTH)
    (hr : padImtRoot MAP_SENTINEL hash MAP_TREE_DEPTH h = r) (hg : Heap.get h k = o) :
    opensTo hash r k o :=
  opensToS_intro MAP_SENTINEL hash MAP_TREE_DEPTH hs hb hlen hr hg

private theorem opensTo_elim (hash : List ℤ → ℤ) {r k : ℤ} {o : Option ℤ}
    (ho : opensTo hash r k o) :
    ∃ h : Heap.FeltHeap, Heap.SortedKeys h ∧ (∀ x ∈ Heap.keys h, x < MAP_SENTINEL)
      ∧ h.length ≤ 2 ^ MAP_TREE_DEPTH
      ∧ padImtRoot MAP_SENTINEL hash MAP_TREE_DEPTH h = r ∧ Heap.get h k = o :=
  opensToS_elim MAP_SENTINEL hash MAP_TREE_DEPTH ho

private theorem writesTo_intro (hash : List ℤ → ℤ) {h : Heap.FeltHeap} {r k v r' : ℤ}
    (hs : Heap.SortedKeys h) (hb : ∀ x ∈ Heap.keys h, x < MAP_SENTINEL)
    (hlen : h.length ≤ 2 ^ MAP_TREE_DEPTH)
    (hlen' : (Heap.set h k v).length ≤ 2 ^ MAP_TREE_DEPTH)
    (hr : padImtRoot MAP_SENTINEL hash MAP_TREE_DEPTH h = r)
    (hr' : r' = padImtRoot MAP_SENTINEL hash MAP_TREE_DEPTH (Heap.set h k v)) :
    writesTo hash r k v r' :=
  writesToS_intro MAP_SENTINEL hash MAP_TREE_DEPTH hs hb hlen hlen' hr hr'

private theorem writesTo_elim (hash : List ℤ → ℤ) {r k v r' : ℤ}
    (hw : writesTo hash r k v r') :
    ∃ h : Heap.FeltHeap, Heap.SortedKeys h ∧ (∀ x ∈ Heap.keys h, x < MAP_SENTINEL)
      ∧ h.length ≤ 2 ^ MAP_TREE_DEPTH ∧ (Heap.set h k v).length ≤ 2 ^ MAP_TREE_DEPTH
      ∧ padImtRoot MAP_SENTINEL hash MAP_TREE_DEPTH h = r
      ∧ r' = padImtRoot MAP_SENTINEL hash MAP_TREE_DEPTH (Heap.set h k v) :=
  writesToS_elim MAP_SENTINEL hash MAP_TREE_DEPTH hw

private theorem heap_eq_or_resid (hash : List ℤ → ℤ) {h₁ h₂ : Heap.FeltHeap}
    (hz₁ : h₁.length ≤ 2 ^ MAP_TREE_DEPTH) (hz₂ : h₂.length ≤ 2 ^ MAP_TREE_DEPTH)
    (he : padImtRoot MAP_SENTINEL hash MAP_TREE_DEPTH h₁
        = padImtRoot MAP_SENTINEL hash MAP_TREE_DEPTH h₂) :
    h₁ = h₂ ∨ mapTeeth.Resid hash MAP_TREE_DEPTH h₁ h₂ :=
  heapS_eq_or_resid MAP_SENTINEL hash MAP_TREE_DEPTH hz₁ hz₂ he

/-- **The schema residual is REACHABLE at the deployed depth** — the anti-vacuity canary for
`SupplyResid`. At the degenerate all-zero hash EVERY live arity-3 leaf digest IS the padding
constant, so `PadGhost3` fires on any non-empty heap. A residual that could never hold would mean
completeness below was unconditional, which it is not. -/
theorem mapResid_reachable {h : Heap.FeltHeap} (hne : h ≠ []) :
    mapTeeth.Resid (fun _ => 0) MAP_TREE_DEPTH h h :=
  residS_reachable MAP_SENTINEL MAP_TREE_DEPTH hne

/-! ## §3 — the concrete decidable openings (no `∃ heap`: the supplied witness IS the heap). -/

/-- **`decOpensTo hash h r k o`** — the supplied heap `h` is an ADMISSIBLE heap of the DEPLOYED
schema (sorted, every key below the terminal sentinel, at most `2^16` live entries) whose deployed
arity-3 padded indexed-Merkle root is `r`, reading `o` at `k`. The DECIDABLE body of
`opensToMerkleS mapSchema` for the SUPPLIED heap (no existential). -/
def decOpensTo (hash : List ℤ → ℤ) (h : Heap.FeltHeap) (r k : ℤ) (o : Option ℤ) : Bool :=
  decide (Heap.SortedKeys h)
    && decide (∀ x ∈ Heap.keys h, x < MAP_SENTINEL)
    && decide (h.length ≤ 2 ^ MAP_TREE_DEPTH)
    && decide (padImtRoot MAP_SENTINEL hash MAP_TREE_DEPTH h = r)
    && decide (Heap.get h k = o)

/-- `decOpensTo` decides exactly the `opensToMerkleS mapSchema` body for the SUPPLIED heap — the
existential witnessed by `h`. -/
theorem decOpensTo_iff (hash : List ℤ → ℤ) (h : Heap.FeltHeap) (r k : ℤ) (o : Option ℤ) :
    decOpensTo hash h r k o = true
      ↔ (Heap.SortedKeys h ∧ (∀ x ∈ Heap.keys h, x < MAP_SENTINEL)
          ∧ h.length ≤ 2 ^ MAP_TREE_DEPTH
          ∧ padImtRoot MAP_SENTINEL hash MAP_TREE_DEPTH h = r ∧ Heap.get h k = o) := by
  simp only [decOpensTo, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-- **`decWritesTo hash h r k v r'`** — the supplied PRE-heap is admissible at the deployed schema
and behind the deployed root `r`, and the sorted insert-or-update of `(k, v)` still fits the tree and
produces root `r'`. The DECIDABLE body of `writesToMerkleS mapSchema` for the SUPPLIED pre-heap.

⚠ It does NOT check `HeapOk` of the POST-heap, because `writesToMerkleS` does not require it — the
deployed denotation constrains the post-state only through its size and its root. Mirroring that
exactly is the point; strengthening the check here would make the decider refuse rows the denotation
accepts. -/
def decWritesTo (hash : List ℤ → ℤ) (h : Heap.FeltHeap) (r k v r' : ℤ) : Bool :=
  decide (Heap.SortedKeys h)
    && decide (∀ x ∈ Heap.keys h, x < MAP_SENTINEL)
    && decide (h.length ≤ 2 ^ MAP_TREE_DEPTH)
    && decide ((Heap.set h k v).length ≤ 2 ^ MAP_TREE_DEPTH)
    && decide (padImtRoot MAP_SENTINEL hash MAP_TREE_DEPTH h = r)
    && decide (r' = padImtRoot MAP_SENTINEL hash MAP_TREE_DEPTH (Heap.set h k v))

/-- `decWritesTo` decides exactly the `writesToMerkleS mapSchema` body for the SUPPLIED pre-heap. -/
theorem decWritesTo_iff (hash : List ℤ → ℤ) (h : Heap.FeltHeap) (r k v r' : ℤ) :
    decWritesTo hash h r k v r' = true
      ↔ (Heap.SortedKeys h ∧ (∀ x ∈ Heap.keys h, x < MAP_SENTINEL)
          ∧ h.length ≤ 2 ^ MAP_TREE_DEPTH
          ∧ (Heap.set h k v).length ≤ 2 ^ MAP_TREE_DEPTH
          ∧ padImtRoot MAP_SENTINEL hash MAP_TREE_DEPTH h = r
          ∧ r' = padImtRoot MAP_SENTINEL hash MAP_TREE_DEPTH (Heap.set h k v)) := by
  simp only [decWritesTo, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-! ## §4 — `mapDecMerkle`: the concrete map-op decider over the witness supply. -/

/-- The supply of opening witnesses the trace carries: the sorted leaf vector (the heap) behind each
map-op's column root, for each row environment. The deployment carries exactly this as part of the
trace WITNESS (the opening path / the sorted heap), NOT discovered from the published root. -/
abbrev WitnessSupply := VmRowEnv → MapOp → Heap.FeltHeap

/-- **`mapDecMerkle hash wit env m`** — the CONCRETE decision of `MapOp.holdsAt` for the map op `m` on
row `env`, using the SUPPLIED witness heap `wit env m`. When the guard does not fire the op is vacuously
satisfied (`true`); else it dispatches on the op kind, checking the supplied heap against the columns by
the decidable `decOpensTo` / `decWritesTo`. NO existential — the witness IS the heap. -/
def mapDecMerkle (hash : List ℤ → ℤ) (wit : WitnessSupply) (env : VmRowEnv) (m : MapOp) : Bool :=
  if m.guard.eval env.loc = 1 then
    match m.op with
    | .read   => decOpensTo hash (wit env m) ((m.root 0).eval env.loc) (m.key.eval env.loc)
                   (some (m.value.eval env.loc))
                 && decide ((m.newRoot 0).eval env.loc = (m.root 0).eval env.loc)
    | .absent => decOpensTo hash (wit env m) ((m.root 0).eval env.loc) (m.key.eval env.loc) none
                 && decide ((m.newRoot 0).eval env.loc = (m.root 0).eval env.loc)
    | .write  => decWritesTo hash (wit env m) ((m.root 0).eval env.loc) (m.key.eval env.loc)
                   (m.value.eval env.loc) ((m.newRoot 0).eval env.loc)
    | .insert => decWritesTo hash (wit env m) ((m.root 0).eval env.loc) (m.key.eval env.loc)
                   (m.value.eval env.loc) ((m.newRoot 0).eval env.loc)
    | .aafiInsert => decWritesTo hash (wit env m) ((m.root 0).eval env.loc) (m.key.eval env.loc)
                   (m.value.eval env.loc) ((m.newRoot 0).eval env.loc)
  else true

/-! ## §5 — soundness of the concrete decider (`mapDecMerkle = true → holdsAt`), UNCONDITIONAL.

The supplied heap WITNESSES the existential: `decOpensTo`/`decWritesTo true` is literally the
`opensToMerkleS`/`writesToMerkleS` body at the deployed schema for `wit env m`. No floor, no residual,
no well-formedness side-condition. -/

theorem mapDecMerkle_sound (hash : List ℤ → ℤ) (wit : WitnessSupply) (env : VmRowEnv) (m : MapOp) :
    mapDecMerkle hash wit env m = true → m.holdsAt hash env := by
  intro hdec
  unfold mapDecMerkle at hdec
  unfold MapOp.holdsAt
  intro hguard
  rw [if_pos hguard] at hdec
  cases hop : m.op with
  | read =>
    rw [hop] at hdec
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hdec
    obtain ⟨hopen, hnr⟩ := hdec
    rw [decOpensTo_iff] at hopen
    obtain ⟨hs, hb, hz, hr, hg⟩ := hopen
    exact ⟨opensTo_intro hash hs hb hz hr hg, hnr⟩
  | absent =>
    rw [hop] at hdec
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hdec
    obtain ⟨hopen, hnr⟩ := hdec
    rw [decOpensTo_iff] at hopen
    obtain ⟨hs, hb, hz, hr, hg⟩ := hopen
    exact ⟨opensTo_intro hash hs hb hz hr hg, hnr⟩
  | write =>
    rw [hop] at hdec
    rw [decWritesTo_iff] at hdec
    obtain ⟨hs, hb, hz, hz', hr, hr'⟩ := hdec
    exact writesTo_intro hash hs hb hz hz' hr hr'
  | insert =>
    rw [hop] at hdec
    rw [decWritesTo_iff] at hdec
    obtain ⟨hs, hb, hz, hz', hr, hr'⟩ := hdec
    exact writesTo_intro hash hs hb hz hz' hr hr'
  | aafiInsert =>
    rw [hop] at hdec
    rw [decWritesTo_iff] at hdec
    obtain ⟨hs, hb, hz, hz', hr, hr'⟩ := hdec
    exact writesTo_intro hash hs hb hz hz' hr hr'

/-! ## §6 — completeness (`holdsAt → mapDecMerkle = true`), FLOOR-FREE, up to a named residual.

Completeness needs two things the decider cannot see:

  1. the SUPPLIED heap must be a GENUINE opening of the op's column root — the prover published it,
     so this is its structured OBLIGATION (`WitnessOpens`), a DECIDABLE well-formedness fact; and
  2. the supplied heap and the heap the DENOTATION's existential carries must be forced equal by
     their shared root.

(2) used to be `mapRoot_injective` under `Poseidon2SpongeCR hash` — a hypothesis proved FALSE at the
prover's own parameters. It is now the deployed schema's floor-free binding, whose failure mode is the
NAMED `SupplyResid` below rather than a global assumption about the sponge. -/

/-- **`WitnessOpens hash wit`** — the prover's supply is well-formed: for every FIRING map op, the
supplied heap `wit env m` is ADMISSIBLE at the deployed schema (sorted; every key below the terminal
sentinel; at most `2^16` live entries) and its DEPLOYED arity-3 padded root is the op's `root` column.
Exactly what `decOpensTo`/`decWritesTo` check on the supply — a decidable fact about published
openings, not an oracle. -/
def WitnessOpens (hash : List ℤ → ℤ) (wit : WitnessSupply) : Prop :=
  ∀ (env : VmRowEnv) (m : MapOp), m.guard.eval env.loc = 1 →
    Heap.SortedKeys (wit env m) ∧ (∀ x ∈ Heap.keys (wit env m), x < MAP_SENTINEL)
      ∧ (wit env m).length ≤ 2 ^ MAP_TREE_DEPTH
      ∧ padImtRoot MAP_SENTINEL hash MAP_TREE_DEPTH (wit env m) = (m.root 0).eval env.loc

/-- **`SupplyResid hash wit env m` — THE NAMED RESIDUAL OF COMPLETENESS, and it is not a floor.**
Some heap ADMISSIBLE at the deployed schema commits to this op's very `root` column and carries the
schema's residual against the supplied heap: a live arity-3 leaf digest equal to the padding constant
(`PadGhost3` — a DEPLOYED wound, since the padding is the literal `BabyBear::ZERO` and a fixed-target
preimage of a literal is not excluded by collision resistance), or a genuine sponge collision at the
ONE pair `padImtRootFind` returns.

Per-instance and per-commitment: it quantifies over co-preimages of ONE published root, not over the
hash's whole domain, so it is neither a global assumption nor refuted by pigeonhole the way a
`∀ h₁ h₂, ¬ Resid` side condition would be. It is REFUTABLE
(`supplyResid_refuted_at_oddSponge`) and REACHABLE (`mapResid_reachable`). -/
def SupplyResid (hash : List ℤ → ℤ) (wit : WitnessSupply) (env : VmRowEnv) (m : MapOp) : Prop :=
  ∃ h : Heap.FeltHeap, Heap.SortedKeys h ∧ (∀ x ∈ Heap.keys h, x < MAP_SENTINEL)
    ∧ h.length ≤ 2 ^ MAP_TREE_DEPTH
    ∧ padImtRoot MAP_SENTINEL hash MAP_TREE_DEPTH h = (m.root 0).eval env.loc
    ∧ mapTeeth.Resid hash MAP_TREE_DEPTH (wit env m) h

/-- **THE RESIDUAL IS REFUTED AT AN INHABITED INSTANCE, WITH NO FLOOR BINDER.** `oddSponge` is the
in-tree encodable injection with no preimage of the padding constant
(`DeployedMapDenotation.oddSponge_injective` / `_padFree3`), so it satisfies the deployed teeth's
`Good`. Stating the refutation AT it rather than under a `Good hash` binder keeps the refuted
`Function.Injective (· : List ℤ → ℤ)` out of every type in this file. -/
theorem supplyResid_refuted_at_oddSponge (wit : WitnessSupply) (env : VmRowEnv) (m : MapOp) :
    ¬ SupplyResid oddSponge wit env m := by
  rintro ⟨h, -, -, -, -, hc⟩
  exact mapTeeth.resid_refuted oddSponge ⟨oddSponge_injective, oddSponge_padFree3⟩
    MAP_TREE_DEPTH _ _ hc

/-- **`mapDecMerkle_complete` — FLOOR-FREE.** Under the prover's well-formed opening supply and the
NAMED per-instance residual's refusal, the concrete decider accepts everything the deployed denotation
holds of. ⚑ No hypothesis on `hash`: this used to take `Poseidon2SpongeCR hash`, which is false at
deployed BabyBear, and the statement was therefore vacuous. -/
theorem mapDecMerkle_complete (hash : List ℤ → ℤ) (wit : WitnessSupply)
    (hwit : WitnessOpens hash wit) (env : VmRowEnv) (m : MapOp)
    (hno : ¬ SupplyResid hash wit env m) :
    m.holdsAt hash env → mapDecMerkle hash wit env m = true := by
  intro hhold
  unfold mapDecMerkle
  by_cases hguard : m.guard.eval env.loc = 1
  · rw [if_pos hguard]
    obtain ⟨hws, hwb, hwl, hwr⟩ := hwit env m hguard
    unfold MapOp.holdsAt at hhold
    have hh := hhold hguard
    cases hop : m.op with
    | read =>
      rw [hop] at hh
      obtain ⟨hopen, hnr⟩ := hh
      obtain ⟨h', hs', hb', hl', hr', hg'⟩ := opensTo_elim hash hopen
      have heq : wit env m = h' := by
        rcases heap_eq_or_resid hash hwl hl' (hwr.trans hr'.symm) with he | hc
        · exact he
        · exact absurd ⟨h', hs', hb', hl', hr', hc⟩ hno
      rw [Bool.and_eq_true, decide_eq_true_eq, decOpensTo_iff]
      exact ⟨⟨hws, hwb, hwl, hwr, by rw [heq]; exact hg'⟩, hnr⟩
    | absent =>
      rw [hop] at hh
      obtain ⟨hopen, hnr⟩ := hh
      obtain ⟨h', hs', hb', hl', hr', hg'⟩ := opensTo_elim hash hopen
      have heq : wit env m = h' := by
        rcases heap_eq_or_resid hash hwl hl' (hwr.trans hr'.symm) with he | hc
        · exact he
        · exact absurd ⟨h', hs', hb', hl', hr', hc⟩ hno
      rw [Bool.and_eq_true, decide_eq_true_eq, decOpensTo_iff]
      exact ⟨⟨hws, hwb, hwl, hwr, by rw [heq]; exact hg'⟩, hnr⟩
    | write =>
      rw [hop] at hh
      obtain ⟨h', hs', hb', hl', hsl', hr', hnr'⟩ := writesTo_elim hash hh
      have heq : wit env m = h' := by
        rcases heap_eq_or_resid hash hwl hl' (hwr.trans hr'.symm) with he | hc
        · exact he
        · exact absurd ⟨h', hs', hb', hl', hr', hc⟩ hno
      rw [decWritesTo_iff]
      exact ⟨hws, hwb, hwl, by rw [heq]; exact hsl', hwr, by rw [heq]; exact hnr'⟩
    | insert =>
      rw [hop] at hh
      obtain ⟨h', hs', hb', hl', hsl', hr', hnr'⟩ := writesTo_elim hash hh
      have heq : wit env m = h' := by
        rcases heap_eq_or_resid hash hwl hl' (hwr.trans hr'.symm) with he | hc
        · exact he
        · exact absurd ⟨h', hs', hb', hl', hr', hc⟩ hno
      rw [decWritesTo_iff]
      exact ⟨hws, hwb, hwl, by rw [heq]; exact hsl', hwr, by rw [heq]; exact hnr'⟩
    | aafiInsert =>
      rw [hop] at hh
      obtain ⟨h', hs', hb', hl', hsl', hr', hnr'⟩ := writesTo_elim hash hh
      have heq : wit env m = h' := by
        rcases heap_eq_or_resid hash hwl hl' (hwr.trans hr'.symm) with he | hc
        · exact he
        · exact absurd ⟨h', hs', hb', hl', hr', hc⟩ hno
      rw [decWritesTo_iff]
      exact ⟨hws, hwb, hwl, by rw [heq]; exact hsl', hwr, by rw [heq]; exact hnr'⟩
  · rw [if_neg hguard]

/-- The same, with the residual in the CONCLUSION rather than as a hypothesis: the decider accepts,
OR the named per-instance residual holds. Takes NOTHING beyond the supply's well-formedness. -/
theorem mapDecMerkle_complete_or_resid (hash : List ℤ → ℤ) (wit : WitnessSupply)
    (hwit : WitnessOpens hash wit) (env : VmRowEnv) (m : MapOp) :
    m.holdsAt hash env →
      mapDecMerkle hash wit env m = true ∨ SupplyResid hash wit env m := by
  intro hhold
  by_cases hno : SupplyResid hash wit env m
  · exact Or.inr hno
  · exact Or.inl (mapDecMerkle_complete hash wit hwit env m hno hhold)

/-! ## §7 — `mapDecMerkle_faithful`: the `hmapDec` shape, no free oracle and NO REFUTED FLOOR. -/

/-- **`mapDecMerkle_faithful` — the discharged oracle.** Under the prover's well-formed opening supply
(`hwit`) and the refusal of the named per-instance residual (`hno`), the CONCRETE decider
`mapDecMerkle hash wit` satisfies EXACTLY the faithfulness shape `hmapDec` that `decideSatisfied2`
demanded. Soundness is unconditional (the witness IS the heap); completeness rides the deployed
schema's floor-free binding.

⚑ Neither hypothesis is a statement about `hash`. The pre-2026-07-30 version took
`Poseidon2SpongeCR hash`, which this tree refutes at deployed BabyBear parameters — so it was
vacuous, and it is one of the four names this file contributes to
`Verify/FloorRatchetBaseline`. Those four entries are now stale in the healthy direction. -/
theorem mapDecMerkle_faithful (hash : List ℤ → ℤ) (wit : WitnessSupply)
    (hwit : WitnessOpens hash wit)
    (hno : ∀ (env : VmRowEnv) (m : MapOp), ¬ SupplyResid hash wit env m) :
    ∀ (env : VmRowEnv) (m : MapOp), mapDecMerkle hash wit env m = true ↔ m.holdsAt hash env :=
  fun env m => ⟨mapDecMerkle_sound hash wit env m,
                mapDecMerkle_complete hash wit hwit env m (hno env m)⟩

/-! ## §8 — `decideSatisfied2'`: the bridge specialized to the concrete decider — NO free oracle. -/

/-- **`decideSatisfied2' hash wit …`** — the WHOLE-TRACE kernel bridge with the map-op leg decided
CONCRETELY by `mapDecMerkle hash wit` (the prover's opening supply, against the DEPLOYED arity-3
indexed-Merkle commitment), rather than by an assumed-faithful oracle. -/
def decideSatisfied2' (hash : List ℤ → ℤ) (wit : WitnessSupply)
    (d : EffectVmDescriptor2) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace) : Bool :=
  decideSatisfied2 (mapDecMerkle hash wit) hash d minit mfin maddrs t

/-- **`decideSatisfied2'_iff_Satisfied2` — THE deliverable, oracle-free AND floor-free.** Under the
prover's well-formed opening supply and the named per-instance residual's refusal (both carried,
neither a free `mapDec`/`hmapDec` parameter, neither a hypothesis on `hash`), the total reference
DECIDES the deployed accept-set. The map-op leg is decided concretely over the witness supply against
the commitment `heap_root.rs` actually computes. -/
theorem decideSatisfied2'_iff_Satisfied2 (hash : List ℤ → ℤ)
    (wit : WitnessSupply) (hwit : WitnessOpens hash wit)
    (hno : ∀ (env : VmRowEnv) (m : MapOp), ¬ SupplyResid hash wit env m)
    (d : EffectVmDescriptor2) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace) :
    decideSatisfied2' hash wit d minit mfin maddrs t = true
      ↔ Satisfied2 hash d minit mfin maddrs t :=
  decideSatisfied2_iff_Satisfied2 (mapDecMerkle hash wit) hash
    (mapDecMerkle_faithful hash wit hwit hno) d minit mfin maddrs t

/-- **`Satisfied2` is DECIDABLE under the prover's opening supply + the named residual's refusal** —
no assumed-faithful oracle and no refuted floor remain. The instance form, so the Rust enumerator's
accept/reject resolves through the verified core with the map-op leg decided concretely. -/
def instDecidableSatisfied2' (hash : List ℤ → ℤ)
    (wit : WitnessSupply) (hwit : WitnessOpens hash wit)
    (hno : ∀ (env : VmRowEnv) (m : MapOp), ¬ SupplyResid hash wit env m)
    (d : EffectVmDescriptor2) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace) :
    Decidable (Satisfied2 hash d minit mfin maddrs t) :=
  decidable_of_iff _ (decideSatisfied2'_iff_Satisfied2 hash wit hwit hno d minit mfin maddrs t)

/-! ## §9 — Axiom hygiene. -/

#assert_axioms decOpensTo_iff
#assert_axioms decWritesTo_iff
#assert_axioms mapResid_reachable
#assert_axioms supplyResid_refuted_at_oddSponge
#assert_axioms mapDecMerkle_sound
#assert_axioms mapDecMerkle_complete
#assert_axioms mapDecMerkle_complete_or_resid
#assert_axioms mapDecMerkle_faithful
#assert_axioms decideSatisfied2'_iff_Satisfied2

end Dregg2.Circuit.DecideMapMerkle
