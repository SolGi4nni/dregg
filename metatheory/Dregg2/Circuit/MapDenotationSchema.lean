/-
# `Dregg2.Circuit.MapDenotationSchema` — the LEAF-SCHEMA PARAMETER that lets the map-op
  DENOTATION move onto the deployed arity-3 indexed-Merkle commitment, with the deployed
  arity-2 objects recovered as the narrow instance DEFINITIONALLY.

## The problem this is the first step of

`MapReconcileImtRepoint` proves (machine-checked) that the deployed map tree commits **arity-3**
IMT leaves `hash[addr, value, next_addr]` for EVERY map-op kind
(`circuit/src/descriptor_ir2.rs::map_leaf_input_cols = [MAP_KEY, value_col, MAP_NEXT]`;
`circuit/src/heap_root.rs::HeapLeaf::digest`), while `DescriptorIR2.opensTo`/`writesTo` — hence
`MapOp.holdsAt`, hence the `.mapOp` arm of `Satisfied2`, hence every `AlgoStarkSound*` conclusion —
quantify over **arity-2** `Heap.leafOf` leaves. At an injective sponge those are provably different
commitments (`imtRoot_ne_mapRoot`), so `MapOp.holdsAt` is REFUTED at a deployed pre-root
(`mapOpHoldsAt_unsat_at_imtRoot`): the apex's CONCLUSION, not merely its premise, is false there.
No repointing of a premise can fix that. The DENOTATION has to move.

## What this file is

The **conservativity vehicle** for that move, and nothing more. It is strictly ADDITIVE: no
existing definition changes, no deployed byte is touched, no `Satisfied2` gains a parameter.

`MapLeafSchema` factors out of the map denotation the two things the arity change touches:

  * `commit` — **the leaf-schema-dependent COMMITMENT of a committed heap**, as a FUNCTION. At
    `narrowSchema` it IS `MapMerkleRoot.mapRoot` (the deployed arity-2 binary fold); at
    `imtSchema sent` it is the arity-3 indexed-Merkle fold of the SAME heap, with the `next_addr`
    pointers relinked to each entry's sorted successor and the terminal pointer set to `sent`.
  * `HeapOk` — **the admissible committed heap**, the extraction premise's domain. At
    `narrowSchema` it IS `Heap.SortedKeys` (so every conservativity `rfl` below survives); at
    `imtSchema sent` it is `Heap.SortedKeys` PLUS "every committed key is below the terminal
    sentinel", which is exactly what makes the relinked chain a well-linked `ImtSorted` chain
    (`imtSchema_chain_imtSorted`) rather than merely a sorted vector.

This is the `LaneEnc`/`HeapOk` move of the wide-key epoch (`MapOpWideKeyGate`), applied to leaf
ARITY instead of key WIDTH — and it is *cleaner* than that one, because the extra committed datum
the arity-3 leaf carries needs no existential: `heap_root.rs::relink_next_addrs` DERIVES every
pointer from the sorted successor and pins the terminal one to the constant `SENTINEL_MAX`, so the
arity-3 commitment is a FUNCTION of the same `Heap.FeltHeap` the arity-2 one folds. That is why
`commit` can be a plain field and every deployed object comes back by `rfl`.

## ★ CONSERVATIVITY, kernel-certified (§2)

`opensToMerkleS narrowSchema = opensToMerkle`, `writesToMerkleS narrowSchema = writesToMerkle`,
and `MapOp.holdsAtS narrowSchema ↔ DescriptorIR2.MapOp.holdsAt` — all THREE by `rfl`/`Iff.rfl`.
The kernel, not the eye, certifies that parameterising the leaf schema changed no deployed meaning.
⚠ TWO MECHANICAL FACTS, both measured, both load-bearing for anyone extending this:

  * The `writesToMerkleS` body mirrors `writesToMerkle`'s conjunct ORIENTATION verbatim
    (`r' = commit …`, not `commit … = r'`). Writing it the other way costs the `rfl`.
  * **The two `rfl`s hold at GENERIC depth and CANNOT BE RE-CHECKED at the deployed one.** Stating
    the same equation with `MAP_TREE_DEPTH` in place of the variable `d` and closing it by a FRESH
    `rfl` dies at the heartbeat limit: with a concrete depth the elaborator can make progress inside
    `perfectRoot hash 16 _` and starts splitting the symbolic leaf vector. `narrow_holdsAtS_is_instance`
    therefore TRANSPORTS the generic `rfl`s by rewriting instead of re-deriving them — same kernel
    certificate, no dive. This is `MapReconcileImtRepoint` §4a's discipline; it applies to the
    conservativity layer too, and it is the shape any cutover-site repair will have to take.

## ★ THE PAYOFF, on the very row where today's denotation is REFUTED (§4)

`topGap_holdsAtS_holds_where_holdsAt_is_refuted`: on the deployed-depth (`MAP_TREE_DEPTH = 16`)
top-gap `.absent` row of `MapReconcileImtRepoint` §4 — the ordinary path, where every fresh
nullifier and cell-id lands — `MapOp.holdsAtS (imtSchema _)` **HOLDS** while
`DescriptorIR2.MapOp.holdsAt` is **REFUTED**. That is the one thing that is not true today: there
is now a map-op denotation that is INHABITED at the commitment the deployed prover computes.

## What this does NOT do (named, not claimed closed)

  1. **Nothing downstream consumes it yet.** `VmConstraint2.holdsAt`'s `.mapOp` arm still reads
     `MapOp.holdsAt`. Rebinding it is a ONE-LINE change (§5's note) whose blast radius is the set
     of theorems that destructure the arity-2 CONTENT of `MapOp.holdsAt` — priced in
     `docs/DESIGN-mapop-denotation-move.md`, not attempted here.
  2. **Only the `.absent` kind has an arity-3 GATE law.** `MapAbsentImtGate` repointed that one arm;
     `.read`/`.write`/`.insert`/`.aafiInsert` have no arity-3 opener yet, so the modeller cannot
     yet DERIVE `holdsAtS (imtSchema _)` for them. §4's payoff is exhibited, not derived from a gate
     model, for exactly that reason.
  3. **⚑ THE SECOND SHAPE GAP — DENSITY — IS NOT CLOSED HERE, AND ARITY ALONE DOES NOT CLOSE IT.**
     `opensToMerkle` demands `Heap.SortedKeys h ∧ h.length = 2 ^ d`: a DENSE vector of `2 ^ 16`
     STRICTLY INCREASING keys. The deployed tree holds `n ≪ 2 ^ 16` real leaves and pads every
     position `≥ n` with the literal constant `BabyBear::ZERO`
     (`heap_root.rs`: `EMPTY_SUBTREE_ROOTS[0]` "is the empty-leaf digest (`BabyBear::ZERO`, the
     padding marker)"), which is not the `leafOf` image — nor the `imtLeafHash` image — of any
     entry at all. So the deployed prover has no witness for the denotation's `∃ h` for a SECOND,
     INDEPENDENT reason, and moving the leaf arity does not touch it.
     `imtSchema` below therefore describes the deployed LEAF and the deployed RELINK but still the
     DENSE fold, so it is faithful to `heap_root.rs` only on a full tree. That is why the schema
     carries `SizeOk` as a FIELD (`h.length = 2 ^ d` at BOTH instances here, so every `rfl`
     survives): the sparse/padded instance is a further instance of this same structure — a
     `commit` that folds a prefix against the constant-zero padding and a `SizeOk` reading
     `h.length ≤ 2 ^ d` — and needs no further structural change. Landing it is the next lane, and
     it is a PREREQUISITE for the apex saying anything about a real turn, not an optional polish.
  4. **No floor is discharged and none is added.** `imtSchema` is a fold of `imtLeafHash`; nothing
     here assumes injectivity of anything. ⚠ Note that `Poseidon2SpongeCR` — the floor
     `MapReconcileImtRepoint`'s separation theorems carry — is PROVED FALSE at deployed BabyBear
     parameters (`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`); the §4 payoff is stated over
     `refSponge`, which does carry it, and over an ARBITRARY hash wherever possible.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; sorry-free; no `native_decide`; no
`decide` on any object containing the depth-16 spine. NEW file; every import read-only.
-/
import Dregg2.Circuit.MapReconcileImtRepoint

namespace Dregg2.Circuit.MapDenotationSchema

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2 (MapOp MapOpKind MAP_TREE_DEPTH envAt)
open Dregg2.Circuit.MapMerkleRoot (perfectRoot mapRoot opensToMerkle writesToMerkle)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.IndexedMerkleTree (ImtLeaf ImtSorted imtLeafHash imtToHeap imtSorted_sortedKeys)
open Dregg2.Substrate

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — THE SCHEMA. -/

/-- **`MapLeafSchema`** — the map tree's LEAF SCHEMA: how a committed heap becomes a root, together
with the admissible shape of a committed heap under that schema.

`commit` is the whole arity story. `HeapOk` is the extraction premise's DOMAIN — the class of heaps a
prover can actually have committed under this schema — carried here rather than at each use site,
exactly as `MapOpWideKeyGate.LaneEnc.HeapOk` carries the wide-key canonicity. -/
structure MapLeafSchema where
  /-- The admissible committed heap. -/
  HeapOk : Heap.FeltHeap → Prop
  /-- An admissible heap is sorted, so every `Heap` lemma the openers call still applies. -/
  heapOk_sorted : ∀ h, HeapOk h → Heap.SortedKeys h
  /-- **THE OCCUPANCY DISCIPLINE.** How many entries a depth-`d` commitment admits. A field rather
  than the hard-wired `h.length = 2 ^ d` because the DEPLOYED tree is SPARSE — see §2b. -/
  SizeOk : Nat → Heap.FeltHeap → Prop
  /-- **THE COMMITMENT.** The depth-`d` root this schema folds an admissible heap to. -/
  commit : (List ℤ → ℤ) → Nat → Heap.FeltHeap → ℤ

/-- **The DEPLOYED-TODAY schema** — the arity-2 `Heap.leafOf` binary fold, whose `commit` IS
`MapMerkleRoot.mapRoot`, whose `HeapOk` IS `Heap.SortedKeys`, and whose `SizeOk` IS the dense
`h.length = 2 ^ d`. All three fields are the deployed objects themselves, which is precisely why
§2's conservativity is `rfl`. -/
def narrowSchema : MapLeafSchema where
  HeapOk := Heap.SortedKeys
  heapOk_sorted := fun _ h => h
  SizeOk := fun d h => h.length = 2 ^ d
  commit := mapRoot

/-- **`imtChainOf sent h`** — the deployed RELINK (`heap_root.rs::relink_next_addrs`) as a function:
turn a sorted heap into the well-linked IMT chain by pointing each leaf at its sorted successor's
address, and the last leaf at the terminal sentinel `sent`. -/
def imtChainOf (sent : ℤ) : Heap.FeltHeap → List ImtLeaf
  | [] => []
  | [e] => [⟨e.1, e.2, sent⟩]
  | e :: e' :: rest => ⟨e.1, e.2, e'.1⟩ :: imtChainOf sent (e' :: rest)

/-- **The DEPLOYED-ACTUAL schema** — the arity-3 indexed-Merkle fold of the same heap.
`commit` relinks and folds `imtLeafHash`; `HeapOk` adds the one thing sortedness does not give,
namely that the terminal sentinel really is above every committed key. -/
def imtSchema (sent : ℤ) : MapLeafSchema where
  HeapOk := fun h => Heap.SortedKeys h ∧ ∀ x ∈ Heap.keys h, x < sent
  heapOk_sorted := fun _ h => h.1
  SizeOk := fun d h => h.length = 2 ^ d
  commit := fun hash d h => perfectRoot hash d ((imtChainOf sent h).map (imtLeafHash hash))

/-- The IMT schema's admissibility unfolds to exactly its two conjuncts. -/
theorem imtSchema_heapOk_iff (sent : ℤ) (h : Heap.FeltHeap) :
    (imtSchema sent).HeapOk h ↔ (Heap.SortedKeys h ∧ ∀ x ∈ Heap.keys h, x < sent) := Iff.rfl

/-! ## §2 — THE SCHEMA-PARAMETRIC DENOTATION, AND CONSERVATIVITY BY `rfl`.

Each body mirrors its deployed counterpart CONJUNCT FOR CONJUNCT, in the same order and the same
orientation, with `Heap.SortedKeys` replaced by `S.HeapOk` and `mapRoot` by `S.commit`. -/

/-- **`opensToMerkleS S hash d r k o`** — some admissible `2^d`-leaf heap committed by `r` under
schema `S` reads `o` at `k`. -/
def opensToMerkleS (S : MapLeafSchema) (hash : List ℤ → ℤ) (d : Nat) (r k : ℤ)
    (o : Option ℤ) : Prop :=
  ∃ h : Heap.FeltHeap, S.HeapOk h ∧ S.SizeOk d h ∧ S.commit hash d h = r ∧ Heap.get h k = o

/-- **`writesToMerkleS S hash d r k v r'`** — the sorted insert-or-update of `(k, v)` moves the
committed root `r` to `r'` under schema `S`. -/
def writesToMerkleS (S : MapLeafSchema) (hash : List ℤ → ℤ) (d : Nat) (r k v r' : ℤ) : Prop :=
  ∃ h : Heap.FeltHeap, S.HeapOk h ∧ S.SizeOk d h
    ∧ S.SizeOk d (Heap.set h k v)
    ∧ S.commit hash d h = r ∧ r' = S.commit hash d (Heap.set h k v)

/-- **★ CONSERVATIVE EXTENSION (opening).** The DEPLOYED `opensToMerkle` — hence
`DescriptorIR2.opensTo` — IS the narrow instance, definitionally. -/
theorem opensToMerkleS_narrow (hash : List ℤ → ℤ) (d : Nat) (r k : ℤ) (o : Option ℤ) :
    opensToMerkleS narrowSchema hash d r k o = opensToMerkle hash d r k o := rfl

/-- **★ CONSERVATIVE EXTENSION (write).** The DEPLOYED `writesToMerkle` — hence
`DescriptorIR2.writesTo` — IS the narrow instance, definitionally. -/
theorem writesToMerkleS_narrow (hash : List ℤ → ℤ) (d : Nat) (r k v r' : ℤ) :
    writesToMerkleS narrowSchema hash d r k v r' = writesToMerkle hash d r k v r' := rfl

/-- **`MapOp.holdsAtS S hash env m`** — the per-row map-op denotation at leaf schema `S`. The body is
`DescriptorIR2.MapOp.holdsAt`'s, kind for kind, at the schema's commitment. -/
def MapOp.holdsAtS (S : MapLeafSchema) (hash : List ℤ → ℤ) (env : VmRowEnv) (m : MapOp) : Prop :=
  m.guard.eval env.loc = 1 →
    match m.op with
    | .read   => opensToMerkleS S hash MAP_TREE_DEPTH ((m.root 0).eval env.loc)
                   (m.key.eval env.loc) (some (m.value.eval env.loc))
                 ∧ (m.newRoot 0).eval env.loc = (m.root 0).eval env.loc
    | .absent => opensToMerkleS S hash MAP_TREE_DEPTH ((m.root 0).eval env.loc)
                   (m.key.eval env.loc) none
                 ∧ (m.newRoot 0).eval env.loc = (m.root 0).eval env.loc
    | .write  => writesToMerkleS S hash MAP_TREE_DEPTH ((m.root 0).eval env.loc)
                   (m.key.eval env.loc) (m.value.eval env.loc) ((m.newRoot 0).eval env.loc)
    | .insert => writesToMerkleS S hash MAP_TREE_DEPTH ((m.root 0).eval env.loc)
                   (m.key.eval env.loc) (m.value.eval env.loc) ((m.newRoot 0).eval env.loc)
    | .aafiInsert => writesToMerkleS S hash MAP_TREE_DEPTH ((m.root 0).eval env.loc)
                   (m.key.eval env.loc) (m.value.eval env.loc) ((m.newRoot 0).eval env.loc)

/-- **★★ THE CONSERVATIVITY KEYSTONE.** The DEPLOYED per-row denotation `MapOp.holdsAt` — the
`.mapOp` arm of `Satisfied2` and what every `AlgoStarkSound*` theorem concludes about — IS the narrow
instance of the schema-parametric one, by KERNEL DEFEQ. Parameterising the leaf schema changed no
deployed meaning; the eye is not being asked to check it. -/
theorem narrow_holdsAtS_is_instance (hash : List ℤ → ℤ) (env : VmRowEnv) (m : MapOp) :
    MapOp.holdsAtS narrowSchema hash env m ↔ DescriptorIR2.MapOp.holdsAt hash env m := by
  unfold MapOp.holdsAtS DescriptorIR2.MapOp.holdsAt DescriptorIR2.opensTo DescriptorIR2.writesTo
  cases m.op <;> simp only [opensToMerkleS_narrow, writesToMerkleS_narrow]

/-! ## §3 — THE WELD: the relink is INVERSE to the projection, and the IMT schema's admissible
heaps commit genuine `ImtSorted` chains.

This is what connects the new denotation to the arity-3 gate family that already exists
(`MapAbsentImtGate.AbsentImtGatesAt` and everything `MapReconcileImtRepoint` proves over it), whose
committed object is a `List ImtLeaf` with `ImtSorted`. -/

/-- **`ImtLinkedTo sent c`** — `c`'s pointers are the deployed relink: each leaf points at its
successor's address, the last at `sent`. (`ImtSorted` is this PLUS `addr < nextAddr` per leaf.) -/
def ImtLinkedTo (sent : ℤ) : List ImtLeaf → Prop
  | [] => True
  | [l] => l.nextAddr = sent
  | l :: l' :: rest => l.nextAddr = l'.addr ∧ ImtLinkedTo sent (l' :: rest)

/-- The relink's cons step, with the produced pointer NAMED — the shape both inductions below need
(the tail of `imtChainOf` is not syntactically a cons, so `ImtSorted`'s own three-case match is
otherwise stuck). -/
theorem imtChainOf_cons (sent : ℤ) (e : ℤ × ℤ) (rest : Heap.FeltHeap) :
    ∃ n : ℤ, imtChainOf sent (e :: rest) = ⟨e.1, e.2, n⟩ :: imtChainOf sent rest := by
  cases rest with
  | nil => exact ⟨sent, rfl⟩
  | cons e' rest' => exact ⟨e'.1, rfl⟩

/-- **★ THE RELINK INVERTS THE PROJECTION.** A chain whose pointers ARE the deployed relink is
recovered exactly from its `(addr, value)` projection — so the arity-3 leaf carries no committed
datum that `Heap.FeltHeap` plus the terminal sentinel does not already determine. This is the fact
that lets `commit` be a FUNCTION field rather than an existential, hence the fact that makes §2's
conservativity `rfl`. -/
theorem imtChainOf_imtToHeap (sent : ℤ) :
    ∀ c : List ImtLeaf, ImtLinkedTo sent c → imtChainOf sent (imtToHeap c) = c := by
  intro c
  induction c with
  | nil => intro _; rfl
  | cons l rest ih =>
    cases rest with
    | nil =>
      intro hlk
      obtain ⟨a, v, n⟩ := l
      simp only [ImtLinkedTo] at hlk
      subst hlk
      rfl
    | cons l' rest' =>
      intro hlk
      obtain ⟨hptr, htail⟩ := hlk
      have hrec : imtChainOf sent (imtToHeap (l' :: rest')) = l' :: rest' := ih htail
      show (⟨l.addr, l.value, l'.addr⟩ : ImtLeaf) :: imtChainOf sent (imtToHeap (l' :: rest'))
        = l :: l' :: rest'
      rw [hrec]
      congr 1
      obtain ⟨a, v, n⟩ := l
      simp only at hptr
      subst hptr
      rfl

/-- **★ AN ADMISSIBLE IMT-SCHEMA HEAP COMMITS A WELL-LINKED SORTED CHAIN.** The `HeapOk` field is
doing real work: `Heap.SortedKeys` alone would leave the terminal pointer unconstrained, and the
relinked chain would fail `ImtSorted` at its last leaf. With the sentinel bound it is a genuine
`ImtSorted` chain — the object every arity-3 gate law is stated over. -/
theorem imtSchema_chain_imtSorted (sent : ℤ) :
    ∀ h : Heap.FeltHeap, (imtSchema sent).HeapOk h → ImtSorted (imtChainOf sent h) := by
  intro h
  induction h with
  | nil => intro _; trivial
  | cons e rest ih =>
    cases rest with
    | nil =>
      intro hok
      show e.1 < sent
      exact hok.2 e.1 (by simp [Heap.keys])
    | cons e' rest' =>
      intro hok
      obtain ⟨hs, hb⟩ := hok
      have hpw := hs
      rw [Heap.SortedKeys, Heap.keys, List.map_cons, List.map_cons,
        List.pairwise_cons] at hpw
      have hlt : e.1 < e'.1 := hpw.1 e'.1 (by simp)
      have hstail : Heap.SortedKeys (e' :: rest') := by
        have h2 := hs
        rw [Heap.SortedKeys, Heap.keys, List.map_cons, List.pairwise_cons] at h2
        exact h2.2
      have hbtail : ∀ x ∈ Heap.keys (e' :: rest'), x < sent := by
        intro x hx
        exact hb x (by rw [Heap.keys, List.map_cons] at hx ⊢; exact List.mem_cons_of_mem _ hx)
      cases rest' with
      | nil =>
        show ImtSorted [(⟨e.1, e.2, e'.1⟩ : ImtLeaf), (⟨e'.1, e'.2, sent⟩ : ImtLeaf)]
        exact ⟨hlt, rfl, hbtail e'.1 (by simp [Heap.keys])⟩
      | cons e'' rest'' =>
        show ImtSorted ((⟨e.1, e.2, e'.1⟩ : ImtLeaf)
          :: (⟨e'.1, e'.2, e''.1⟩ : ImtLeaf) :: imtChainOf sent (e'' :: rest''))
        exact ⟨hlt, rfl, ih ⟨hstail, hbtail⟩⟩

/-- **★ THE GATE-SIDE BRIDGE.** For a chain the deployed relink produced, the IMT schema's `commit`
of its projection IS the committed root every arity-3 gate law names
(`perfectRoot hash d (c.map imtLeafHash)`). So the new denotation and `MapAbsentImtGate`'s
acceptance predicate speak about the SAME felt. -/
theorem imtSchema_commit_of_chain (sent : ℤ) (hash : List ℤ → ℤ) (d : Nat) (c : List ImtLeaf)
    (hlk : ImtLinkedTo sent c) :
    (imtSchema sent).commit hash d (imtToHeap c) = perfectRoot hash d (c.map (imtLeafHash hash)) := by
  show perfectRoot hash d ((imtChainOf sent (imtToHeap c)).map (imtLeafHash hash))
    = perfectRoot hash d (c.map (imtLeafHash hash))
  rw [imtChainOf_imtToHeap sent c hlk]

/-! ## §4 — THE PAYOFF, ON THE ROW WHERE TODAY'S DENOTATION IS REFUTED.

`MapReconcileImtRepoint` §4's exhibit: ONE descriptor, ONE fired `.absent` row at the DEPLOYED depth
`MAP_TREE_DEPTH = 16`, whose key is the fresh key just above the committed maximum — the ordinary
path. There `DescriptorIR2.MapOp.holdsAt` is REFUTED (`topGap_mapOpHoldsAt_false`). Below, the
schema-parametric denotation at the DEPLOYED leaf schema HOLDS on the same row. -/

section Payoff

open Dregg2.Circuit.Poseidon2Binding.Reference (refSponge refSponge_CR)
open Dregg2.Circuit.MapOpsColumnLayout (toyAbsentOp)
open Dregg2.Circuit.MapReconcileImtRepoint (spineC spineC_length depT depSpine depKey
  depSpine_length depSpine_sorted depHeap_length depSpine_addr_lt traceOf traceOf_loc traceOf_rows_length
  rowOf rowOf_root rowOf_newRoot rowOf_key rowOf_guard topGap_imt_absence_fires
  topGap_mapOpHoldsAt_false)

/-- The spine's pointers ARE the deployed relink, with terminal sentinel `a + 2n`. -/
theorem spineC_linkedTo : ∀ (n : Nat) (a : ℤ), ImtLinkedTo (a + 2 * (n : ℤ)) (spineC n a) := by
  intro n
  induction n with
  | zero => intro a; trivial
  | succ n ih =>
    intro a
    cases n with
    | zero =>
      show (⟨a, 0, a + 2⟩ : ImtLeaf).nextAddr = a + 2 * ((1 : Nat) : ℤ)
      push_cast
      ring
    | succ m =>
      have hih := ih (a + 2)
      show ((⟨a, 0, a + 2⟩ : ImtLeaf).nextAddr = (⟨a + 2, 0, a + 2 + 2⟩ : ImtLeaf).addr)
        ∧ ImtLinkedTo (a + 2 * ((m + 1 + 1 : Nat) : ℤ))
            ((⟨a + 2, 0, a + 2 + 2⟩ : ImtLeaf) :: spineC m (a + 2 + 2))
      refine ⟨rfl, ?_⟩
      have hcast : a + 2 * ((m + 1 + 1 : Nat) : ℤ) = (a + 2) + 2 * ((m + 1 : Nat) : ℤ) := by
        push_cast; ring
      rw [hcast]
      exact hih

/-- The deployed-depth spine's terminal sentinel. -/
def depSent : ℤ := 2 + 2 * depT

theorem depSpine_linkedTo : ImtLinkedTo depSent depSpine := by
  have h := spineC_linkedTo (2 ^ MAP_TREE_DEPTH) 2
  have hcast : (2 : ℤ) + 2 * ((2 ^ MAP_TREE_DEPTH : Nat) : ℤ) = depSent := by
    simp only [depSent, depT]; push_cast; ring
  rw [hcast] at h
  exact h

/-- The projected top-gap heap is ADMISSIBLE at the deployed IMT schema: sorted (from the chain
invariant) and entirely below the terminal sentinel (from the top-gap address bound). -/
theorem depHeap_heapOk : (imtSchema depSent).HeapOk (imtToHeap depSpine) := by
  refine ⟨imtSorted_sortedKeys depSpine_sorted, ?_⟩
  intro x hx
  rw [Dregg2.Circuit.IndexedMerkleTree.keys_imtToHeap] at hx
  have h1 : x < depKey := depSpine_addr_lt x hx
  have h2 : depKey < depSent := by simp only [depKey, depSent]; linarith
  exact h1.trans h2

/-- **★★ THE PAYOFF, IN ONE STATEMENT.** On the DEPLOYED-DEPTH top-gap `.absent` row — the ordinary
path, where every fresh nullifier and cell-id lands — the schema-parametric denotation at the
DEPLOYED arity-3 leaf schema **HOLDS**, while the denotation the apex actually concludes about is
**REFUTED**. This is exactly what is not true today: a map-op denotation inhabited at the commitment
`heap_root.rs` computes. -/
theorem topGap_holdsAtS_holds_where_holdsAt_is_refuted :
    MapOp.holdsAtS (imtSchema depSent) refSponge
        (envAt (traceOf
          (perfectRoot refSponge MAP_TREE_DEPTH (depSpine.map (imtLeafHash refSponge))) depKey) 0)
        toyAbsentOp
    ∧ ¬ DescriptorIR2.MapOp.holdsAt refSponge
        (envAt (traceOf
          (perfectRoot refSponge MAP_TREE_DEPTH (depSpine.map (imtLeafHash refSponge))) depKey) 0)
        toyAbsentOp := by
  refine ⟨?_, topGap_mapOpHoldsAt_false⟩
  intro _
  show opensToMerkleS (imtSchema depSent) refSponge MAP_TREE_DEPTH
      ((toyAbsentOp.root 0).eval
        (envAt (traceOf
          (perfectRoot refSponge MAP_TREE_DEPTH (depSpine.map (imtLeafHash refSponge))) depKey) 0).loc)
      (toyAbsentOp.key.eval
        (envAt (traceOf
          (perfectRoot refSponge MAP_TREE_DEPTH (depSpine.map (imtLeafHash refSponge))) depKey) 0).loc)
      none
    ∧ _
  rw [traceOf_loc, rowOf_root, rowOf_newRoot, rowOf_key]
  refine ⟨⟨imtToHeap depSpine, depHeap_heapOk, depHeap_length, ?_, ?_⟩, rfl⟩
  · exact imtSchema_commit_of_chain depSent refSponge MAP_TREE_DEPTH depSpine depSpine_linkedTo
  · exact topGap_imt_absence_fires.2.1

end Payoff

/-! ## §5 — WHAT THE CUTOVER WOULD BE.

`VmConstraint2.holdsAt`'s `.mapOp` arm reads `m.holdsAt hash env`. The cutover is to rebind
`DescriptorIR2.MapOp.holdsAt`'s BODY to `MapOp.holdsAtS (imtSchema SENTINEL_MAX)` — ONE line, with
`Satisfied2` and every `AlgoStarkSound*` statement UNCHANGED, because none of them mentions the
schema. What must then be repaired is exactly the set of theorems that destructure the arity-2
CONTENT of `MapOp.holdsAt` (as opposed to merely passing it along), plus the per-kind gate laws that
PRODUCE it — of which only `.absent` currently has an arity-3 version. That inventory and its price
are `docs/DESIGN-mapop-denotation-move.md`. -/

/-! ## §6 — AXIOM HYGIENE. -/

#assert_axioms opensToMerkleS_narrow
#assert_axioms writesToMerkleS_narrow
#assert_axioms narrow_holdsAtS_is_instance
#assert_axioms imtSchema_heapOk_iff
#assert_axioms imtChainOf_imtToHeap
#assert_axioms imtSchema_chain_imtSorted
#assert_axioms imtSchema_commit_of_chain
#assert_axioms spineC_linkedTo
#assert_axioms depSpine_linkedTo
#assert_axioms depHeap_heapOk
#assert_axioms topGap_holdsAtS_holds_where_holdsAt_is_refuted

end Dregg2.Circuit.MapDenotationSchema
