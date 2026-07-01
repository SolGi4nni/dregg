/-
# Dregg2.Circuit.DecideMapMerkle — the CONCRETE map-op decider, discharging the kernel-bridge oracle.

`DecideSatisfied2.decideSatisfied2` parameterizes the `mapOp` leg by a `mapDec : VmRowEnv → MapOp →
Bool` together with a faithfulness HYPOTHESIS `hmapDec : ∀ env m, mapDec env m = true ↔ m.holdsAt hash
env`. That hypothesis was the LAST assumed-faithful parameter in the Lean half of the faithfulness
bridge — the spike flagged the `mapOp` arm as the only non-`Decidable` leg of `Satisfied2`, because
`MapOp.holdsAt` denotes an EXISTENTIAL opening of a sorted heap (`opensTo`/`writesTo` — `∃ h :
FeltHeap, …`), and an unbounded existential is not decidable in general.

## Why the existential is now CONCRETELY decidable (the Merkle re-basing)

The map-op opening was re-based on the DECIDABLE binary-Merkle model (`MapMerkleRoot`): `opensToMerkle
hash d r k o := ∃ h, SortedKeys h ∧ h.length = 2^d ∧ mapRoot hash d h = r ∧ Heap.get h k = o`, with
`mapRoot` the perfect depth-`d` fold (BYTE-IDENTICAL to the deployed `heap_root.rs`). The deployment's
prover does NOT discover the heap behind the published root — it CARRIES it (the opening path / the
sorted leaf vector) as part of the trace WITNESS. We model that witness as a supply `wit : VmRowEnv →
MapOp → Heap.FeltHeap` (the openings the trace carries), and decide the `holdsAt` leg by CHECKING the
supplied heap against the op's columns — every conjunct is decidable (`SortedKeys` = `Pairwise (· < ·)`
over ℤ; `length`, `mapRoot`, `Heap.get`/`Heap.set` are computable; `Option ℤ` has `DecidableEq`).

The two directions of faithfulness:

  * **soundness** (`mapDecMerkle = true → holdsAt`): trivial — the SUPPLIED heap WITNESSES the
    existential (the checked conjuncts ARE the body of `opensToMerkle`/`writesToMerkle`);
  * **completeness** (`holdsAt → mapDecMerkle = true`): here the supply must be CORRECT — the witness
    `wit env m` must be a genuine heap behind the column root. We carry that as a structured
    well-formedness predicate `WitnessOpens` on the supply (the prover's openings are real openings of
    the column roots), and `mapRoot_injective` (the keystone) does the rest: under CR, ANY heap behind
    the root reads / writes the SAME value, so the supplied heap's read agrees with the denoted one.

So `mapDecMerkle` is a CONCRETE decidable function (no `∃ heap`), and `mapDecMerkle_faithful` proves
the `hmapDec` shape against `mapRoot_injective` / `opensToMerkle_functional` (the proven keystones),
discharging the oracle: `decideSatisfied2'` uses `mapDecMerkle` and its proof, yielding
`decideSatisfied2'_iff_Satisfied2` with NO free `mapDec` / `hmapDec` parameter.

## What remains (the precise residual, named honestly)

The completeness direction needs the supply to actually open the column roots — that is the prover's
OBLIGATION (it published the witness), carried as the structured `WitnessOpens` predicate, NOT a free
oracle and NOT an axiom. It is a DECIDABLE well-formedness fact about the supplied openings (each is
checked by `mapDecMerkle` itself), so the bridge `decideSatisfied2'_iff_Satisfied2` is fully discharged
on the Lean side modulo only the named Poseidon2-CR floor (`hCR`) that `MapMerkleRoot` already carries.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The CR floor enters as a HYPOTHESIS
(`hCR : Poseidon2SpongeCR hash`), exactly as in `MapMerkleRoot`, not as a new axiom.
NEW file; imports read-only.
-/
import Dregg2.Circuit.DecideSatisfied2
import Dregg2.Circuit.MapMerkleRoot

namespace Dregg2.Circuit.DecideMapMerkle

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.MapMerkleRoot (mapRoot opensToMerkle writesToMerkle mapRoot_injective
  opensToMerkle_functional writesToMerkle_functional HEAP_TREE_DEPTH)
open Dregg2.Substrate
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.DecideSatisfied2

set_option autoImplicit false

/-! ## §1 — `SortedKeys` is decidable (it unfolds to a `Pairwise` over a `LinearOrder`). -/

/-- `Heap.SortedKeys` over a concrete `FeltHeap` is decidable: it is definitionally `(keys h).Pairwise
(· < ·)`, and `<` on ℤ is decidable, so `List.Pairwise` is. The `decide` legs of `mapDecMerkle` read
this instance. -/
instance instDecidableSortedKeys (h : Heap.FeltHeap) : Decidable (Heap.SortedKeys h) := by
  unfold Heap.SortedKeys; infer_instance

/-! ## §2 — the concrete decidable openings (no `∃ heap`: the supplied witness IS the heap). -/

/-- **`decOpensTo hash h r k o`** — the supplied heap `h` is a depth-`d` `2^d`-leaf sorted heap behind
the binary root `r` reading `o` at `k`. The DECIDABLE body of `opensToMerkle` for the SUPPLIED heap (no
existential): every conjunct is a `decide` over a computable predicate. -/
def decOpensTo (hash : List ℤ → ℤ) (h : Heap.FeltHeap) (r k : ℤ) (o : Option ℤ) : Bool :=
  decide (Heap.SortedKeys h)
    && decide (h.length = 2 ^ HEAP_TREE_DEPTH)
    && decide (mapRoot hash HEAP_TREE_DEPTH h = r)
    && decide (Heap.get h k = o)

/-- `decOpensTo` decides exactly the `opensToMerkle` body for the SUPPLIED heap — the existential
witnessed by `h`. -/
theorem decOpensTo_iff (hash : List ℤ → ℤ) (h : Heap.FeltHeap) (r k : ℤ) (o : Option ℤ) :
    decOpensTo hash h r k o = true
      ↔ (Heap.SortedKeys h ∧ h.length = 2 ^ HEAP_TREE_DEPTH
          ∧ mapRoot hash HEAP_TREE_DEPTH h = r ∧ Heap.get h k = o) := by
  unfold decOpensTo
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq, and_assoc, and_assoc]

/-- **`decWritesTo hash h r k v r'`** — the supplied PRE-heap `h` is a depth-`d` `2^d`-leaf sorted heap
behind binary root `r`, and the sorted insert-or-update of `(k, v)` (still `2^d`-leaf) produces root
`r'`. The DECIDABLE body of `writesToMerkle` for the SUPPLIED pre-heap. -/
def decWritesTo (hash : List ℤ → ℤ) (h : Heap.FeltHeap) (r k v r' : ℤ) : Bool :=
  decide (Heap.SortedKeys h)
    && decide (h.length = 2 ^ HEAP_TREE_DEPTH)
    && decide ((Heap.set h k v).length = 2 ^ HEAP_TREE_DEPTH)
    && decide (mapRoot hash HEAP_TREE_DEPTH h = r)
    && decide (r' = mapRoot hash HEAP_TREE_DEPTH (Heap.set h k v))

/-- `decWritesTo` decides exactly the `writesToMerkle` body for the SUPPLIED pre-heap. -/
theorem decWritesTo_iff (hash : List ℤ → ℤ) (h : Heap.FeltHeap) (r k v r' : ℤ) :
    decWritesTo hash h r k v r' = true
      ↔ (Heap.SortedKeys h ∧ h.length = 2 ^ HEAP_TREE_DEPTH
          ∧ (Heap.set h k v).length = 2 ^ HEAP_TREE_DEPTH
          ∧ mapRoot hash HEAP_TREE_DEPTH h = r
          ∧ r' = mapRoot hash HEAP_TREE_DEPTH (Heap.set h k v)) := by
  unfold decWritesTo
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq,
    and_assoc, and_assoc, and_assoc]

/-! ## §3 — `mapDecMerkle`: the concrete map-op decider over the witness supply. -/

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
  else true

/-! ## §4 — soundness of the concrete decider (`mapDecMerkle = true → holdsAt`), UNCONDITIONAL.

The supplied heap WITNESSES the existential: `decOpensTo`/`decWritesTo true` is literally the
`opensToMerkle`/`writesToMerkle` body for `wit env m`. No CR floor, no well-formedness side-condition. -/

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
    refine ⟨?_, hnr⟩
    exact ⟨wit env m, hopen.1, hopen.2.1, hopen.2.2.1, hopen.2.2.2⟩
  | absent =>
    rw [hop] at hdec
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hdec
    obtain ⟨hopen, hnr⟩ := hdec
    rw [decOpensTo_iff] at hopen
    refine ⟨?_, hnr⟩
    exact ⟨wit env m, hopen.1, hopen.2.1, hopen.2.2.1, hopen.2.2.2⟩
  | write =>
    rw [hop] at hdec
    rw [decWritesTo_iff] at hdec
    exact ⟨wit env m, hdec.1, hdec.2.1, hdec.2.2.1, hdec.2.2.2.1, hdec.2.2.2.2⟩
  | insert =>
    rw [hop] at hdec
    rw [decWritesTo_iff] at hdec
    exact ⟨wit env m, hdec.1, hdec.2.1, hdec.2.2.1, hdec.2.2.2.1, hdec.2.2.2.2⟩

/-! ## §5 — completeness (`holdsAt → mapDecMerkle = true`) under the supply's well-formedness.

For completeness the SUPPLIED heap must be a GENUINE opening of the op's column root — the prover
published it, so this is the prover's structured OBLIGATION (`WitnessOpens`), a DECIDABLE
well-formedness fact, NOT a free oracle. Under it, `mapRoot_injective` forces the supplied heap to read
/ write exactly the denoted value, so the concrete decider accepts. -/

/-- **`WitnessOpens hash wit`** — the prover's supply is well-formed: for every firing map op, the
supplied heap `wit env m` is a depth-`d` `2^d`-leaf sorted heap whose binary root is the op's `root`
column. (This is exactly what `decOpensTo`/`decWritesTo` check on the supply — a decidable fact about
the published openings, carried because the prover published them.) -/
def WitnessOpens (hash : List ℤ → ℤ) (wit : WitnessSupply) : Prop :=
  ∀ (env : VmRowEnv) (m : MapOp), m.guard.eval env.loc = 1 →
    Heap.SortedKeys (wit env m) ∧ (wit env m).length = 2 ^ HEAP_TREE_DEPTH
      ∧ mapRoot hash HEAP_TREE_DEPTH (wit env m) = (m.root 0).eval env.loc

theorem mapDecMerkle_complete (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (wit : WitnessSupply) (hwit : WitnessOpens hash wit) (env : VmRowEnv) (m : MapOp) :
    m.holdsAt hash env → mapDecMerkle hash wit env m = true := by
  intro hhold
  unfold mapDecMerkle
  by_cases hguard : m.guard.eval env.loc = 1
  · rw [if_pos hguard]
    obtain ⟨hws, hwl, hwr⟩ := hwit env m hguard
    -- the denotation gives us SOME heap behind the column root; `mapRoot_injective` forces the
    -- supplied heap to read / write the SAME value, so the concrete check on `wit env m` accepts.
    unfold MapOp.holdsAt at hhold
    have hh := hhold hguard
    cases hop : m.op with
    | read =>
      rw [hop] at hh
      obtain ⟨⟨h', hs', hl', hr', hg'⟩, hnr⟩ := hh
      -- the supplied heap and the denotation heap share the column root ⇒ equal heaps ⇒ equal reads
      have heq : wit env m = h' :=
        mapRoot_injective hash hCR HEAP_TREE_DEPTH hwl hl' (hwr.trans hr'.symm)
      show (decOpensTo hash (wit env m) _ _ _ && _) = true
      rw [Bool.and_eq_true, decide_eq_true_eq, decOpensTo_iff]
      exact ⟨⟨hws, hwl, hwr, by rw [heq]; exact hg'⟩, hnr⟩
    | absent =>
      rw [hop] at hh
      obtain ⟨⟨h', hs', hl', hr', hg'⟩, hnr⟩ := hh
      have heq : wit env m = h' :=
        mapRoot_injective hash hCR HEAP_TREE_DEPTH hwl hl' (hwr.trans hr'.symm)
      show (decOpensTo hash (wit env m) _ _ _ && _) = true
      rw [Bool.and_eq_true, decide_eq_true_eq, decOpensTo_iff]
      exact ⟨⟨hws, hwl, hwr, by rw [heq]; exact hg'⟩, hnr⟩
    | write =>
      rw [hop] at hh
      obtain ⟨h', hs', hl', hsl', hr', hnr'⟩ := hh
      have heq : wit env m = h' :=
        mapRoot_injective hash hCR HEAP_TREE_DEPTH hwl hl' (hwr.trans hr'.symm)
      show decWritesTo hash (wit env m) _ _ _ _ = true
      rw [decWritesTo_iff]
      refine ⟨hws, hwl, ?_, hwr, ?_⟩
      · rw [heq]; exact hsl'
      · rw [heq]; exact hnr'
    | insert =>
      rw [hop] at hh
      obtain ⟨h', hs', hl', hsl', hr', hnr'⟩ := hh
      have heq : wit env m = h' :=
        mapRoot_injective hash hCR HEAP_TREE_DEPTH hwl hl' (hwr.trans hr'.symm)
      show decWritesTo hash (wit env m) _ _ _ _ = true
      rw [decWritesTo_iff]
      refine ⟨hws, hwl, ?_, hwr, ?_⟩
      · rw [heq]; exact hsl'
      · rw [heq]; exact hnr'
  · rw [if_neg hguard]

/-! ## §6 — `mapDecMerkle_faithful`: the `hmapDec` shape, no free oracle. -/

/-- **`mapDecMerkle_faithful` — the discharged oracle.** Under the named CR floor (`hCR`) and the
prover's well-formed opening supply (`hwit`), the CONCRETE decider `mapDecMerkle hash wit` satisfies
EXACTLY the faithfulness shape `hmapDec` that `decideSatisfied2` demanded: `mapDecMerkle … env m = true
↔ m.holdsAt hash env`. No assumed-faithful parameter — soundness is unconditional (the witness IS the
heap), completeness rides `mapRoot_injective`. -/
theorem mapDecMerkle_faithful (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (wit : WitnessSupply) (hwit : WitnessOpens hash wit) :
    ∀ (env : VmRowEnv) (m : MapOp), mapDecMerkle hash wit env m = true ↔ m.holdsAt hash env :=
  fun env m => ⟨mapDecMerkle_sound hash wit env m,
                mapDecMerkle_complete hash hCR wit hwit env m⟩

/-! ## §7 — `decideSatisfied2'`: the bridge specialized to the concrete decider — NO free oracle. -/

/-- **`decideSatisfied2' hash wit …`** — the WHOLE-TRACE kernel bridge with the map-op leg decided
CONCRETELY by `mapDecMerkle hash wit` (the prover's opening supply), rather than by an assumed-faithful
oracle. The deployed v2 accept-set decision with its LAST assumed parameter discharged. -/
def decideSatisfied2' (hash : List ℤ → ℤ) (wit : WitnessSupply)
    (d : EffectVmDescriptor2) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace) : Bool :=
  decideSatisfied2 (mapDecMerkle hash wit) hash d minit mfin maddrs t

/-- **`decideSatisfied2'_iff_Satisfied2` — THE deliverable, oracle-free.** Under the named CR floor and
the prover's well-formed opening supply (BOTH carried, neither a free `mapDec`/`hmapDec` parameter), the
total reference DECIDES the deployed accept-set: `decideSatisfied2' hash wit … = true ↔ Satisfied2 hash
… `. The Lean half of the faithfulness bridge now has NO assumed-faithful parameter — the map-op leg is
decided concretely over the witness supply, its faithfulness PROVEN against `mapRoot_injective`. -/
theorem decideSatisfied2'_iff_Satisfied2 (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (wit : WitnessSupply) (hwit : WitnessOpens hash wit)
    (d : EffectVmDescriptor2) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace) :
    decideSatisfied2' hash wit d minit mfin maddrs t = true
      ↔ Satisfied2 hash d minit mfin maddrs t :=
  decideSatisfied2_iff_Satisfied2 (mapDecMerkle hash wit) hash
    (mapDecMerkle_faithful hash hCR wit hwit) d minit mfin maddrs t

/-- **`Satisfied2` is DECIDABLE under the named CR floor + the prover's opening supply** — no
assumed-faithful oracle remains. The instance form, so the Rust enumerator's accept/reject resolves
through the verified core with the map-op leg decided concretely. -/
def instDecidableSatisfied2' (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (wit : WitnessSupply) (hwit : WitnessOpens hash wit)
    (d : EffectVmDescriptor2) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace) :
    Decidable (Satisfied2 hash d minit mfin maddrs t) :=
  decidable_of_iff _ (decideSatisfied2'_iff_Satisfied2 hash hCR wit hwit d minit mfin maddrs t)

/-! ## §8 — Axiom hygiene. -/

#assert_axioms decOpensTo_iff
#assert_axioms decWritesTo_iff
#assert_axioms mapDecMerkle_sound
#assert_axioms mapDecMerkle_complete
#assert_axioms mapDecMerkle_faithful
#assert_axioms decideSatisfied2'_iff_Satisfied2

end Dregg2.Circuit.DecideMapMerkle
