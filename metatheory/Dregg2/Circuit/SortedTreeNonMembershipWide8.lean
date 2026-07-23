/-
# Dregg2.Circuit.SortedTreeNonMembershipWide8 — the LEAF-SCHEMA WIDENING (felt-width site #10):
  the sorted-tree NON-MEMBERSHIP open re-keyed from a 1-felt (~31-bit, birthday-collidable) key to
  the FULL 8-felt `Digest8Key`, so non-membership binds on the WHOLE digest.

## What was already proven (do not re-derive)

  * `Crypto/NonMembership.lean::sorted_gap_excludes` — the adjacent-neighbor bracketing keystone,
    `[LinearOrder Digest]`-GENERIC (its proof never touches ℤ arithmetic).
  * `Crypto/Digest8KeySpike.lean` — `Digest8Key := Lex (Fin 8 → ℤ)` with its synthesized
    `LinearOrder` (via `Pi.Lex`), and `sorted_gap_excludes_digest8` (the combinatorial heart AT the
    8-felt lex key), plus the concrete multi-felt bracket teeth (`keyLo`/`keyE`/`keyHi`,
    `keyLo_lt_keyE` decided at felt 7, `keyE_lt_keyHi` at felt 0, `spikeLeaves`/`spike_adjacent`/
    `spike_excluded`).
  * `Circuit/Emit/LexCompare8Emit.lean::lexLt8_refines` — the emitted 8-limb lex-`<` AIR gadget.

So the CORE 8-felt non-membership at `Digest8Key` is already machine-checked. The `SortedTree`-
NonMembership**Heap8** WRAPPER, however (`GapOpen8`/`keysOf8`/`SpineCommits8`/`nonMembership_sound8`),
is still keyed by the single addr felt `keyOfH e = e.1` — THE ~31-bit waist. This file carries the
generic result THROUGH that wrapper layer.

## What this file adds

A `[LinearOrder K]`-GENERIC key-widened non-membership wrapper (`keyOfW`/`SpineCommitsW`/`keysOfW`/
`GapOpenW`/`GapOpenW.excludesSpine`/`nonMembership_soundW`), reusing `sorted_gap_excludes` for the
combinatorics (NOT re-proved), then INSTANTIATED at `K := Digest8Key`:

  * `nonMembership_sound_digest8` — the widened non-membership keystone at the full 8-felt lex key:
    a valid gap open against the committed spine ⟹ the queried key is ABSENT from the tree, indexed
    by all 8 felts.
  * `demo_excludes` — NON-VACUITY at the wrapper level: a real 8-felt gap excludes `keyE` from a
    committed `[keyLo, keyHi]` tree (the `keyLo < keyE` bracket decided at felt 7).
  * `security_delta` / `lowfelt_would_collide` — THE SECURITY DELTA, machine-checked: the queried
    `keyE` and the PRESENT neighbor `keyLo` COLLIDE on the low felt (`proj0 keyE = proj0 keyLo`, a
    birthday hit) yet are distinct 8-felt keys — the 1-felt projection sees `keyE`'s key as present
    and cannot authorize its absence, while the full 8-felt key EXCLUDES it. The excluded region is
    now indexed by the whole digest; a low-felt collision no longer forges a non-membership.
  * `nonMember_digest8` — the BRIDGE: the widened exclusion lands as the generic
    `Crypto.NonMembership.NonMember` statement at `Digest := Digest8Key` (the SAME interface the
    deployed narrow wrapper rides), so a deploy is a re-instantiation of this generic object, not a
    re-proof. The deployed narrow `SortedTreeNonMembershipHeap8.keysOf8`/`nonMembership_sound8` are
    definitionally the `K := ℤ` shadow of `keysOfW`/`nonMembership_soundW`.

## Honest scope (residuals, NOT closed here)

This is the leaf-widening SOUNDNESS proof-half. NOT here (named residuals): the value-widening
(`hash_many → hash_many_8`, `felt_to_bytes32 → digest8_to_bytes32`, Rust-calls-Lean); the widened
in-circuit chip ROW (`NonMemberRowInner` rides the DEPLOYED narrow `DeployedCapOpen.Satisfied` — the
8-felt-addr opening `Opens` is left abstract, its realizing chip is the leaf-widening Rust re-emit);
the update/insert keystone (`update_sound8` analogue, needs the mechanical `ℤ → [LinearOrder K]`
generalization of `SortedTreeNonMembership.{mem_sortedInsert,sortedInsert_sorted}`); and the
EMBER-GATED frozen kernel flip (`NullifierAccumulator.lean:12-23`, "do NOT fire piecemeal"). The
deploy stays gated; the DEPLOYED sorted-tree descriptor bytes are untouched (byte-safe additive).

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The `Digest8Key` `LinearOrder` is
noncomputable (well-founded first-differing-index comparison ⇒ `Classical.choice`, in the triple);
the AIR gadget implements the compare, Lean needs only the ORDER for the combinatorics. NEW file;
all imports read-only. No `sorry`/`admit`/`native_decide`.
-/
import Dregg2.Crypto.Digest8KeySpike
import Dregg2.Crypto.NonMembership
import Dregg2.Tactics

namespace Dregg2.Circuit.SortedTreeNonMembershipWide8

open Dregg2.Crypto.NonMembership (Sorted Adjacent sorted_gap_excludes head_lt_of_sorted NonMember)
open Dregg2.Crypto.Digest8KeySpike (Digest8Key z8 keyLo keyE keyHi spikeLeaves
  keyLo_lt_keyE keyE_lt_keyHi spikeLeaves_sorted spike_adjacent spike_member spike_excluded)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §0 — the `[LinearOrder K]`-GENERIC key-widened non-membership wrapper.

The deployed `SortedTreeNonMembershipHeap8` wrapper is `keyOfH e = e.1 : ℤ` (one addr felt). Its
non-membership proofs NEVER touch ℤ arithmetic — they ride `sorted_gap_excludes`, which is
`[LinearOrder Digest]`-generic. So the whole wrapper generalizes: a key type `K` with a linear
order, a value type `V`, a root type `Root`, and an opening predicate `Opens : Root → K × V → Prop`
(the leaf-at-root membership — the DEPLOYED chip opening, left abstract here). Instantiating
`K := ℤ, V := ℤ, Root := Digest8, Opens := MembersAt8 S8` recovers the deployed narrow wrapper;
`K := Digest8Key` is the widening. -/

section Generic

variable {K : Type*} [LinearOrder K] {V : Type*} {Root : Type*}

/-- **`keyOfW e`** — the sort key of a widened leaf: its key limb `e.1`. Widening `keyOfH`'s
`(ℤ × ℤ).1` to `(K × V).1`; at `K := Digest8Key` the key is all 8 felts. -/
def keyOfW (e : K × V) : K := e.1

/-- **`SpineCommitsW Opens root spine`** — the realizable sorted-key-spine↔root binding at the
widened key: `spine` (strictly increasing) is the sorted list of `keyOfW` keys the leaf set committed
by `root` opens at, a leaf opens at key `k` IFF `k ∈ spine`. A HYPOTHESIS, never an axiom (the
deployed `compute_canonical_heap_root_8` fold discipline). Generic twin of `SpineCommits8`. -/
structure SpineCommitsW (Opens : Root → K × V → Prop) (root : Root) (spine : List K) : Prop where
  /-- The committed key spine is strictly increasing (sorted-by-key). -/
  sorted : Sorted spine
  /-- The root binds the spine: a leaf opens at key `k` IFF `k` is a spine key. -/
  present_iff : ∀ k : K, (∃ e : K × V, keyOfW e = k ∧ Opens root e) ↔ k ∈ spine

/-- **`keysOfW Opens root`** — the committed key set at the widened key: the keys at which a leaf
opens. The non-membership target (`k ∉ keysOfW Opens root` = "the key is absent"). -/
def keysOfW (Opens : Root → K × V → Prop) (root : Root) : Set K :=
  { k | ∃ e : K × V, keyOfW e = k ∧ Opens root e }

/-- Under `SpineCommitsW`, the abstract committed key set IS the spine. -/
theorem keysOfW_eq_spine (Opens : Root → K × V → Prop) (root : Root) (spine : List K)
    (hc : SpineCommitsW Opens root spine) : ∀ k, k ∈ keysOfW Opens root ↔ k ∈ spine :=
  fun k => hc.present_iff k

/-- **`GapOpenW Opens root k`** — a non-membership covering-gap open for `k` at the widened key.
Each present neighbor is an `Opens` opening; the shape says where `k` sits. Generic twin of
`GapOpen8`. -/
inductive GapOpenW (Opens : Root → K × V → Prop) (root : Root) (k : K) where
  /-- The tree is EMPTY: everything is absent. -/
  | empty
  /-- `k` is BELOW the minimum present key: the head leaf `b` opens with `k < keyOfW b`. -/
  | below (b : K × V) (hopen : Opens root b) (hlt : k < keyOfW b)
  /-- `k` is strictly BETWEEN two ADJACENT present neighbors `a`, `b` (the widened-key bracketing
  heart — at `K := Digest8Key`, `keyOfW a < k < keyOfW b` are 8-limb lex compares). -/
  | inner (a b : K × V) (hoa : Opens root a) (hob : Opens root b)
      (hlo : keyOfW a < k) (hhi : k < keyOfW b)
  /-- `k` is ABOVE the maximum present key: the last leaf `a` opens with `keyOfW a < k`. -/
  | above (a : K × V) (hopen : Opens root a) (hgt : keyOfW a < k)

namespace GapOpenW

variable {Opens : Root → K × V → Prop} {root : Root} {k : K}

/-- **`coversSpine g spine`** — the gap's claim is VALID against the committed key spine. -/
def coversSpine : GapOpenW Opens root k → List K → Prop
  | .empty, spine => spine = []
  | .below b _ _, spine => spine.head? = some (keyOfW b)
  | .inner a b _ _ _ _, spine => Adjacent spine (keyOfW a) (keyOfW b)
  | .above a _ _, spine => spine.getLast? = some (keyOfW a)

/-- **`GapOpenW.excludesSpine` — THE COMBINATORIAL KEYSTONE (widened).** A gap open valid against the
SORTED spine proves `k ∉ spine`: the `inner` case is LITERALLY `sorted_gap_excludes` (at `K`, e.g.
the 8-felt lex key); the boundary cases ride the same strict order. UNCONDITIONAL — no crypto, no
ℤ arithmetic. Verbatim the deployed `GapOpen8.excludesSpine`, now over any `[LinearOrder K]`. -/
theorem excludesSpine (g : GapOpenW Opens root k) {spine : List K}
    (hs : Sorted spine) (hv : g.coversSpine spine) : k ∉ spine := by
  cases g with
  | empty =>
    simp only [coversSpine] at hv; subst hv; simp
  | below b _ hlt =>
    simp only [coversSpine] at hv
    cases spine with
    | nil => simp
    | cons x t =>
      have hx : x = keyOfW b := by simpa using hv
      subst hx
      intro hmem
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact absurd hlt (lt_irrefl _)
      · exact absurd ((head_lt_of_sorted hs k htail).trans hlt) (lt_irrefl _)
  | inner a b _ _ hlo hhi =>
    simp only [coversSpine] at hv
    exact sorted_gap_excludes spine (keyOfW a) (keyOfW b) k hs hv hlo hhi
  | above a _ hgt =>
    simp only [coversSpine] at hv
    obtain ⟨pre, rfl⟩ := List.getLast?_eq_some_iff.mp hv
    intro hmem
    rcases List.mem_append.mp hmem with hpre | hlast
    · have hlt : k < keyOfW a := (List.pairwise_append.mp hs).2.2 k hpre (keyOfW a) (by simp)
      exact absurd (hlt.trans hgt) (lt_irrefl _)
    · rw [List.mem_singleton.mp hlast] at hgt
      exact absurd hgt (lt_irrefl _)

end GapOpenW

/-- **`nonMembership_soundW` — THE WIDENED KEYSTONE.** Given the realizable spine↔root binding
`SpineCommitsW` and a gap open valid against that spine, the queried key `k` is ABSENT from the
committed tree (`k ∉ keysOfW Opens root`), indexed by the FULL key `K`. The bracketing is
`excludesSpine` (unconditional); `SpineCommitsW` is the only crypto residue. Generic twin of
`nonMembership_sound8`. -/
theorem nonMembership_soundW (Opens : Root → K × V → Prop) (root : Root) (k : K)
    (spine : List K) (hc : SpineCommitsW Opens root spine)
    (g : GapOpenW Opens root k) (hv : g.coversSpine spine) :
    k ∉ keysOfW Opens root := by
  have habsent : k ∉ spine := g.excludesSpine hc.sorted hv
  intro hmem
  exact habsent ((keysOfW_eq_spine Opens root spine hc k).mp hmem)

end Generic

/-! ## §1 — INSTANTIATION at the 8-felt lex key `Digest8Key`: the leaf-widening keystone. -/

/-- **`nonMembership_sound_digest8` — the widened non-membership keystone AT THE FULL 8-FELT KEY.**
A valid covering-gap open against the committed spine (whose brackets are 8-limb lex compares) proves
the queried key ABSENT — indexed by all 8 felts, not the ~31-bit addr felt. The `Digest8Key`
instantiation of `nonMembership_soundW`; the leaf-widening of `SortedTreeNonMembershipHeap8`'s
`nonMembership_sound8`. -/
theorem nonMembership_sound_digest8 {V : Type*} {Root : Type*}
    (Opens : Root → Digest8Key × V → Prop) (root : Root) (k : Digest8Key)
    (spine : List Digest8Key) (hc : SpineCommitsW Opens root spine)
    (g : GapOpenW Opens root k) (hv : g.coversSpine spine) :
    k ∉ keysOfW Opens root :=
  nonMembership_soundW Opens root k spine hc g hv

/-! ## §2 — NON-VACUITY at the wrapper level: a real 8-felt gap the 1-felt key would collide. -/

/-- The demo opening predicate over the fixed committed leaf set (root `= Unit`): a widened leaf
`(key, val)` opens IFF its 8-felt key is one of the committed spike leaves `[keyLo, keyHi]`. -/
def demoOpens : Unit → Digest8Key × ℤ → Prop := fun _ e => e.1 ∈ spikeLeaves

/-- The committed tree binds the sorted spike spine `[keyLo, keyHi]` (sorted from the spike). -/
theorem demoOpens_spine : SpineCommitsW demoOpens () spikeLeaves :=
  { sorted := spikeLeaves_sorted
    present_iff := fun k =>
      ⟨fun ⟨_e, he, hmem⟩ => he ▸ hmem, fun hk => ⟨(k, 0), rfl, hk⟩⟩ }

theorem keyHi_mem : keyHi ∈ spikeLeaves := by simp [spikeLeaves]

/-- The inner gap open for `keyE` against `[keyLo, keyHi]`: both neighbors open, and
`keyLo < keyE < keyHi` — the LOW compare decided at felt 7, the HIGH at felt 0 (genuinely 8-limb,
not a felt-0 disguise). -/
def demoGap : GapOpenW demoOpens () keyE :=
  .inner (keyLo, 0) (keyHi, 0) spike_member keyHi_mem keyLo_lt_keyE keyE_lt_keyHi

theorem demoGap_covers : demoGap.coversSpine spikeLeaves := spike_adjacent

/-- **★ NON-VACUITY (wrapper level).** The widened non-membership keystone EXCLUDES `keyE` from the
committed 8-felt-keyed tree `[keyLo, keyHi]` — the wrapper FIRES on a real multi-felt bracket. -/
theorem demo_excludes : keyE ∉ keysOfW demoOpens () :=
  nonMembership_sound_digest8 demoOpens () keyE spikeLeaves demoOpens_spine demoGap demoGap_covers

/-! ## §3 — THE SECURITY DELTA: the low-felt collision no longer forges a non-membership. -/

/-- The deployed ~31-bit waist reads a SINGLE limb of the digest (`keyOfH e = e.1`) — modeled here
as the felt-0 projection `proj0`. Two 8-felt keys agreeing on this limb are CONFLATED by the 1-felt
key even when distinct. -/
def proj0 (d : Digest8Key) : ℤ := ofLex d 0

theorem proj0_keyLo : proj0 keyLo = 0 := rfl

theorem proj0_keyE : proj0 keyE = 0 := by
  show (if (0 : Fin 8) = 7 then (1 : ℤ) else 0) = 0
  decide

/-- The queried key `keyE` and the PRESENT neighbor `keyLo` COLLIDE on the low felt (both project to
`0`) yet are DISTINCT 8-felt keys — a real birthday hit the 1-felt key cannot separate (`keyLo < keyE`
is decided at felt 7, a limb `proj0` discards). -/
theorem lowfelt_collision : proj0 keyE = proj0 keyLo ∧ keyE ≠ keyLo :=
  ⟨by rw [proj0_keyE, proj0_keyLo], keyLo_lt_keyE.ne'⟩

theorem keyLo_present : keyLo ∈ keysOfW demoOpens () :=
  ⟨(keyLo, 0), rfl, spike_member⟩

/-- **★ THE SECURITY DELTA, machine-checked.** Against the SAME committed tree `[keyLo, keyHi]`:
  * (collision) `proj0 keyE = proj0 keyLo` with `keyLo` PRESENT — the deployed 1-felt projection maps
    the queried `keyE` onto a present key, so a non-membership indexed by `proj0` cannot authorize
    `keyE`'s absence (it looks present);
  * (widened exclusion) the FULL 8-felt lex key EXCLUDES `keyE` (`keyE ∉ keysOfW demoOpens ()`),
    because the `keyLo < keyE` bracket is decided at felt 7 — a limb the 1-felt projection discards;
  * (real hit) `keyE ≠ keyLo` — the collision is a genuine distinct-key birthday hit, not equality.
The excluded region is now indexed by ALL 8 felts: a low-felt (~31-bit, 2^15.5-collidable) collision
no longer forges a non-membership open. -/
theorem security_delta :
    (proj0 keyE = proj0 keyLo ∧ keyLo ∈ keysOfW demoOpens ()) ∧
    keyE ∉ keysOfW demoOpens () ∧ keyE ≠ keyLo :=
  ⟨⟨lowfelt_collision.1, keyLo_present⟩, demo_excludes, lowfelt_collision.2⟩

/-- The delta restated as the projection GAP: the 1-felt image of the committed key set CONTAINS
`proj0 keyE` (via the colliding present neighbor `keyLo`), even though the 8-felt key set does NOT
contain `keyE`. The gap between "present under `proj0`" and "absent under the full key" is exactly the
~31-bit waist this widening closes. -/
theorem lowfelt_would_collide :
    (∃ x ∈ keysOfW demoOpens (), proj0 x = proj0 keyE) ∧ keyE ∉ keysOfW demoOpens () :=
  ⟨⟨keyLo, keyLo_present, lowfelt_collision.1.symm⟩, demo_excludes⟩

/-! ## §4 — the BRIDGE: the widened exclusion IS an instance of the generic `NonMembership`. -/

/-- **`nonMember_digest8` — the re-instantiation bridge.** The widened exclusion lands as the generic
`Crypto.NonMembership.NonMember` statement at `Digest := Digest8Key` — the SAME interface the deployed
narrow (`SortedTreeNonMembershipHeap8`, via `sorted_gap_excludes`) rides, now at the full 8-felt key.
A deploy is a re-instantiation of this generic object, not a re-proof; the deployed narrow
`keysOf8`/`nonMembership_sound8` are the definitional `K := ℤ` shadow of `keysOfW`/
`nonMembership_soundW`. -/
theorem nonMember_digest8 : NonMember spikeLeaves keyE :=
  ⟨spikeLeaves_sorted, spike_excluded⟩

/-! ## §5 — axiom hygiene: every widened keystone rests on the kernel triple only. -/

#assert_axioms keysOfW_eq_spine
#assert_axioms GapOpenW.excludesSpine
#assert_axioms nonMembership_soundW
#assert_axioms nonMembership_sound_digest8
#assert_axioms demo_excludes
#assert_axioms security_delta
#assert_axioms lowfelt_would_collide
#assert_axioms nonMember_digest8

end Dregg2.Circuit.SortedTreeNonMembershipWide8
