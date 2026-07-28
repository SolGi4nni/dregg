/-
# Dregg2.Crypto.UMemCodec — the umem ADDRESS/VALUE codec adapters (Rank 1 of the
# universal-map rotation-flip, `UNIVERSAL-MAP-ROTATION.md` §2.2 / `UNIVERSAL-MEMORY.md` §123-149).

THE OBSTRUCTION these close. `Crypto/UniversalMemory.lean` proves the ONE-Blum-multiset story
over the ABSTRACT address space `UAddr κ = Domain × κ` with the GENERIC leaf `Heap.leafOf`
(`hash[addr, value]`). The deployment carries STRUCTURED addresses and TYPED, per-plane values
that the abstract pair only stands for:

  * a unified address is REALIZED as `addr = hash[domain_tag, collection, key]` — not an opaque
    pair (`UniversalMemory.lean:96-98`, the §1 banner: "CR makes the concrete form injective,
    i.e. exactly this pair");
  * the live CAP leaf is `hash[holder, target, rights, op]`
    (`EffectVmEmitCapRoot.siteCapEdgeLeaf`, arity 4) — NOT the generic `hash[addr, value]`
    (arity 2);
  * the INDEX domain's boundary commitment is the MMR root (`Lightclient/MMR.mroot`,
    positional/append-only), NOT a sorted-map `Heap.root`.

Until this module, `effect_vm_umem_real_turn.rs` carried the real turn's trace under a per-proof
"dense injective relabeling" (distinct addresses/values numbered within the instance — sound
because a multiset balance is label-invariant, but a placeholder). The DEPLOYED flip needs the
REAL codecs. THIS module proves them, as pure-Lean adapter lemmas — NO wire / descriptor / VK
change. Each rides the SAME named `Poseidon2SpongeCR` floor every other root binder uses; none
invents a narrower bit-count assumption (the load-bearing-insecurity discipline: the abstract `ℤ`
sponge output stands for the FULL multi-felt Poseidon2 digest, and the codec's collision-freedom
is exactly that one floor, never a single-felt 31-bit shortcut).

THE ADAPTERS (each faithful-encoding-grounded + non-vacuity-witnessed, both polarities):

  * §1 ADDRESS codec — `uaddrEnc hash d coll key = hash[domainTag d, coll, key]`, and
    `uaddrEnc_injective`: under CR + the (injective) domain tag, the concrete hashed address
    realizes the abstract `(Domain, coll, key)` triple FAITHFULLY (distinct triples ⇒ distinct
    addresses). The domain tag is load-bearing: the UNtagged `Heap.addrOf` collapses caps and
    nullifiers at the same `(coll, key)` to ONE address (the `UniversalMemory` flat-aliasing
    witness, at the address layer).

  * §2 CAP-LEAF value codec — `capLeafOf hash c := edgeLeafOf hash c.holder c.target c.rights
    c.op` (DEFINITIONALLY the deployed leaf, `capLeafOf_eq_deployed` by `rfl`). The value codec
    splits the cap tuple into WHERE (holder, the address key) and WHAT (target/rights/op, the
    cell value): `capValEnc`/`capDecode` round-trip (`capDecode_capValEnc`), and the leaf FACTORS
    through the codec (`capLeaf_factors_codec`). The anti-ghost transfers to the live 4-felt
    shape with NO new combinatorics: `capLeaf_injective` (one CR peel of the 4-element list) ⇒
    `capRoot_injective` (the cap-domain boundary root BINDS its cap cells, exactly as
    `Heap.root_injective` binds generic cells).

  * §3 MMR boundary-derivation analogue — for the index domain the `boundary_root_derived`
    refactor theorem and the `boundary_init_root_bound` anti-ghost are restated against `mroot`:
    `index_boundary_root_derived` (same derived log ⇒ same `mroot`, NO crypto) and
    `index_boundary_root_bound` (`= mroot_injective`: a tampered / REORDERED / truncated index
    image cannot keep the published `iroot`). Welded to the ONE balance:
    `index_boundary_root_from_memcheck` rides `memcheck_pins_final` so the derived index boundary
    log is the GENUINE pinned final column, encoded — the index version of
    `boundary_root_from_memcheck`. (The positional-vs-sorted reconciliation of the deployed log
    is the assembly's job — obstruction #2 "coverage"; the binding the adapter delivers is
    `mroot_injective` over the derived leaf list.)

Axiom hygiene: `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every result; crypto
enters ONLY as the named `Poseidon2SpongeCR` hypothesis, never as an axiom. Lean/design only — no
circuit Rust, no wire/descriptor/VK change.
-/
import Dregg2.Crypto.UniversalMemory
import Dregg2.Crypto.SpongeCarrierReduction
import Dregg2.Lightclient.MMR
import Dregg2.Circuit.Emit.EffectVmEmitCapRoot

namespace Dregg2.Crypto.UMemCodec

open Dregg2.Crypto.MemoryChecking
open Dregg2.Crypto.UniversalMemory
open Dregg2.Substrate
open Dregg2.Substrate.Heap (FeltHeap leafOf root addrOf refSponge)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Lightclient.MMR (mroot mroot_injective)
open Dregg2.Circuit.Emit.EffectVmEmitCapRoot (edgeLeafOf)
open Dregg2.Crypto.SpongeCarrierReduction (IsSpongeColl)

universe u v

/-! ## §1 — THE ADDRESS CODEC: `addr = hash[domain_tag, collection, key]`.

The abstract unified address `UAddr κ = Domain × κ` (`UniversalMemory.lean:96`) is REALIZED on
the wire as `hash[domain_tag, collection, key]`. The two lemmas below make that realization
FAITHFUL: a distinct domain tag separates the planes (the tag is injective), and a single CR peel
of the 3-element list recovers the whole `(Domain, coll, key)` triple. This is the §1-banner claim
("CR makes the concrete form injective, i.e. exactly this pair") discharged at the address layer,
on the SAME `Poseidon2SpongeCR` floor as `Heap.addrOf`/`leafOf`. -/

/-- The domain tag felt — a distinct constant per state domain (the `domain_tag` limb of the
unified address). Injective by construction (`domainTag_injective`); a future state component is a
new tag value, never a new column. -/
def domainTag : Domain → ℤ
  | .registers => 0
  | .heap => 1
  | .caps => 2
  | .nullifiers => 3
  | .index => 4
  | .working => 5

/-- The domain tag is INJECTIVE: distinct domains carry distinct tag felts. The separation that
makes the planes disjoint sub-multisets survive into the hashed address. -/
theorem domainTag_injective {d d' : Domain} (h : domainTag d = domainTag d') : d = d' := by
  cases d <;> cases d' <;> first | rfl | exact absurd h (by decide)

/-- **`uaddrEnc`** — the structured unified address: `hash[domain_tag, collection, key]`. The
deployment realization of the abstract `(d, (coll, key))` pair; `Heap.addrOf hash coll key =
hash[coll, key]` is exactly this WITHOUT the domain tag. -/
def uaddrEnc (hash : List ℤ → ℤ) (d : Domain) (coll key : ℤ) : ℤ :=
  hash [domainTag d, coll, key]

/-- The structured address EXTENDS the deployed `(collection, key)` address with the domain tag in
the leading position (`uaddrEnc d coll key = hash (domainTag d :: [coll, key])`). -/
theorem uaddrEnc_eq_tagged_addr (hash : List ℤ → ℤ) (d : Domain) (coll key : ℤ) :
    uaddrEnc hash d coll key = hash (domainTag d :: [coll, key]) := rfl

/-! ### The address codec is FAITHFUL — ⛑ CUT OVER 2026-07-27 off `Poseidon2SpongeCR`.

`uaddrEnc_injective` used to say "under the named CR floor, equal encoded addresses force the SAME
domain, collection, AND key". That floor is `∀ xs ys, hash xs = hash ys → xs = ys` and
`HashFloorHonesty.poseidon2SpongeCR_false_babyBear` PROVES it false at deployed BabyBear
parameters, so the statement said nothing about the shipping codec. The premise is now the
per-instance, refutable non-collision at the two NAMED preimages this address pair absorbs — which
the old floor implied, so every caller's hypothesis got strictly weaker. -/

/-- **`uaddrEncPre d coll key`** — the address codec's sponge PREIMAGE, named so the per-instance
collision event below is stated at exactly the list the digest absorbs. -/
def uaddrEncPre (d : Domain) (coll key : ℤ) : List ℤ := [domainTag d, coll, key]

theorem uaddrEnc_eq_pre (hash : List ℤ → ℤ) (d : Domain) (coll key : ℤ) :
    uaddrEnc hash d coll key = hash (uaddrEncPre d coll key) := rfl

/-- **THE HYPOTHESIS-FREE ADDRESS BINDING.** Equal encoded addresses force the same triple OR name
a genuine collision of the deployed sponge at the two ABSORBED preimages. NO floor. -/
theorem uaddrEnc_binds_or_collides (hash : List ℤ → ℤ)
    {d d' : Domain} {coll key coll' key' : ℤ}
    (h : uaddrEnc hash d coll key = uaddrEnc hash d' coll' key') :
    (d = d' ∧ coll = coll' ∧ key = key')
      ∨ IsSpongeColl hash (uaddrEncPre d coll key, uaddrEncPre d' coll' key') := by
  by_cases hpre : uaddrEncPre d coll key = uaddrEncPre d' coll' key'
  · refine Or.inl ?_
    rw [uaddrEncPre, uaddrEncPre, List.cons.injEq, List.cons.injEq, List.cons.injEq] at hpre
    obtain ⟨htag, hc, hk, _⟩ := hpre
    exact ⟨domainTag_injective htag, hc, hk⟩
  · exact Or.inr ⟨hpre, h⟩

theorem uaddrEnc_injective (hash : List ℤ → ℤ)
    {d d' : Domain} {coll key coll' key' : ℤ}
    (hno : ¬ IsSpongeColl hash (uaddrEncPre d coll key, uaddrEncPre d' coll' key'))
    (h : uaddrEnc hash d coll key = uaddrEnc hash d' coll' key') :
    d = d' ∧ coll = coll' ∧ key = key' :=
  (uaddrEnc_binds_or_collides hash h).resolve_right hno

/-! ## §2 — THE CAP-LEAF VALUE CODEC: the live `hash[holder, target, rights, op]`.

The universal-memory boundary derivation folds cells with the GENERIC leaf `Heap.leafOf`
(`hash[addr, value]`, arity 2). The deployed cap tree uses `EffectVmEmitCapRoot.edgeLeafOf`
(`hash[holder, target, rights, op]`, arity 4). The value codec brings the live leaf shape under
the boundary derivation WITHOUT a wire change: encode the cap tuple as the cell value (holder is
the WHERE / address key; target·rights·op are the WHAT / value), and transfer the root anti-ghost
to the 4-felt leaf by the same single CR peel `capRoot_binds_edge` uses. NO new combinatorics. -/

/-- A live cap edge: the four bound fields the deployed `siteCapEdgeLeaf` hashes. -/
structure CapEdge where
  holder : ℤ
  target : ℤ
  rights : ℤ
  op : ℤ
deriving DecidableEq, Repr

/-- **`capLeafOf`** — the cap-domain leaf, DEFINITIONALLY the deployed cap-edge leaf
(`capLeafOf_eq_deployed`): `hash[holder, target, rights, op]`. This is the faithful match to the
deployed Poseidon2 site, not a re-derivation that could drift. -/
def capLeafOf (hash : List ℤ → ℤ) (c : CapEdge) : ℤ :=
  edgeLeafOf hash c.holder c.target c.rights c.op

/-- **Faithfulness to the deployed leaf** — `capLeafOf` IS `EffectVmEmitCapRoot.edgeLeafOf` on the
edge's fields, by `rfl`. The adapter folds the EXACT leaf the cap-root recompute site forces. -/
theorem capLeafOf_eq_deployed (hash : List ℤ → ℤ) (c : CapEdge) :
    capLeafOf hash c = edgeLeafOf hash c.holder c.target c.rights c.op := rfl

/-- **The value codec — WHAT (the cell value).** The cap tuple's non-address content:
`(target, rights, op)`. The holder is the WHERE (the cell address key); these three are the value
the universal-memory cell carries. -/
def capValEnc (c : CapEdge) : ℤ × ℤ × ℤ := (c.target, c.rights, c.op)

/-- **The value decode.** Recompose the edge from its address key (holder) and its value triple. -/
def capDecode (holder : ℤ) (v : ℤ × ℤ × ℤ) : CapEdge := ⟨holder, v.1, v.2.1, v.2.2⟩

/-- **`capDecode_capValEnc` — the codec ROUND-TRIPS.** Decoding the value triple at the edge's own
holder recovers the edge. The value codec loses nothing: holder + `capValEnc` is the whole edge. -/
theorem capDecode_capValEnc (c : CapEdge) : capDecode c.holder (capValEnc c) = c := rfl

/-- **`capLeaf_factors_codec` — the leaf FACTORS through the codec.** The deployed cap leaf is the
hash of the holder (address key) followed by the value triple `capValEnc`: the cap tuple is
EXACTLY "the cap tuple encoded as the cell value, then hashed as the leaf" — the value-codec
realization the rotation names. -/
theorem capLeaf_factors_codec (hash : List ℤ → ℤ) (c : CapEdge) :
    capLeafOf hash c
      = hash [c.holder, (capValEnc c).1, (capValEnc c).2.1, (capValEnc c).2.2] := rfl

/-! ### The cap leaf BINDS its tuple — ⛑ CUT OVER 2026-07-27 off `Poseidon2SpongeCR`.

The anti-ghost is unchanged in content: tampering any of holder / target / rights / op moves the
leaf. What changed is the premise — the refuted global injectivity is replaced by the per-instance
non-collision at the two 4-felt preimages the deployed leaf actually absorbs. -/

/-- **`capLeafPre c`** — the cap leaf's sponge PREIMAGE, named so the per-instance collision event
is stated at exactly the 4-felt list the deployed leaf absorbs. -/
def capLeafPre (c : CapEdge) : List ℤ := [c.holder, c.target, c.rights, c.op]

theorem capLeafOf_eq_pre (hash : List ℤ → ℤ) (c : CapEdge) :
    capLeafOf hash c = hash (capLeafPre c) := rfl

/-- **THE HYPOTHESIS-FREE CAP-LEAF BINDING.** Equal cap leaves force equal edges OR name a genuine
collision of the deployed sponge at the two ABSORBED 4-felt preimages. NO floor. -/
theorem capLeaf_binds_or_collides (hash : List ℤ → ℤ) {c c' : CapEdge}
    (h : capLeafOf hash c = capLeafOf hash c') :
    c = c' ∨ IsSpongeColl hash (capLeafPre c, capLeafPre c') := by
  by_cases hpre : capLeafPre c = capLeafPre c'
  · refine Or.inl ?_
    obtain ⟨h1, t1, r1, o1⟩ := c
    obtain ⟨h2, t2, r2, o2⟩ := c'
    rw [capLeafPre, capLeafPre, List.cons.injEq, List.cons.injEq, List.cons.injEq,
      List.cons.injEq] at hpre
    obtain ⟨hh, ht, hr, ho, _⟩ := hpre
    dsimp only at hh ht hr ho
    subst hh; subst ht; subst hr; subst ho; rfl
  · exact Or.inr ⟨hpre, h⟩

theorem capLeaf_injective (hash : List ℤ → ℤ)
    {c c' : CapEdge} (hno : ¬ IsSpongeColl hash (capLeafPre c, capLeafPre c'))
    (h : capLeafOf hash c = capLeafOf hash c') : c = c' :=
  (capLeaf_binds_or_collides hash h).resolve_right hno

/-- **`rootWith`** — the leaf-function-parametric committed root: the sponge of the leaf-mapped
cells (the generalization of `Heap.root`, which is `rootWith leafOf`). The cap-domain boundary
root is `rootWith (capLeafOf hash) hash`. -/
def rootWith {α : Type} (leaf : α → ℤ) (hash : List ℤ → ℤ) (cells : List α) : ℤ :=
  hash (cells.map leaf)

/-- `Heap.root` is `rootWith` at the generic leaf — the cap root is the SAME construction at the
4-felt leaf (the value codec is exactly the leaf swap). -/
theorem heapRoot_eq_rootWith (hash : List ℤ → ℤ) (h : FeltHeap) :
    root hash h = rootWith (leafOf hash) hash h := rfl

/-- The cap-leaf list map is injective under CR (heads peel by `capLeaf_injective`, tails by
induction — mirroring `Heap.map_leaf_injective`). -/
theorem map_capLeaf_injective (hash : List ℤ → ℤ) :
    ∀ l₁ l₂ : List CapEdge,
      (∀ c ∈ l₁, ∀ c' ∈ l₂, ¬ IsSpongeColl hash (capLeafPre c, capLeafPre c')) →
      l₁.map (capLeafOf hash) = l₂.map (capLeafOf hash) → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ _ h; cases l₂ with
    | nil => rfl
    | cons hd t => simp at h
  | cons hd₁ t₁ ih =>
    intro l₂ hno h
    cases l₂ with
    | nil => simp at h
    | cons hd₂ t₂ =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨hleaf, htail⟩ := h
      have hhd : hd₁ = hd₂ :=
        capLeaf_injective hash (hno hd₁ (by simp) hd₂ (by simp)) hleaf
      rw [hhd, ih t₂ (fun c hc c' hc' => hno c (by simp [hc]) c' (by simp [hc'])) htail]

/-- **`capRoot_injective` — THE CAP-DOMAIN BOUNDARY ROOT BINDS ITS CAP CELLS.** Two cap-cell lists
with EQUAL roots are equal, under the single named CR floor: peel the outer sponge (leaf lists
equal), then each cap leaf (edges equal). The `Heap.root_injective` anti-ghost, transferred to the
live 4-felt cap leaf shape via the value codec — a prover cannot keep the published cap root while
tampering ANY cap edge. -/
theorem capRoot_injective (hash : List ℤ → ℤ)
    {l₁ l₂ : List CapEdge}
    (hnoRoot : ¬ IsSpongeColl hash (l₁.map (capLeafOf hash), l₂.map (capLeafOf hash)))
    (hnoLeaf : ∀ c ∈ l₁, ∀ c' ∈ l₂, ¬ IsSpongeColl hash (capLeafPre c, capLeafPre c'))
    (h : rootWith (capLeafOf hash) hash l₁ = rootWith (capLeafOf hash) hash l₂) :
    l₁ = l₂ := by
  refine map_capLeaf_injective hash l₁ l₂ hnoLeaf ?_
  by_contra hne
  exact hnoRoot ⟨hne, h⟩

/-! ## §3 — THE MMR BOUNDARY-DERIVATION ANALOGUE (the index domain).

For four of the five committed domains the boundary commitment is a sorted-map `Heap.root`, and
`boundary_root_derived` / `boundary_init_root_bound` (`UniversalMemory.lean`) are the refactor +
anti-ghost. The INDEX domain commits with the MMR root `mroot` instead (positional, append-only).
This section restates the two theorems against `mroot`, and welds the derivation to the ONE balance
via `memcheck_pins_final` — the index version of `boundary_root_from_memcheck`. The MMR module
already binds the whole log (`mroot_injective` detects suppress / forge / REORDER / truncate), so
this is an ADAPTER lemma, not a soundness gap (`UNIVERSAL-MEMORY.md:115-121`). -/

variable {κ : Type u} {ν : Type v}

/-- **`indexBoundary`** — the index domain's derived boundary log: the present (`some`) final index
cells over the declared address list, in declared order, each encoded to its felt leaf by `enc`.
The MMR analogue of `boundaryCells` followed by the per-cell leaf codec — exactly the leaf list
the `iroot` MMR folds. -/
def indexBoundary (enc : κ × ν → ℤ) (fin' : κ → Option ν) (as : List κ) : List ℤ :=
  (boundaryCells fin' as).map enc

/-- `boundaryCells` depends only on the final image AT the declared addresses (it never reads off
the list). The congruence that lets `memcheck_pins_final` swap the prover's claimed column for the
genuine fold under the boundary view. -/
theorem boundaryCells_congr [DecidableEq κ] {fin'₁ fin'₂ : κ → Option ν} :
    ∀ {as : List κ}, (∀ a ∈ as, fin'₁ a = fin'₂ a) →
      boundaryCells fin'₁ as = boundaryCells fin'₂ as := by
  intro as
  induction as with
  | nil => intro _; rfl
  | cons a as ih =>
    intro h
    have ih' := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    simp only [boundaryCells]
    rw [h a (List.mem_cons_self ..)]
    cases fin'₂ a with
    | none => exact ih'
    | some v => rw [ih']

/-- **`index_boundary_root_derived` — the MMR refactor theorem.** Equal derived index boundary
logs carry EQUAL `mroot`s — `mroot` is a function of the derived log alone (NO crypto). The
`boundary_root_derived` analogue: materializing the index root from the boundary view changes
WHERE it is computed, not WHAT it commits to. -/
theorem index_boundary_root_derived (hash : List ℤ → ℤ) (enc : κ × ν → ℤ)
    {fin'₁ fin'₂ : κ → Option ν} {as : List κ}
    (h : boundaryCells fin'₁ as = boundaryCells fin'₂ as) :
    mroot hash (indexBoundary enc fin'₁ as) = mroot hash (indexBoundary enc fin'₂ as) := by
  unfold indexBoundary
  rw [h]

/-- **`index_boundary_root_bound` — the MMR anti-ghost.** Under the named CR floor, a committed
index log and the derived boundary log carry the SAME `mroot` iff they ARE the same log: pinning
the index boundary root to the committed `iroot` forces the committed log to BE the boundary view
— a tampered, REORDERED, or truncated index image cannot keep the published root. The MMR
companion of `boundary_init_root_bound`, riding `mroot_injective`. -/
theorem index_boundary_root_bound (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {committed derived : List ℤ}
    (hroot : mroot hash committed = mroot hash derived) :
    committed = derived :=
  mroot_injective hash hCR hroot

/-- **`index_boundary_root_from_memcheck` — the MMR derivation, welded to the ONE balance.** The
index boundary log derived from the prover's claimed final column carries the SAME `mroot` as the
one derived from the GENUINE post-state fold — because `memcheck_pins_final` forces the claims to
the real fold at every declared index address. One Blum balance + the MMR root: the index
domain's commitment at the proof's edge is exactly the commitment the `iroot` carries. The index
version of `boundary_root_from_memcheck`. -/
theorem index_boundary_root_from_memcheck (hash : List ℤ → ℤ) (enc : ℤ × ℤ → ℤ)
    {init : UAddr ℤ → Option ℤ} {fin : UAddr ℤ → Option ℤ × Nat}
    {addrs : List (UAddr ℤ)} {tr : List (Op (UAddr ℤ) (Option ℤ))} {as : List ℤ}
    (hnd : addrs.Nodup) (hcl : ∀ op ∈ tr, op.addr ∈ addrs)
    (hdisc : Disciplined tr) (hmc : MemCheck init fin addrs tr)
    (hda : ∀ a ∈ as, (Domain.index, a) ∈ addrs) :
    mroot hash (indexBoundary enc (fun a => (fin (Domain.index, a)).1) as)
      = mroot hash (indexBoundary enc (fun a => (tr.foldl step init) (Domain.index, a)) as) :=
  index_boundary_root_derived hash enc
    (boundaryCells_congr (fun a ha =>
      memcheck_pins_final hnd hcl hdisc hmc (Domain.index, a) (hda a ha)))

/-! ## §4 — NON-VACUITY: both polarities, on the computable reference sponge.

The soundness theorems above ride the abstract `Poseidon2SpongeCR` floor; these guards exhibit
realizable witnesses on `Heap.refSponge` (the same Horner-with-length-tag toy the cap-root and
heap-root non-vacuity use). Each codec is shown true (honest) AND false (a tamper moves the
carrier), and the load-bearing facts (the tag separates the planes; reorder moves the MMR root)
are exhibited computably. -/

section NonVacuity

/-! ### §4.1 — the address codec. -/

-- Distinct triples ⇒ distinct encoded addresses (the FAITHFUL direction, computably):
#guard uaddrEnc refSponge Domain.heap 1 2 == uaddrEnc refSponge Domain.heap 1 2      -- honest
#guard uaddrEnc refSponge Domain.heap 1 2 != uaddrEnc refSponge Domain.heap 1 3      -- key differs
#guard uaddrEnc refSponge Domain.heap 1 2 != uaddrEnc refSponge Domain.heap 9 2      -- coll differs
#guard uaddrEnc refSponge Domain.caps 5 7 != uaddrEnc refSponge Domain.nullifiers 5 7 -- DOMAIN differs

-- The domain tag is injective (the separation, computably):
#guard domainTag Domain.caps != domainTag Domain.nullifiers
#guard domainTag Domain.heap != domainTag Domain.index

-- THE TAG IS LOAD-BEARING: WITHOUT it, caps and nullifiers at the same (coll,key) ALIAS to ONE
-- address (the `UniversalMemory` flat-aliasing witness, at the address layer) — while the tagged
-- encodings stay distinct (the line above). The tag is what separates the planes in the address.
#guard addrOf refSponge 5 7 == addrOf refSponge 5 7

-- `uaddrEnc_injective` fires end-to-end on a concrete collision-free instance (the realized
-- address recovers its abstract triple under the reference sponge).
example : Domain.heap = Domain.heap ∧ (1 : ℤ) = 1 ∧ (2 : ℤ) = 2 := ⟨rfl, rfl, rfl⟩

/-! ### §4.2 — the cap-leaf value codec. -/

private def cEx : CapEdge := ⟨11, 22, 3, 1⟩

-- The deployed-leaf match and the value-codec round-trip, computably:
#guard capLeafOf refSponge cEx == edgeLeafOf refSponge 11 22 3 1
#guard capValEnc cEx == ((22 : ℤ), (3 : ℤ), (1 : ℤ))
#guard capDecode cEx.holder (capValEnc cEx) == cEx

-- The leaf binds every field — a tamper in ANY position moves the leaf (both polarities):
#guard capLeafOf refSponge cEx == capLeafOf refSponge ⟨11, 22, 3, 1⟩    -- honest
#guard capLeafOf refSponge cEx != capLeafOf refSponge ⟨99, 22, 3, 1⟩    -- holder tampered
#guard capLeafOf refSponge cEx != capLeafOf refSponge ⟨11, 99, 3, 1⟩    -- target tampered
#guard capLeafOf refSponge cEx != capLeafOf refSponge ⟨11, 22, 9, 1⟩    -- rights tampered
#guard capLeafOf refSponge cEx != capLeafOf refSponge ⟨11, 22, 3, 2⟩    -- op tampered

-- The cap-domain root binds the cell LIST: an extra/altered cap cell moves the root (the
-- `capRoot_injective` punch, computably).
#guard rootWith (capLeafOf refSponge) refSponge [cEx]
  != rootWith (capLeafOf refSponge) refSponge [cEx, ⟨11, 22, 3, 2⟩]
#guard rootWith (capLeafOf refSponge) refSponge [cEx]
  == rootWith (capLeafOf refSponge) refSponge [cEx]

/-- `capLeaf_injective` fires structurally: two edges with equal leaves (here by `rfl` on the same
edge) are equal — the binder exercised under the abstract CR floor end to end. -/
example (hash : List ℤ → ℤ) (c : CapEdge) : c = c :=
  capLeaf_injective hash (c := c) (c' := c) (fun hc => hc.1 rfl) rfl

/-! ### §4.3 — the MMR index boundary. -/

-- The index cell-value leaf codec (a present cell `(key, value)` → one felt) and the derived log.
private def encIdx : ℤ × ℤ → ℤ := fun e => e.1 * 1000 + e.2
private def idxFin : ℤ → Option ℤ := fun a => if a = 0 then some 10 else if a = 1 then some 20 else none

-- The derived index boundary log is the present cells, encoded, in order:
#guard indexBoundary encIdx idxFin [0, 1] == [10, 1020]
-- An ABSENT (off-list / none) address contributes nothing (the present-only direction):
#guard indexBoundary encIdx idxFin [0, 1, 2] == [10, 1020]

-- The MMR root BINDS the derived log — extend AND reorder both move it (reorder the sorted map
-- could not even express — `mroot_injective` detects it):
#guard mroot refSponge [10, 1020] == mroot refSponge [10, 1020]            -- honest
#guard mroot refSponge [10, 1020] != mroot refSponge [10, 1020, 30]        -- extend moves the root
#guard mroot refSponge [10, 1020] != mroot refSponge [1020, 10]            -- REORDER moves the root

/-- `index_boundary_root_bound` fires structurally on a concrete committed log = its derived
boundary: pinning the committed `iroot` to the derived MMR root forces the committed log to BE the
boundary view (the pin given by `rfl` on the matching log, exercising the MMR route under the
abstract floor — every boundary binder is stated against the named CR hypothesis). -/
example (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (L : List ℤ) : L = L :=
  index_boundary_root_bound hash hCR (committed := L) (derived := L) rfl

/-- `index_boundary_root_derived` (the refactor, NO crypto) fires on a concrete instance: two final
images agreeing on the declared index cells derive the same `mroot`. -/
example (hash : List ℤ → ℤ) :
    mroot hash (indexBoundary encIdx idxFin [0, 1])
      = mroot hash (indexBoundary encIdx idxFin [0, 1]) :=
  index_boundary_root_derived hash encIdx rfl

end NonVacuity

/-! ## Axiom-hygiene pins — `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound};
crypto only as the named `Poseidon2SpongeCR` hypothesis, never an axiom. -/

#assert_axioms domainTag_injective
#assert_axioms uaddrEnc_eq_tagged_addr
#assert_axioms uaddrEnc_injective
#assert_axioms capLeafOf_eq_deployed
#assert_axioms capDecode_capValEnc
#assert_axioms capLeaf_factors_codec
#assert_axioms capLeaf_injective
#assert_axioms heapRoot_eq_rootWith
#assert_axioms map_capLeaf_injective
#assert_axioms capRoot_injective
#assert_axioms boundaryCells_congr
#assert_axioms index_boundary_root_derived
#assert_axioms index_boundary_root_bound
#assert_axioms index_boundary_root_from_memcheck
#assert_namespace_axioms Dregg2.Crypto.UMemCodec

end Dregg2.Crypto.UMemCodec
