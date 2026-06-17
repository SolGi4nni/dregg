/-
# Dregg2.Circuit.DeployedCapTree — THE FAITHFUL model of the DEPLOYED 7-field cap-tree.

## Why this file exists (the authority-leg ground-truth correction)

The kernel-authority bridge (`Dregg2.Circuit.CapRootBridge`) and the in-circuit non-amplification
proofs (`EffectVmEmitRotationV3.attenuateV3_non_amp`) discharge their cap-openings against
`DescriptorIR2.opensTo`, whose denotation is `Dregg2.Substrate.Heap`:

    opensTo hash r k o := ∃ h : FeltHeap, SortedKeys h ∧ Heap.root hash h = r ∧ Heap.get h k = o
    Heap.root hash h   := hash (h.map (fun e => hash [e.1, e.2]))           -- FLAT sponge, 2-field leaf

That model is a FLAT SPONGE of a sorted list of **2-field** leaves `hash[addr, value]`.

The value the CELL actually commits (and the EffectVM circuit seeds `cap_root` from) is
`dregg_cell::compute_canonical_capability_root_felt` → `circuit/src/cap_root.rs::CanonicalCapTree`:

    leaf  = cap_chip_absorb[slot_hash, target, auth_tag, mask_lo, mask_hi, expiry, breadstuff] -- 7 fields
    node  = cap_chip_absorb[FACT_MARK, left, right]                                            -- arity-3
    root  = the depth-16 BINARY MERKLE fold of the sorted-by-slot_hash padded leaf list

## The unification (THIS revision — decision #1, the chip-rate gap CLOSED)

`circuit/src/cap_root.rs::cap_chip_absorb` is now the SINGLE in-circuit hash the cap-tree commits to:
ONE width-16 Poseidon2 permutation, byte-identical to the IR-v2 Poseidon2 chip's BUS_P2 absorb
(`descriptor_ir2.rs::Ir2Air::Chip`). The chip distinguishes two seedings by `big = [arity == 7]`:

  * `arity ≤ 4` (rate-4 regime): `state[0..len] = ins`, `state[4] = len` (the length tag),
    `state[5..] = 0`. The cap NODE rides this as the arity-3 absorb of `[FACT_MARK, l, r]`.
  * `arity == 7` (rate-8 leaf): `state[0..7] = ins`, NO tag lane (`state[7..] = 0`). The cap LEAF
    rides this as the arity-7 absorb of the 7 leaf fields.

So the deployed leaf and node are BOTH a single chip-realizable permutation call. We model the one
hash as `Dregg2.Crypto.CommitmentBinding.Compress1CR` — ONE permutation call (`squeeze ∘ perm ∘
absorb`), the same primitive #4 the 2-to-1 Merkle node `hash_2_to_1` rides — and define BOTH
`capLeafDigest` and `nodeOf` OVER it. Because the leaf-field list (length 7) and the node block
`[FACT_MARK, l, r]` (length 3) are length-disjoint, the chip's per-row `(arity, padded ins)` seeding
separates the two domains for free; `Compress1CR` (equal output ⇒ equal input list) is exactly the
chip's per-row collision-resistance.

This makes the IR-v2 chip GENUINELY realize the deployed cap hash: `DeployedCapOpen`'s
`SchemeRealizedByChip sponge S` is now PROVABLE (the chip's rate-8 absorb IS the deployed scheme, by
construction), so it is DISCHARGED, not carried. The prior revision's rate-4 `hash_many` leaf +
capacity-tagged `hash_fact` node (the source of the gap) are GONE.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY as the named
`Compress1CR` floor (the SAME single-permutation-call floor #4 the whole commitment tower carries).
No `sorry`, no `:= True`, no `native_decide`.
-/
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Crypto.CommitmentBinding
import Dregg2.Exec.Kernel
import Dregg2.Exec.FacetAuthority
import Dregg2.Circuit.Emit.EffectVmEmitCapReshape

namespace Dregg2.Circuit.DeployedCapTree

open Dregg2.Crypto.CommitmentBinding (Compress1CR)
open Dregg2.Authority (Cap Auth Caps Label capAuthConferred)
open Dregg2.Circuit.Emit.EffectVmEmitCapReshape (authBitN rightsMaskOf)
open Dregg2.Exec.FacetAuthority
  (AuthTier AuthProvided FacetCap FacetCaps EffectMask EFFECT_TRANSFER isEffectPermitted
   authorizedFacetB authorizedFacetB_holds_transfer_cap turnEffectBit capAuthorizesFacet)

set_option autoImplicit false

/-! ## §0 — the deployed leaf (the 7-field `CapLeaf`, byte-faithful to `cap_root.rs`). -/

/-- The 7 canonical leaf fields, in `cap_root.rs::CapLeaf` order. The deployed tree stores
`capLeafDigest` of these at each leaf position. (`slot_hash` is the sort key; here we keep the
fields abstract `ℤ` — the deployment instance is BabyBear.) -/
structure CapLeaf where
  /-- The sort key: a Poseidon2 image of the (unique) c-list slot (`cap_root.rs:95`). -/
  slot_hash : ℤ
  /-- The capability's target cell id, folded to one felt (`cap_root.rs:98`). -/
  target : ℤ
  /-- The `AuthRequired` tier (+ absorbed vk_hash for `Custom`), one felt (`cap_root.rs:99`). -/
  auth_tag : ℤ
  /-- `EffectMask` low 16 bits (`cap_root.rs:101`). -/
  mask_lo : ℤ
  /-- `EffectMask` high 16 bits (`cap_root.rs:103`). -/
  mask_hi : ℤ
  /-- Optional expiry height (`NONE_SENTINEL` when absent) (`cap_root.rs:105`). -/
  expiry : ℤ
  /-- Optional breadstuff hash folded to one felt (`cap_root.rs:107`). -/
  breadstuff : ℤ
  deriving DecidableEq

/-- The 7 leaf fields in canonical `cap_root.rs::CapLeaf::digest` order — the EXACT list `hash_many`
absorbs (`cap_root.rs:115-124`). The leaf digest is the rate-4 sponge over THIS list. -/
def leafFields (l : CapLeaf) : List ℤ :=
  [l.slot_hash, l.target, l.auth_tag, l.mask_lo, l.mask_hi, l.expiry, l.breadstuff]

/-- `leafFields` is injective in the whole `CapLeaf` (it is just the seven fields in order). -/
theorem leafFields_inj {l₁ l₂ : CapLeaf} (h : leafFields l₁ = leafFields l₂) : l₁ = l₂ := by
  simp only [leafFields, List.cons.injEq] at h
  cases l₁; cases l₂; simp_all

/-! ## §1 — the deployed node layout (the arity-3 chip absorb `[FACT_MARK, l, r]`).

`cap_root.rs::cap_node` folds each internal node as `cap_chip_absorb(&[CAP_FACT_MARK, l, r])` — the
arity-3 (rate-4 regime) single chip absorb. `FACT_MARK = 0xFACF` rides RATE lane 0 (a genuine rate
input, NOT a capacity tag), `l` lane 1, `r` lane 2, the length tag `3` in lane 4. So
`nodeOf l r = chipAbsorb [FACT_MARK, l, r]`, one permutation call over the length-3 block. -/

/-- The cap-node domain-separation marker `0xFACF` (`cap_root.rs::CAP_FACT_MARK`), absorbed as the
FIRST RATE input of the arity-3 node block (NOT a capacity tag). -/
def FACT_MARK : ℤ := 0xFACF

/-- **`packNode l r`** — the deployed `cap_node` chip-absorb input block `[FACT_MARK, l, r]`
(`cap_root.rs::cap_node` = `cap_chip_absorb(&[CAP_FACT_MARK, l, r])`). `FACT_MARK` at rate lane 0,
`l` at 1, `r` at 2 — a genuine rate-input list, length 3 (length-disjoint from the length-7 leaf
block, so the chip's per-row arity seeding separates the two domains). -/
def packNode (l r : ℤ) : List ℤ := [FACT_MARK, l, r]

/-- `packNode` is injective in `(l, r)` (`FACT_MARK` is the constant head; the two children sit at
fixed positions 1, 2). The STRUCTURAL half of node injectivity. -/
theorem packNode_inj {l₁ r₁ l₂ r₂ : ℤ} (h : packNode l₁ r₁ = packNode l₂ r₂) :
    l₁ = l₂ ∧ r₁ = r₂ := by
  simp only [packNode, List.cons.injEq] at h
  exact ⟨h.2.1, h.2.2.1⟩

/-! ## §2 — the `CapHashScheme` bundle: the ONE deployed chip-absorb carrier.

The deployed cap tree commits ONE hash everywhere — `cap_root.rs::cap_chip_absorb`, the IR-v2 chip's
single rate-8 absorb. Both the leaf (arity 7) and the node (arity 3) ride this one permutation call.
We bundle exactly that carrier. -/

/-- **`CapHashScheme State`** — the deployed cap-tree's SINGLE Poseidon2 carrier: the chip absorb
`chipAbsorb : List ℤ → ℤ` (`cap_root.rs::cap_chip_absorb` = the IR-v2 chip's `squeeze ∘ perm ∘
(state from arity+inputs)`), collision-resistant per row (`Compress1CR`, primitive #4 — equal output
forces equal input list, which is exactly the chip's per-row `(arity, padded inputs)` injectivity).
The `State` parameter is vestigial (the carrier is the per-row compression); the deployment instance
is the real BabyBear width-16 permutation. `nodeOf`/`capLeafDigest` are defined over it. -/
structure CapHashScheme (State : Type) where
  /-- The single chip-absorb compression (`cap_chip_absorb`, `squeeze ∘ perm ∘ stateFromArityInputs`),
  shared by the leaf (arity 7) and the node (arity 3). -/
  chipAbsorb : List ℤ → ℤ
  /-- CRYPTO CARRIER: the single permutation call is collision-resistant on its input list
  (primitive #4). This IS the chip's per-row `(arity, padded inputs) → digest` injectivity. -/
  chipCR : Compress1CR chipAbsorb

namespace CapHashScheme

variable {State : Type} (S : CapHashScheme State)

/-! ## §3 — the re-grounded primitives (`capLeafDigest`/`nodeOf` BOTH ride `chipAbsorb`). -/

/-- **`capLeafDigest S l`** — the 7-field deployed leaf digest, the SINGLE rate-8 chip absorb over the
7 leaf fields in canonical order. BYTE-IDENTICAL to `cap_root.rs::CapLeaf::digest`
(`cap_chip_absorb(&[slot_hash, target, auth_tag, mask_lo, mask_hi, expiry, breadstuff])` — ONE
permute, lanes 0..6 the genuine fields, no length tag, the chip's `big` row). -/
def capLeafDigest (l : CapLeaf) : ℤ := S.chipAbsorb (leafFields l)

/-- **`nodeOf S l r`** — the internal node hash, the arity-3 chip absorb over `packNode l r =
[FACT_MARK, l, r]`. BYTE-IDENTICAL to `cap_root.rs::cap_node` (`cap_chip_absorb(&[CAP_FACT_MARK, l,
r])` — ONE permute, `FACT_MARK` at rate lane 0). The SAME `chipAbsorb` carrier as the leaf — one cap
hash everywhere. -/
def nodeOf (l r : ℤ) : ℤ := S.chipAbsorb (packNode l r)

/-! ## §4 — injectivity (over the single chip-absorb carrier). -/

/-- **Leaf injectivity under the chip-absorb CR** — distinct 7-tuples yield distinct digests. PROVED
by the single-permutation-call `chipCR` (primitive #4) composed with `leafFields` injectivity. -/
theorem capLeafDigest_injective {l₁ l₂ : CapLeaf}
    (h : capLeafDigest S l₁ = capLeafDigest S l₂) : l₁ = l₂ :=
  leafFields_inj (S.chipCR _ _ h)

/-- **Node injectivity under the chip-absorb CR** — equal node images ⇒ equal children. PROVED by the
single-permutation-call `chipCR` (primitive #4) composed with `packNode` injectivity. The per-level
peel of the membership recompose's anti-ghost. -/
theorem nodeOf_injective {l₁ r₁ l₂ r₂ : ℤ}
    (h : nodeOf S l₁ r₁ = nodeOf S l₂ r₂) : l₁ = l₂ ∧ r₁ = r₂ := by
  unfold nodeOf at h
  exact packNode_inj (S.chipCR _ _ h)

/-! ## §5 — the membership opening (the depth-16 binary-Merkle recompose up a sibling path).

A membership witness is a list of `(sibling, direction)` steps (`cap_root.rs::prove_membership`
returns exactly `(siblings, directions)`; `directions[i] = 0` ⇔ the current node is the LEFT child
at level `i`). Recomposing folds `nodeOf` up the path, mixing `(cur, sib)` by the direction bit —
LITERALLY the `descriptor_ir2` MapOps AIR's `mix` closure (`descriptor_ir2.rs:2109`):
`left = (1-dir)·cur + dir·sib`, `right = (1-dir)·sib + dir·cur`. -/

/-- One Merkle path step: the sibling digest at this level + the direction bit. -/
structure Step where
  /-- The sibling digest at this level (`cap_root.rs` `siblings[level]`). -/
  sib : ℤ
  /-- The direction bit: `0` ⇒ `cur` is the LEFT child (sibling right), `1` ⇒ right child. -/
  dir : Bool
  deriving DecidableEq

/-- **`recomposeUp S cur path`** — fold the held digest up the sibling/direction path to the root. At
each level, if `dir = false` (LEFT child) the node is `nodeOf cur sib`, else `nodeOf sib cur`. This is
the exact `attenuation_witness` / MapOps-AIR fold (`cap_root.rs:425-431`, `descriptor_ir2.rs:2116`),
now over the deployed capacity-tagged `nodeOf`. -/
def recomposeUp (cur : ℤ) : List Step → ℤ
  | [] => cur
  | s :: rest =>
    recomposeUp (if s.dir then nodeOf S s.sib cur else nodeOf S cur s.sib) rest

/-- **`MembersAt S root leaf`** — the deployed-tree membership statement: there is a sibling/direction
path recomposing `root` from the 7-field leaf's digest. The witness is the path
(`cap_root.rs::prove_membership`); the relation hides it behind the existential, exactly as the
in-circuit opening realizes it. The HONEST replacement for `Substrate.Heap`'s flat-sponge `opensTo` —
the REAL rate-4 leaf digest and the REAL capacity-tagged `hash_fact` binary fold. -/
def MembersAt (root : ℤ) (leaf : CapLeaf) : Prop :=
  ∃ path : List Step, recomposeUp S (capLeafDigest S leaf) path = root

/-- **`recomposeUp` is injective in its STARTING digest under the node CR** — equal recomposed roots
from the SAME path force the same starting leaf digest (peel each level by `nodeOf_injective`). The
anti-ghost spine: a prover cannot keep the published root while swapping the opened leaf along a fixed
path. -/
theorem recomposeUp_inj_of_path (path : List Step) :
    ∀ {a b : ℤ}, recomposeUp S a path = recomposeUp S b path → a = b := by
  induction path with
  | nil => intro a b h; simpa [recomposeUp] using h
  | cons s rest ih =>
    intro a b h
    simp only [recomposeUp] at h
    have hstep := ih h
    cases hd : s.dir with
    | false =>
      rw [hd] at hstep
      simp only [Bool.false_eq_true, if_false] at hstep
      exact (nodeOf_injective S hstep).1
    | true =>
      rw [hd] at hstep
      simp only [if_true] at hstep
      exact (nodeOf_injective S hstep).2

/-! ## §6 — the FAITHFUL commitment relation + the authority bridge against THIS tree.

The replacement for `CapRootBridge.CapsEncodes` (which is over `Substrate.Heap`). `DeployedEncodes`
says `cap_root` is the deployed `CanonicalCapTree`-root of a leaf set that FAITHFULLY realizes the
kernel `caps`: a write-rights membership opening of an authority-edge leaf witnesses a real held
endpoint cap. We carry the faithfulness as the runtime-encoding contract, exactly the
`compute_canonical_capability_root_felt` discipline. -/

/-! ### §6.0 — the FAITHFUL two-axis leaf decode (THE CUTOVER, FacetAuthority §10(C)).

The deployed leaf commits the authority on TWO axes, both in the 7-field leaf (`cap_root.rs:41-51`):
a FACET (`mask_lo`/`mask_hi`, two 16-bit limbs of one `EffectMask` u32) and a TIER (`auth_tag`, the
`AuthRequired` byte None=0…Custom=5). The cutover decodes BOTH off the leaf and gates the turn on
`authorizedFacetB` — NOT the toy `mask_lo == write-mask` shadow. -/

/-- **`maskOfLimbs lo hi`** — recombine the deployed split mask `(mask_lo, mask_hi)` into the one
`EffectMask` `u32`: `mask = mask_lo + mask_hi · 2^16` (`cap_root.rs::split_effect_mask`: `lo = mask &
0xFFFF`, `hi = (mask >> 16) & 0xFFFF`). The leaf-faithful inverse of the deployed limb split. -/
def maskOfLimbs (lo hi : ℤ) : ℤ := lo + hi * 65536

/-- **`tierOfTag tag`** — decode the deployed `auth_tag` BYTE to an `AuthTier` (`cap_root.rs:46`:
None=0…Custom=5; `AuthTier.tierByte` is the forward map). The IPC tiers (None…Impossible) decode by
the discriminant byte; tag `5` decodes to a `Custom` whose `vkHash` is the residual felt-absorb
(carried as `vkOfTag`, the one named crypto residual — transfers never use `Custom`, see §10). -/
def tierOfTag (vkOfTag : ℤ → Nat) : ℤ → AuthTier
  | 0 => .none
  | 1 => .signature
  | 2 => .proof
  | 3 => .either
  | 4 => .impossible
  | tag => .custom (vkOfTag tag)   -- tag = 5 (Custom): vkHash absorbed (NAMED residual `vkOfTag`)

/-- **`facetOfLeaf l`** — the leaf's decoded `Option EffectMask` facet: `some (maskOfLimbs mask_lo
mask_hi)` (the deployed `allowed_effects`; here always `some` — the leaf commits a concrete mask). -/
def facetOfLeaf (l : CapLeaf) : Option EffectMask := some (maskOfLimbs l.mask_lo l.mask_hi).toNat

/-- **`confersTransferLeaf vkOfTag provided l`** — THE FAITHFUL two-axis leaf gate (replaces the toy
`confersWriteLeaf`). The leaf confers TRANSFER authority iff (1) its decoded FACET permits the
`EFFECT_TRANSFER` bit (`isEffectPermitted`, `facet.rs:123`) AND (2) its decoded TIER (`tierOfTag
auth_tag`) is satisfied by the auth the turn `provided` (`AuthTier.isSatisfiedBy`, `permissions.rs:33`).
This is the deployed `(allowed_effects, permissions)` authority core, decoded off the committed leaf. -/
def confersTransferLeaf (vkOfTag : ℤ → Nat) (provided : AuthProvided) (l : CapLeaf) : Prop :=
  isEffectPermitted (facetOfLeaf l) EFFECT_TRANSFER = true
    ∧ (tierOfTag vkOfTag l.auth_tag).isSatisfiedBy provided = true

/-- **`confersLeaf vkOfTag provided effectBit l`** (F6 — the GENERAL two-axis leaf gate). The
generalization of `confersTransferLeaf` from the pinned `EFFECT_TRANSFER` constant to an ARBITRARY
effect-kind bit `effectBit`: the leaf confers `effectBit` authority iff (1) its decoded FACET
(`facetOfLeaf`, the genuine `maskOfLimbs mask_lo mask_hi`) permits `effectBit` AND (2) its decoded
TIER (`tierOfTag auth_tag`, the genuine committed byte — NOT a constant) is satisfied by `provided`.
`confersTransferLeaf vkOfTag provided = confersLeaf vkOfTag provided EFFECT_TRANSFER` (by `rfl`). -/
def confersLeaf (vkOfTag : ℤ → Nat) (provided : AuthProvided) (effectBit : EffectMask)
    (l : CapLeaf) : Prop :=
  isEffectPermitted (facetOfLeaf l) effectBit = true
    ∧ (tierOfTag vkOfTag l.auth_tag).isSatisfiedBy provided = true

/-- `confersTransferLeaf` is the `EFFECT_TRANSFER` instance of the general `confersLeaf`. -/
theorem confersTransferLeaf_eq_general (vkOfTag : ℤ → Nat) (provided : AuthProvided) (l : CapLeaf) :
    confersTransferLeaf vkOfTag provided l = confersLeaf vkOfTag provided EFFECT_TRANSFER l := rfl

/-- **`DeployedFaithful S vkOfTag provided caps root leafAt`** — the leaf-set `leafAt` faithfully
realizes the FACET caps `caps`: every TRANSFER-conferring member leaf at an `(actor ⇒ src)` edge is
backed by a real held `FacetCap` over `src` whose facet permits TRANSFER and whose tier is satisfied by
`provided`. The forward encoding contract (caps ⇒ tree); the bridge below reads it backward through one
opening into `authorizedFacetB`. -/
structure DeployedFaithful (vkOfTag : ℤ → Nat) (provided : AuthProvided)
    (caps : FacetCaps) (root : ℤ) (leafAt : Label → Label → CapLeaf) : Prop where
  /-- FAITHFULNESS: a transfer-conferring member opening witnesses a REAL held `FacetCap` whose facet
  permits TRANSFER under a tier the `provided` auth satisfies. -/
  backed : ∀ (actor src : Label),
    MembersAt S root (leafAt actor src) →
    confersTransferLeaf vkOfTag provided (leafAt actor src) →
    ∃ c : FacetCap, c ∈ caps actor ∧ c.target = src
      ∧ isEffectPermitted c.facet EFFECT_TRANSFER = true
      ∧ c.tier.isSatisfiedBy provided = true

/-- **`DeployedEncodes S vkOfTag provided caps root`** — THE deployed commitment relation: `root` is
the deployed cap-tree root of SOME leaf assignment that faithfully realizes the FACET caps `caps`. -/
def DeployedEncodes (vkOfTag : ℤ → Nat) (provided : AuthProvided) (caps : FacetCaps) (root : ℤ) : Prop :=
  ∃ leafAt : Label → Label → CapLeaf, DeployedFaithful S vkOfTag provided caps root leafAt

/-- **`deployedCapOpen_implies_authorizedB` — THE FAITHFUL AUTHORITY BRIDGE against the deployed tree.**
GIVEN the deployed commitment relation, AND an in-circuit membership opening whose leaf confers TRANSFER
on BOTH axes (facet permits `EFFECT_TRANSFER`, tier satisfied by `provided`) — THEN the kernel's FAITHFUL
`authorizedFacetB` PASSES for the turn `⟨actor, src, dst, amt⟩`. The circuit's depth-16 binary-Merkle
membership proof discharges the deployed two-axis (tier × facet) authority gate, reusing
`authorizedFacetB_holds_transfer_cap`. -/
theorem deployedCapOpen_implies_authorizedB
    (vkOfTag : ℤ → Nat) (provided : AuthProvided)
    (caps : FacetCaps) (root : ℤ) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithful S vkOfTag provided caps root leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hopen : MembersAt S root (leafAt actor src))
    (hconf : confersTransferLeaf vkOfTag provided (leafAt actor src)) :
    authorizedFacetB caps provided { actor := actor, src := src, dst := dst, amt := amt } = true := by
  obtain ⟨c, hmem, htgt, hfacet, htier⟩ := hfaith.backed actor src hopen hconf
  exact authorizedFacetB_holds_transfer_cap caps provided
    { actor := actor, src := src, dst := dst, amt := amt } c hmem htgt
    (by simpa [turnEffectBit] using hfacet) htier

end CapHashScheme

/-! ## §7 — NON-VACUITY: the deployed-tree bridge FIRES on a concrete edge, and the gate is REAL.

Mirrors `CapRootBridge.bridge_fires`/`empty_caps_unauthorized`, re-seated on the deployed tree. We
exhibit a concrete `caps` (actor 5 holds a read+write cap over src 9), a faithful leaf assignment for
that edge, and the bridge firing; plus a witness-FALSE where the empty cap-table backs no opening. -/

open CapHashScheme

/-- A trivial vk-decode (no `Custom` leaf in the demo; transfers never use `Custom`). -/
def demoVkOfTag : ℤ → Nat := fun _ => 0

/-- A single-edge FACET cap-table: actor 5 holds a TRANSFER-facet, `Signature`-tier cap over src 9;
everyone else holds nothing. -/
def oneEdgeCaps : FacetCaps := fun a =>
  if a = 5 then [{ target := 9, tier := .signature, facet := some EFFECT_TRANSFER }] else []

/-- The faithful leaf assignment for `oneEdgeCaps`: the `(5 ⇒ 9)` edge carries a TRANSFER-facet,
`Signature`-tier (`auth_tag = 1`) leaf; every other edge carries a deny-all (`mask = 0` ⇒ facet rejects)
leaf, so `confersTransferLeaf` is false there and faithfulness is vacuously met. -/
def oneEdgeLeaf : Label → Label → CapLeaf := fun actor src =>
  if actor = 5 ∧ src = 9 then
    { slot_hash := 0, target := 9, auth_tag := 1,   -- tier = Signature
      mask_lo := EFFECT_TRANSFER, mask_hi := 0, expiry := 0, breadstuff := 0 }
  else
    { slot_hash := 0, target := 0, auth_tag := 1,
      mask_lo := 0, mask_hi := 0, expiry := 0, breadstuff := 0 }   -- mask 0 ⇒ deny-all

/-- **`oneEdge_faithful`** — `oneEdgeLeaf` faithfully realizes `oneEdgeCaps` (under a provided signature)
against any root: the ONLY transfer-conferring edge is `(5 ⇒ 9)`, where actor 5 holds the matching
`FacetCap`. The deny-all leaf elsewhere makes `confersTransferLeaf` false (facet rejects), so the
faithfulness obligation is vacuous off the edge. -/
theorem oneEdge_faithful {State : Type} (S : CapHashScheme State) (root : ℤ) :
    DeployedFaithful S demoVkOfTag .signature oneEdgeCaps root oneEdgeLeaf := by
  refine ⟨?_⟩
  intro actor src _hopen hconf
  by_cases hedge : actor = 5 ∧ src = 9
  · obtain ⟨ha, hs⟩ := hedge
    subst ha; subst hs
    refine ⟨{ target := 9, tier := .signature, facet := some EFFECT_TRANSFER }, by simp [oneEdgeCaps], rfl, ?_, rfl⟩
    decide
  · exfalso
    obtain ⟨hfacet, _⟩ := hconf
    simp only [oneEdgeLeaf, if_neg hedge, facetOfLeaf, maskOfLimbs] at hfacet
    -- the off-edge leaf has mask 0 ⇒ `isEffectPermitted (some 0) _ = false`.
    revert hfacet; decide

/-- **`deployedEncodes_inhabited`** — the deployed commitment relation is INHABITED. -/
theorem deployedEncodes_inhabited {State : Type} (S : CapHashScheme State) (root : ℤ) :
    DeployedEncodes S demoVkOfTag .signature oneEdgeCaps root :=
  ⟨oneEdgeLeaf, oneEdge_faithful S root⟩

/-- **NON-VACUITY (the bridge FIRES on a real edge).** Given a membership opening of the `(5 ⇒ 9)`
transfer leaf against the deployed tree (with a provided signature), the bridge yields
`authorizedFacetB oneEdgeCaps .signature ⟨5,9,…⟩ = true`. -/
theorem bridge_fires {State : Type} (S : CapHashScheme State) (root : ℤ)
    (hopen : MembersAt S root (oneEdgeLeaf 5 9)) :
    authorizedFacetB oneEdgeCaps .signature { actor := 5, src := 9, dst := 0, amt := 0 } = true := by
  apply deployedCapOpen_implies_authorizedB S demoVkOfTag .signature oneEdgeCaps root oneEdgeLeaf
      (oneEdge_faithful S root) 5 9 0 0 hopen
  have hleaf : oneEdgeLeaf 5 9
      = { slot_hash := 0, target := 9, auth_tag := 1,
          mask_lo := EFFECT_TRANSFER, mask_hi := 0, expiry := 0, breadstuff := 0 } := by
    unfold oneEdgeLeaf; simp
  rw [hleaf]
  refine ⟨?_, ?_⟩ <;> decide

/-- **NON-VACUITY (witness FALSE — the gate is real).** Over the EMPTY FACET cap-table, the faithful gate
rejects a non-owned src — so the bridge's conclusion is NOT vacuously always-true. -/
theorem empty_caps_unauthorized :
    authorizedFacetB (fun _ => []) .signature { actor := 5, src := 9, dst := 0, amt := 0 } = false := by
  decide

/-! ## §8 — Axiom hygiene. -/

#assert_axioms CapHashScheme.capLeafDigest_injective
#assert_axioms CapHashScheme.nodeOf_injective
#assert_axioms CapHashScheme.recomposeUp_inj_of_path
#assert_axioms CapHashScheme.deployedCapOpen_implies_authorizedB
#assert_axioms oneEdge_faithful
#assert_axioms deployedEncodes_inhabited
#assert_axioms bridge_fires
#assert_axioms empty_caps_unauthorized

end Dregg2.Circuit.DeployedCapTree
