/-
# Dregg2.Circuit.Emit.EffectVmEmitCapReshape — the OPENABLE `capability_root` (the ARGUS linchpin).

The cap-reshape crown (#103): an OPENABLE `capability_root` — a sorted-Poseidon2 Merkle commitment
over a cell's HELD capabilities — so the circuit can witness, IN-CIRCUIT, the two capability-security
properties a light client must trust WITHOUT re-running history:

  (a) **non-amplification** — a granted cap is `≤` a held cap: an OPENING of the parent's held cap
      proves the parent holds at least what it confers, so a grant cannot amplify authority;
  (b) **production-authority** — a mint/production is gated on HOLDING the issuer's capability: the
      production effect OPENS the issuer-cap it requires from the producer's held-set root. Authority
      is PRODUCTION under non-forgeability (`unsealer ⊗ sealed ⊢ contents`, mint/powerbox), NOT affine
      descent — the constructive-knowledge correction (`CONSTRUCTIVE-KNOWLEDGE.md` §3): "only
      connectivity begets connectivity" = epistemic non-forgeability (generative acts authorized-BY-HELD
      + receipt-disclosed), never weakening-only. We NEVER re-make the §3 affine error.

## What "openable" means here, and why this is NOT a re-invention

`EffectVmEmitCapRoot` advances `cap_root` as a prepend-accumulator DIGEST (Phase A) and explicitly
defers the genuine sorted-tree OPEN ("Phase E, out of scope here"). `EffectVmEmitV2.attenuateV2_non_amp`
opens a v2 `MapOp` map with a bitwise submask — but over a GENERIC map, not the real `is_attenuation`
`Finset Auth` lattice, and with NO production-authority leg. The proven OPENABLE sorted-Poseidon2 map
already EXISTS: `Dregg2.Substrate.Heap` ("the cap_root machinery generalized to a generic leaf":
`get` = membership opening, `set` = sorted insert-or-update, `root`/`root_injective`/`root_binds_get` =
the openable committed root + its anti-ghost, `ext_get` = canonicity). And the real attenuation lattice
already EXISTS: `Dregg2.Exec.Caps` (`confRights : Cap → ExecAuth = Finset Auth`, `≤` is `⊆`,
`attenuate_confRights_le` = `granted ≤ held`).

This module WELDS those two proven primitives — the openable sorted map + the real lattice — into the
ONE openable `capability_root` model the ARGUS apex needs, AND adds the production-authority leg that
existed NOWHERE: a held-set whose committed root OPENS to the issuer cap a mint requires. The WELD
method: the capability usually already exists, disconnected; welding beats building.

## The two levels (honest, each clean)

  * The COMMITTED level — `HeldEntry` = the leaf CONTENT `(slot, target, rightsMask)` the deployed
    `cap_root.rs` tree holds (a digest, not the executor `Cap` object). The held-set is a sorted-by-slot
    map of entries; `capRoot` is the sponge of the sorted leaf list, EXACTLY `Heap.root`. Equal roots
    BIND the whole held-set (`heldSet_determined`, via `Heap.ext_get` + CR) — the anti-ghost: a forged
    held leaf with inflated rights is excluded. An OPENING (`OpensEntry`) = the root opens at a slot to
    an entry (membership + the recomputed root); the opening is FUNCTIONAL (`opensEntry_functional`).
  * The LATTICE level — the real `is_attenuation` over `Cap`/`ExecAuth = Finset Auth`. `nonAmplifying`
    = `confRights granted ≤ confRights held` (the genuine `⊆`); `grant_attenuated_nonAmplifying` admits
    every honest attenuation; `overGrant_rejected`/`incomparableGrant_rejected` are the two-valued teeth
    (the FULL partial order, not a cardinality scalar).
  * The BRIDGE — `entryEncodes c e`: the committed entry `e`'s `rightsMask` is the submask digest of
    `c`'s conferred rights (`rightsMaskOf c`), and its target is `c`'s. So the in-circuit SUBMASK gate
    `granted.rightsMask ⊑ held.rightsMask` is the committed shadow of the lattice order, the rights
    digest binding both. `submask_of_attenuate` witnesses that an honest attenuation passes BOTH the
    lattice gate and the committed submask gate — the two levels agree on honest grants.

## §3 — PRODUCTION-AUTHORITY (the §3-correct leg, NEW)

`ProductionAuthorized` = the producer's held-set root OPENS, at a slot, to the ISSUER entry for asset
`A` (`IssuerEntry`: targets `A`, carries the `control`/mint bit). `production_of_held_issuer` is the
constructive witness (EXHIBIT the held issuer entry ⟹ authority); `unauthorizedMint_rejected` is the
anti-unauthorized-mint tooth (no opening ⟹ rejected); `wrongAssetMint_rejected` binds the asset.

## §4 — the CIRCUIT DESCRIPTOR (the LAW#1 emit)

`capReshapeVmDescriptor : EffectVmDescriptor` — in-row sites RECOMPUTE the held-entry leaf + the
granted-entry leaf + bind them into `cap_root`, plus the submask non-amp gate (`granted & held =
granted`) and the production-authority issuer-leaf site, with the anti-amplify + anti-unauthorized-mint
teeth proven at `satisfiedVm`. Byte-pinned via `emitVmJson` (→ `circuit/descriptors/*.json`).

## The honest seam (the carried hypothesis for the full ARGUS apex)

The committed-level anti-ghost + the lattice-level non-amp are both axiom-clean against the abstract CR
sponge (`Poseidon2SpongeCR`). The descriptor's in-circuit non-amp checks the SUBMASK shadow and binds
the rights digest; the bridge to the genuine `Finset Auth` order is `entryEncodes` (the rights-encoding
faithfulness, a per-cell-bound named correspondence — the boundary `EffectVmEmitV2` carries). The
TURN-level binding of the opened `cap_root` to the producer's authenticated cell-root is the sdk
authority-binding (`full_turn_proof.rs`, the Phase-D payoff), cited not claimed here.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. Crypto enters ONLY as the
named `Poseidon2SpongeCR` hypothesis (via `Heap`), never as an axiom.
NEW file; imports are read-only.
-/
-- Declared directly (2026-07-10): previously transitive via an upstream
-- `Mathlib.Tactic` umbrella, since trimmed.
import Mathlib.Tactic.IntervalCases
import Dregg2.Substrate.Heap
import Dregg2.Exec.Caps
import Dregg2.Circuit.Emit.EffectVmEmitCapRoot

namespace Dregg2.Circuit.Emit.EffectVmEmitCapReshape

open Dregg2.Substrate.Heap
open Dregg2.Exec (ExecAuth confRights attenuate attenuate_confRights_le)
open Dregg2.Authority (Auth Cap capAuthConferred)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Exec.CircuitEmit (EmittedExpr)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §1 — the OPENABLE held-set: a slot-keyed sorted map of cap-LEAF CONTENT.

A cell's HELD capabilities commit, in the deployed `cap_root.rs` tree, as a sorted-by-slot map whose
leaves bind the CONTENT `(slot, target, rightsMask)` (slot unique per the c-list,
`validate_capability_uniqueness` → injective key → one leaf per slot). The committed `capRoot` is the
sponge of the sorted cap-leaf list — EXACTLY the openable `Heap.root` shape with the cap leaf
`capLeaf = hash[slot, target, rightsMask]`. So every `Heap` opening theorem (`get`/`set`/`root_injective`/
`ext_get`) applies to the held-set VERBATIM. -/

/-- A committed cap-LEAF entry: the content the deployed sorted-Poseidon2 cap-tree leaf binds — the
cap's connectivity `target` and its conferred-`rightsMask` (a bitmask digest). NOT the executor `Cap`
object (the tree holds the digest content, the cell holds the function); `entryEncodes` is the bridge. -/
structure HeldEntry where
  /-- the cap's connectivity TARGET cell (a felt). -/
  target : ℤ
  /-- the conferred-rights MASK (the bitwise digest the submask gate compares). -/
  rightsMask : ℤ
deriving DecidableEq, Repr

/-- The HELD-SET: a slot-keyed (`ℤ`) sorted association list of cap-leaf entries. The in-order leaf
list of the sorted-Poseidon2 cap-tree, keyed by the unique `slot`. -/
abbrev HeldCaps := List (ℤ × HeldEntry)

/-- **`capLeaf hash slot e`** — the openable cap LEAF: `hash[slot, target, rightsMask]` — binds WHERE
the cap sits (slot), WHAT it points at (target) and WHAT it confers (rights mask). The cap-specific
instance of `Heap.leafOf`'s generic content leaf. -/
def capLeaf (hash : List ℤ → ℤ) (slot : ℤ) (e : HeldEntry) : ℤ :=
  hash [slot, e.target, e.rightsMask]

/-- **`capRoot hash held`** — the openable committed capability root: the sponge of the sorted cap-leaf
list. The value the `cap_root` column carries; computed from the SAME held-set list the cell holds
(cell≡circuit identity is BY DEFINITION at this layer — both read THIS function). `Heap.root` with the
cap leaf. -/
def capRoot (hash : List ℤ → ℤ) (held : HeldCaps) : ℤ :=
  hash (held.map (fun p => capLeaf hash p.1 p.2))

/-- **`OpensEntry hash root slot e held`** — the MEMBERSHIP OPENING: the published `root` IS the
capRoot of a SORTED held-set in which `slot` opens to entry `e`. The witness the circuit gates consume:
a prover exhibits the held-set (private witness), the slot, and the held entry; the opening asserts the
published root recomputes from a sorted held-set holding exactly that entry at that slot. -/
structure OpensEntry (hash : List ℤ → ℤ) (root slot : ℤ) (e : HeldEntry) (held : HeldCaps) : Prop where
  /-- the held-set is sorted (the c-list uniqueness invariant → a canonical openable tree). -/
  sorted : SortedKeys held
  /-- the published root IS the held-set's committed cap-root. -/
  rootEq : capRoot hash held = root
  /-- the slot OPENS to the held entry (the membership leg). -/
  member : get held slot = some e

/-! ### The opening is FUNCTIONAL: under CR, the root determines the WHOLE held-set (the anti-ghost).

A prover cannot publish the same `cap_root` and OPEN to a DIFFERENT (e.g. rights-inflated) held-set.
Equal capRoots ⇒ (outer CR) equal leaf lists ⇒ (per-leaf CR) equal `(slot, entry)` pairs ⇒ equal
held-sets (`heldSet_determined`). Then the per-slot opening is determined (`opensEntry_functional`).
The cap-specific form of "a forged held leaf with inflated rights is excluded". -/

/-- **`capLeaf_injective`** — under CR, the cap leaf BINDS its `(slot, target, rightsMask)`: equal
leaves force equal slot AND equal entry content. The inner-leaf half of the anti-ghost. -/
theorem capLeaf_injective (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {s₁ s₂ : ℤ} {e₁ e₂ : HeldEntry}
    (h : capLeaf hash s₁ e₁ = capLeaf hash s₂ e₂) :
    s₁ = s₂ ∧ e₁ = e₂ := by
  unfold capLeaf at h
  have hlist := hCR _ _ h
  rw [List.cons.injEq, List.cons.injEq, List.cons.injEq] at hlist
  obtain ⟨hs, ht, hr, _⟩ := hlist
  obtain ⟨t₁, r₁⟩ := e₁
  obtain ⟨t₂, r₂⟩ := e₂
  exact ⟨hs, by simp_all⟩

/-- The keyed-pair leaf map is injective under CR (heads peel by leaf-CR, tails by induction) — the
list lift of `capLeaf_injective`, mirroring `Heap.map_leaf_injective`. -/
theorem capLeafList_injective (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    ∀ (l₁ l₂ : HeldCaps),
      l₁.map (fun p => capLeaf hash p.1 p.2) = l₂.map (fun p => capLeaf hash p.1 p.2) → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ h; cases l₂ with
    | nil => rfl
    | cons hd t => simp at h
  | cons hd₁ t₁ ih =>
    intro l₂ h
    cases l₂ with
    | nil => simp at h
    | cons hd₂ t₂ =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨hleaf, htail⟩ := h
      obtain ⟨s₁, e₁⟩ := hd₁
      obtain ⟨s₂, e₂⟩ := hd₂
      obtain ⟨hs, he⟩ := capLeaf_injective hash hCR hleaf
      simp only at hs he
      subst hs; subst he
      rw [ih t₂ htail]

/-- **`heldSet_determined` — the root BINDS the WHOLE held-set (the anti-ghost).** Under CR, two
held-sets with EQUAL published `capRoot`s are EQUAL (leaf lists). So a prover cannot keep the published
`cap_root` while tampering ANY slot / target / conferred-rights mask — the cap-reshape `root_injective`
tooth (the cap-specific form of `Heap.root_injective`). -/
theorem heldSet_determined (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {h₁ h₂ : HeldCaps} (h : capRoot hash h₁ = capRoot hash h₂) : h₁ = h₂ :=
  capLeafList_injective hash hCR h₁ h₂ (hCR _ _ h)

/-- **`opensEntry_functional` — THE OPENING IS FUNCTIONAL (anti-ghost).** Under CR, two openings of
the SAME root at the SAME slot agree on the held entry. So a prover cannot keep the published `cap_root`
while opening the slot to a forged, rights-inflated held entry: the opened entry's rights mask is pinned
by the root. The cap-specific `root_injective`/`root_binds_get` tooth. -/
theorem opensEntry_functional (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {root slot : ℤ} {e₁ e₂ : HeldEntry} {h₁ h₂ : HeldCaps}
    (o₁ : OpensEntry hash root slot e₁ h₁) (o₂ : OpensEntry hash root slot e₂ h₂) :
    e₁ = e₂ := by
  -- equal published roots ⇒ equal held-sets ⇒ same `get slot` ⇒ same opened entry.
  have hroots : capRoot hash h₁ = capRoot hash h₂ := by rw [o₁.rootEq, o₂.rootEq]
  have hsets := heldSet_determined hash hCR hroots
  have hm₁ := o₁.member
  rw [hsets, o₂.member] at hm₁
  exact (Option.some.injEq _ _ ▸ hm₁).symm

/-- **`opens_member` — an opening exhibits the held entry at the slot.** The membership leg, named for
the consumers below. -/
theorem opens_member {hash : List ℤ → ℤ} {root slot : ℤ} {e : HeldEntry} {held : HeldCaps}
    (h : OpensEntry hash root slot e held) : get held slot = some e := h.member

/-! ## §2 — NON-AMPLIFICATION: a granted cap cannot exceed the opened held cap.

The crown property, at the genuine `is_attenuation` lattice (`Cap`/`ExecAuth = Finset Auth`), NOT the
cardinality shadow nor a `()≤()` collapse. Because a genuine `attenuate` structurally narrows, the gate
ADMITS every honest attenuation (`grant_attenuated_nonAmplifying`) and REJECTS a rights-superset or
incomparable pair (`overGrant_rejected`/`incomparableGrant_rejected`) — two-valued, the FULL partial
order. The COMMITTED-level submask shadow (`submask`) is what the circuit checks; `submask_of_attenuate`
shows an honest attenuation also passes the submask gate (so the two levels agree on honest grants). -/

/-- **`nonAmplifying held granted`** — the NON-AMPLIFICATION predicate: the granted cap confers `≤`
the held cap, over the genuine `ExecAuth = Finset Auth` `⊆` order (the real `is_attenuation`). The
grant gate admits IFF this holds; a grant that amplifies (rights ⊄ held) is rejected. -/
def nonAmplifying (held granted : Cap) : Prop := confRights granted ≤ confRights held

/-- `nonAmplifying` is DECIDABLE (the `Finset Auth` order is decidable), so the gate is computable. -/
instance (held granted : Cap) : Decidable (nonAmplifying held granted) := by
  unfold nonAmplifying; infer_instance

/-- **`grant_attenuated_nonAmplifying` — the gate ADMITS every honest attenuation.** A cap granted by
ATTENUATING the held cap (`attenuate keep held` — the only way to derive a child cap) is
non-amplifying: directly the executor's structural narrowing `attenuate_confRights_le`. So an honest
grant always passes the gate (fail-closed, never fail-stuck). -/
theorem grant_attenuated_nonAmplifying (held : Cap) (keep : List Auth) :
    nonAmplifying held (attenuate keep held) :=
  attenuate_confRights_le keep held

/-- **`nonAmplifying_admits_iff` — the gate is exactly the FULL subset check.** The non-amplification
predicate holds IFF `granted`'s conferred rights are `⊆` `held`'s, over the genuine `Finset Auth`
order — so the gate is two-valued (admits a subset, rejects a non-subset). -/
theorem nonAmplifying_admits_iff (held granted : Cap) :
    nonAmplifying held granted ↔ confRights granted ≤ confRights held := Iff.rfl

/-- **`overGrant_rejected` — THE ANTI-AMPLIFY TOOTH (witness FALSE).** A grant whose rights are a
strict SUPERSET of the held cap is REJECTED: a parent holding only `{read}` cannot grant `{read, write}`
— `¬ nonAmplifying`. The gate fails closed on amplification. -/
theorem overGrant_rejected :
    ¬ nonAmplifying (Cap.endpoint 7 [Auth.read]) (Cap.endpoint 7 [Auth.read, Auth.write]) := by
  unfold nonAmplifying confRights
  simp only [capAuthConferred]
  decide

/-- **`incomparableGrant_rejected` — the FULL partial-order tooth (witness FALSE).** The thing a
cardinality gate could NEVER do: a parent holding only `{read}` cannot grant `{write}` (EQUAL
cardinality, but neither ⊆ the other) — `¬ nonAmplifying`. The gate decides the genuine `Finset Auth`
partial order, not a scalar. -/
theorem incomparableGrant_rejected :
    ¬ nonAmplifying (Cap.endpoint 7 [Auth.read]) (Cap.endpoint 7 [Auth.write]) := by
  unfold nonAmplifying confRights
  simp only [capAuthConferred]
  decide

/-! ### §2′ — the BRIDGE: the committed submask shadow of the lattice order.

The deployed cap-tree leaf holds a rights MASK (a felt), not the `Finset Auth`; the in-circuit non-amp
gate compares two masks bitwise (`granted ⊑ held` ⟺ `granted &&& held = granted`). `rightsMaskOf c` is
the canonical mask of a cap's conferred rights; an opening at the committed level exposes
`held.rightsMask`, and the gate checks `granted.rightsMask ⊑ held.rightsMask`. This is the shadow the
circuit can enforce per-row; the genuine lattice non-amp (§2) is the model property the encoding
faithfulness (`entryEncodes`) lifts to. -/

/-- The per-`Auth` bit weight as a NAT (for the bitwise OR fold; the canonical positional mask matching
`cap_root.rs`'s mask split). -/
def authBitN : Auth → Nat
  | .read    => 1
  | .write   => 2
  | .grant   => 4
  | .call    => 8
  | .reply   => 16
  | .reset   => 32
  | .control => 64
  | .notify  => 128

/-- The per-`Auth` bit weight as a felt (the committed mask uses `ℤ`). -/
def authBit (a : Auth) : ℤ := (authBitN a : ℤ)

/-- **`rightsMaskOf c`** — the conferred-rights MASK of a cap (the bitwise OR of its conferred `Auth`
bits, as a felt). The committed value the cap leaf binds (`entryEncodes`); the mask the submask gate
reads. -/
def rightsMaskOf (c : Cap) : ℤ :=
  (((capAuthConferred c).foldr (fun a m => m ||| authBitN a) 0 : Nat) : ℤ)

/-- **`capTargetOf c`** — the cap's connectivity TARGET as a felt (the committed leaf's `target`). -/
def capTargetOf : Cap → ℤ
  | .endpoint t _ => (t : ℤ)
  | .node t       => (t : ℤ)
  | .null         => -1

/-- **`entryEncodes c e`** — the BRIDGE: the committed entry `e` is the digest of cap `c` (same target,
same conferred-rights mask). The per-cell-bound correspondence the descriptor's submask gate rides on:
on a row where the opened held entry encodes the parent cap and the granted entry encodes the child,
the submask gate `granted.rightsMask ⊑ held.rightsMask` is the committed shadow of `nonAmplifying`. -/
def entryEncodes (c : Cap) (e : HeldEntry) : Prop :=
  e.target = capTargetOf c ∧ e.rightsMask = rightsMaskOf c

/-- **`submask a b`** — the committed-level non-amp check: `a ⊑ b` bitwise (`a &&& b = a`). The exact
relation the in-circuit submask gate / `EffectVmEmitV2.subsetTable` enforces over the felt masks. -/
def submask (a b : ℤ) : Prop := (a.toNat &&& b.toNat) = a.toNat

/-- `submask` is decidable. -/
instance (a b : ℤ) : Decidable (submask a b) := by unfold submask; infer_instance

/-- **`submask_self`** — a mask is a submask of itself (the identity attenuation passes the gate). -/
theorem submask_self (a : ℤ) : submask a a := by
  unfold submask; exact Nat.and_self _

/-- **`submask_of_attenuate` — THE BRIDGE (the two levels agree on an honest attenuation).** For a
concrete honest attenuation — narrowing `endpoint`-rights `[read, write]` (mask `3`) to `[read]` (mask
`1`) — the GRANTED mask IS a submask of the HELD mask (`1 ⊑ 3`, `1 &&& 3 = 1`). So a grant that the
lattice gate `nonAmplifying` admits ALSO passes the in-circuit committed SUBMASK gate: the committed
shadow agrees with the genuine `Finset Auth` order on honest grants (the `entryEncodes` correspondence,
witnessed). Non-vacuous in BOTH directions: the genuine attenuation `confRights {read} ≤ {read,write}`
holds (`grant_attenuated_nonAmplifying`-shape) AND its mask shadow `1 ⊑ 3` holds. -/
theorem submask_of_attenuate :
    -- the LATTICE-level honest attenuation (the §2 gate admits) …
    nonAmplifying (Cap.endpoint 7 [Auth.read, Auth.write]) (Cap.endpoint 7 [Auth.read])
    -- … AND its COMMITTED mask shadow (the in-circuit submask gate admits): the two levels agree.
    ∧ submask (rightsMaskOf (Cap.endpoint 7 [Auth.read]))
              (rightsMaskOf (Cap.endpoint 7 [Auth.read, Auth.write])) := by
  refine ⟨?_, ?_⟩
  · -- {read} ⊆ {read,write} over the genuine Finset Auth order.
    unfold nonAmplifying confRights; simp only [capAuthConferred]; decide
  · -- mask 1 ⊑ mask 3 (the committed submask shadow): 1 &&& 3 = 1.
    unfold submask rightsMaskOf authBitN; simp only [capAuthConferred]; decide

/-- **`submask_overGrant_rejected` — the committed anti-amplify tooth (witness FALSE).** `{read,write}`
(mask 3) is NOT a submask of `{read}` (mask 1): `3 &&& 1 = 1 ≠ 3`. So the in-circuit submask gate, like
the lattice gate, REJECTS an amplifying grant at the committed level. -/
theorem submask_overGrant_rejected : ¬ submask 3 1 := by decide

/-! ## §3 — PRODUCTION-AUTHORITY: a mint is gated on OPENING the issuer's capability.

Authority is PRODUCTION under non-forgeability, NOT affine descent (the §3 correction). A mint/
production of asset `A` is authorized IFF the producer HOLDS the issuer capability for `A` — and the
circuit witnesses that by OPENING the issuer entry from the producer's held-set root. The producer
cannot conjure authority it does not hold; it can only EXHIBIT (open) a held issuer cap. The mint right
is the `control` bit; the issuer cap TARGETS `A` (modeled as its issuer cell id). -/

/-- The `control` (mint) bit in the rights mask. -/
def CONTROL_BIT : ℤ := authBit .control

/-- **`IssuerEntry A e`** — the committed entry `e` is the ISSUER entry for asset `A`: it targets `A`'s
issuer cell (`A`) and its mask carries the `control` (mint) bit. Holding THIS — and OPENING it — is what
authorizes a mint of `A`. The "only connectivity begets connectivity" production authority. -/
def IssuerEntry (A : ℤ) (e : HeldEntry) : Prop :=
  e.target = A ∧ submask CONTROL_BIT e.rightsMask

/-- `IssuerEntry` is decidable. -/
instance (A : ℤ) (e : HeldEntry) : Decidable (IssuerEntry A e) := by unfold IssuerEntry; infer_instance

/-- **`ProductionAuthorized hash root A slot held`** — the production-authority OPENING: the producer's
held-set root OPENS, at `slot`, to the ISSUER entry for asset `A`. A mint of `A` verifies this opening
in-circuit; a mint WITHOUT it is rejected. Production gated on HELD authority — the non-forgeability
formulation, never affine descent. -/
def ProductionAuthorized (hash : List ℤ → ℤ) (root A slot : ℤ) (held : HeldCaps) : Prop :=
  ∃ e, OpensEntry hash root slot e held ∧ IssuerEntry A e

/-- **`production_of_held_issuer` — the WELD (witness TRUE): holding+opening the issuer cap authorizes
the mint.** If the producer's held-set is sorted, opens at `slot` to the issuer entry for `A`, and its
root is published as `root`, then the production is authorized. The constructive direction: EXHIBIT the
held issuer cap ⟹ authority. -/
theorem production_of_held_issuer (hash : List ℤ → ℤ) (root A slot : ℤ) (e : HeldEntry)
    (held : HeldCaps)
    (hsorted : SortedKeys held)
    (hmem : get held slot = some e)
    (hroot : capRoot hash held = root)
    (hissuer : IssuerEntry A e) :
    ProductionAuthorized hash root A slot held :=
  ⟨e, ⟨hsorted, hroot, hmem⟩, hissuer⟩

/-- **`unauthorizedMint_rejected` — THE ANTI-UNAUTHORIZED-MINT TOOTH (witness FALSE).** A mint with NO
issuer-cap opening is rejected: if the producer's held-set does NOT hold ANY cap at the queried slot
(`get held slot = none` — the slot is absent), then `ProductionAuthorized` is FALSE. A producer cannot
mint `A` without opening a held issuer cap for `A`. -/
theorem unauthorizedMint_rejected (hash : List ℤ → ℤ) (root A slot : ℤ) (held : HeldCaps)
    (habsent : get held slot = none) :
    ¬ ProductionAuthorized hash root A slot held := by
  rintro ⟨e, hopen, _⟩
  rw [hopen.member] at habsent
  exact absurd habsent (by simp)

/-- **`wrongAssetMint_rejected` — the issuer-cap must be for THE asset (witness FALSE).** Even holding
an entry at the slot, if it is the issuer entry for a DIFFERENT asset `B ≠ A` (its target is `B`), it
does NOT authorize a mint of `A`: `¬ IssuerEntry A e`. The production opening must bind the asset. -/
theorem wrongAssetMint_rejected (A B : ℤ) (e : HeldEntry) (hAB : A ≠ B)
    (htarget : e.target = B) :
    ¬ IssuerEntry A e := by
  rintro ⟨ht, _⟩
  rw [htarget] at ht
  exact hAB ht.symm

/-- **`noControlMint_rejected` — the issuer-cap must carry the MINT (control) bit (witness FALSE).** An
entry targeting `A` but WITHOUT the `control` bit (e.g. a read-only mask `1`) does NOT authorize a mint:
`¬ IssuerEntry A e`. So a held read-only cap on the issuer cell cannot be opened as a mint authority —
production needs the genuine mint right, not mere connectivity. -/
theorem noControlMint_rejected (A : ℤ) :
    ¬ IssuerEntry A { target := A, rightsMask := 1 } := by
  rintro ⟨_, hctrl⟩
  -- `submask CONTROL_BIT 1` would be `64 &&& 1 = 64`, but `64 &&& 1 = 0 ≠ 64`.
  have : ¬ submask CONTROL_BIT 1 := by decide
  exact this hctrl

/-! ## §4 — THE CIRCUIT DESCRIPTOR (the LAW#1 emit): the in-circuit non-amp + production-authority gates.

The model (§1–§3) is the openable-root SEMANTICS; this section EMITS the verified-by-construction
`EffectVmDescriptor` whose `satisfiedVm` ENFORCES the two openings in-row, so the Rust prover (which
INTERPRETS the descriptor, authors no constraint) checks them. The descriptor carries, on the active
cap-reshape row:

  * the HELD-LEAF recompute (`siteHeldLeaf`): `held_leaf = hash[slot, target, held_mask]` — binds the
    opened held entry's content (its bits are the in-circuit `held_mask`);
  * an 8-bit DECOMPOSITION of the held mask + the granted mask (the `Auth` mask is 8 bits), each bit
    booleaned (`b·(b−1)=0`) and the mask RECONSTRUCTED from its bits (`mask = Σ bᵢ·2ⁱ`);
  * the NON-AMP submask gate, per-bit: `gᵢ·(1−hᵢ)=0` — a granted bit may be set ONLY where the held bit
    is (`granted ⊑ held` bitwise), the in-row anti-amplify tooth;
  * the PRODUCTION-AUTHORITY gate: `held_target = asset` (PI) AND the control bit `h₆ = 1` — the opened
    held leaf IS the issuer leaf for the minted asset, the in-row anti-unauthorized-mint tooth.

The `satisfiedVm` teeth (`capReshape_nonAmp_in_circuit`, `capReshape_production_in_circuit`) extract
exactly these from a satisfying witness; the rejections (`capReshape_rejects_amplify`,
`capReshape_rejects_no_control`) are the two-valued anti-ghost. -/

/-- The bit width of the `Auth` rights mask (8 atoms ⇒ 8 bits, `authBit` covers `read`..`notify`). -/
def MASK_BITS : Nat := 8

namespace col
/-- The cap SLOT param column (the slot being opened). Reuses `EffectVmEmitCapRoot.cp.HOLDER`. -/
def SLOT : Nat := EffectVmEmitCapRoot.cp.HOLDER
/-- The cap TARGET param column (the held cap's connectivity target). Reuses `cp.TARGET`. -/
def TARGET : Nat := EffectVmEmitCapRoot.cp.TARGET
/-- The HELD rights-mask param column (the opened parent cap's mask). Reuses `cp.RIGHTS`. -/
def HELD_MASK : Nat := EffectVmEmitCapRoot.cp.RIGHTS
/-- The GRANTED rights-mask param column (the child cap's mask; must be a submask of held). The 7th
param slot (param 6), free on a cap-reshape row. -/
def GRANTED_MASK : Nat := 6
/-- The recomputed HELD-LEAF carrier (an aux column; distinct from the cap-root recompute carriers). -/
def HELD_LEAF : Nat := auxCol aux_off.STATE_INTER3 + 3
/-- The base aux column of the HELD mask's bit decomposition (`MASK_BITS` columns). -/
def HELD_BIT_BASE : Nat := auxCol aux_off.STATE_INTER3 + 4
/-- The base aux column of the GRANTED mask's bit decomposition (`MASK_BITS` columns). -/
def GRANTED_BIT_BASE : Nat := auxCol aux_off.STATE_INTER3 + 4 + MASK_BITS
/-- The held bit at position `i`. -/
def heldBit (i : Nat) : Nat := HELD_BIT_BASE + i
/-- The granted bit at position `i`. -/
def grantedBit (i : Nat) : Nat := GRANTED_BIT_BASE + i
end col

/-- The PI index the production-authority gate binds the held `target` to (the MINTED ASSET id). -/
def PI_ASSET : Nat := 0

/-- The control-bit POSITION in the mask (`authBit .control = 64 = 2^6`). -/
def CONTROL_BIT_POS : Nat := 6

/-! ### §4.0 — gate-body builders (the `EmittedExpr` polynomials the AIR asserts ZERO). -/

/-- `e₁ − e₂` as an `EmittedExpr` (the `assert_zero(lhs − rhs)` shape). -/
def eSub (a b : EmittedExpr) : EmittedExpr := .add a (.mul (.const (-1)) b)

/-- A column read. -/
def eCol (c : Nat) : EmittedExpr := .var c

/-- **`gBool c`** — the BOOLEAN gate body `c·(c−1)`: zero iff column `c` is `0` or `1`. -/
def gBool (c : Nat) : EmittedExpr := .mul (eCol c) (eSub (eCol c) (.const 1))

/-- **`gSubmaskBit i`** — the per-bit NON-AMP gate body `gᵢ·(1 − hᵢ)`: zero iff the granted bit is NOT
set OR the held bit IS set (i.e. `gᵢ ≤ hᵢ`). The in-row anti-amplify tooth, one bit at a time. -/
def gSubmaskBit (i : Nat) : EmittedExpr :=
  .mul (eCol (col.grantedBit i)) (eSub (.const 1) (eCol (col.heldBit i)))

/-- The bit-weighted reconstruction `Σ_{i<n} bitCol(i)·2ⁱ` of a mask from its bit columns. -/
def reconstruct (bitCol : Nat → Nat) : Nat → EmittedExpr
  | 0 => .const 0
  | n + 1 => .add (reconstruct bitCol n) (.mul (eCol (bitCol n)) (.const ((2 ^ n : Nat) : ℤ)))

/-- **`gMaskRecon maskCol bitCol`** — the mask-reconstruction gate body: `maskCol − Σ bitᵢ·2ⁱ`, zero
iff the mask column equals its bit decomposition (so the bits genuinely decode the mask). -/
def gMaskRecon (maskCol : Nat) (bitCol : Nat → Nat) : EmittedExpr :=
  eSub (eCol maskCol) (reconstruct bitCol MASK_BITS)

/-! ### §4.1 — the descriptor's constraint segments. -/

/-- The per-bit BOOLEAN + SUBMASK + reconstruction gates (the non-amplification leg, in-circuit). -/
def nonAmpGates : List VmConstraint :=
  ((List.range MASK_BITS).map (fun i => VmConstraint.gate (gBool (col.heldBit i))))
    ++ ((List.range MASK_BITS).map (fun i => VmConstraint.gate (gBool (col.grantedBit i))))
    ++ ((List.range MASK_BITS).map (fun i => VmConstraint.gate (gSubmaskBit i)))
    ++ [ VmConstraint.gate (gMaskRecon col.HELD_MASK col.heldBit)
       , VmConstraint.gate (gMaskRecon col.GRANTED_MASK col.grantedBit) ]

/-- The PRODUCTION-AUTHORITY gates: the held `target` param equals the minted-asset PI (binds the
issuer cell), and the control bit is set (`h₆ = 1`, i.e. `h₆ − 1 = 0`). The anti-unauthorized-mint leg. -/
def productionGates : List VmConstraint :=
  [ VmConstraint.piBinding .first (prmCol col.TARGET) PI_ASSET
  , VmConstraint.gate (eSub (eCol (col.heldBit CONTROL_BIT_POS)) (.const 1)) ]

/-- The HELD-LEAF recompute site: `held_leaf = hash[slot, target, held_mask, 0]` — the opened parent
cap's content leaf, the membership-opening's recomputed leaf (so a tampered slot/target/mask moves the
leaf). Arity 4 (the deployed Poseidon2 rate; the 4th input is the spare `.zero`, matching
`EffectVmEmitCapRoot.siteCapEdgeLeaf`'s 4-arity shape). -/
def siteHeldLeaf : VmHashSite :=
  { digestCol := col.HELD_LEAF
  , inputs := [ .col (prmCol col.SLOT), .col (prmCol col.TARGET), .col (prmCol col.HELD_MASK), .zero ]
  , arity := 4 }

/-- **`capReshapeVmDescriptor`** — the emitted cap-reshape circuit: the held-leaf recompute site + the
non-amplification submask gates + the production-authority gates. `traceWidth = EFFECT_VM_WIDTH` (186),
so the Rust `parse_vm_descriptor` ingests it on the base layout; the bit/leaf carriers are aux columns
within `[0, 186)`. -/
def capReshapeVmDescriptor : EffectVmDescriptor :=
  { name        := "dregg-effectvm-capreshape-v1"
  , traceWidth  := EFFECT_VM_WIDTH
  , piCount     := 1
  , constraints := nonAmpGates ++ productionGates
  , hashSites   := [ siteHeldLeaf ]
  , ranges      := [] }

/-! ### §4.2 — `satisfiedVm` consequences: the descriptor ENFORCES the two openings in-row.

We extract the per-bit submask (non-amp) and the issuer binding (production) from a satisfying witness.
The boundary flags: the production `piBinding .first` fires on the (single active) first row, so we take
`isFirst = true`. The per-bit gates are `.gate` bodies — under the deployed `when_transition()` they bind
on EVERY row but the last, so the in-circuit teeth are extracted at `isLast = false` (the active
transition row, which any real ≥2-row trace carries; the final row is the wrap/pad row). -/

/-- **`capReshape_nonAmp_in_circuit` — THE IN-CIRCUIT NON-AMP TOOTH.** A satisfying witness FORCES, on a
transition row (`isLast = false`), for every bit `i < MASK_BITS`, the granted bit ≤ the held bit
(`gᵢ = 0 ∨ hᵢ = 1`) — i.e. `granted ⊑ held` bitwise, per bit. The gate body vanishes mod the BabyBear
prime `p`, so the exact-`ℤ` conclusion needs CANONICALITY of the two bit cells (`0 ≤ cell < p` — what
the deployed range check supplies), then primality of `p` splits the product residual. The light client
reads ONLY the proof; this is the in-circuit non-amplification it now sees, not an executor-trusted
side-check. -/
theorem capReshape_nonAmp_in_circuit (hash : List ℤ → ℤ) (env : VmRowEnv) (isFirst isLast : Bool)
    (hlast : isLast = false)
    (hsat : satisfiedVm hash capReshapeVmDescriptor env isFirst isLast)
    (i : Nat) (hi : i < MASK_BITS)
    (hgc : 0 ≤ env.loc (col.grantedBit i) ∧ env.loc (col.grantedBit i) < 2013265921)
    (hhc : 0 ≤ env.loc (col.heldBit i) ∧ env.loc (col.heldBit i) < 2013265921) :
    env.loc (col.grantedBit i) = 0 ∨ env.loc (col.heldBit i) = 1 := by
  obtain ⟨hcon, _, _⟩ := hsat
  -- the submask gate for bit `i` is a member of the constraint list.
  have hsm : VmConstraint.gate (gSubmaskBit i) ∈
      (List.range MASK_BITS).map (fun j => VmConstraint.gate (gSubmaskBit j)) :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  have hmem : VmConstraint.gate (gSubmaskBit i) ∈ capReshapeVmDescriptor.constraints := by
    show _ ∈ (nonAmpGates ++ productionGates)
    refine List.mem_append_left _ ?_
    unfold nonAmpGates
    exact List.mem_append_left _ (List.mem_append_right _ hsm)
  have hg := hcon _ hmem
  -- the gate body `gᵢ·(1 − hᵢ) ≡ 0 [ZMOD p]` + primality + canonicality force `gᵢ = 0 ∨ hᵢ = 1`
  -- (on the transition row): `p ∣ gᵢ·(1−hᵢ)` splits, and each factor's only in-range multiple of `p`
  -- pins the exact value.
  subst hlast
  simp only [VmConstraint.holdsVm, gSubmaskBit, eSub, eCol, EmittedExpr.eval] at hg
  have hp : Prime (2013265921 : ℤ) := by
    exact_mod_cast Nat.prime_iff_prime_int.mp Dregg2.Circuit.BabyBearFriField.babyBearP_prime
  rw [Int.modEq_zero_iff_dvd] at hg
  rcases hp.dvd_mul.mp hg with h0 | h1
  · -- `p ∣ gᵢ` with `0 ≤ gᵢ < p` forces `gᵢ = 0`.
    obtain ⟨k, hk⟩ := h0
    exact Or.inl (by omega)
  · -- `p ∣ (1 − hᵢ)` with `0 ≤ hᵢ < p` forces `hᵢ = 1`.
    obtain ⟨k, hk⟩ := h1
    exact Or.inr (by omega)

/-- **`capReshape_production_in_circuit` — THE IN-CIRCUIT PRODUCTION-AUTHORITY TOOTH.** A satisfying
witness on the active (first) row FORCES: the held `target` param is CONGRUENT mod the BabyBear prime
to the minted-asset PI (the field-faithful PI binding — the AIR compares felts, so the pin is
`≡ [ZMOD p]`) AND the control bit is set exactly (`h₆ = 1`, the mint right — the exact value needs
CANONICALITY `0 ≤ h₆ < p`, what the deployed range check supplies). So a verifying proof genuinely
means the producer OPENED a held issuer cap for the asset — production gated on held authority,
in-circuit. -/
theorem capReshape_production_in_circuit (hash : List ℤ → ℤ) (env : VmRowEnv) (isLast : Bool)
    (hlast : isLast = false)
    (hsat : satisfiedVm hash capReshapeVmDescriptor env true isLast)
    (hhc : 0 ≤ env.loc (col.heldBit CONTROL_BIT_POS)
           ∧ env.loc (col.heldBit CONTROL_BIT_POS) < 2013265921) :
    (env.loc (prmCol col.TARGET) ≡ env.pub PI_ASSET [ZMOD 2013265921])
    ∧ env.loc (col.heldBit CONTROL_BIT_POS) = 1 := by
  obtain ⟨hcon, _, _⟩ := hsat
  have hmemPI : VmConstraint.piBinding .first (prmCol col.TARGET) PI_ASSET
      ∈ capReshapeVmDescriptor.constraints := by
    show _ ∈ (nonAmpGates ++ productionGates)
    refine List.mem_append_right _ ?_
    unfold productionGates
    exact List.mem_cons_self
  have hmemCtl : VmConstraint.gate (eSub (eCol (col.heldBit CONTROL_BIT_POS)) (.const 1))
      ∈ capReshapeVmDescriptor.constraints := by
    show _ ∈ (nonAmpGates ++ productionGates)
    refine List.mem_append_right _ ?_
    unfold productionGates
    exact List.mem_cons_of_mem _ List.mem_cons_self
  have hPI := hcon _ hmemPI
  have hCtl := hcon _ hmemCtl
  subst hlast
  simp only [VmConstraint.holdsVm, true_implies] at hPI
  simp only [VmConstraint.holdsVm, eSub, eCol, EmittedExpr.eval] at hCtl
  -- `h₆ − 1 ≡ 0 [ZMOD p]` + canonicality `0 ≤ h₆ < p` pin `h₆ = 1` exactly.
  rw [Int.modEq_zero_iff_dvd] at hCtl
  obtain ⟨k, hk⟩ := hCtl
  exact ⟨hPI, by omega⟩

/-- **`capReshape_rejects_amplify` — the anti-amplify rejection (witness FALSE).** A row where the
granted bit `i` is SET (`= 1`) but the held bit `i` is CLEAR (`= 0`) — an amplifying grant on bit `i` —
does NOT satisfy the descriptor: the submask gate `gᵢ·(1 − hᵢ) = 1·1 = 1 ≠ 0` FAILS. So the circuit
rejects amplification at the bit level. -/
theorem capReshape_rejects_amplify (hash : List ℤ → ℤ) (env : VmRowEnv) (isFirst isLast : Bool)
    (hlast : isLast = false)
    (i : Nat) (hi : i < MASK_BITS)
    (hg : env.loc (col.grantedBit i) = 1) (hh : env.loc (col.heldBit i) = 0) :
    ¬ satisfiedVm hash capReshapeVmDescriptor env isFirst isLast := by
  intro hsat
  -- the literal bit values 1/0 are canonical (`0 ≤ · < p`) by inspection.
  rcases capReshape_nonAmp_in_circuit hash env isFirst isLast hlast hsat i hi
      (by rw [hg]; norm_num) (by rw [hh]; norm_num) with h0 | h1
  · rw [hg] at h0; exact absurd h0 (by norm_num)
  · rw [hh] at h1; exact absurd h1 (by norm_num)

/-- **`capReshape_rejects_no_control` — the anti-unauthorized-mint rejection (witness FALSE).** A row
on the active (first) boundary whose held control bit is CLEAR (`= 0`) does NOT satisfy the descriptor:
the production-authority control gate `h₆ − 1 = −1 ≠ 0` FAILS. So a mint WITHOUT the held issuer cap's
mint bit is rejected in-circuit. -/
theorem capReshape_rejects_no_control (hash : List ℤ → ℤ) (env : VmRowEnv) (isLast : Bool)
    (hlast : isLast = false)
    (hh : env.loc (col.heldBit CONTROL_BIT_POS) = 0) :
    ¬ satisfiedVm hash capReshapeVmDescriptor env true isLast := by
  intro hsat
  -- the literal control-bit value 0 is canonical (`0 ≤ 0 < p`) by inspection.
  have := (capReshape_production_in_circuit hash env isLast hlast hsat (by rw [hh]; norm_num)).2
  rw [hh] at this
  exact absurd this (by norm_num)

/-! ### §4.3 — descriptor well-formedness + the byte-pinned wire string.

The carriers are distinct and in-range (`< EFFECT_VM_WIDTH`), so the Rust `parse_vm_descriptor`'s
bounds check passes; the descriptor is the SAME 186-col base trace every EffectVM descriptor shares. -/

/-- The held-leaf + the 16 bit carriers are DISTINCT and all `< EFFECT_VM_WIDTH = 186` (so the Rust
interpreter's `check_bounds` accepts; aux columns past the state block, within the base layout). -/
theorem capReshape_carriers_in_range :
    col.HELD_LEAF < EFFECT_VM_WIDTH
    ∧ (∀ i, i < MASK_BITS → col.heldBit i < EFFECT_VM_WIDTH)
    ∧ (∀ i, i < MASK_BITS → col.grantedBit i < EFFECT_VM_WIDTH) := by
  refine ⟨by decide, ?_, ?_⟩
  · intro i hi
    simp only [MASK_BITS] at hi
    unfold col.heldBit col.HELD_BIT_BASE auxCol AUX_BASE STATE_AFTER_BASE PARAM_BASE
      STATE_BEFORE_BASE aux_off.STATE_INTER3 EFFECT_VM_WIDTH NUM_EFFECTS STATE_SIZE NUM_PARAMS
    omega
  · intro i hi
    simp only [MASK_BITS] at hi
    unfold col.grantedBit col.GRANTED_BIT_BASE auxCol AUX_BASE STATE_AFTER_BASE PARAM_BASE
      STATE_BEFORE_BASE aux_off.STATE_INTER3 EFFECT_VM_WIDTH NUM_EFFECTS STATE_SIZE NUM_PARAMS MASK_BITS
    omega

/-- The non-amp segment has `3·MASK_BITS + 2` gates (held-bool + granted-bool + submask + 2 recon), and
the production segment has 2 (the PI binding + the control gate). The descriptor is non-trivial. -/
theorem capReshapeVmDescriptor_shape :
    capReshapeVmDescriptor.constraints.length = (3 * MASK_BITS + 2) + 2
    ∧ capReshapeVmDescriptor.hashSites.length = 1
    ∧ capReshapeVmDescriptor.traceWidth = EFFECT_VM_WIDTH := by
  refine ⟨by decide, by decide, rfl⟩

/-- **`capReshapeJson`** — the canonical wire string for the cap-reshape descriptor (`emitVmJson`). This
is the byte-exact JSON the Rust `parse_vm_descriptor` ingests (committed to
`circuit/descriptors/dregg-effectvm-capreshape-v1.json` and fingerprinted by the loader test). -/
def capReshapeJson : String := emitVmJson capReshapeVmDescriptor

#assert_axioms capReshape_nonAmp_in_circuit
#assert_axioms capReshape_production_in_circuit
#assert_axioms capReshape_rejects_amplify
#assert_axioms capReshape_rejects_no_control
#assert_axioms capReshape_carriers_in_range
#assert_axioms capReshapeVmDescriptor_shape

/-! ## §4D — THE DELEGATION-FAMILY NON-AMP GATES (the cap-root recompute's `granted ⊑ held` leg).

`§4` above is the MINT/production flavour: the held mask is the OPENED issuer leaf and the production
gate binds `held_target = asset` + the control bit. The cap-GRAPH family (`delegate`, `delegateAtten`,
`attenuate`, `introduce`, `revoke`, `refresh`) needs the OTHER leg of the SAME non-amp shadow: every
cap-graph row RECOMPUTES `cap_root` by hashing a `(holder, target, rights, op)` edge leaf
(`EffectVmEmitCapRoot.siteCapEdgeLeaf`), where `rights` (`cp.RIGHTS`, param 4) is the GRANTED edge's
conferred-rights mask — the value COMMITTED into the recomputed root. The delegation non-amp leg gates,
IN-CIRCUIT, that this granted mask is a SUBMASK of the delegator's HELD mask (`granted ⊑ held`), so a
grant cannot confer rights the delegator does not hold — and the very rights it binds into `cap_root`.

The per-bit gate `gᵢ·(1−hᵢ)=0` over `dcol.grantedBit i` / `dcol.heldBit i` is the anti-amplify tooth.
NO production gate (a delegate is not a mint), NO new width (aux columns < `EFFECT_VM_WIDTH` = 188).

### The wiring that makes this LOAD-BEARING (was a param-INDEX/COLUMN conflation; fixed 2026-07-17)

The GRANTED bit decomposition reconstructs `prmCol cp.RIGHTS` = **column 72** — the SAME column
`siteCapEdgeLeaf` hashes into the cap-edge leaf. So tampering the `rights` felt to confer rights the
delegator does not hold breaks the granted-recon gate; keeping the felt honest leaves the per-bit
submask gate in force. The two legs read ONE felt, and the "tamper `rights` ⇒ recon breaks (and the
recomputed root moves ⇒ `state_commit` moves) ⇒ UNSAT" interlock is real.

Until 2026-07-17 it was NOT. `gMaskRecon` consumes a raw COLUMN (`eSub (eCol maskCol) …`) while
`dcol.GRANTED_MASK := cp.RIGHTS` is a param INDEX, so the emitted gate read `v4` — an effect-SELECTOR
column (the selector block is `0..54`) — and `dcol.HELD_MASK := 7` emitted `v7`, not `prmCol 7 = 75`.
Nothing constrained col 72 against the granted bits, so a prover could confer ARBITRARY rights through
the recomputed `cap_root`. No proof and no `#assert_axioms` ever flagged it: `capDeleg_nonAmp_in_circuit`
/ `capDeleg_rejects_amplify` quantify over the BIT CARRIERS and were true either way — it was the PROSE
that was wrong, and the Rust differential
(`circuit/src/cap_delegation_nonamp_descriptor.rs::nonamp_leg_binds_the_hashed_rights_felt`) is
what proved the gap behaviourally. The `prmCol`-wrap in `capDelegNonAmpGates` closes it; that test now
asserts the tamper is REFUSED. The descriptor was never routed, so the defect was LATENT throughout.

⚠ RESIDUAL — the HELD mask is still a FREE PARAM on this flavour. `prmCol dcol.HELD_MASK` (col 75) is
read by the recon gate and by NOTHING else: no hash-site absorbs it and no PI binds it. So the tooth
this leg emits is "the rights committed into `cap_root` are a submask of a mask the PROVER CHOSE" — it
stops rights-felt forgery, but a prover free to set col 75 = `0xFF` still amplifies. Binding col 75 to
an OPENED parent cap (the mint flavour's `siteHeldLeaf` shape — `held_leaf = hash[slot,target,held,0]`
against a membership opening) is the NEXT rung and is NOT done here. Do not read `granted ⊑ held` as
conferred-rights non-amplification until col 75 is bound.

⚠ The mint-flavour `nonAmpGates` (§4.1) carries the IDENTICAL conflation — VERIFIED, not merely
suspected: `dregg-effectvm-capreshape-v1.json` gates 24/25 read `v4`/`v6` where `prmCol` gives 72/74.
Its `col.SLOT`/`col.TARGET`/`col.HELD_MASK` uses in `siteHeldLeaf`/`productionGates` are already
correctly `prmCol`-wrapped, so the fix is the same two call sites. Deliberately NOT fixed here:
`capReshapeVmDescriptor` is a separate emitted JSON with its own Rust consumer
(`circuit/src/cap_reshape_descriptor.rs`), out of this lane's file set. In HORIZONLOG. -/

namespace dcol
/-- The GRANTED rights-mask column for a delegation row: `cp.RIGHTS` (param 4) — the rights the cap-edge
leaf binds into the recomputed `cap_root`. The granted-bit decomposition reconstructs THIS, so the
non-amp gate constrains the exact rights committed into the root (the load-bearing tie). -/
def GRANTED_MASK : Nat := EffectVmEmitCapRoot.cp.RIGHTS
/-- The HELD rights-mask param for a delegation row: param 7 (free on a cap-graph row — params 2..5 are
the edge `(holder,target,rights,op)`, param 6 is the mint-flavour granted mask). The delegator's own
held-cap mask, the upper bound the granted mask may not exceed. -/
def HELD_MASK : Nat := 7
/-- The base aux column of the delegation HELD mask's bit decomposition (`MASK_BITS` columns). Past the
mint-flavour bit block (`col.GRANTED_BIT_BASE + MASK_BITS`), so the two non-amp legs never alias. -/
def HELD_BIT_BASE : Nat := col.GRANTED_BIT_BASE + MASK_BITS
/-- The base aux column of the delegation GRANTED mask's bit decomposition (`MASK_BITS` columns). -/
def GRANTED_BIT_BASE : Nat := col.GRANTED_BIT_BASE + MASK_BITS + MASK_BITS
/-- The delegation held bit at position `i`. -/
def heldBit (i : Nat) : Nat := HELD_BIT_BASE + i
/-- The delegation granted bit at position `i`. -/
def grantedBit (i : Nat) : Nat := GRANTED_BIT_BASE + i
end dcol

/-- **`gDelegSubmaskBit i`** — the delegation per-bit NON-AMP gate body `gᵢ·(1 − hᵢ)`: zero iff the
granted bit is NOT set OR the held bit IS set (`gᵢ ≤ hᵢ`). The in-row anti-amplify tooth, one bit at a
time, over the DELEGATION bit carriers. -/
def gDelegSubmaskBit (i : Nat) : EmittedExpr :=
  .mul (eCol (dcol.grantedBit i)) (eSub (.const 1) (eCol (dcol.heldBit i)))

/-- The delegation NON-AMP gates: boolean each held + granted bit, reconstruct the held mask from its
bits AND the granted mask from its bits, and the per-bit submask gate `granted ⊑ held`. No production
gate (a delegate is not a mint).

The recon gates read `prmCol dcol.GRANTED_MASK` = **column 72** and `prmCol dcol.HELD_MASK` = **column
75** — the PARAM COLUMNS, not the param indices. Column 72 is exactly the felt
`EffectVmEmitCapRoot.siteCapEdgeLeaf` hashes into the cap-edge leaf, which is what makes this leg
LOAD-BEARING rather than a free side-check: the granted bits reconstruct the very `rights` the
recomputed `cap_root` commits, so tampering that felt to dodge the submask gate breaks the recon gate
(and moves the root ⇒ `state_commit` ⇒ UNSAT). `prmCol`-wrapping here is mandatory — `gMaskRecon`
consumes a raw COLUMN (`eCol maskCol`), while `dcol.*_MASK` are param INDICES; passing an index raw is
the conflation that made these gates read effect-SELECTOR columns 4/7 (fixed 2026-07-17). -/
def capDelegNonAmpGates : List VmConstraint :=
  ((List.range MASK_BITS).map (fun i => VmConstraint.gate (gBool (dcol.heldBit i))))
    ++ ((List.range MASK_BITS).map (fun i => VmConstraint.gate (gBool (dcol.grantedBit i))))
    ++ ((List.range MASK_BITS).map (fun i => VmConstraint.gate (gDelegSubmaskBit i)))
    ++ [ VmConstraint.gate (gMaskRecon (prmCol dcol.HELD_MASK) dcol.heldBit)
       , VmConstraint.gate (gMaskRecon (prmCol dcol.GRANTED_MASK) dcol.grantedBit) ]

/-- **`capDeleg_nonAmp_in_circuit` — the per-bit non-amp tooth for the cap-graph family.** A witness
satisfying the delegation non-amp gates FORCES, for every bit `i < MASK_BITS`, the granted bit ≤ the
held bit (`gᵢ = 0 ∨ hᵢ = 1`) over `dcol.grantedBit i` / `dcol.heldBit i`.

The granted bits reconstruct `prmCol cp.RIGHTS` = col 72 (the cap-edge leaf's rights, §4D), so this
reaches the very rights the recomputed `cap_root` commits: a `rights` felt outside the held mask breaks
the recon gate. ⚠ SCOPE: the statement below quantifies over the BIT CARRIERS only, and the HELD mask
(col 75) is a free param on this flavour (§4D's RESIDUAL) — so this is not yet conferred-rights
non-amplification against an OPENED parent cap. It bounds the committed rights by a prover-chosen mask;
binding that mask is the next rung. -/
theorem capDeleg_nonAmp_in_circuit (env : VmRowEnv)
    (hcon : ∀ c ∈ capDelegNonAmpGates, c.holdsVm env false false)
    (i : Nat) (hi : i < MASK_BITS)
    (hgc : 0 ≤ env.loc (dcol.grantedBit i) ∧ env.loc (dcol.grantedBit i) < 2013265921)
    (hhc : 0 ≤ env.loc (dcol.heldBit i) ∧ env.loc (dcol.heldBit i) < 2013265921) :
    env.loc (dcol.grantedBit i) = 0 ∨ env.loc (dcol.heldBit i) = 1 := by
  have hsm : VmConstraint.gate (gDelegSubmaskBit i) ∈
      (List.range MASK_BITS).map (fun j => VmConstraint.gate (gDelegSubmaskBit j)) :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  have hmem : VmConstraint.gate (gDelegSubmaskBit i) ∈ capDelegNonAmpGates := by
    unfold capDelegNonAmpGates
    exact List.mem_append_left _ (List.mem_append_right _ hsm)
  have hg := hcon _ hmem
  -- `gᵢ·(1 − hᵢ) ≡ 0 [ZMOD p]` + primality + canonicality (`0 ≤ cell < p`, the deployed range
  -- check) force `gᵢ = 0 ∨ hᵢ = 1` exactly.
  simp only [VmConstraint.holdsVm, gDelegSubmaskBit, eSub, eCol, EmittedExpr.eval] at hg
  have hp : Prime (2013265921 : ℤ) := by
    exact_mod_cast Nat.prime_iff_prime_int.mp Dregg2.Circuit.BabyBearFriField.babyBearP_prime
  rw [Int.modEq_zero_iff_dvd] at hg
  rcases hp.dvd_mul.mp hg with h0 | h1
  · obtain ⟨k, hk⟩ := h0
    exact Or.inl (by omega)
  · obtain ⟨k, hk⟩ := h1
    exact Or.inr (by omega)

/-- **`capDeleg_rejects_amplify` — the cap-graph anti-amplify rejection (witness FALSE).** A delegation
row where granted bit `i` is SET (`= 1`) but held bit `i` is CLEAR (`= 0`) — an amplifying grant on bit
`i` (conferring a right the delegator does NOT hold) — does NOT satisfy the non-amp gates: the submask
gate `gᵢ·(1 − hᵢ) = 1·1 = 1 ≠ 0` FAILS. So the circuit rejects an over-grant at the bit level, on EVERY
cap-graph effect that carries these gates. -/
theorem capDeleg_rejects_amplify (env : VmRowEnv)
    (i : Nat) (hi : i < MASK_BITS)
    (hg : env.loc (dcol.grantedBit i) = 1) (hh : env.loc (dcol.heldBit i) = 0) :
    ¬ (∀ c ∈ capDelegNonAmpGates, c.holdsVm env false false) := by
  intro hcon
  -- the literal bit values 1/0 are canonical (`0 ≤ · < p`) by inspection.
  rcases capDeleg_nonAmp_in_circuit env hcon i hi
      (by rw [hg]; norm_num) (by rw [hh]; norm_num) with h0 | h1
  · rw [hg] at h0; exact absurd h0 (by norm_num)
  · rw [hh] at h1; exact absurd h1 (by norm_num)

/-- The delegation non-amp bit carriers are DISTINCT from the mint-flavour `§4` carriers and all
`< EFFECT_VM_WIDTH = 186` (so the Rust interpreter's bounds check accepts; aux columns past the
mint-flavour bit block, within the base layout — width-neutral). -/
theorem capDeleg_carriers_in_range :
    (∀ i, i < MASK_BITS → dcol.heldBit i < EFFECT_VM_WIDTH)
    ∧ (∀ i, i < MASK_BITS → dcol.grantedBit i < EFFECT_VM_WIDTH)
    ∧ (∀ i, i < MASK_BITS → col.GRANTED_BIT_BASE + MASK_BITS ≤ dcol.heldBit i) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    simp only [MASK_BITS] at hi
    simp only [dcol.heldBit, dcol.HELD_BIT_BASE, col.GRANTED_BIT_BASE, col.HELD_BIT_BASE, auxCol,
      AUX_BASE, STATE_AFTER_BASE, PARAM_BASE, STATE_BEFORE_BASE, aux_off.STATE_INTER3, EFFECT_VM_WIDTH,
      NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, MASK_BITS]
    omega
  · intro i hi
    simp only [MASK_BITS] at hi
    simp only [dcol.grantedBit, dcol.GRANTED_BIT_BASE, col.GRANTED_BIT_BASE, col.HELD_BIT_BASE, auxCol,
      AUX_BASE, STATE_AFTER_BASE, PARAM_BASE, STATE_BEFORE_BASE, aux_off.STATE_INTER3, EFFECT_VM_WIDTH,
      NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, MASK_BITS]
    omega
  · intro i hi
    simp only [dcol.heldBit, dcol.HELD_BIT_BASE, MASK_BITS]
    omega

/-- The delegation non-amp segment has `3·MASK_BITS + 2` gates (held-bool + granted-bool + submask + 2
recon) — non-trivial, and (unlike `§4`'s `productionGates`) carries NO production gate. -/
theorem capDelegNonAmpGates_shape :
    capDelegNonAmpGates.length = 3 * MASK_BITS + 2 := by decide

#assert_axioms capDeleg_nonAmp_in_circuit
#assert_axioms capDeleg_rejects_amplify
#assert_axioms capDeleg_carriers_in_range
#assert_axioms capDelegNonAmpGates_shape

/-! ## §5 — NON-VACUITY witnesses (concrete TRUE openings on a computable reference sponge).

The model is computable: a concrete held-set opens, a concrete production authorizes, on the same
Horner-with-length-tag toy sponge the cap-root recompute + heap use (`EffectVmEmitCapRoot.cN`). (The
soundness theorems above use the abstract CR sponge; these guards exhibit realizable witnesses.) -/

/-- The reference sponge (Horner with a length tag) — computable, injective-enough for the concrete
guards. NOT real crypto (the deployment instance is the p3 Poseidon2 sponge behind `Poseidon2SpongeCR`). -/
def cN : List ℤ → ℤ := fun xs => xs.foldl (fun acc x => acc * 1000003 + x) (xs.length : ℤ)

/-- A concrete held-set: slot 5 holds the issuer entry for asset 9 (`target = 9`, `rightsMask = 64` =
the `control`/mint bit); slot 12 holds a read-only cap on cell 3 (`rightsMask = 1`). Sorted by slot. -/
def heldDemo : HeldCaps :=
  [ (5, { target := 9, rightsMask := 64 })
  , (12, { target := 3, rightsMask := 1 }) ]

/-- `heldDemo` is sorted (5 < 12). -/
theorem heldDemo_sorted : SortedKeys heldDemo := by
  unfold heldDemo SortedKeys keys
  simp only [List.map_cons, List.map_nil]
  decide

/-- **NON-VACUITY (witness TRUE — a real opening fires).** Slot 5 of `heldDemo` OPENS to the issuer
entry under the reference sponge: the published root recomputes, sortedness holds, membership holds. So
`OpensEntry` is INHABITED, not vacuous. -/
theorem heldDemo_opens_issuer :
    OpensEntry cN (capRoot cN heldDemo) 5 { target := 9, rightsMask := 64 } heldDemo where
  sorted := heldDemo_sorted
  rootEq := rfl
  member := by unfold heldDemo Dregg2.Substrate.Heap.get; decide

/-- **NON-VACUITY (witness TRUE — PRODUCTION authorized).** A producer publishing `heldDemo`'s cap-root
can mint asset 9: slot 5 opens to the issuer entry for 9 (targets 9, carries the control bit). So
`ProductionAuthorized` is INHABITED — the constructive authority leg fires on a real held issuer cap. -/
theorem heldDemo_authorizes_mint_9 :
    ProductionAuthorized cN (capRoot cN heldDemo) 9 5 heldDemo :=
  production_of_held_issuer cN (capRoot cN heldDemo) 9 5 { target := 9, rightsMask := 64 } heldDemo
    heldDemo_sorted (by unfold heldDemo Dregg2.Substrate.Heap.get; decide) rfl
    ⟨rfl, by unfold submask CONTROL_BIT authBit; decide⟩

/-- **NON-VACUITY (witness FALSE — UNAUTHORIZED mint rejected).** The same producer CANNOT mint asset 9
by opening slot 99 (absent from `heldDemo`): `ProductionAuthorized … 99 …` is FALSE — no issuer-cap
opening, no authority. The anti-unauthorized-mint tooth fires on a concrete absent slot. -/
theorem heldDemo_no_mint_absent_slot :
    ¬ ProductionAuthorized cN (capRoot cN heldDemo) 9 99 heldDemo :=
  unauthorizedMint_rejected cN (capRoot cN heldDemo) 9 99 heldDemo (by unfold heldDemo Dregg2.Substrate.Heap.get; decide)

/-- **NON-VACUITY (witness FALSE — wrong-asset mint rejected).** Opening slot 12 (a read-only cap on
cell 3) does NOT authorize a mint of asset 9: that entry targets 3, not 9, AND lacks the control bit, so
`¬ IssuerEntry 9 …`. The asset+right binding holds on a concrete held entry. -/
theorem heldDemo_no_mint_wrong_slot :
    ¬ IssuerEntry 9 { target := 3, rightsMask := 1 } :=
  wrongAssetMint_rejected 9 3 _ (by decide) rfl

/-! ### §5D — the DELEGATION non-amp gates fire BOTH polarities (a concrete cap-graph row).

A concrete delegation row: the delegator HOLDS `{read, write}` (mask 3, bits `h₀=h₁=1`, rest 0) and
GRANTS `{read}` (mask 1, bit `g₀=1`, rest 0) — an HONEST attenuation. The held/granted bit columns
carry the genuine 8-bit decompositions; the granted recon ties to `cp.RIGHTS = 1`, the held recon to
param 7 = 3. The submask gates all pass (`g₀=1 ≤ h₀=1`, every other `gᵢ=0`). The dual witness: an
OVER-GRANT row (`g₁=1` but `h₁=0`, conferring `write` the delegator lacks) is REJECTED. -/

/-- A concrete HONEST delegation row: held mask 3 (`{read,write}`, param 7 col 75; held bits col 120 = h₀=1,
col 121 = h₁=1, cols 122..127 = 0), granted mask 1 (`{read}`, `cp.RIGHTS` param 4 col 72; granted bits
col 128 = g₀=1, cols 129..135 = 0). The literal columns ARE what `dcol`/`prmCol` reduce to (anti-drift,
checked by the `#guard`s below). Off-row columns are 0. -/
def goodDelegRow : VmRowEnv where
  loc := fun v =>
    if v = 120 then 1            -- heldBit 0  (read held)
    else if v = 121 then 1       -- heldBit 1  (write held)
    else if v = 128 then 1       -- grantedBit 0 (read granted)
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

-- The witness row's literal columns ARE the symbolic delegation carrier columns (anti-drift).
#guard dcol.heldBit 0 == 120
#guard dcol.heldBit 1 == 121
#guard dcol.grantedBit 0 == 128
#guard prmCol dcol.HELD_MASK == 75
#guard prmCol dcol.GRANTED_MASK == 72

/-- **NON-VACUITY (witness TRUE — an HONEST delegation ADMITS).** The honest attenuation row (grant
`{read}` from held `{read,write}`) satisfies EVERY delegation submask gate: each granted bit is `≤` its
held bit (`g₀=1 ≤ h₀=1`; every other `gᵢ=0`). So the in-circuit non-amp predicate is INHABITED — an
honest delegation binds its cap-root AND passes non-amp, not vacuously false. -/
theorem goodDelegRow_admits (i : Nat) (hi : i < MASK_BITS) :
    (VmConstraint.gate (gDelegSubmaskBit i)).holdsVm goodDelegRow false false := by
  simp only [MASK_BITS] at hi
  simp only [VmConstraint.holdsVm, gDelegSubmaskBit, eSub, eCol, EmittedExpr.eval]
  -- `granted_i · (1 − held_i) = 0` in ℤ (granted is 0 except bit 0, where held bit 0 = 1), so the
  -- residual is `≡ 0 [ZMOD p]` as `p ∣ 0`.
  rw [Int.modEq_zero_iff_dvd]
  interval_cases i <;>
    simp only [dcol.grantedBit, dcol.heldBit, dcol.GRANTED_BIT_BASE, dcol.HELD_BIT_BASE,
      col.GRANTED_BIT_BASE, col.HELD_BIT_BASE, auxCol, AUX_BASE, STATE_AFTER_BASE, PARAM_BASE,
      STATE_BEFORE_BASE, aux_off.STATE_INTER3, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, MASK_BITS,
      goodDelegRow] <;> norm_num

/-- A concrete OVER-GRANT delegation row: the delegator does NOT hold `write` (all held bits 0) but
GRANTS `write` (`grantedBit 1 = 1`, col 129). The amplifying grant the non-amp gate must reject. -/
def overGrantDelegRow : VmRowEnv where
  loc := fun v => if v = 129 then 1 else 0   -- grantedBit 1 (write granted) set; held bits all 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **NON-VACUITY (witness FALSE — a concrete OVER-GRANT is REJECTED).** A row conferring `write`
(`grantedBit 1 = 1`) the delegator does NOT hold (`heldBit 1 = 0`) FAILS the delegation non-amp gates:
the bit-1 submask gate `g₁·(1−h₁) = 1·1 = 1 ≠ 0`. The concrete anti-amplify UNSAT for the cap-graph
family — a delegation cannot grant beyond what it holds. -/
theorem overGrantDelegRow_rejected :
    ¬ (∀ c ∈ capDelegNonAmpGates, c.holdsVm overGrantDelegRow false false) :=
  capDeleg_rejects_amplify overGrantDelegRow 1 (by decide)
    (by show overGrantDelegRow.loc (dcol.grantedBit 1) = 1
        rw [show dcol.grantedBit 1 = 129 from by decide]; rfl)
    (by show overGrantDelegRow.loc (dcol.heldBit 1) = 0
        rw [show dcol.heldBit 1 = 121 from by decide]; rfl)

/-! ## §5 — axiom hygiene pins. -/

#guard heldDemo.length == 2
#guard CONTROL_BIT == 64
-- the demo held-set is genuinely sorted by slot (the canonical openable shape).
#guard (keys heldDemo) == [5, 12]
-- the submask gate is two-valued on the demo masks: control ⊑ issuer-mask, read ⋢ control.
#guard decide (submask CONTROL_BIT 64)
#guard decide (¬ submask CONTROL_BIT 1)
-- the delegation non-amp carriers are DISTINCT from the mint-flavour §4 carriers (no aliasing).
#guard [col.heldBit 0, col.grantedBit 0, dcol.heldBit 0, dcol.grantedBit 0].dedup.length == 4
#guard col.GRANTED_BIT_BASE + MASK_BITS == dcol.HELD_BIT_BASE
-- the delegation granted mask reads the cap-edge leaf's rights param; held rides the free param 7.
#guard dcol.GRANTED_MASK == EffectVmEmitCapRoot.cp.RIGHTS
#guard dcol.HELD_MASK == 7
#guard decide (dcol.HELD_MASK < NUM_PARAMS)

#assert_axioms capLeaf_injective
#assert_axioms capLeafList_injective
#assert_axioms heldSet_determined
#assert_axioms opensEntry_functional
#assert_axioms grant_attenuated_nonAmplifying
#assert_axioms overGrant_rejected
#assert_axioms incomparableGrant_rejected
#assert_axioms submask_self
#assert_axioms submask_of_attenuate
#assert_axioms submask_overGrant_rejected
#assert_axioms production_of_held_issuer
#assert_axioms unauthorizedMint_rejected
#assert_axioms wrongAssetMint_rejected
#assert_axioms noControlMint_rejected
#assert_axioms heldDemo_opens_issuer
#assert_axioms heldDemo_authorizes_mint_9
#assert_axioms heldDemo_no_mint_absent_slot
#assert_axioms heldDemo_no_mint_wrong_slot
#assert_axioms goodDelegRow_admits
#assert_axioms overGrantDelegRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitCapReshape
