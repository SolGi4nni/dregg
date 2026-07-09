/-
# `Dregg2.Crypto.XmVrfRefinement` — the DEPLOYED XM-VRF refines the abstract VRF; uniqueness ⇒ HashCR.

The DOWN direction for the consensus VRF, mirroring `Dregg2.Crypto.DreggPqRefinement` (which connects the
deployed `dregg-pq` signer to the abstract `SigScheme`). Here the deployed object is `crypto-xmvrf`: a
hash-based, key-updatable verifiable random function (the XM-VRF family, IACR ePrint 2026/052) whose
`(keygen, eval, verify)` this file connects to the abstract `Dregg2.Crypto.VRF`, so `SortitionGame`'s
leader-election guarantees apply to the CODE, not just to the model.

## What the Rust deploys (`crypto-xmvrf/src/{vrf,merkle,hash}.rs`)

  * KeyGen walks a forward-secure PRG chain; each epoch `t`'s output `y_t` and opening `r_t` are committed
    as a Merkle LEAF `leaf_t = H(0x01 ‖ t ‖ y_t ‖ r_t)`. The public key is the Merkle ROOT over all leaves.
  * `eval sk t = (y_t, π)` with `π = (r_t, auth_path(t))`.
  * `verify pk t y π` recomputes `leaf = H(0x01 ‖ t ‖ y ‖ r)` and folds the auth-path up to `pk.root`,
    with internal node hash `H(0x02 ‖ left ‖ right)`; it accepts iff the recomputed root equals `pk.root`
    at position `t`.
  * `update` ratchets the chain, destroying the ability to recompute past epochs (forward security).

## The keystone — uniqueness reduces to HashCR, the FLOOR (not a fresh trusted boundary)

The security-critical property for sortition is UNIQUENESS: at most one `y` verifies per `(pk, t)`. In
`crypto-xmvrf` this is bought by the Merkle CR commitment. The reduction, proved here in full:

  * `merkle_leaf_binding` — two leaves authenticating to ONE root at ONE position (same position bits)
    force the same leaf, ELSE a collision of the internal node hash. This is the "two leaves to one root"
    Merkle-binding, derived by induction from `nodeH` injectivity.
  * `nodeH`/`leafCommit` injectivity come from `HashCR` (the `Dregg2.Crypto.HermineHintMLWE.CommitReveal`
    carrier, indexed by a leaf/node `Role` mirroring the Rust `0x01`/`0x02` domain separation) plus the
    injective length-framing — exactly the `IdentityCommitment` reduction shape.
  * `xm_unique` chains them: two verifying outputs ⇒ same leaf (`merkle_leaf_binding`) ⇒ same output
    (`leaf_unique`). `distinct_outputs_break_hashcr` is the contrapositive (mirror of
    `IdentityCommitment.distinct_verifying_pairs_break_hashcr`): two distinct verifying outputs BREAK
    `HashCR`. So the ONLY irreducible object is `HashCR` — no `…Hard`, no fresh boundary.

## The X-VRF pitfall (`crypto-xmvrf/src/naive_wots.rs`) is the load-bearing tooth

A WOTS+-chain "VRF" verify accepts a whole family of `(position, sig)` pairs (the chain shift), so
`output = f(sig)` is multi-valued: `naiveChainVrf` exhibits TWO distinct outputs verifying under one key,
refuting `UniqueOutputs`. `naive_not_merkle_backed` proves the deeper point: such an accept-family verify
CANNOT be realized as a Merkle CR check under `HashCR` — the Merkle commitment is precisely what buys
uniqueness. `two_outputs_break_uniqueness` (from `VRF.lean`) is the abstract witness both feed.

## Inheritance — the deployed VRF gets the model's guarantees

`xm_vrf_refines` proves the model faithfully abstracts the API contract (mirror of
`dregg_pq_refines_sigscheme`). Then the deployed VRF inherits: UNIQUENESS (`xm_unique`, floor `HashCR`),
PROVABILITY (`xm_provability` from the honest-construction `Correct`), and PSEUDORANDOMNESS (a pass-through
of the abstract `Pseudorandom` game — its floor is the PRG, UNCHANGED, not introduced here). Hence
`SortitionGame.sortition_unique` / `sortition_fair` apply to the DEPLOYED VRF (`xm_sortition_unique`,
`xm_sortition_fair`).

Reads matched to the actual Rust: `verify_path` + `hash_node`/`hash_leaf` (the Merkle recompute and the
role-separated hashes), `Proof = (r, auth_path)`, `PublicKey = root`. The only new irreducible base is
`HashCR`; everything else is proved glue or an inherited model game.
-/
import Dregg2.Crypto.SortitionGame
import Dregg2.Crypto.HermineHintMLWE

namespace Dregg2.Crypto.XmVrfRefinement

open Dregg2.Crypto.VRF
open Dregg2.Crypto.SortitionGame
open Dregg2.Crypto.HermineHintMLWE

/-! ## PART 0 — the hash surface: a role-indexed CR hash + injective framings.

The Rust uses ONE blake3 with one-byte domain separation: `0x01` for a Merkle LEAF, `0x02` for an internal
NODE (`hash.rs`). We mirror that with a `CommitReveal Role Pre Digest` — the SAME collision-resistance
carrier `IdentityCommitment` / `HermineHintMLWE` / `RandomnessBeacon` ride — indexed by `Role`, so `HashCR`
(injectivity per index) is exactly "no leaf/node collision". The framings encode the fixed-width /
length-prefixed pre-images the Rust hashes. -/

/-- The Merkle hash role, mirroring the Rust `0x01`/`0x02` domain-separation tags: a LEAF hash
`H(0x01 ‖ t ‖ y ‖ r)` versus an internal NODE hash `H(0x02 ‖ left ‖ right)`. `HashCR` on the indexed hash
is injectivity WITHIN each role — a leaf can never collide with a node by construction. -/
inductive Role
  | leaf
  | node
  deriving DecidableEq

/-- A 3-ary injectivity, the leaf analogue of `Function.Injective2`: distinct `(epoch, output, opening)`
triples give distinct leaf pre-images (the fixed-width `epoch`/`y`/`r` fields make `frame_leaf` injective). -/
def Injective3 {A B C D : Type*} (f : A → B → C → D) : Prop :=
  ∀ a b c a' b' c', f a b c = f a' b' c' → a = a' ∧ b = b' ∧ c = c'

/-- **The XM-VRF hash surface.** A role-indexed collision-resistant hash `cr` (the `CommitReveal` carrier)
plus the two injective framings: `frameLeaf t y r` for the epoch commitment `0x01 ‖ t ‖ y ‖ r`, and
`frameNode l r` for the internal node `0x02 ‖ l ‖ r`. Everything the deployed `verify` recomputes is built
from these. -/
structure XmVrf (Epoch Output Rand Pre Digest : Type*) where
  /-- The role-indexed CR hash (`CommitReveal`, the shared `HashCR` carrier). -/
  cr : CommitReveal Role Pre Digest
  /-- The leaf pre-image framing `0x01 ‖ epoch ‖ y ‖ r` (length-framed, injective). -/
  frameLeaf : Epoch → Output → Rand → Pre
  /-- The node pre-image framing `0x02 ‖ left ‖ right` (fixed-width children, injective). -/
  frameNode : Digest → Digest → Pre

variable {Epoch Output Rand Pre Digest : Type*}

/-- **The leaf commitment** `hash_leaf(epoch, y, r) = H(Role.leaf, frameLeaf epoch y r)`. -/
def XmVrf.leafCommit (X : XmVrf Epoch Output Rand Pre Digest)
    (e : Epoch) (y : Output) (r : Rand) : Digest :=
  X.cr.H Role.leaf (X.frameLeaf e y r)

/-- **The internal node hash** `hash_node(l, r) = H(Role.node, frameNode l r)`. -/
def XmVrf.nodeH (X : XmVrf Epoch Output Rand Pre Digest) (a b : Digest) : Digest :=
  X.cr.H Role.node (X.frameNode a b)

/-! ## PART 1 — the Merkle recompute and its binding (the heart of the reduction).

`recompose nodeH leaf path` folds a leaf up an authentication path — each step carries the position bit
`b` (`b = true`: current is the RIGHT child, sibling on the left → `nodeH sib acc`; `b = false`: left child
→ `nodeH acc sib`), exactly `merkle.rs::verify_path`'s `idx & 1` branch. -/

/-- **Recompose the root from a leaf up an annotated auth-path** — the `verify_path` fold. Each step
`(b, sib)`: if `b` (current is the right child) hash `nodeH sib acc`, else `nodeH acc sib`. Mirrors
`Dregg2.Crypto.Merkle.recompose`, carrying the position bit for left/right ordering. -/
def recompose {Digest : Type*} (nodeH : Digest → Digest → Digest) :
    Digest → List (Bool × Digest) → Digest
  | acc, [] => acc
  | acc, (b, sib) :: rest => recompose nodeH (cond b (nodeH sib acc) (nodeH acc sib)) rest

/-- **`nodeH` is injective (from `HashCR` + injective node framing).** A collision `nodeH a b = nodeH c d`
is a collision of the underlying CR hash at index `Role.node`, hence `frameNode a b = frameNode c d`, hence
(injective framing) `a = c ∧ b = d`. No fresh assumption — this is `HashCR`. -/
theorem XmVrf.nodeH_injective (X : XmVrf Epoch Output Rand Pre Digest)
    (hfn : Function.Injective2 X.frameNode) (hcr : HashCR X.cr) :
    ∀ a b c d, X.nodeH a b = X.nodeH c d → a = c ∧ b = d := by
  intro a b c d h
  exact hfn (hcr Role.node (X.frameNode a b) (X.frameNode c d) h)

/-- **THE MERKLE-BINDING (two leaves to one root ⇒ one leaf).** If two leaves authenticate to the SAME
recomposed root via paths with the SAME position bits (`map Prod.fst` equal — the epoch's index bits, which
the verifier threads, not the prover), then the leaves are EQUAL. By induction: equal roots force the two
one-step-up nodes equal (IH), and `nodeH` injectivity peels the leaf out of each node. A leaf difference
would therefore exhibit a node-hash collision — the whole binding rests on `nodeH` injectivity, i.e. on
`HashCR`. This is the Lean image of `merkle.rs`'s binding property. -/
theorem merkle_leaf_binding {Digest : Type*} (nodeH : Digest → Digest → Digest)
    (hinj : ∀ a b c d, nodeH a b = nodeH c d → a = c ∧ b = d) :
    ∀ (p₁ p₂ : List (Bool × Digest)) (l₁ l₂ : Digest),
      p₁.map Prod.fst = p₂.map Prod.fst →
      recompose nodeH l₁ p₁ = recompose nodeH l₂ p₂ → l₁ = l₂ := by
  intro p₁
  induction p₁ with
  | nil =>
    intro p₂ l₁ l₂ hmap hrec
    cases p₂ with
    | nil => simpa [recompose] using hrec
    | cons hd tl => simp at hmap
  | cons hd tl ih =>
    intro p₂ l₁ l₂ hmap hrec
    cases p₂ with
    | nil => simp at hmap
    | cons hd2 tl2 =>
      obtain ⟨b, s⟩ := hd
      obtain ⟨b2, s2⟩ := hd2
      simp only [List.map_cons, List.cons.injEq] at hmap
      obtain ⟨hb, htl⟩ := hmap
      subst hb
      simp only [recompose] at hrec
      have hcomb := ih tl2 _ _ htl hrec
      cases b with
      | false =>
        simp only [cond_false] at hcomb
        exact (hinj _ _ _ _ hcomb).1
      | true =>
        simp only [cond_true] at hcomb
        exact (hinj _ _ _ _ hcomb).2

/-- **THE LEAF-BINDING (one leaf ⇒ one output).** `leafCommit e y₁ r₁ = leafCommit e y₂ r₂` is a collision
of the CR hash at index `Role.leaf`, so (injective leaf framing) `y₁ = y₂`. The last mile of uniqueness,
again bottoming out at `HashCR`. -/
theorem XmVrf.leaf_unique (X : XmVrf Epoch Output Rand Pre Digest)
    (hfl : Injective3 X.frameLeaf) (hcr : HashCR X.cr)
    (e : Epoch) (y₁ y₂ : Output) (r₁ r₂ : Rand)
    (h : X.leafCommit e y₁ r₁ = X.leafCommit e y₂ r₂) : y₁ = y₂ := by
  have hcol : X.frameLeaf e y₁ r₁ = X.frameLeaf e y₂ r₂ :=
    hcr Role.leaf (X.frameLeaf e y₁ r₁) (X.frameLeaf e y₂ r₂) h
  exact (hfl _ _ _ _ _ _ hcol).2.1

/-! ## PART 2 — the API contract, the model, and the observable `verify`.

`XmVrfApi` captures the deployed surface as function shapes only (keygen/eval/verify/update), matched to the
Rust signatures — no proof fields, exactly as `DreggPqApi` carries none. `MerkleAccept` states what the
observable `verify` computes; `IsMerkleVerify` says the API's `Bool` verify agrees with it (the observable
Rust behaviour, faithfully captured — the honest toy proves it by construction). -/

/-- The observable `crypto-xmvrf` surface: `keygen_from_seed` (→ the root PK), `eval` (→ `(y, (r, path))`),
`verify` (the fail-closed `Bool` `verify_path` check), and `update` (the forward-secure ratchet). Carries
NO proof fields — its correctness/uniqueness are theorems below, reduced to `HashCR`. -/
structure XmVrfApi (SK Epoch Output Rand Digest : Type*) where
  /-- `keygen_from_seed(msk, h).0` — the Merkle root public key. -/
  keygen : SK → Digest
  /-- `SecretKey::eval(epoch) = (y, Proof { r, path })`. -/
  eval : SK → Epoch → Output × (Rand × List (Bool × Digest))
  /-- `vrf::verify(pk, epoch, y, proof)` — the fail-closed Bool Merkle check. -/
  verify : Digest → Epoch → Output → (Rand × List (Bool × Digest)) → Bool
  /-- `SecretKey::update` — advance one epoch, destroying past-epoch secrets (forward security). -/
  update : SK → SK

variable {SK : Type*}

/-- **The observable `verify` computation** (`verify_path`): the proof's position bits equal the epoch's
index bits, and the leaf `hash_leaf(epoch, y, r)` recomposes up the path to the root. The `Prop` image of
the deployed Bool `verify`. -/
def MerkleAccept (X : XmVrf Epoch Output Rand Pre Digest) (posBits : Epoch → List Bool)
    (root : Digest) (epoch : Epoch) (y : Output) (π : Rand × List (Bool × Digest)) : Prop :=
  π.2.map Prod.fst = posBits epoch ∧
    recompose X.nodeH (X.leafCommit epoch y π.1) π.2 = root

/-- **THE OBSERVABLE-BEHAVIOUR CAPTURE.** The API's Bool `verify` is `true` exactly when the Merkle check
holds — i.e. `verify` recomputes the leaf and authenticates the path (`verify_path`). This is a faithful
description of what the Rust `verify` DOES, not a trusted floor; the honest instance proves it by
construction (`decide_eq_true_iff`). The floor is `HashCR`, stated separately. -/
def IsMerkleVerify (X : XmVrf Epoch Output Rand Pre Digest) (posBits : Epoch → List Bool)
    (api : XmVrfApi SK Epoch Output Rand Digest) : Prop :=
  ∀ pk epoch y π, api.verify pk epoch y π = true ↔ MerkleAccept X posBits pk epoch y π

/-- **The modeled VRF** — the API contract read as an abstract `Dregg2.Crypto.VRF`: PK = root (`Digest`),
input = epoch, proof = `(r, path)`, and `pkOf`/`eval`/`verify` forward to the API. Mirror of
`dreggPqSigScheme`. -/
@[reducible] def xmVrfModel (api : XmVrfApi SK Epoch Output Rand Digest) :
    VRF SK Digest Epoch Output (Rand × List (Bool × Digest)) where
  pkOf := api.keygen
  eval := api.eval
  verify := api.verify

/-! ## PART 3 — UNIQUENESS, reduced to HashCR (the keystone). -/

/-- **THE DEPLOYED XM-VRF HAS UNIQUE OUTPUTS — reduced to `HashCR`.** For any root and epoch, at most one
output verifies. Two verifying outputs give (same position bits) two leaves authenticating to one root ⇒
(`merkle_leaf_binding`, i.e. `nodeH`/`HashCR`) the SAME leaf ⇒ (`leaf_unique`, i.e. `HashCR`) the same
output. The ONLY irreducible object is `HashCR` — no `…Hard`, no fresh boundary. This is the `UniqueOutputs`
`SortitionGame` needs, now PROVED for the code's construction. -/
theorem xm_unique (X : XmVrf Epoch Output Rand Pre Digest) (posBits : Epoch → List Bool)
    (hfl : Injective3 X.frameLeaf) (hfn : Function.Injective2 X.frameNode) (hcr : HashCR X.cr)
    (api : XmVrfApi SK Epoch Output Rand Digest) (hv : IsMerkleVerify X posBits api) :
    UniqueOutputs (xmVrfModel api) := by
  rintro pk x y₁ y₂ ⟨π₁, h1⟩ ⟨π₂, h2⟩
  obtain ⟨hpos1, hrec1⟩ := (hv pk x y₁ π₁).mp h1
  obtain ⟨hpos2, hrec2⟩ := (hv pk x y₂ π₂).mp h2
  have hmap : π₁.2.map Prod.fst = π₂.2.map Prod.fst := hpos1.trans hpos2.symm
  have hrec : recompose X.nodeH (X.leafCommit x y₁ π₁.1) π₁.2
            = recompose X.nodeH (X.leafCommit x y₂ π₂.1) π₂.2 := hrec1.trans hrec2.symm
  have hleaf := merkle_leaf_binding X.nodeH (X.nodeH_injective hfn hcr) π₁.2 π₂.2 _ _ hmap hrec
  exact X.leaf_unique hfl hcr x y₁ y₂ π₁.1 π₂.1 hleaf

/-- **THE REDUCTION — two distinct verifying outputs BREAK `HashCR`** (mirror of
`IdentityCommitment.distinct_verifying_pairs_break_hashcr`). The contrapositive of `xm_unique`: an
equivocating VRF output at a fixed `(pk, epoch)` is, definitionally, a Merkle/hash collision. This grounds
the whole XM-VRF uniqueness in the ONE standard carrier `HashCR`, verbatim from the tree. -/
theorem distinct_outputs_break_hashcr (X : XmVrf Epoch Output Rand Pre Digest)
    (posBits : Epoch → List Bool)
    (hfl : Injective3 X.frameLeaf) (hfn : Function.Injective2 X.frameNode)
    (api : XmVrfApi SK Epoch Output Rand Digest) (hv : IsMerkleVerify X posBits api)
    (pk : Digest) (x : Epoch) (y₁ y₂ : Output) (π₁ π₂ : Rand × List (Bool × Digest))
    (hne : y₁ ≠ y₂)
    (h1 : (xmVrfModel api).verify pk x y₁ π₁ = true)
    (h2 : (xmVrfModel api).verify pk x y₂ π₂ = true) :
    ¬ HashCR X.cr :=
  fun hcr => hne (xm_unique X posBits hfl hfn hcr api hv pk x y₁ y₂ ⟨π₁, h1⟩ ⟨π₂, h2⟩)

/-! ## PART 4 — the refinement relation and the inheritance payoff. -/

/-- **THE REFINEMENT RELATION** (mirror of `DreggPqRefinement.Refines`). The model `V` faithfully abstracts
the API contract: keygen, eval, and verify all agree pointwise. A model that mis-reads any clause does NOT
refine. -/
def Refines (api : XmVrfApi SK Epoch Output Rand Digest)
    (V : VRF SK Digest Epoch Output (Rand × List (Bool × Digest))) : Prop :=
  (∀ sk, V.pkOf sk = api.keygen sk) ∧
  (∀ sk x, V.eval sk x = api.eval sk x) ∧
  (∀ pk x y π, V.verify pk x y π = api.verify pk x y π)

/-- **THE REFINEMENT HOLDS.** `xmVrfModel api` is a faithful abstraction of its API contract — each clause
is definitional (the model is BUILT from the contract). The beachhead: the deployed `crypto-xmvrf` surface
and the proved `VRF` model are one connected object. Mirror of `dregg_pq_refines_sigscheme`. -/
theorem xm_vrf_refines (api : XmVrfApi SK Epoch Output Rand Digest) : Refines api (xmVrfModel api) :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- **PROVABILITY INHERITED.** Given the honest-construction correctness `Correct (xmVrfModel api)` (the
honest keygen/eval consistency — a structural property of the honest tree, witnessed concretely below), an
honestly-evaluated `(y, π)` verifies. Directly `VRF.provability`. -/
theorem xm_provability (api : XmVrfApi SK Epoch Output Rand Digest)
    (hc : Correct (xmVrfModel api)) (sk : SK) (x : Epoch) (y : Output)
    (π : Rand × List (Bool × Digest)) (h : (xmVrfModel api).eval sk x = (y, π)) :
    (xmVrfModel api).verify ((xmVrfModel api).pkOf sk) x y π = true :=
  provability (xmVrfModel api) hc sk x y π h

/-- **SORTITION UNIQUENESS, ON THE DEPLOYED VRF.** Two verifying election claims for one `(pk, epoch)`
present the SAME output — a validator cannot double-claim a committee seat. `SortitionGame.sortition_unique`
applied to the deployed model, its `UniqueOutputs` premise DISCHARGED by `xm_unique` (floor `HashCR`). -/
theorem xm_sortition_unique [LinearOrder Output] (X : XmVrf Epoch Output Rand Pre Digest)
    (posBits : Epoch → List Bool)
    (hfl : Injective3 X.frameLeaf) (hfn : Function.Injective2 X.frameNode) (hcr : HashCR X.cr)
    (api : XmVrfApi SK Epoch Output Rand Digest) (hv : IsMerkleVerify X posBits api)
    (pk : Digest) (x : Epoch) (thr : Output) (y y' : Output) (π π' : Rand × List (Bool × Digest))
    (h : ElectionProof (xmVrfModel api) pk x thr y π)
    (h' : ElectionProof (xmVrfModel api) pk x thr y' π') : y = y' :=
  sortition_unique (xmVrfModel api) (xm_unique X posBits hfl hfn hcr api hv) pk x thr y y' π π' h h'

/-- **SORTITION FAIRNESS, ON THE DEPLOYED VRF.** Under the abstract `Pseudorandom` game (a PASS-THROUGH of
the model's own assumption — its floor is the PRG, unchanged, not introduced by this refinement), the real
output's election bit matches any uniform draw's: the honest validator is elected with exactly the base-rate
density. `SortitionGame.sortition_fair` on the deployed model. -/
theorem xm_sortition_fair [LinearOrder Output] (api : XmVrfApi SK Epoch Output Rand Digest)
    (hpr : Pseudorandom (xmVrfModel api)) (sk : SK) (x : Epoch) (thr u : Output) :
    elected (xmVrfModel api) sk x thr = decide (u < thr) :=
  sortition_fair (xmVrfModel api) hpr sk x thr u

/-! ## Teeth — an honest instance (respecting), the X-VRF pitfall (violating), and refinement teeth.

The concrete surface over `List ℕ` digests (a single-epoch `Unit` height-1 tree isolates the property):
`H(role, p) = tag(role) :: p` (injective per role ⇒ `HashCR`), `frameLeaf () y r = [y, r]`,
`frameNode a b = a.length :: (a ++ b)` (length-framed ⇒ injective). Then:

(a) `goodApi` — honest `eval` verifies, uniqueness HOLDS (`goodApi_unique`, via `xm_unique`), a forged
    output / wrong position is REJECTED, and `Correct` holds so provability fires.
(b) `naiveChainVrf` — the WOTS+ chain-shift: TWO distinct outputs verify under one key, refuting
    `UniqueOutputs`. `naive_not_merkle_backed` shows such an accept-family verify CANNOT be a Merkle CR
    check under `HashCR` — the load-bearing tooth that the Merkle commitment buys uniqueness.
(c) `Refines` has teeth — an accept-all model does NOT refine the honest `goodApi`. -/

section Teeth

/-! ### (a) The honest, correct, unique instance. -/

/-- Role → domain tag (`0x01` leaf / `0x02` node), here `0`/`1`. -/
def roleTag : Role → ℕ
  | Role.leaf => 0
  | Role.node => 1

/-- The concrete role-indexed CR hash `H(role, p) = tag(role) :: p` — injective per role, so `HashCR`. -/
def goodCR : CommitReveal Role (List ℕ) (List ℕ) := ⟨fun role p => roleTag role :: p⟩

/-- The concrete XM-VRF surface over `List ℕ`: leaf framing `[y, r]`, node framing `len(a) ‖ a ‖ b`. -/
def goodX : XmVrf Unit ℕ ℕ (List ℕ) (List ℕ) where
  cr := goodCR
  frameLeaf := fun _ y r => [y, r]
  frameNode := fun a b => a.length :: (a ++ b)

/-- `H(role, ·)` is injective — `HashCR` for the concrete hash. -/
theorem goodX_hashcr : HashCR goodX.cr := by
  intro i w w' h
  injection h

/-- The leaf framing `[y, r]` is 3-injective (epoch is `Unit`). -/
theorem goodX_frameLeaf_inj : Injective3 goodX.frameLeaf := by
  intro a b c a' b' c' h
  injection h with hb h'
  injection h' with hc _
  exact ⟨Subsingleton.elim a a', hb, hc⟩

/-- The node framing `len(a) ‖ a ‖ b` is 2-injective (length prefix disambiguates the split). -/
theorem goodX_frameNode_inj : Function.Injective2 goodX.frameNode := by
  intro a b c d h
  injection h with hlen hcat
  exact List.append_inj hcat hlen

/-- Epoch-0 position bits for the height-1 tree: leaf 0 is the LEFT child. -/
def toyPos : Unit → List Bool := fun _ => [false]

/-- Leaf 0 of the honest tree: `hash_leaf((), 7, 3)`. -/
def L0 : List ℕ := goodX.leafCommit () 7 3
/-- Leaf 1 of the honest tree: `hash_leaf((), 9, 4)`. -/
def L1 : List ℕ := goodX.leafCommit () 9 4
/-- The honest root: `hash_node(L0, L1)` — the public key. -/
def toyRoot : List ℕ := goodX.nodeH L0 L1

/-- The honest `crypto-xmvrf` API instance: keygen = root, eval serves epoch 0 with proof `(3, [(false, L1)])`,
verify = the fail-closed Merkle check (`decide`). -/
def goodApi : XmVrfApi Unit Unit ℕ ℕ (List ℕ) where
  keygen _ := toyRoot
  eval _ _ := (7, (3, [(false, L1)]))
  verify pk e y π :=
    decide (π.2.map Prod.fst = toyPos e ∧
      recompose goodX.nodeH (goodX.leafCommit e y π.1) π.2 = pk)
  update _ := ()

/-- `goodApi.verify` IS the Merkle check — `IsMerkleVerify` holds by `decide_eq_true_iff`. -/
theorem goodApi_isMerkle : IsMerkleVerify goodX toyPos goodApi :=
  fun _ _ _ _ => decide_eq_true_iff

/-- **UNIQUENESS FIRES on the honest instance** — via `xm_unique`, floor `HashCR`. Non-vacuous. -/
theorem goodApi_unique : UniqueOutputs (xmVrfModel goodApi) :=
  xm_unique goodX toyPos goodX_frameLeaf_inj goodX_frameNode_inj goodX_hashcr goodApi goodApi_isMerkle

/-- **CORRECTNESS of the honest construction** — every honestly-evaluated pair verifies (the honest tree's
auth-path recomposes to the root). Witnesses the `xm_provability` premise. -/
theorem goodApi_correct : Correct (xmVrfModel goodApi) := by
  rintro ⟨⟩ ⟨⟩; decide

/-- Provability THROUGH the abstract theorem: the honest `(7, (3, [(false, L1)]))` verifies. -/
example :
    (xmVrfModel goodApi).verify ((xmVrfModel goodApi).pkOf ()) () 7 (3, [(false, L1)]) = true :=
  xm_provability goodApi goodApi_correct () () 7 (3, [(false, L1)]) rfl

-- The honest output VERIFIES (round-trip on concrete data).
#guard goodApi.verify toyRoot () 7 (3, [(false, L1)]) = true
-- A FORGED output (`8 ≠ 7`) is REJECTED — uniqueness in action (verify is not always true).
#guard goodApi.verify toyRoot () 8 (3, [(false, L1)]) = false
-- A WRONG position bit (`true` vs the epoch's `false`) is REJECTED — the index is threaded by the verifier.
#guard goodApi.verify toyRoot () 7 (3, [(true, L1)]) = false

/-! ### (b) The X-VRF pitfall — the WOTS+ chain shift violates uniqueness, and is NOT Merkle-backed. -/

/-- The naive WOTS+-chain "VRF" (`naive_wots.rs`), over `ℕ` with `chain n x = x + n`, length `L = 4`. The
proof is `(position b, sig)`; `verify` accepts iff `sig + (L - b) = pk ∧ y = sig` — i.e. the chain reaches
`pk` from the claimed position. UNSOUND on purpose: the verifier accepts the prover-supplied position, the
structural hole the chain shift drives through. -/
def naiveChainVrf : VRF Unit ℕ Unit ℕ (ℕ × ℕ) where
  pkOf _ := 4
  eval _ _ := (1, (1, 1))
  verify pk _ y p := decide (p.2 + (4 - p.1) = pk ∧ y = p.2)

/-- **THE X-VRF UNIQUENESS BREAK.** Under one public key `pk = 4`, the chain shift yields TWO distinct valid
outputs: `(b = 1, sig = 1)` and `(b = 2, sig = 2)` both verify, with outputs `1 ≠ 2`. `UniqueOutputs` is
FALSE — exactly the "Breaking X-VRF" (FC24) failure `two_outputs_break_uniqueness` witnesses. -/
theorem naiveChainVrf_not_unique : ¬ UniqueOutputs naiveChainVrf :=
  two_outputs_break_uniqueness naiveChainVrf 4 () 1 2 (1, 1) (2, 2) (by decide) (by decide) (by decide)

-- The chain shift: position 1 → output 1 verifies, AND position 2 → output 2 ALSO verifies (one pk).
#guard naiveChainVrf.verify 4 () 1 (1, 1) = true
#guard naiveChainVrf.verify 4 () 2 (2, 2) = true

/-- A naive API in the XM-VRF proof-type whose `verify` accepts ANY output (the limit of the chain
accepting any position) — NO Merkle CR commitment binds the output. -/
def naiveApi : XmVrfApi Unit Unit ℕ ℕ (List ℕ) where
  keygen _ := []
  eval _ _ := (0, (0, []))
  verify _ _ _ _ := true
  update _ := ()

/-- The accept-all naive VRF has NON-unique outputs — two distinct outputs verify. -/
theorem naiveApi_not_unique : ¬ UniqueOutputs (xmVrfModel naiveApi) :=
  two_outputs_break_uniqueness (xmVrfModel naiveApi) [] () 0 1 (0, []) (0, [])
    (by decide) rfl rfl

/-- **THE LOAD-BEARING TOOTH — the naive construction CANNOT be Merkle-backed under `HashCR`.** If the
accept-family `naiveApi.verify` WERE a Merkle CR check (`IsMerkleVerify`) over the honest hash surface,
`xm_unique` would force `UniqueOutputs` — contradicting `naiveApi_not_unique`. So the Merkle commitment is
exactly what buys uniqueness: a WOTS+-style chain (no CR commitment to the output) provably cannot satisfy
the deployed `verify`'s contract without collapsing to a collision. -/
theorem naive_not_merkle_backed (h : IsMerkleVerify goodX toyPos naiveApi) : False :=
  naiveApi_not_unique
    (xm_unique goodX toyPos goodX_frameLeaf_inj goodX_frameNode_inj goodX_hashcr naiveApi h)

/-! ### (c) `Refines` has teeth — an accept-all model does not refine the honest API. -/

/-- An UNFAITHFUL model whose `verify` accepts everything — it is a `VRF`, but does NOT abstract `goodApi`
(which fail-closes on forged outputs). -/
def badRefModel : VRF Unit (List ℕ) Unit ℕ (ℕ × List (Bool × List ℕ)) where
  pkOf := goodApi.keygen
  eval := goodApi.eval
  verify _ _ _ _ := true

/-- **REFINEMENT TEETH.** `badRefModel` does NOT refine `goodApi`: at the forged point its accept-all verify
(`true`) disagrees with `goodApi`'s fail-closed verify (`false`). So `Refines` genuinely rejects a wrong
abstraction — not vacuously true. -/
theorem badRefModel_not_refines : ¬ Refines goodApi badRefModel :=
  fun ⟨_, _, hv⟩ => absurd (hv toyRoot () 8 (3, [(false, L1)])) (by decide)

end Teeth

#assert_all_clean [
  merkle_leaf_binding,
  XmVrf.nodeH_injective,
  XmVrf.leaf_unique,
  xm_unique,
  distinct_outputs_break_hashcr,
  xm_vrf_refines,
  xm_provability,
  xm_sortition_unique,
  xm_sortition_fair,
  goodX_hashcr,
  goodX_frameLeaf_inj,
  goodX_frameNode_inj,
  goodApi_isMerkle,
  goodApi_unique,
  goodApi_correct,
  naiveChainVrf_not_unique,
  naiveApi_not_unique,
  naive_not_merkle_backed,
  badRefModel_not_refines
]

end Dregg2.Crypto.XmVrfRefinement
