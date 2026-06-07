/-
# Dregg2.Authority.BiscuitGraph — the biscuit public-key delegation chain (offline attenuation).

Track F (handoff §4). `Authority/CDT.lean` already models the GENERIC delegation order — a
content-addressed `(child → parent)` DAG with the keystone `path_attenuates` ("authority never grows
down a derivation chain"), and it even notes "CDT ≡ strand-log ≡ biscuit-graph". What CDT *abstracts
away* is the mechanism a real **biscuit** token uses to delegate: a **public-key signature chain**.

This module supplies exactly that missing dimension. A biscuit is a chain of **blocks**; each block
carries the rights it confers plus a verification key `vkey`, and is signed so that block `n+1` verifies
under block `n`'s `vkey` (the root block verifies under the root-authority key). Crucially this enables
**OFFLINE ATTENUATION**: anyone holding a biscuit can append a more-restricted block and sign it with the
current tail key — no contact with the issuer — and the whole chain still verifies under the root key.

Two faces, both proved:
- the LEAN LAW (mirroring `CDT.path_attenuates`): along a well-formed chain, authority only SHRINKS
  (`biscuit_narrows`: the leaf block confers ⊆ the root block) — attenuation is structural.
- the §8 SIGNATURE carrier: signature verification is an opaque `SigChecker` oracle (the real one =
  `Crypto.PortalFloor.SignatureKernel`, ed25519); its UNFORGEABILITY is the §8 obligation, never a Lean
  law. The Lean law assumes only that the chain's signatures *verify*, exactly as CDT assumes the
  content-address *resolves*.

Teeth (non-vacuous): an **amplifying** block (claims a right its parent lacks) is rejected; a **forged**
block (signature does not verify under the parent's key) is rejected; a forged root is rejected.

Pure, computable, `#eval`-able.
-/
import Dregg2.Authority.Positional
import Dregg2.Tactics
import Mathlib.Data.Finset.Basic

namespace Dregg2.Authority.Biscuit

open Dregg2.Authority

/-! ## Opaque crypto ids (the §8 surface) + the rights lattice. -/

/-- A public (verification) key — opaque (`Nat` for `#eval`); no Lean theorem uses any property of it.
The real key is ed25519 (`Crypto.PortalFloor.SignatureKernel`). -/
abbrev PubKey := Nat

/-- A signature — opaque. Its unforgeability is the §8 `SignatureKernel` obligation, never a Lean law. -/
abbrev Sig := Nat

/-- The rights a block confers — the authority lattice (`Authority.Auth`, ordered by ⊆), same carrier as
`CDT.Rights`. Attenuation narrows along this order. -/
abbrev Rights := Finset Auth

/-! ## The block + the signature oracle. -/

/-- **A biscuit `Block`.** `authority` = the rights it confers (must be ⊆ its parent's — attenuation);
`vkey` = the verification key under which the NEXT (more-delegated) block's signature is checked — this
is what makes OFFLINE delegation possible; `sig` = this block's signature, verified under its PARENT's
`vkey` (the root block: under the root-authority key). -/
structure Block where
  /-- The rights this block confers (⊆ its parent's). -/
  authority : Rights
  /-- The key under which the next block down the chain is verified. -/
  vkey : PubKey
  /-- This block's signature (checked under the parent's `vkey`; the root's under the root key). -/
  sig : Sig
  deriving DecidableEq

/-- **`SigChecker`** — the §8 signature-verification oracle: "does block `b`'s signature correctly sign
`b` under key `k`?" An opaque `PubKey → Block → Bool` (the real one is the ed25519
`SignatureKernel.verify`). UNFORGEABILITY — that no adversary lacking the secret for `k` can produce a
`b` with `SigChecker k b = true` — is the §8 obligation; the Lean law below only ever READS this oracle,
exactly as `CDT` reads its content-address `lookup`. -/
abbrev SigChecker := PubKey → Block → Bool

/-- **`attenuates child parent`** — the edge invariant (the ONE rule, lifted from `CDT.attenuates`): a
child block confers no more authority than its parent. -/
def attenuates (child parent : Block) : Prop := child.authority ⊆ parent.authority

instance (child parent : Block) : Decidable (attenuates child parent) := by
  unfold attenuates; exact inferInstance

/-! ## Well-formedness — the signed, narrowing chain (newest-first). -/

/-- **`WellFormed sigOk rk blocks`** — `blocks` is a valid biscuit chain under root key `rk`, listed
NEWEST-FIRST (head = the most-delegated leaf, last = the root). Inductively:
  * `[]` — the empty biscuit (vacuously well-formed);
  * `[root]` — the root block, whose signature verifies under the root-authority key `rk`;
  * `b :: prev :: rest` — `b` (newer) verifies under `prev`'s key (`sigOk prev.vkey b`) AND attenuates
    `prev`'s authority, and `prev :: rest` is itself well-formed.
So a valid biscuit is a signature chain that ALSO narrows authority at every step — the two biscuit
guarantees, jointly. -/
def WellFormed (sigOk : SigChecker) (rk : PubKey) : List Block → Prop
  | []              => True
  | [root]          => sigOk rk root = true
  | b :: prev :: rest =>
      sigOk prev.vkey b = true ∧ attenuates b prev ∧ WellFormed sigOk rk (prev :: rest)

/-! ## The keystone — authority only shrinks down a well-formed biscuit (mirrors `CDT.path_attenuates`). -/

/-- **`biscuit_narrows` (KEYSTONE)** — in a well-formed biscuit, the leaf block (head) confers no more
authority than the root block (last): `leaf.authority ⊆ root.authority`. The public-key analogue of
`CDT.path_attenuates`: offline attenuation can only RESTRICT — a holder appending signed blocks can never
grant themselves a right the issuer withheld. Proved by induction on the chain, chaining the per-edge
attenuation through transitivity of ⊆. -/
theorem biscuit_narrows {sigOk : SigChecker} {rk : PubKey} :
    ∀ {blocks : List Block}, WellFormed sigOk rk blocks →
      ∀ {leaf root : Block}, blocks.head? = some leaf → blocks.getLast? = some root →
        leaf.authority ⊆ root.authority := by
  intro blocks
  induction blocks with
  | nil => intro _ leaf root hh _; simp at hh
  | cons b tl ih =>
    intro wf leaf root hh hl
    simp only [List.head?_cons, Option.some.injEq] at hh; subst hh
    cases tl with
    | nil =>
      -- single block: it is both leaf and root.
      simp only [List.getLast?_singleton, Option.some.injEq] at hl; subst hl
      exact Finset.Subset.refl _
    | cons prev rest =>
      -- b :: prev :: rest — `wf` reduces to the three-part conjunction.
      obtain ⟨_hsig, hatt, wfrest⟩ : sigOk prev.vkey b = true ∧ attenuates b prev ∧
          WellFormed sigOk rk (prev :: rest) := wf
      rw [List.getLast?_cons_cons] at hl
      exact Finset.Subset.trans hatt (ih wfrest (by rfl) hl)

/-! ## Teeth — amplifying and forged blocks are rejected (the invariant is not vacuous). -/

/-- **`amplifying_block_rejected`** — a block that claims a right its parent lacks (`¬ attenuates b
prev`) makes the chain ill-formed. Offline delegation cannot AMPLIFY authority. -/
theorem amplifying_block_rejected (sigOk : SigChecker) (rk : PubKey)
    {b prev : Block} {rest : List Block} (hamp : ¬ attenuates b prev) :
    ¬ WellFormed sigOk rk (b :: prev :: rest) := fun wf => hamp wf.2.1

/-- **`forged_block_rejected`** — a block whose signature does NOT verify under its parent's key
(`sigOk prev.vkey b = false`) makes the chain ill-formed. With the §8 unforgeability of `sigOk`, this is
"you cannot splice in a delegation you weren't given the key to sign" — the teeth the signature carrier
provides over a bare content-address chain. -/
theorem forged_block_rejected (sigOk : SigChecker) (rk : PubKey)
    {b prev : Block} {rest : List Block} (hforge : sigOk prev.vkey b = false) :
    ¬ WellFormed sigOk rk (b :: prev :: rest) := by
  intro wf; rw [wf.1] at hforge; exact absurd hforge (by simp)

/-- **`forged_root_rejected`** — a root block whose signature does not verify under the root-authority
key is rejected: the chain must bottom out in a genuinely root-signed block. -/
theorem forged_root_rejected (sigOk : SigChecker) (rk : PubKey) {root : Block}
    (hforge : sigOk rk root = false) : ¬ WellFormed sigOk rk [root] := by
  intro wf; rw [wf] at hforge; exact absurd hforge (by simp)

/-! ## `#eval`/`example` — a concrete root → mid → leaf biscuit, narrowing, with signature teeth.

Toy oracle: a block is "correctly signed under `k`" iff its `sig` field equals `k` (the real oracle is
ed25519). The root is signed under `rootKey`; each block down the chain is signed under its parent's
`vkey`. Authority narrows read/write/grant → read/write → read. -/

/-- The toy signature oracle: `sig == k` (stands in for ed25519 `verify`). -/
def demoSig : SigChecker := fun k b => b.sig == k

/-- The root-authority key. -/
def rootKey : PubKey := 100

/-- Root block: full rights, signed under `rootKey`, hands key `7` to its child. -/
def rootBlock : Block := { authority := {Auth.read, Auth.write, Auth.grant}, vkey := 7, sig := rootKey }
/-- Mid block: drops `grant`, signed under the root's key `7`, hands key `8` down. -/
def midBlock : Block := { authority := {Auth.read, Auth.write}, vkey := 8, sig := 7 }
/-- Leaf block: drops `write` (read-only), signed under the mid's key `8`. -/
def leafBlock : Block := { authority := {Auth.read}, vkey := 9, sig := 8 }

/-- A well-formed biscuit (newest-first): `leaf ← mid ← root`, signed at every step and narrowing. -/
def goodBiscuit : List Block := [leafBlock, midBlock, rootBlock]

/-- **`goodBiscuit_wellFormed`** — the chain verifies AND narrows at every step: signatures
(`8`,`7`,`rootKey`) check under the parent keys, and read ⊆ read/write ⊆ read/write/grant. -/
theorem goodBiscuit_wellFormed : WellFormed demoSig rootKey goodBiscuit :=
  ⟨by decide, by decide, by decide, by decide, (by decide : demoSig rootKey rootBlock = true)⟩

/-- **`goodBiscuit_keystone`** — the keystone on the concrete biscuit: the read-only leaf confers ⊆ the
full-rights root. Offline attenuation only restricted. -/
theorem goodBiscuit_keystone : leafBlock.authority ⊆ rootBlock.authority :=
  biscuit_narrows goodBiscuit_wellFormed (by rfl) (by rfl)

/-- A FORGED leaf: signature `999` does not match the mid's key `8` — rejected. -/
def forgedLeaf : Block := { authority := {Auth.read}, vkey := 9, sig := 999 }
/-- **`forged_rejected`** — splicing a block you can't sign for the parent key is rejected. -/
theorem forged_rejected : ¬ WellFormed demoSig rootKey [forgedLeaf, midBlock, rootBlock] :=
  forged_block_rejected demoSig rootKey (by decide)

/-- An AMPLIFYING leaf: claims `grant`, which the mid block dropped — rejected. -/
def amplifyLeaf : Block := { authority := {Auth.read, Auth.grant}, vkey := 9, sig := 8 }
/-- **`amplify_rejected`** — offline delegation cannot grab a right the parent lacks. -/
theorem amplify_rejected : ¬ WellFormed demoSig rootKey [amplifyLeaf, midBlock, rootBlock] :=
  amplifying_block_rejected demoSig rootKey (by decide)

#guard decide (attenuates leafBlock midBlock)               -- read ⊆ read/write
#guard demoSig midBlock.vkey leafBlock                      -- leaf.sig 8 == mid.vkey 8
#guard demoSig midBlock.vkey forgedLeaf == false            -- 999 ≠ 8 — forged
#guard decide (attenuates amplifyLeaf midBlock) == false    -- grant ∉ mid's rights — amplifies
#guard decide (leafBlock.authority ⊆ rootBlock.authority)   -- the keystone, computed

/-! ### Axiom hygiene. -/

#assert_axioms biscuit_narrows
#assert_axioms amplifying_block_rejected
#assert_axioms forged_block_rejected
#assert_axioms goodBiscuit_keystone

end Dregg2.Authority.Biscuit
