/-
# Dregg2.CryptoKernel — the portal between Lean semantics and the Rust world (§8 boundary).

The dregg2 semantics are parametric over a `CryptoKernel`: an interface of the cryptographic
operations (hash, verify, commit, nullifier) bundled with the algebraic laws Lean proofs rely
on. Operation types (`Digest`, `Proof`) and implementations are uninterpreted in Lean —
crypto-soundness is assumed as interface laws (obligations the Rust impl + circuits discharge,
never proved in Lean).

Two realizations of the same interface:
  * Proving — abstract `[CryptoKernel Digest Proof]`; every theorem holds for any lawful impl.
  * Running — Rust supplies concrete types + impls (Poseidon/Pedersen/WHIR-verify); the
    compiled Lean calls them via FFI, which is a lawful instance.

This module is the portal; everything cryptographic in the metatheory routes through it.
(Network/clock/randomness for consensus are a sibling `World` oracle.)
-/
-- Runtime-import discipline (FFI closure trim): `CryptoKernel` is on the compiled FFI path
-- (`FFI → FullForestAuth → CryptoKernel`). It uses only `ring` (`commit_hom`) plus
-- `exact_mod_cast` (`refHash_inj`, which lives in Lean core via `import Lean`/`Dregg2.Tactics`),
-- so we import the single minimal tactic module `Mathlib.Tactic.Ring` rather than the whole
-- `Mathlib.Tactic` blob — the latter drags the entire mathlib tactic+CategoryTheory framework
-- (≈6900 modules) into the executor's `initialize_` closure (every imported module runs an
-- `initialize_` at boot, so DCE cannot strip it; the import GRAPH is the cause of the 287MB archive).
import Mathlib.Tactic.Ring
import Mathlib.Logic.Encodable.Basic
import Mathlib.Logic.Equiv.List   -- `Encodable (List ℕ)` for `refHash` (was transitive via `Mathlib.Tactic`)
import Dregg2.Laws
import Dregg2.Authority.Positional

namespace Dregg2.Crypto

open Dregg2.Laws Dregg2.Authority

/-- **The CryptoKernel interface.** `Digest` (hashes / commitments / Merkle roots) and
`Proof` (ZK proofs / witnesses) are uninterpreted; the operations are opaque; the fields
ending in a law are the obligations the Rust impl + circuits must satisfy (assumed, never
proved, in Lean — `dregg2 §8`). `Digest` is an `AddCommGroup` because commitments compose
(Pedersen). -/
class CryptoKernel (Digest : Type) (Proof : Type) [AddCommGroup Digest] where
  /-- Collision-resistant hash (Poseidon/BLAKE3): Merkle roots, turn-ids, chainlinks. -/
  hash : List Nat → Digest
  /-- **The Verify oracle (`dregg2 §8`).** Does `proof` discharge the statement committed
  by `stmt`? An opaque `Bool`; its soundness/extractability is the CIRCUIT obligation,
  NEVER a Lean law — Lean treats it as a decidable oracle (the verify/find seam). -/
  verify : Digest → Proof → Bool
  /-- Pedersen commitment `commit value blinding` (hiding + additively homomorphic). -/
  commit : Int → Int → Digest
  /-- Deterministic per-note nullifier (Zcash): the anti-double-spend tag. -/
  nullifier : Digest → Digest
  /-- **LAW — homomorphic commitment** (value-tier conservation over *hidden* amounts):
  the obligation the Pedersen impl + circuit satisfy. This is the one grounded
  ALGEBRAIC law (the metatheory uses it; Pedersen satisfies it exactly). -/
  commit_hom : ∀ v w r s, commit (v + w) (r + s) = commit v r + commit w s
  /-- **CARRIER — collision-resistance of the hash** (`Prop`, the CORRECT KIND of
  assumption). The previous `hash_inj : Function.Injective hash` was an *idealized
  INJECTIVITY* — but real Poseidon2 is only collision-RESISTANT, not injective: a mismatch
  of KIND, not strength. So this is a `Prop` carrier — "no PPT adversary finds a collision"
  — the crypto layer discharges, NEVER a Lean law. (The fully-split form
  lives in `Crypto/Primitives.lean::CryptoPrimitives.collisionHard`.) -/
  collisionHard : Prop

variable {Digest Proof : Type} [AddCommGroup Digest]

/-! ## The portal IS the verify/find seam: a CryptoKernel instantiates `Laws.Verifiable`. -/

/-- **A CryptoKernel induces the abstract verify/find seam** (`Laws.Verifiable`): the
predicate is a statement `Digest`, the witness is a `Proof`, and `Verify` is the kernel's
`verify`. This is how the §8 oracle is *instantiated* — the portal IS the `Verify`. -/
instance verifiableOfCryptoKernel [CryptoKernel Digest Proof] :
    Verifiable Digest Proof where
  Verify stmt proof := CryptoKernel.verify stmt proof

/-- **`Discharged` over a CryptoKernel is exactly `verify = true`** (definitional). -/
theorem discharged_iff_verify [CryptoKernel Digest Proof] (stmt : Digest) (proof : Proof) :
    Discharged stmt proof ↔ CryptoKernel.verify stmt proof = true :=
  Iff.rfl

/-! ## Closing the cross-vat integrity bridge via the portal. -/

/-- **The cross-vat integrity bridge, CLOSED via the portal.** A non-owner
(cross-vat) change is admissible per `Authority.Integrity` exactly when the actor presents
a `Proof` that the CryptoKernel `verify`s against the change's admissibility statement
`p ko ko'`. This is the `Integrity.cross` case with the **CryptoKernel proof as the
discharging witness** — resolving the open seam the kernel's cap-layer left (the cap's
authorization across a vat boundary IS a `verify`). -/
theorem cross_vat_via_verify [CryptoKernel Digest Proof]
    (owner : Label) (subjects : List Label) {KO : Type}
    (p : KO → KO → Digest) (ko ko' : KO) (proof : Proof)
    (h : CryptoKernel.verify (p ko ko') proof = true) :
    Integrity Proof owner subjects p ko ko' :=
  Integrity.cross proof h

/-- **Intra-vat owner change** stays admissible with no proof needed (l4v `troa_lrefl`) —
the portal is only consulted across a boundary. -/
theorem intra_vat [CryptoKernel Digest Proof]
    (owner : Label) (subjects : List Label) {KO : Type}
    (p : KO → KO → Digest) (ko ko' : KO) (hown : owner ∈ subjects) :
    Integrity Proof owner subjects p ko ko' :=
  Integrity.intra hown

/-! ## A reference (test) CryptoKernel — the Lean-as-host realization.

A trivial lawful instance over `ℤ` (commit = a linear form, verify = a stub accepting a
matching tag) — enough to `#eval`/test the Lean semantics without Rust. The real instance
is the Rust FFI one. This witnesses that the interface is inhabitable. -/
namespace Reference

/-- Reference digest = ℤ (a stand-in group; the real one is the curve/field). -/
abbrev D := Int
/-- Reference proof = the claimed statement (a trivial "proof" = echo). -/
abbrev P := Int

/-- Reference hash: an injective `Encodable` encoding (a test stand-in). Lifted to a top-level
`def` so its injectivity reduces. -/
def refHash (l : List Nat) : Int := (Encodable.encode l : Int)

theorem refHash_inj : Function.Injective refHash := by
  intro a b h
  apply Encodable.encode_injective
  unfold refHash at h
  exact_mod_cast h

instance : CryptoKernel D P where
  hash := refHash
  verify stmt proof := decide (stmt = proof)        -- accepts iff the proof echoes the statement
  commit v r := v + r                                -- a (degenerate) linear commitment
  nullifier d := d
  commit_hom := by intro v w r s; ring
  collisionHard := True                             -- carrier `True`-discharged in the toy model

end Reference

end Dregg2.Crypto
