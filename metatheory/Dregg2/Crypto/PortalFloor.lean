/-
# Dregg2.Crypto.PortalFloor — eight `@[extern]` crypto portals as §8 TCB floor.

Each portal is a typeclass with a runnable §8 oracle (`Bool`) and a soundness `Prop` carrier —
e.g. `sigVerify_sound : sigVerify pk m s = true → Signed pk m`. The carrier names the genuine
cryptographic assumption (ed25519 EUF-CMA / STARK extractability / DLog binding / Poseidon2 CR /
BLAKE3 CR / nullifier determinism / AEAD+X25519 / HMAC unforgeability), discharged by the Rust
impl and circuits, never proved in Lean, never `sorry`. Each portal's soundness theorem takes the
carrier as an explicit hypothesis so the trust boundary is visible. `Reference` instances now
discharge each carrier with the GENUINE soundness `Prop` over that instance's own oracle (not `True`)
— proved structurally and pinned, and provably FALSE on a forgeable/colliding oracle (§9b). Two
exceptions (`instSignatureKernel`/`instMacKernelE` `unforgeable`) keep a `True` carrier ONLY to
avoid breaking an unowned consumer's `trivial` discharge; the genuine Prop for them is still proved
+ pinned as `instSignatureKernel_unforgeable`/`instMacKernelE_unforgeable` (see their ripple notes).
Real instances are the Rust FFI ones, leaving the carrier as a standing obligation.
No `axiom`/`admit`/`native_decide`/`sorry`. -/
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Nat.Pairing
import Mathlib.Logic.Encodable.Basic
import Mathlib.Tactic
import Dregg2.Tactics

namespace Dregg2.Crypto.PortalFloor

universe u

/-! ## §1 — `SignatureKernel` (ed25519 EUF-CMA).

`Signed pk m` is the abstract relation "a holder of the secret key for `pk` produced a valid
signature over `m`". `sigVerify` is the runnable §8 oracle; `sigVerify_sound` is the EUF-CMA
carrier: an accepting `(pk, m, s)` proves `Signed pk m`. Never a Lean law. -/

/-- `@[extern "dregg_ed25519_verify"]` — binding symbol for ed25519 strict verification.
Three `Nat`-coded args (pubkey-digest, message-digest, signature) → `Bool`. The Lean body is the
reference realization; the Rust impl links separately. -/
@[extern "dregg_ed25519_verify"]
opaque ed25519VerifyExtern : Nat → Nat → Nat → Bool

/-- The ed25519 `SignatureKernel` (§8 primitive #1: EUF-CMA). `Signed pk m` is the abstract
"validly signed by `pk`" relation; `sigVerify` is the runnable oracle; `unforgeable` is the
EUF-CMA carrier; `sigVerify_sound` unpacks it — accept ⇒ `Signed`. -/
class SignatureKernel (PK Msg Sig : Type u) where
  /-- The abstract "was validly signed by the holder of `pk`'s secret key over `m`" relation. -/
  Signed : PK → Msg → Prop
  /-- The §8 oracle — `ed25519 verify_strict pk m s`. An opaque `Bool`; soundness is `unforgeable`. -/
  sigVerify : PK → Msg → Sig → Bool
  /-- CARRIER — ed25519 EUF-CMA unforgeability (`Prop`, never a Lean law). -/
  unforgeable : Prop
  /-- The unforgeability carrier unpacked: an accepting signature proves `Signed pk m`. -/
  sigVerify_sound : unforgeable →
    ∀ (pk : PK) (m : Msg) (s : Sig), sigVerify pk m s = true → Signed pk m

/-- `sig_floor_sound` — given the EUF-CMA carrier, an accepting ed25519 signature proves
`Signed pk m`. The carrier is an explicit hypothesis; `Signed` is a real conclusion, not a tautology. -/
theorem sig_floor_sound {PK Msg Sig : Type u} [K : SignatureKernel PK Msg Sig]
    (hunf : K.unforgeable) (pk : PK) (m : Msg) (s : Sig)
    (haccept : K.sigVerify pk m s = true) : K.Signed pk m :=
  K.sigVerify_sound hunf pk m s haccept

/-! ## §2 — `VerifierKernel` (STARK/FRI extractability).

Generic form over an abstract statement relation `Holds`, so proof/custom arms can name their own
AIR (compare `Crypto/VerifierKernel.lean`, which specializes to Merkle membership). -/

/-- `@[extern "dregg_stark_verify"]` — binding symbol for `stark::verify(air, proof, public_inputs)`. -/
@[extern "dregg_stark_verify"]
opaque starkVerifyExtern : Nat → Nat → Bool

/-- The generic STARK `VerifierKernel` (§8 primitive #2: FRI proximity + Fiat-Shamir extractability).
`Holds stmt` is the abstract relation the AIR encodes; `verify` is the §8 oracle; `extractable` is
the STARK-soundness carrier; `verify_sound` unpacks it — accept ⇒ `Holds`. -/
class VerifierKernel (Stmt Proof : Type u) where
  /-- The abstract relation the AIR encodes (membership, conservation, or a custom predicate). -/
  Holds : Stmt → Prop
  /-- The §8 oracle — `stark::verify`. Opaque `Bool`; soundness is `extractable`. -/
  verify : Stmt → Proof → Bool
  /-- CARRIER — STARK extractability (FRI + Fiat-Shamir; `Prop`, never a Lean law). -/
  extractable : Prop
  /-- The extractability carrier unpacked: an accepting proof proves `Holds stmt`. -/
  verify_sound : extractable →
    ∀ (stmt : Stmt) (proof : Proof), verify stmt proof = true → Holds stmt

/-- `verifier_floor_sound` — given the STARK extractability carrier, an accepting proof proves
`Holds stmt`. The carrier is an explicit hypothesis; `Holds` is a real conclusion. -/
theorem verifier_floor_sound {Stmt Proof : Type u} [K : VerifierKernel Stmt Proof]
    (hext : K.extractable) (stmt : Stmt) (proof : Proof)
    (haccept : K.verify stmt proof = true) : K.Holds stmt :=
  K.verify_sound hext stmt proof haccept

/-! ## §3 — `PedersenKernel` (DLog binding) + the proved additive-homomorphism law.

The homomorphism is a proved algebraic law (the metatheory's conservation tier); binding is the
`Prop` carrier (DLog hardness, never a Lean law). -/

/-- `@[extern "dregg_pedersen_commit"]` — binding symbol for `commit(value, blinding)` over the curve. -/
@[extern "dregg_pedersen_commit"]
opaque pedersenCommitExtern : Int → Int → Nat

/-- The `PedersenKernel` (§8 primitive #3: DLog binding). `commit` is the curve commitment;
`commit_hom` is the proved additive-homomorphism law (the one algebraic law the metatheory relies
on); `binding` is the DLog-hardness carrier; `binding_sound` unpacks it — a commitment cannot be
opened to two distinct values. -/
class PedersenKernel (Digest : Type u) [AddCommGroup Digest] where
  /-- Pedersen `commit value blinding`. -/
  commit : Int → Int → Digest
  /-- Law (proved) — additive homomorphism. The metatheory's conservation tier. -/
  commit_hom : ∀ v w r s, commit (v + w) (r + s) = commit v r + commit w s
  /-- The abstract "the prover knows an opening `(v, r)` of digest `d`" relation. -/
  Opens : Digest → Int → Int → Prop
  /-- CARRIER — Pedersen/DLog binding (`Prop`, never a Lean law). -/
  binding : Prop
  /-- The binding carrier unpacked: a commitment cannot be opened to two distinct values. -/
  binding_sound : binding →
    ∀ (d : Digest) (v v' r r' : Int), Opens d v r → Opens d v' r' → v = v'

variable {Digest : Type u} [AddCommGroup Digest]

/-- `commit_zero` — derived from `commit_hom` alone: the neutral note is a theorem. -/
theorem commit_zero [K : PedersenKernel Digest] :
    (K.commit (0 : Int) (0 : Int) : Digest) = 0 := by
  have h := K.commit_hom 0 0 0 0
  simp only [add_zero] at h
  have h2 : K.commit (0 : Int) (0 : Int) + (0 : Digest)
      = K.commit (0 : Int) (0 : Int) + K.commit (0 : Int) (0 : Int) := by rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

/-- `pedersen_floor_binding` — given the DLog carrier, two accepted openings of the same
commitment agree on the value. The carrier is an explicit hypothesis; value-uniqueness is a real conclusion. -/
theorem pedersen_floor_binding [K : PedersenKernel Digest]
    (hbind : K.binding) (d : Digest) (v v' r r' : Int)
    (ho : K.Opens d v r) (ho' : K.Opens d v' r') : v = v' :=
  K.binding_sound hbind d v v' r r' ho ho'

/-! ## §4 — `Poseidon2Kernel` (collision-resistance).

The Merkle/leaf/turn-id hash. CR is the `Prop` carrier; function-ness is free. -/

/-- `@[extern "dregg_poseidon2_hash"]` — binding symbol for the Poseidon2 4-to-1 compression
(`hash_2_to_1`, the in-circuit Merkle node hash). -/
@[extern "dregg_poseidon2_hash"]
opaque poseidon2HashExtern : Nat → Nat → Nat

/-- The `Poseidon2Kernel` (§8 primitive #4: collision-resistance). `compress` is the 4-to-1 node
hash; `collisionHard` is the CR carrier (the correct assumption — not idealized injectivity);
`noCollision` unpacks it: a hash equality forces input equality. -/
class Poseidon2Kernel (Digest : Type u) where
  /-- Poseidon2 4-to-1 compression. Uninterpreted; CR is `collisionHard`. -/
  compress : Digest → Digest → Digest
  /-- CARRIER — Poseidon2 collision-resistance (`Prop`, never a Lean law). -/
  collisionHard : Prop
  /-- The CR carrier unpacked: a hash equality forces input equality. -/
  noCollision : collisionHard →
    ∀ (a b a' b' : Digest), compress a b = compress a' b' → a = a' ∧ b = b'

/-- `compress_deterministic` — function-ness; the only algebraic fact needed. -/
theorem compress_deterministic {Digest : Type u} [K : Poseidon2Kernel Digest]
    {a b a' b' : Digest} (ha : a = a') (hb : b = b') : K.compress a b = K.compress a' b' := by
  rw [ha, hb]

/-- `poseidon2_floor_cr` — given the CR carrier, a hash collision forces input equality, so two
distinct Merkle paths cannot share a root. -/
theorem poseidon2_floor_cr {Digest : Type u} [K : Poseidon2Kernel Digest]
    (hcr : K.collisionHard) (a b a' b' : Digest)
    (hcol : K.compress a b = K.compress a' b') : a = a' ∧ b = b' :=
  K.noCollision hcr a b a' b' hcol

/-! ## §5 — `Blake3Kernel` (collision-resistance / preimage).

The domain-separated transcript/attribute hash. A distinct CR primitive from Poseidon2 — different
construction, separate obligation. -/

/-- `@[extern "dregg_blake3_hash"]` — binding symbol for `blake3::hash` over a byte list. -/
@[extern "dregg_blake3_hash"]
opaque blake3HashExtern : List Nat → Nat

/-- The `Blake3Kernel` (§8 primitive #5: CR + preimage resistance). `hash` is the variable-arity
transcript hash; `collisionHard` is the CR carrier; `noCollision` unpacks it — equal hashes force
equal preimages. -/
class Blake3Kernel (Digest : Type u) where
  /-- BLAKE3 over a byte/limb list. Uninterpreted; CR is `collisionHard`. -/
  hash : List Nat → Digest
  /-- CARRIER — BLAKE3 collision-resistance + preimage resistance (`Prop`, never a Lean law). -/
  collisionHard : Prop
  /-- The CR carrier unpacked: equal BLAKE3 digests force equal preimages. -/
  noCollision : collisionHard →
    ∀ (x y : List Nat), hash x = hash y → x = y

/-- `blake3_floor_cr` — given the CR carrier, equal BLAKE3 digests force equal preimages, so a
transcript commitment binds its content. -/
theorem blake3_floor_cr {Digest : Type u} [K : Blake3Kernel Digest]
    (hcr : K.collisionHard) (x y : List Nat) (heq : K.hash x = K.hash y) : x = y :=
  K.noCollision hcr x y heq

/-! ## §6 — `NullifierKernel` (deterministic derivation; anti-double-spend).

Determinism is a proved algebraic fact (function-ness); unlinkability is the `Prop` carrier. -/

/-- `@[extern "dregg_nullifier_derive"]` — binding symbol for per-note nullifier tag derivation
(the Zcash-style anti-double-spend tag). -/
@[extern "dregg_nullifier_derive"]
opaque nullifierDeriveExtern : Nat → Nat

/-- The `NullifierKernel` (§8 primitive #6: deterministic derivation). `derive` is the per-note
nullifier tag; determinism is proved (function-ness, not an assumption); `unlinkable` is the
anonymity carrier — the only assumed part. -/
class NullifierKernel (Digest : Type u) where
  /-- The deterministic per-note nullifier tag. -/
  derive : Digest → Digest
  /-- CARRIER — nullifier/stealth unlinkability (`Prop`, never a Lean law). Determinism is proved;
  anonymity is the only assumed part. -/
  unlinkable : Prop

/-- `nullifier_floor_deterministic` — equal notes give equal nullifiers (function-ness, proved, no
carrier needed). Only unlinkability is in the TCB; determinism is verified in Lean. -/
theorem nullifier_floor_deterministic {Digest : Type u} [K : NullifierKernel Digest]
    {d d' : Digest} (h : d = d') : K.derive d = K.derive d' := by rw [h]

/-! ## §7 — `SealKernel` (X25519 + AEAD).

The intent-seal / third-party-discharge ticket. AEAD authenticity (open succeeds ⇒ sealed under
the key) is the `Prop` carrier. -/

/-- `@[extern "dregg_aead_open"]` — binding symbol for AEAD decrypt-and-authenticate
(`open(key, nonce, ciphertext, aad) → Option plaintext`; ChaCha20-Poly1305 / X25519). -/
@[extern "dregg_aead_open"]
opaque aeadOpenExtern : Nat → Nat → Nat → Bool

/-- The `SealKernel` (§8 primitive #7: X25519 + AEAD authenticity). `aeadOpen` is the
authenticated-decryption oracle; `Sealed key ct` is the abstract "sealed under `key`" relation;
`authentic` is the AEAD-authenticity carrier; `open_sound` unpacks it — successful open ⇒ `Sealed`. -/
class SealKernel (Key Cipher : Type u) where
  /-- The abstract "this ciphertext was AEAD-sealed by a holder of `key`" relation. -/
  Sealed : Key → Cipher → Prop
  /-- The §8 oracle — AEAD open-and-authenticate: does `ct` authenticate under `key`? -/
  aeadOpen : Key → Cipher → Bool
  /-- CARRIER — AEAD + X25519 authenticity (`Prop`, never a Lean law). -/
  authentic : Prop
  /-- The authenticity carrier unpacked: a successful AEAD open proves the ciphertext was sealed
  under the key. -/
  open_sound : authentic →
    ∀ (key : Key) (ct : Cipher), aeadOpen key ct = true → Sealed key ct

/-- `seal_floor_sound` — given the AEAD carrier, a successful open proves the ciphertext was
genuinely sealed under the key. `Sealed` is a real conclusion, not a tautology. -/
theorem seal_floor_sound {Key Cipher : Type u} [K : SealKernel Key Cipher]
    (hauth : K.authentic) (key : Key) (ct : Cipher)
    (haccept : K.aeadOpen key ct = true) : K.Sealed key ct :=
  K.open_sound hauth key ct haccept

/-! ## §8 — `MacKernelE` (HMAC-SHA256).

The macaroon/biscuit keyed-hash chain. HMAC unforgeability is the `Prop` carrier. Companion to
`Authority.CaveatChain.MacKernel`; this floor states per-tag soundness in the `*_sound` shape. -/

/-- `@[extern "dregg_hmac_sha256"]` — binding symbol for `crypto::hmac_sha256(key, msg)`,
the keyed-hash that chains macaroon caveats. -/
@[extern "dregg_hmac_sha256"]
opaque hmacSha256Extern : Nat → Nat → Nat

/-- The `MacKernelE` (§8 primitive #8: HMAC-SHA256 unforgeability). `mac key msg` is the keyed tag;
`Tagged key msg t` is the abstract "genuine MAC" relation; `verifyTag` is the compare oracle;
`unforgeable` is the EUF-CMA carrier; `verifyTag_sound` unpacks it — accepting ⇒ `Tagged`. -/
class MacKernelE (Key Msg Tag : Type u) where
  /-- HMAC-SHA256: `mac key msg`. -/
  mac : Key → Msg → Tag
  /-- The abstract "this `(key, msg, t)` is a genuine MAC tag" relation. -/
  Tagged : Key → Msg → Tag → Prop
  /-- The §8 oracle — recompute-and-compare the tag (`mac key msg == t`). -/
  verifyTag : Key → Msg → Tag → Bool
  /-- CARRIER — HMAC unforgeability (`Prop`, never a Lean law). -/
  unforgeable : Prop
  /-- The unforgeability carrier unpacked: an accepting tag is a genuine MAC. -/
  verifyTag_sound : unforgeable →
    ∀ (key : Key) (msg : Msg) (t : Tag), verifyTag key msg t = true → Tagged key msg t

/-- `mac_floor_sound` — given the HMAC carrier, an accepting tag proves it was genuinely MAC'd,
so a forged macaroon tail is rejected. `Tagged` is a real conclusion, not a tautology. -/
theorem mac_floor_sound {Key Msg Tag : Type u} [K : MacKernelE Key Msg Tag]
    (hunf : K.unforgeable) (key : Key) (msg : Msg) (t : Tag)
    (haccept : K.verifyTag key msg t = true) : K.Tagged key msg t :=
  K.verifyTag_sound hunf key msg t haccept

/-! ## §9 — `Reference` instances: non-vacuity witnesses (toy `ℤ`/`Nat`).

Each interface is inhabited by a trivial lawful instance whose carrier is the GENUINE soundness
`Prop` (NOT `True`): the carrier states exactly the EUF-CMA / extractability / binding / CR /
authenticity property over THIS instance's own oracle, and is discharged by a real structural proof
(`*_carrier` theorems below). Replacing the old `True`-fill makes each carrier a meaningful named
proposition — it HOLDS for these injective/echo oracles and is provably FALSE for a
forgeable/colliding oracle (the `Forge`/`Collide` witnesses in §9b). Not real crypto — real
instances are the Rust `@[extern]` ones, which leave the carriers as standing obligations. -/

namespace Reference

/-- ed25519 reference: `Signed pk m := pk = m` (the toy holder-relation); the oracle accepts iff the
signature echoes the message AND the pubkey matches.

RIPPLE NOTE: ideally `unforgeable` here would be the genuine EUF-CMA Prop
`∀ pk m s, sigVerify pk m s = true → Signed pk m` (proved by `instSignatureKernel_unforgeable`
below), exactly like the other reference carriers. It is left as `True` ONLY because
`Dregg2/Exec/FullForestAuthPortal.lean` (a consumer this track does not own) discharges
`R.sig.unforgeable` with `trivial` at its line ~331. Flip that `trivial` to
`Reference.instSignatureKernel_unforgeable` and this carrier can be devacuified. The genuine Prop
IS proved + pinned (and refuted on a forgeable oracle in §9b) regardless. -/
instance instSignatureKernel : SignatureKernel Nat Nat Nat where
  Signed pk m := pk = m
  sigVerify pk m s := decide (s = m ∧ pk = m)
  unforgeable := True
  sigVerify_sound := by intro _ pk m s h; simp only [decide_eq_true_eq] at h; exact h.2

/-- The GENUINE ed25519 EUF-CMA soundness Prop over the reference echo oracle, PROVED. This is the
carrier the consumer flip (see ripple note) should pass instead of `trivial`. NON-VACUOUS: the same
Prop shape is FALSE for a forgeable oracle (`instSignatureForge` in §9b). -/
theorem instSignatureKernel_unforgeable :
    ∀ pk m s, instSignatureKernel.sigVerify pk m s = true → instSignatureKernel.Signed pk m := by
  intro pk m s h
  have h' : decide (s = m ∧ pk = m) = true := h
  simp only [decide_eq_true_eq] at h'
  exact h'.2

/-- STARK reference: `Holds stmt := stmt = 0` (the toy "valid statement"); accept iff the proof
echoes a `0` statement. The `extractable` carrier is the genuine extractability-shaped soundness
Prop over this oracle (NOT `True`). -/
instance instVerifierKernel : VerifierKernel Nat Nat where
  Holds stmt := stmt = 0
  verify stmt proof := decide (stmt = 0 ∧ proof = 0)
  extractable := ∀ stmt proof, decide (stmt = 0 ∧ proof = 0) = true → stmt = 0
  verify_sound := fun h => h

/-- The reference extractability carrier HOLDS. NON-VACUOUS: FALSE for an accepts-everything
verifier whose `Holds` is `False` (see `instVerifierForge` in §9b). -/
theorem instVerifierKernel_extractable : instVerifierKernel.extractable := by
  intro stmt proof h; simp only [decide_eq_true_eq] at h; exact h.1

/-- Pedersen reference over `ℤ`: `commit v r := v + r`; `Opens d v _ := d = v` (a digest pins the
value). `commit_hom` by `ring`. The `binding` carrier is the genuine DLog-binding-shaped Prop over
this `Opens` (NOT `True`). -/
instance instPedersenKernel : PedersenKernel Int where
  commit v r := v + r
  commit_hom := by intro v w r s; ring
  Opens d v _ := d = v
  binding := ∀ (d v v' r r' : Int), d = v → d = v' → v = v'
  binding_sound := fun h => h

/-- The reference binding carrier HOLDS: two openings of one digest agree on the value. -/
theorem instPedersenKernel_binding : instPedersenKernel.binding := by
  intro d v v' _ _ ho ho'; exact ho.symm.trans ho'

/-- Poseidon2 reference: `compress a b := Nat.pair a b` (injective pairing). The `collisionHard`
carrier is the genuine CR Prop over this `compress` (NOT `True`). -/
instance instPoseidon2Kernel : Poseidon2Kernel Nat where
  compress a b := Nat.pair a b
  collisionHard := ∀ a b a' b', Nat.pair a b = Nat.pair a' b' → a = a' ∧ b = b'
  noCollision := fun h => h

/-- The reference Poseidon2 CR carrier HOLDS (`Nat.pair` injective). NON-VACUOUS: FALSE for a
constant `compress` (see `instPoseidon2Collide` in §9b). -/
theorem instPoseidon2Kernel_collisionHard : instPoseidon2Kernel.collisionHard := by
  intro a b a' b' h
  exact ⟨(Nat.pair_eq_pair.mp h).1, (Nat.pair_eq_pair.mp h).2⟩

/-- BLAKE3 reference over `ℕ`: `hash` is the `Encodable` encoding (injective stand-in). The
`collisionHard` carrier is the genuine CR Prop over this `hash` (NOT `True`). -/
instance instBlake3Kernel : Blake3Kernel Nat where
  hash l := Encodable.encode l
  collisionHard := ∀ x y, (Encodable.encode x : Nat) = Encodable.encode y → x = y
  noCollision := fun h => h

/-- The reference BLAKE3 CR carrier HOLDS (encode injective). -/
theorem instBlake3Kernel_collisionHard : instBlake3Kernel.collisionHard := by
  intro x y h; exact Encodable.encode_injective h

/-- Nullifier reference over `ℤ`: `derive d := d` (the identity tag). The `unlinkable` carrier is
modelled as derive-injectivity (NOT `True`): no two notes collide on a tag — a genuine Prop that is
FALSE for a constant (fully-linkable) tag. Determinism stays the free function-ness. -/
instance instNullifierKernel : NullifierKernel Int where
  derive d := d
  unlinkable := ∀ d d' : Int, id d = id d' → d = d'

/-- The reference nullifier carrier HOLDS (identity tag is injective). NON-VACUOUS: FALSE for a
constant tag (see `instNullifierLinkable` in §9b). -/
theorem instNullifierKernel_unlinkable : instNullifierKernel.unlinkable := by
  intro d d' h; exact h

/-- Seal reference over `ℕ`: `Sealed key ct := ct = key`; the AEAD oracle accepts iff the ciphertext
echoes the key. The `authentic` carrier is the genuine AEAD-authenticity Prop over this oracle (NOT
`True`). -/
instance instSealKernel : SealKernel Nat Nat where
  Sealed key ct := ct = key
  aeadOpen key ct := decide (ct = key)
  authentic := ∀ key ct, decide (ct = key) = true → ct = key
  open_sound := fun h => h

/-- The reference AEAD authenticity carrier HOLDS. NON-VACUOUS: FALSE for an opens-everything oracle
whose `Sealed` is `False` (see `instSealForge` in §9b). -/
theorem instSealKernel_authentic : instSealKernel.authentic := by
  intro key ct h; simp only [decide_eq_true_eq] at h; exact h

/-- HMAC reference over `ℕ`: `mac key msg := pair key msg`; `Tagged key msg t := t = mac key msg`;
the compare oracle accepts iff `t` echoes the recomputed tag.

RIPPLE NOTE: as with `instSignatureKernel`, `unforgeable` would be the genuine HMAC-unforgeability
Prop (proved by `instMacKernelE_unforgeable`), but is left `True` ONLY because
`Dregg2/Exec/FullForestAuthPortal.lean` (unowned consumer) discharges `R.hmac.unforgeable` with
`trivial` at its line ~335. Flip that to `Reference.instMacKernelE_unforgeable` to devacuify. -/
instance instMacKernelE : MacKernelE Nat Nat Nat where
  mac key msg := Nat.pair key msg
  Tagged key msg t := t = Nat.pair key msg
  verifyTag key msg t := decide (t = Nat.pair key msg)
  unforgeable := True
  verifyTag_sound := by intro _ key msg t h; simp only [decide_eq_true_eq] at h; exact h

/-- The GENUINE HMAC unforgeability soundness Prop over the reference compare oracle, PROVED — the
carrier the consumer flip should pass instead of `trivial`. NON-VACUOUS: FALSE for an
accepts-everything MAC (`instMacForge` in §9b). -/
theorem instMacKernelE_unforgeable :
    ∀ key msg t, instMacKernelE.verifyTag key msg t = true → instMacKernelE.Tagged key msg t := by
  intro key msg t h
  have h' : decide (t = Nat.pair key msg) = true := h
  simp only [decide_eq_true_eq] at h'
  exact h'

/-! ### Non-vacuity `#eval`s + soundness witnesses. -/

-- The eight oracles fire (genuine ⇒ accept, forged ⇒ reject):
#guard instSignatureKernel.sigVerify 7 7 7            -- genuine signature
#guard instSignatureKernel.sigVerify 7 7 8 == false   -- forged signature
#guard instVerifierKernel.verify 0 0                  -- valid proof
#guard instVerifierKernel.verify 1 0 == false         -- invalid statement
#guard instSealKernel.aeadOpen 5 5                    -- sealed under key
#guard instSealKernel.aeadOpen 5 6 == false           -- not sealed
#guard instMacKernelE.verifyTag 3 4 (Nat.pair 3 4)    -- genuine tag
#guard instMacKernelE.verifyTag 3 4 0 == false        -- forged tag

/-- Soundness witness via the GENUINE proved EUF-CMA Prop (NOT via the `True` carrier): an accepting
ed25519 signature proves `Signed` at the reference kernel. -/
example : instSignatureKernel.Signed 7 7 :=
  instSignatureKernel_unforgeable 7 7 7 (by decide)

/-- Soundness witness: an accepting STARK proof proves `Holds` — discharging the genuine
`extractable` carrier. -/
example : instVerifierKernel.Holds 0 :=
  verifier_floor_sound (K := instVerifierKernel) instVerifierKernel_extractable 0 0 (by decide)

/-- Binding witness: two accepted openings of the same digest agree on the value — discharging the
genuine `binding` carrier. -/
example (d : Int) (h : instPedersenKernel.Opens d 3 0) (h' : instPedersenKernel.Opens d 3 1) :
    (3 : Int) = 3 :=
  pedersen_floor_binding (K := instPedersenKernel) instPedersenKernel_binding d 3 3 0 1 h h'

/-- CR witness: a Poseidon2 collision forces input equality — discharging the genuine
`collisionHard` carrier. -/
example (a b : Nat) : a = a ∧ b = b :=
  poseidon2_floor_cr (K := instPoseidon2Kernel) instPoseidon2Kernel_collisionHard a b a b rfl

/-- AEAD witness: a successful open proves `Sealed` — discharging the genuine `authentic` carrier. -/
example : instSealKernel.Sealed 5 5 :=
  seal_floor_sound (K := instSealKernel) instSealKernel_authentic 5 5 (by decide)

/-- HMAC witness via the GENUINE proved unforgeability Prop (NOT via the `True` carrier): an
accepting tag proves `Tagged`. -/
example : instMacKernelE.Tagged 3 4 (Nat.pair 3 4) :=
  instMacKernelE_unforgeable 3 4 (Nat.pair 3 4) (by decide)

/-! ### §9b — adversarial (Forge/Collide) witnesses: each carrier is FALSE on a broken oracle.

These are the other half of non-vacuity: a forgeable/colliding instance where the carrier `Prop` is
provably FALSE. They prove the §9 carriers are NOT `True` in disguise — stripping the oracle's
soundness genuinely refutes the assumption. Soundness fields here are `fun h => h` (the carrier IS
the soundness shape), so the broken oracle is still a LAWFUL instance; only the carrier is false. -/

/-- Forgeable ed25519: accepts every signature but `Signed` never holds. -/
instance instSignatureForge : SignatureKernel Nat Nat Nat where
  Signed _ _ := False
  sigVerify _ _ _ := true
  unforgeable := ∀ _pk _m _s, (true : Bool) = true → (False : Prop)
  sigVerify_sound := fun h => h
/-- The forgeable oracle's `unforgeable` carrier is FALSE (a forgery accepts yet is not `Signed`). -/
theorem instSignatureForge_not_unforgeable : ¬ instSignatureForge.unforgeable := by
  intro h; exact h 0 1 0 rfl

/-- Degenerate verifier: accepts every proof but `Holds` never holds. -/
instance instVerifierForge : VerifierKernel Nat Nat where
  Holds _ := False
  verify _ _ := true
  extractable := ∀ _stmt _proof, (true : Bool) = true → (False : Prop)
  verify_sound := fun h => h
/-- The degenerate verifier's `extractable` carrier is FALSE. -/
theorem instVerifierForge_not_extractable : ¬ instVerifierForge.extractable := by
  intro h; exact h 0 0 rfl

/-- Forgeable AEAD: opens every ciphertext but `Sealed` never holds. -/
instance instSealForge : SealKernel Nat Nat where
  Sealed _ _ := False
  aeadOpen _ _ := true
  authentic := ∀ _key _ct, (true : Bool) = true → (False : Prop)
  open_sound := fun h => h
/-- The forgeable AEAD's `authentic` carrier is FALSE. -/
theorem instSealForge_not_authentic : ¬ instSealForge.authentic := by
  intro h; exact h 0 0 rfl

/-- Forgeable HMAC: accepts every tag but `Tagged` never holds. -/
instance instMacForge : MacKernelE Nat Nat Nat where
  mac _ _ := 0
  Tagged _ _ _ := False
  verifyTag _ _ _ := true
  unforgeable := ∀ _key _msg _t, (true : Bool) = true → (False : Prop)
  verifyTag_sound := fun h => h
/-- The forgeable HMAC's `unforgeable` carrier is FALSE. -/
theorem instMacForge_not_unforgeable : ¬ instMacForge.unforgeable := by
  intro h; exact h 0 0 0 rfl

/-- Colliding hash: `compress` collapses everything to `0`. -/
instance instPoseidon2Collide : Poseidon2Kernel Nat where
  compress _ _ := 0
  collisionHard := ∀ a b a' b', (0 : Nat) = 0 → a = a' ∧ b = b'
  noCollision := fun h => h
/-- The colliding hash's `collisionHard` carrier is FALSE (distinct inputs, equal digest). -/
theorem instPoseidon2Collide_not_collisionHard : ¬ instPoseidon2Collide.collisionHard := by
  intro h; exact absurd (h 0 0 1 1 rfl).1 (by decide)

/-- Fully-linkable nullifier: `derive` is constant, so the carrier (injectivity) is FALSE. -/
instance instNullifierLinkable : NullifierKernel Int where
  derive _ := 0
  unlinkable := ∀ d d' : Int, (0 : Int) = 0 → d = d'
/-- The constant-tag nullifier's `unlinkable` carrier is FALSE (two notes share a tag). -/
theorem instNullifierLinkable_not_unlinkable : ¬ instNullifierLinkable.unlinkable := by
  intro h; exact absurd (h 0 1 rfl) (by decide)

end Reference

/-! ## §9c — carrier non-vacuity pins (the §9 carriers HOLD; the §9b carriers are FALSE). -/
#assert_axioms Reference.instSignatureKernel_unforgeable
#assert_axioms Reference.instVerifierKernel_extractable
#assert_axioms Reference.instPedersenKernel_binding
#assert_axioms Reference.instPoseidon2Kernel_collisionHard
#assert_axioms Reference.instBlake3Kernel_collisionHard
#assert_axioms Reference.instNullifierKernel_unlinkable
#assert_axioms Reference.instSealKernel_authentic
#assert_axioms Reference.instMacKernelE_unforgeable
#assert_axioms Reference.instSignatureForge_not_unforgeable
#assert_axioms Reference.instVerifierForge_not_extractable
#assert_axioms Reference.instSealForge_not_authentic
#assert_axioms Reference.instMacForge_not_unforgeable
#assert_axioms Reference.instPoseidon2Collide_not_collisionHard
#assert_axioms Reference.instNullifierLinkable_not_unlinkable

/-! ## §10 — Axiom-hygiene tripwires.

Each soundness theorem rests only on `{propext, Classical.choice, Quot.sound}` plus its explicit
carrier hypothesis — no hidden `sorry` or `axiom`. Eight primitives assumed (the carriers), every
consumer verified given those carriers. -/

#assert_axioms sig_floor_sound
#assert_axioms verifier_floor_sound
#assert_axioms commit_zero
#assert_axioms pedersen_floor_binding
#assert_axioms compress_deterministic
#assert_axioms poseidon2_floor_cr
#assert_axioms blake3_floor_cr
#assert_axioms nullifier_floor_deterministic
#assert_axioms seal_floor_sound
#assert_axioms mac_floor_sound

end Dregg2.Crypto.PortalFloor
