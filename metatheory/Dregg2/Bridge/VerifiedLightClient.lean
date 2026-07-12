/-
# Dregg2.Bridge.VerifiedLightClient — the SHARED foundation every per-chain verified
light client (Solana Tower-BFT, Ethereum sync-committee, Cosmos Tendermint) instantiates.

dregg builds VERIFIED light clients for other chains: not tested — PROVEN no-forgery. Each
one formalizes a foreign chain's header/update verification RULES in Lean, proves them
fail-closed and sound, and treats the crypto primitives (ed25519 / keccak / bls12-381) as
HONEST, NAMED, MINIMAL verified LEAVES (an EverCrypt-style discharge, never "assume the whole
verification is correct"). This file is the abstraction the per-chain Fables plug into: ONE
proven shape, so each chain proves the SAME three theorems over its own rules.

TWO LAYERS, kept distinct + honest:

  * RULES (formalizable, high value): "an update is valid IFF ≥2/3 of the trusted set signed
    it, the chain-id matches, the finality/inclusion branch reconstructs, the trusting period
    holds." The Nomad $190M hack was a RULES bug — an unproven message accepted by a
    permissive default — NOT a crypto break. Proving the rules FAIL CLOSED (`FailClosed`) is
    exactly the tooth that catches the class of bug that drains bridges.
  * CRYPTO (a mountain to formalize; treated as verified LEAVES): the `CryptoLeaf` bundle
    declares the signature-soundness and hash-collision-resistance HYPOTHESES as EXPLICIT,
    VISIBLE structure fields (`sigSound`, `hashCR`). A per-chain instance either PROVES them
    (a toy scheme) or supplies them as an opaque, named assumption discharged by a verified
    crypto library. The `NoForgery` theorem is legitimately OF THE FORM "IF the crypto leaves
    are sound THEN the rules verify correctly": honest as long as the leaf is minimal + named
    and does not launder the conclusion.

THE THREE THEOREM SHAPES every chain proves (bundled as fields of `ForeignLightClient`, so a
chain instance CANNOT exist without discharging them):

  * `NoForgery`   — `verify` accepts an update ⟹ the foreign-chain validity predicate holds
                    (given the crypto leaves; the leaf's `sigSound` is used in the proof).
  * `FailClosed`  — `verify` REJECTS the empty / default / sub-quorum / tampered update (the
                    Nomad-law tooth: an unproven update is never accepted).
  * `NonVacuous`  — `verify` is `true` on SOME input AND `false` on another — it discriminates
                    (a `True`-by-construction verifier is a DEFECT, not a proof).

COMPOSITION with `Metatheory.Bridge.InterchainAdapter` (read: `Metatheory/Bridge/InterchainAdapter.lean`):
that adapter treats a foreign chain's finality as an ASSUMED oracle (`foreignFinal : Header →
Prop`), pinned to a `TrustRung`. A `ForeignLightClient` PRODUCES that hypothesis: `toAdapter`
builds an `InterchainAdapter` whose `foreignFinal u := verify ts u = true` on the `proof` rung
(finality is DISCHARGED to a decidable predicate the client computes), and
`toAdapter_foreignFinal_discharged` proves that this adapter's finality entails real
foreign-chain validity via `NoForgery`. The adapter no longer BLINDLY assumes finality — a
verified light client discharges its finality assumption.

Kernel-clean: `#assert_axioms` hard-gates every theorem. The only assumptions are the NAMED
crypto-leaf fields the instance supplies (invisible to `#assert_axioms`, which sees only
`axiom`-keyword decls — so the toy instance PROVES its leaf to keep the demonstration
genuinely axiom-clean and the leaf non-laundered).
-/
import Metatheory.Bridge.InterchainAdapter
import Dregg2.Tactics

namespace Dregg2.Bridge.VerifiedLightClient

/-! ## §1 — The HONEST crypto-leaf interface (the verified-primitive hypotheses, made VISIBLE).

`CryptoLeaf` bundles the two primitives a light client leans on — a signature verifier and a
hash — TOGETHER WITH the soundness facts they are trusted to provide (`sigSound`, `hashCR`).
The facts are ordinary structure fields, so a per-chain instance MUST supply them and an
auditor can SEE them; they are not global `axiom`s and not a laundered `def FooHard` used as a
hidden hypothesis. A real chain supplies `sigSound` as the named ed25519/BLS unforgeability
assumption discharged by a verified crypto library; a toy chain proves it. -/

/-- **`CryptoLeaf`** — the honest, named verified-primitive bundle. `sigVerify` and `hash` are
the opaque primitives (a verified crypto lib realizes them); `Signed` is the DENOTATION a
verifying signature is trusted to certify ("`pk` authorized `m`"); `sigSound` and `hashCR` are
the SOUNDNESS HYPOTHESES, visible as fields so no chain can hide them. -/
structure CryptoLeaf where
  /-- Public-key type (a chain plugs its ed25519 / BLS pubkey here). -/
  PubKey : Type
  /-- Signed-message type (the chain's header-bytes / vote domain). -/
  Msg : Type
  /-- Signature type. -/
  Sig : Type
  /-- Digest type (a chain plugs its keccak / SHA-256 output here). -/
  Digest : Type
  /-- The signature verifier (opaque; EverCrypt-style). -/
  sigVerify : PubKey → Msg → Sig → Bool
  /-- The hash (opaque; a verified keccak/SHA realizes it). -/
  hash : Msg → Digest
  /-- The DENOTATION: `Signed pk m` means the holder of `pk` genuinely authorized `m`. -/
  Signed : PubKey → Msg → Prop
  /-- **Signature soundness (the named unforgeability leaf).** A verifying signature entails
  the key holder authorized the message. This is the ONLY signature assumption; it is minimal
  and it does NOT say "the whole update is valid". -/
  sigSound : ∀ pk m s, sigVerify pk m s = true → Signed pk m
  /-- **Hash collision resistance (the named CR leaf).** Equal digests entail equal preimages
  — so a reconstructed inclusion/finality branch pins the committed bytes. -/
  hashCR : ∀ m₁ m₂, hash m₁ = hash m₂ → m₁ = m₂

/-! ## §2 — The three theorem SHAPES every chain must prove, as reusable predicates.

Stated over the bare components (a `verify` verdict, a foreign-validity predicate, an empty
update) so a per-chain Fable can name them independently; they are ALSO bundled as fields of
`ForeignLightClient` below, so a chain instance cannot exist without discharging them. -/

/-- **`NoForgery verify ForeignValid`** — the RULES are sound: whenever `verify` accepts an
update, the foreign chain's OWN validity predicate holds for it. (The crypto leaves are used
in the per-chain PROOF of this; the shape is "verify accepts ⟹ foreign-valid".) -/
def NoForgery {Update TrustedState : Type}
    (verify : TrustedState → Update → Bool) (ForeignValid : Update → Prop) : Prop :=
  ∀ ts u, verify ts u = true → ForeignValid u

/-- **`FailClosed verify emptyUpdate`** — the Nomad-law tooth: `verify` REJECTS the
empty / default / uninitialized update for EVERY trusted state. An unproven update is never
accepted by a permissive default. -/
def FailClosed {Update TrustedState : Type}
    (verify : TrustedState → Update → Bool) (emptyUpdate : Update) : Prop :=
  ∀ ts, verify ts emptyUpdate = false

/-- **`NonVacuous verify`** — `verify` DISCRIMINATES: it is `true` on some input and `false`
on another. A verifier that accepts everything (or nothing) is a defect; this forbids the
`True`-by-construction (or `False`-by-construction) verifier. -/
def NonVacuous {Update TrustedState : Type}
    (verify : TrustedState → Update → Bool) : Prop :=
  ∃ ts u₁ u₂, verify ts u₁ = true ∧ verify ts u₂ = false

/-! ## §3 — `ForeignLightClient`: the bundled shape a per-chain Fable instantiates.

A chain supplies its `Update`/`TrustedState` types, its foreign-validity predicate, its
`verify` RULES, an `emptyUpdate` default, the crypto `leaf`, and — as FIELDS — proofs of the
three theorem shapes. Because the theorems are fields, `ForeignLightClient.mk` is a proof
obligation: no chain instance exists until `NoForgery`, `FailClosed`, and `NonVacuous` are
discharged. The `leaf` is bundled so it is VISIBLE at the instance site (an auditor reads
which primitive soundness the `noForgery` proof rests on). -/

/-- **`ForeignLightClient`** — the shared shape. The per-chain lanes fill in the fields; the
top theorems (`NoForgery`/`FailClosed`/`NonVacuous`) are proof obligations carried as fields. -/
structure ForeignLightClient where
  /-- The crypto-primitive bundle this client's rules lean on (VISIBLE; the `noForgery` proof
  uses `leaf.sigSound`). -/
  leaf : CryptoLeaf
  /-- The chain's update/header type (a sync-committee update, a Tower-BFT vote set, …). -/
  Update : Type
  /-- The chain's trusted state (the current committee / validator set + chain-id + period). -/
  TrustedState : Type
  /-- The foreign chain's OWN validity predicate — what a correct update MUST satisfy. -/
  ForeignValid : Update → Prop
  /-- THE RULES: the executable header/update verification verdict. -/
  verify : TrustedState → Update → Bool
  /-- The empty / default / uninitialized update — the Nomad-law fail-closed probe. -/
  emptyUpdate : Update
  /-- **NO FORGERY** (proof obligation): accept ⟹ foreign-valid. -/
  noForgery : NoForgery verify ForeignValid
  /-- **FAIL CLOSED** (proof obligation): the empty update is rejected. -/
  failClosed : FailClosed verify emptyUpdate
  /-- **NON-VACUOUS** (proof obligation): `verify` discriminates. -/
  nonVacuous : NonVacuous verify

/-! ## §4 — COMPOSITION with `Metatheory.Bridge.InterchainAdapter`.

`InterchainAdapter Header Event` (`Metatheory/Bridge/InterchainAdapter.lean:70`) treats foreign
finality as an ASSUMED oracle `foreignFinal : Header → Prop` on a `TrustRung`. A
`ForeignLightClient` PRODUCES that oracle: its `Update` IS the header (a finality proof), and
`foreignFinal u := verify ts u = true` — finality is the light client's decidable verdict,
DISCHARGED, not assumed. The rung is `proof`: the finality predicate is dischargeable to a
theorem, and `NoForgery` is exactly that discharge (accept ⟹ real foreign validity). -/

open Metatheory.Bridge in
/-- **`toAdapter V ts incl`** — build the `InterchainAdapter` a `ForeignLightClient` produces.
`foreignFinal u := V.verify ts u = true` (the client's decidable finality verdict); `inclusion`
is the chain's event-in-header relation supplied by the caller; the rung is `proof` because
finality is DISCHARGED (via `V.noForgery`), not assumed. -/
def toAdapter (V : ForeignLightClient) (ts : V.TrustedState)
    {Event : Type} (incl : Event → V.Update → Prop) :
    InterchainAdapter V.Update Event where
  foreignFinal := fun u => V.verify ts u = true
  inclusion    := incl
  trust        := TrustRung.proof

open Metatheory.Bridge in
/-- **`toAdapter_foreignFinal_discharged` (THE DISCHARGE).** The adapter's `foreignFinal`
hypothesis — for the adapter a `ForeignLightClient` produces — is NOT a blind assumption: it
ENTAILS the foreign chain's real validity predicate, via `NoForgery`. This is the wire: the
`InterchainAdapter` finality assumption is discharged by the verified rules. -/
theorem toAdapter_foreignFinal_discharged (V : ForeignLightClient) (ts : V.TrustedState)
    {Event : Type} (incl : Event → V.Update → Prop) (u : V.Update)
    (h : (toAdapter V ts incl).foreignFinal u) : V.ForeignValid u :=
  V.noForgery ts u h

open Metatheory.Bridge in
/-- **`toAdapter_accepts_entails_valid`.** If the produced adapter ACCEPTS a cross-chain event
(`InterchainAdapter.accepts` — a finalized header includes it), then there is an update that is
FOREIGN-VALID (not merely verify-accepted) and includes the event. Composes
`InterchainAdapter.accepts` with `NoForgery`: acceptance rests on proven validity. -/
theorem toAdapter_accepts_entails_valid (V : ForeignLightClient) (ts : V.TrustedState)
    {Event : Type} (incl : Event → V.Update → Prop) (ev : Event)
    (h : (toAdapter V ts incl).accepts ev) :
    ∃ u, V.ForeignValid u ∧ incl ev u := by
  obtain ⟨u, hfin, hinc⟩ := h
  exact ⟨u, V.noForgery ts u hfin, hinc⟩

open Metatheory.Bridge in
/-- **`toAdapter_rejects_empty` (Nomad tooth, at the adapter boundary).** The produced adapter's
`foreignFinal` is FALSE on the empty/default update — `FailClosed` lifts into the adapter, so an
uninitialized update is never treated as final. -/
theorem toAdapter_rejects_empty (V : ForeignLightClient) (ts : V.TrustedState)
    {Event : Type} (incl : Event → V.Update → Prop) :
    ¬ (toAdapter V ts incl).foreignFinal V.emptyUpdate := by
  show ¬ (V.verify ts V.emptyUpdate = true)
  rw [V.failClosed ts]; simp

/-! ## §5 — A NON-VACUOUS worked template: a toy 1-signer chain.

The per-chain lanes need a worked instance proving the shape is inhabitable AND the theorems
DISCRIMINATE. This toy chain has one trusted signer (key `7`). An update carries a signer, a
content word, a signature, and a claimed content digest. The RULES accept iff the signer is the
trusted key, the signature verifies, and the digest matches the hash. To keep the demonstration
genuinely axiom-clean and the crypto leaf NON-LAUNDERED, the toy PROVES its leaf (`toyLeaf`)
rather than assuming it — a real chain replaces `toyLeaf` with an ed25519/BLS leaf whose
`sigSound` is the named library assumption. -/

/-- The toy signature verifier: `s` verifies for `(pk, m)` iff `pk = 7` (the sole genuine key)
AND `s = pk + m` (a toy MAC). Concrete `Nat` primitive (a real chain plugs ed25519 here). -/
def toySigVerify (pk m s : Nat) : Bool := (pk == 7) && (s == pk + m)

/-- The toy hash — the identity (a real chain plugs keccak/SHA here). -/
def toyHash (m : Nat) : Nat := m

/-- The toy `Signed` denotation: the holder of key `7` genuinely authorized `m`. Discriminates
— `toySigned 3 m` is `(3 = 7)`, false. -/
def toySigned (pk _m : Nat) : Prop := pk = 7

/-- **The named signature-soundness leaf, PROVED for the toy.** A verifying toy signature
entails the genuine key `7` signed — exactly `CryptoLeaf.sigSound`. (A real chain leaves this
as its opaque, named ed25519/BLS unforgeability assumption.) -/
theorem toySigSound (pk m s : Nat) (h : toySigVerify pk m s = true) : toySigned pk m := by
  simp only [toySigVerify, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

/-- **The named hash-CR leaf, PROVED for the toy** — injectivity of the identity hash. -/
theorem toyHashCR (m₁ m₂ : Nat) (h : toyHash m₁ = toyHash m₂) : m₁ = m₂ := h

/-- The concrete crypto leaf, assembled from the proved toy primitives — the interface slot a
per-chain Fable fills with an ed25519/BLS + keccak leaf whose `sigSound`/`hashCR` are the named
library assumptions. Here both soundness fields are genuinely PROVED, so the demonstration is
axiom-clean and the leaf is non-laundered. -/
def toyLeaf : CryptoLeaf where
  PubKey := Nat
  Msg := Nat
  Sig := Nat
  Digest := Nat
  sigVerify := toySigVerify
  hash := toyHash
  Signed := toySigned
  sigSound := toySigSound
  hashCR := toyHashCR

/-- A toy update: who signed, the content word, the toy signature, and the claimed digest. -/
structure ToyUpdate where
  signer : Nat
  content : Nat
  sig : Nat
  contentHash : Nat
deriving DecidableEq, Repr

/-- The toy trusted state: the single trusted signer key. -/
structure ToyState where
  trustedKey : Nat
deriving DecidableEq, Repr

/-- **The toy RULES.** Accept iff the signer is the trusted key, the toy signature verifies
(`toyLeaf.sigVerify` — load-bearing: `noForgery` reads `sigSound` from it), AND the claimed
digest matches the hash of the content (`toyLeaf.hash` — load-bearing via `hashCR`). -/
def toyVerify (ts : ToyState) (u : ToyUpdate) : Bool :=
  (u.signer == ts.trustedKey)
    && toySigVerify u.signer u.content u.sig
    && (toyHash u.content == u.contentHash)

/-- **The toy foreign-validity predicate** (the chain's OWN notion of a valid update): the
content was genuinely signed by the trusted key AND the claimed digest is the real hash. Both
conjuncts are non-trivial — `Signed` is `signer = 7` (false for a forged signer) and the digest
binding discriminates. -/
def toyForeignValid (u : ToyUpdate) : Prop :=
  toySigned u.signer u.content ∧ toyHash u.content = u.contentHash

/-- The empty / uninitialized update — signer `0` (not the trusted key), zero everything. -/
def toyEmptyUpdate : ToyUpdate := ⟨0, 0, 0, 0⟩

/-- **NO FORGERY (toy).** A verify-accepted update is foreign-valid. The proof USES the crypto
leaf: `toyLeaf.sigSound` turns the verifying signature into `signer = 7` (the `Signed`
denotation); the digest conjunct comes from the hash-match check. This is the "IF the crypto
leaf is sound THEN the rules are sound" shape, discharged. -/
theorem toyNoForgery : NoForgery toyVerify toyForeignValid := by
  intro ts u h
  unfold toyVerify at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨_hsigner, hsig⟩, hhash⟩ := h
  refine ⟨?_, ?_⟩
  · -- signature soundness leaf ⟹ the content was genuinely signed by key 7
    exact toyLeaf.sigSound u.signer u.content u.sig hsig
  · -- the hash-match check ⟹ the claimed digest is the real hash
    exact beq_iff_eq.mp hhash

/-- **FAIL CLOSED (toy).** The empty update is rejected for EVERY trusted state — the toy
signature `toyLeaf.sigVerify 0 0 0` fails (`0 ≠ 7`), so the `&&`-chain is `false` regardless of
`ts`. The Nomad-law default. -/
theorem toyFailClosed : FailClosed toyVerify toyEmptyUpdate := by
  intro ts
  simp [toyVerify, toyEmptyUpdate, toySigVerify, toyHash]

/-- **NON-VACUOUS (toy).** `toyVerify` accepts a genuine update (signer `7`, sig `10 = 7+3`,
digest `3`) and REJECTS a forged one (signer `3 ≠ 7`) under the SAME trusted state — it
discriminates. -/
theorem toyNonVacuous : NonVacuous toyVerify :=
  ⟨⟨7⟩, ⟨7, 3, 10, 3⟩, ⟨3, 3, 6, 3⟩, by decide, by decide⟩

/-- **The toy `ForeignLightClient`** — the shape is inhabitable: all three theorem obligations
discharge. This is the template a per-chain Fable copies (swap `toyLeaf` → ed25519/BLS, the toy
rules → the real sync-committee / Tower-BFT / Tendermint rules). -/
def toyClient : ForeignLightClient where
  leaf := toyLeaf
  Update := ToyUpdate
  TrustedState := ToyState
  ForeignValid := toyForeignValid
  verify := toyVerify
  emptyUpdate := toyEmptyUpdate
  noForgery := toyNoForgery
  failClosed := toyFailClosed
  nonVacuous := toyNonVacuous

/-! ## §6 — The toy DISCRIMINATORS bite (the load-bearing teeth), on concrete data. -/

/-- **TRUE side.** The genuine update is foreign-valid (signed by key `7`, digest matches). -/
theorem toy_valid_holds : toyForeignValid ⟨7, 3, 10, 3⟩ := ⟨rfl, rfl⟩

/-- **FORGED-SIGNER DISCRIMINATOR.** An update from signer `3` is NOT foreign-valid — the
`Signed` denotation (`signer = 7`) fails. The crypto leaf is what separates them. -/
theorem toy_forged_signer_invalid : ¬ toyForeignValid ⟨3, 3, 6, 3⟩ := by
  rintro ⟨hsigned, _⟩
  exact absurd (show (3 : Nat) = 7 from hsigned) (by decide)

/-- **TAMPERED-DIGEST DISCRIMINATOR.** An update whose claimed digest (`99`) is not the real
hash of its content (`3`) is NOT foreign-valid — the hash binding fails. -/
theorem toy_tampered_digest_invalid : ¬ toyForeignValid ⟨7, 3, 10, 99⟩ := by
  rintro ⟨_, hhash⟩
  exact absurd hhash (by decide)

/-- **THE DISCRIMINATOR, ASSEMBLED.** `toyVerify` accepts the genuine update, rejects the forged
signer, rejects the tampered digest, and rejects the empty update — all under the SAME trusted
state. The rules are not a `True`-carrier. -/
theorem toy_gate_discriminates :
    toyVerify ⟨7⟩ ⟨7, 3, 10, 3⟩ = true
    ∧ toyVerify ⟨7⟩ ⟨3, 3, 6, 3⟩ = false
    ∧ toyVerify ⟨7⟩ ⟨7, 3, 10, 99⟩ = false
    ∧ toyVerify ⟨7⟩ toyEmptyUpdate = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §7 — The composition, on the toy client — a verified light client discharges the adapter.

Build the `InterchainAdapter` the toy client produces (`inclusion` = "the event's claimed
height equals the update's content"), and witness the discharge end-to-end: the adapter accepts
the genuine confirmation, and that acceptance ENTAILS foreign validity — while the empty update
is rejected at the adapter boundary. -/

/-- The toy inclusion relation: a lock confirmation (its claimed content) matches the update. -/
def toyIncl : Nat → ToyUpdate → Prop := fun ev u => ev = u.content

/-- The adapter the toy client produces at trusted state `⟨7⟩`. -/
def toyAdapter : Metatheory.Bridge.InterchainAdapter ToyUpdate Nat :=
  toAdapter toyClient ⟨7⟩ toyIncl

/-- **END-TO-END DISCHARGE.** The toy adapter ACCEPTS the confirmation (there is a verify-final
update including it), and by the discharge that acceptance yields a FOREIGN-VALID update — the
adapter's finality assumption is backed by the verified rules, not assumed. -/
theorem toy_adapter_accepts_and_discharges :
    toyAdapter.accepts 3
    ∧ ∃ u, toyForeignValid u ∧ toyIncl 3 u := by
  have hacc : toyAdapter.accepts 3 :=
    ⟨⟨7, 3, 10, 3⟩, (by decide : toyVerify ⟨7⟩ ⟨7, 3, 10, 3⟩ = true), rfl⟩
  exact ⟨hacc, toAdapter_accepts_entails_valid toyClient ⟨7⟩ toyIncl 3 hacc⟩

/-- **THE EMPTY UPDATE IS REJECTED at the toy adapter boundary** — `FailClosed` lifted. -/
theorem toy_adapter_rejects_empty : ¬ toyAdapter.foreignFinal toyClient.emptyUpdate :=
  toAdapter_rejects_empty toyClient ⟨7⟩ toyIncl

/-! ### It runs (`#guard`): the toy rules discriminate on concrete data. -/

#guard toyVerify ⟨7⟩ ⟨7, 3, 10, 3⟩ == true
#guard toyVerify ⟨7⟩ ⟨3, 3, 6, 3⟩ == false
#guard toyVerify ⟨7⟩ ⟨7, 3, 10, 99⟩ == false
#guard toyVerify ⟨7⟩ toyEmptyUpdate == false
#guard toySigVerify 7 3 10 == true
#guard toySigVerify 3 3 6 == false

/-! ## §8 — Axiom hygiene — every theorem kernel-clean (CI hard-gate). The toy leaf is PROVED,
so nothing here rests on an unproven crypto assumption; a REAL chain's `noForgery` would rest on
its (visible, named) `leaf.sigSound` field — invisible to `#assert_axioms`, so per-chain lanes
document that named leaf explicitly. -/

#assert_axioms toyNoForgery
#assert_axioms toyFailClosed
#assert_axioms toyNonVacuous
#assert_axioms toAdapter_foreignFinal_discharged
#assert_axioms toAdapter_accepts_entails_valid
#assert_axioms toAdapter_rejects_empty
#assert_axioms toy_valid_holds
#assert_axioms toy_forged_signer_invalid
#assert_axioms toy_tampered_digest_invalid
#assert_axioms toy_gate_discriminates
#assert_axioms toy_adapter_accepts_and_discharges
#assert_axioms toy_adapter_rejects_empty

#print axioms toAdapter_foreignFinal_discharged
#print axioms toy_gate_discriminates

end Dregg2.Bridge.VerifiedLightClient
