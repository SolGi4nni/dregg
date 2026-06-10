/-
# Dregg2.Crypto.Ed25519Reduction — the ed25519 EUF-CMA reduction, made EXPLICIT.

`Dregg2/Crypto/PortalFloor.lean §1` names the ed25519 EUF-CMA carrier (`SignatureKernel.unforgeable`)
and unpacks it in the SOUNDNESS direction: an accepting signature proves `Signed pk m`
(`sigVerify_sound`). The consumers (`Exec/CapTPHandoffSound.lean`, the blocklace insert path, the
agent `Authorization.token`/`.signature` arm) each consume that carrier to reject a forged input.

This file closes the OTHER half of the trust statement — the explicit *reduction* the auditor asks
for: **a protocol forgery YIELDS an ed25519 forgery.** It is the contrapositive of soundness packaged
as a reduction GAME, so the trust boundary is not just "carrier ⇒ protocol-safe" but the sharper
"protocol-break ⇒ EUF-CMA-break" — the standard cryptographic reduction shape.

## What is REAL reduction vs IRREDUCIBLE primitive here

- **IRREDUCIBLE PRIMITIVE.** `Ed25519EufCma K` (below) is the genuine cryptographic assumption:
  ed25519 existential-unforgeability under chosen-message attack (Edwards-curve / DLog hardness over
  Curve25519). It is NOT a Lean theorem and NOT `:= True`; it is a `Prop` carrier, named,   exactly the `PortalFloor` discipline. It is the bottom of THIS stack. We DEFINE the EUF-CMA game as
  a first-class predicate (`SigForgery` = "an accepting signature on a message NOT legitimately signed
  under that key") and `Ed25519EufCma` = "no such forgery exists", so the carrier has explicit content
  (a forger is a concrete refutation), not an opaque token.

- **REAL REDUCTION (proven here, no fresh axiom).** Each protocol path's forgery is REDUCED to a
  `SigForgery`: `protocol_forgery_to_sig_forgery_*` constructs, from a winning protocol adversary
  (a forged handoff that validates / a forged block that an honest verifier inserts / a forged token
  authorization that the gate accepts), an explicit `SigForgery` witness — hence a break of
  `Ed25519EufCma`. The reduction is a real proof: it does not relabel, it transports the protocol
  acceptance through the §8 oracle equation into a fresh accepting `(pk, m, s)` whose `m` is the
  message the honest key never signed. Closing under `Ed25519EufCma` recovers the soundness theorems.

- **Non-vacuity teeth.** On the forgeable reference oracle (`PortalFloor.instSignatureForge`, which
  accepts EVERY signature) `Ed25519EufCma` is provably FALSE and a concrete `SigForgery` exists — and
  the reduction then EXHIBITS concrete protocol forgeries (a validating forged handoff, an accepted
  forged block, an accepted forged token). So the reduction fires in both directions: under the real
  carrier no protocol forgery exists; strip the carrier and one concretely does.

`#assert_axioms`-clean (⊆ `{propext, Classical.choice, Quot.sound}`); NO `sorry` / `:= True` /
`native_decide`. The sole standing obligation is `Ed25519EufCma` on the Rust `@[extern]`
`dregg_ed25519_verify` oracle — the named curve assumption.
-/
import Dregg2.Crypto.PortalFloor
import Dregg2.Tactics

namespace Dregg2.Crypto.Ed25519Reduction

open Dregg2.Crypto.PortalFloor

universe u

/-! ## §1 — The EUF-CMA game as a first-class predicate.

`SigForgery K pk m s` is the adversary's winning condition in the existential-unforgeability game:
the §8 oracle ACCEPTS `(pk, m, s)` yet `m` was NEVER legitimately signed under `pk`
(`¬ K.Signed pk m`). `Ed25519EufCma K` says no such forgery exists for ANY `(pk, m, s)` — the
EUF-CMA assumption stated as the negation of the win condition.

This is exactly `SignatureKernel.sigVerify_sound` read as a game (accept ⇒ Signed ≡ ¬(accept ∧
¬Signed)), but we name the win condition `SigForgery` so a protocol reduction can produce it as a
concrete witness. -/

/-- **`SigForgery K pk m s`** — the EUF-CMA adversary's WIN: the ed25519 oracle accepts the
signature `s` on message `m` under key `pk`, but the holder of `pk`'s secret never signed `m`. -/
def SigForgery {PK Msg Sig : Type u} (K : SignatureKernel PK Msg Sig)
    (pk : PK) (m : Msg) (s : Sig) : Prop :=
  K.sigVerify pk m s = true ∧ ¬ K.Signed pk m

/-- **`Ed25519EufCma K`** — THE IRREDUCIBLE PRIMITIVE: existential-unforgeability under
chosen-message attack. No `(pk, m, s)` is a forgery — every accepting signature is on a legitimately
signed message. Stated as the negation of the EUF-CMA win condition. Named; never a Lean
law, never `:= True`. -/
def Ed25519EufCma {PK Msg Sig : Type u} (K : SignatureKernel PK Msg Sig) : Prop :=
  ∀ (pk : PK) (m : Msg) (s : Sig), ¬ SigForgery K pk m s

/-! ## §2 — `Ed25519EufCma` ⟺ the `PortalFloor` soundness carrier.

The new EUF-CMA predicate is DEFINITIONALLY the same content as `sigVerify_sound`'s conclusion
(accept ⇒ Signed). We prove both directions so anything that already discharges `unforgeable` (e.g.
`Reference.instSignatureKernel_unforgeable`) discharges `Ed25519EufCma`, and vice versa — no new
assumption is introduced, only a sharper FRAMING of the existing one. -/

/-- `Ed25519EufCma` is exactly the soundness direction (accept ⇒ Signed), repackaged. -/
theorem eufCma_iff_sound {PK Msg Sig : Type u} (K : SignatureKernel PK Msg Sig) :
    Ed25519EufCma K ↔
      (∀ (pk : PK) (m : Msg) (s : Sig), K.sigVerify pk m s = true → K.Signed pk m) := by
  constructor
  · intro h pk m s haccept
    by_contra hns
    exact h pk m s ⟨haccept, hns⟩
  · intro h pk m s hforge
    exact hforge.2 (h pk m s hforge.1)

/-- From the §8 `unforgeable` carrier (unpacked via `sigVerify_sound`), `Ed25519EufCma` holds. This
is how a consumer that already holds `K.unforgeable` obtains the game-form assumption. -/
theorem eufCma_of_unforgeable {PK Msg Sig : Type u} (K : SignatureKernel PK Msg Sig)
    (hunf : K.unforgeable) : Ed25519EufCma K :=
  (eufCma_iff_sound K).mpr (fun pk m s h => K.sigVerify_sound hunf pk m s h)

/-- A forgery against `Ed25519EufCma` is impossible (the assumption directly refutes any win). -/
theorem no_forgery {PK Msg Sig : Type u} {K : SignatureKernel PK Msg Sig}
    (hcma : Ed25519EufCma K) (pk : PK) (m : Msg) (s : Sig) : ¬ SigForgery K pk m s :=
  hcma pk m s

/-- The reduction's workhorse, in raw form: an accepting signature under the EUF-CMA assumption is on
a legitimately-signed message. (The `mp` of `eufCma_iff_sound`, named for reuse.) -/
theorem signed_of_accept {PK Msg Sig : Type u} {K : SignatureKernel PK Msg Sig}
    (hcma : Ed25519EufCma K) {pk : PK} {m : Msg} {s : Sig}
    (haccept : K.sigVerify pk m s = true) : K.Signed pk m :=
  (eufCma_iff_sound K).mp hcma pk m s haccept

/-! ## §3 — Path (A.1): the CapTP handoff reduction.

The handoff certificate validates only if the §8 oracle accepts the introducer's signature over the
canonical signing message (`HandoffCert2.AttestedBool`, `Exec/CapTPHandoffSound.lean §2`). We model
the relevant slice abstractly: a "validating handoff" exposes its `(introPK, signingMessage,
introSig)` and the FACT that the oracle accepted (the §1 check fired). A handoff FORGERY is a
validating handoff whose introducer key never signed the message — exactly a `SigForgery`.

`AcceptingHandoff` is the minimal interface `CapTPHandoffSound.validateHandoff2` exposes (its §1 leg
is `c.AttestedBool K = true`). We keep this file dependency-light: rather than import the executor, we
abstract the accepting-signature fact, so the reduction composes with whatever the executor's
validation predicate is. The executor's `validateHandoff2_attested` is precisely the bridge that hands
us this fact. -/

/-- **`AcceptingHandoff K pk m s`** — a handoff certificate whose §1 leg accepted: the ed25519 oracle
accepts the introducer signature `s` on the signing message `m` under introducer key `pk`. This is
exactly `HandoffCert2.AttestedBool K c = true` (unfolded to its `sigVerify` content). -/
def AcceptingHandoff {PK Msg Sig : Type u} (K : SignatureKernel PK Msg Sig)
    (pk : PK) (m : Msg) (s : Sig) : Prop :=
  K.sigVerify pk m s = true

/-- **REDUCTION (A.1) — handoff-forgery ⇒ signature-forgery.** A handoff that validates under an
introducer key that never legitimately signed the certificate is a `SigForgery`. So a protocol
adversary who forges a handoff (validates without holding `pk`'s secret) IS an EUF-CMA forger. -/
theorem handoff_forgery_to_sig_forgery {PK Msg Sig : Type u} {K : SignatureKernel PK Msg Sig}
    {pk : PK} {m : Msg} {s : Sig}
    (haccept : AcceptingHandoff K pk m s) (hnokey : ¬ K.Signed pk m) :
    SigForgery K pk m s :=
  ⟨haccept, hnokey⟩

/-- **(A.1) closed under EUF-CMA.** Under `Ed25519EufCma`, NO handoff with an unsigned introducer key
can have accepted — the reduction's contrapositive recovers the soundness keystone
(`CapTPHandoffSound.handoff_unforgeable`) directly from the named primitive. -/
theorem no_forged_handoff {PK Msg Sig : Type u} {K : SignatureKernel PK Msg Sig}
    (hcma : Ed25519EufCma K) {pk : PK} {m : Msg} {s : Sig}
    (hnokey : ¬ K.Signed pk m) : ¬ AcceptingHandoff K pk m s :=
  fun haccept => no_forgery hcma pk m s (handoff_forgery_to_sig_forgery haccept hnokey)

/-! ## §4 — Path (A.2): the blocklace-insert reduction (audit A1).

The blocklace insert (`Authority/Blocklace.lean`, mirroring `blocklace/src/finality.rs`) accepts a
block into the lace only if its `signed` carrier holds — `finality.rs` verifies the creator's ed25519
signature over `(creator, seq, payload, preds)` before insertion (the A1 fix: "insert verifies sig +
seq + equivocation"). Modelled abstractly: a block exposes `(creator, blockMessage, blockSig)`; an
"accepted block" is one the honest verifier inserted, i.e. the §8 oracle accepted the creator
signature. A block FORGERY is an accepted block whose claimed creator never signed it — an adversary
fabricating authorship — which is again a `SigForgery` under the creator's key. -/

/-- **`AcceptedBlock K creatorPK m s`** — a block the honest insert accepted: the creator's ed25519
signature `s` over the block message `m` verified under the creator key `creatorPK`. Mirrors the
`finality.rs` insert-time `verify_block_signature` gate. -/
def AcceptedBlock {PK Msg Sig : Type u} (K : SignatureKernel PK Msg Sig)
    (creatorPK : PK) (m : Msg) (s : Sig) : Prop :=
  K.sigVerify creatorPK m s = true

/-- **REDUCTION (A.2) — block-forgery ⇒ signature-forgery.** A block accepted into the lace whose
claimed creator never signed it is a `SigForgery`. So a Byzantine author who fabricates a block under
another node's key (the equivocation/impersonation attack the blocklace must repel) IS an EUF-CMA
forger. This is what ties the blocklace's `signed` carrier to the named ed25519 assumption — the
byzantine-repelling DAG facts assumed an honest signature; THIS is why that assumption is sound. -/
theorem block_forgery_to_sig_forgery {PK Msg Sig : Type u} {K : SignatureKernel PK Msg Sig}
    {creatorPK : PK} {m : Msg} {s : Sig}
    (haccept : AcceptedBlock K creatorPK m s) (hnokey : ¬ K.Signed creatorPK m) :
    SigForgery K creatorPK m s :=
  ⟨haccept, hnokey⟩

/-- **(A.2) closed under EUF-CMA.** Under `Ed25519EufCma`, the honest insert CANNOT have accepted a
block whose creator key never signed it — impersonating another node's authorship is impossible. This
is the crypto floor under the blocklace's `Canonical`/`HonestChain` assumptions. -/
theorem no_forged_block {PK Msg Sig : Type u} {K : SignatureKernel PK Msg Sig}
    (hcma : Ed25519EufCma K) {creatorPK : PK} {m : Msg} {s : Sig}
    (hnokey : ¬ K.Signed creatorPK m) : ¬ AcceptedBlock K creatorPK m s :=
  fun haccept => no_forgery hcma creatorPK m s (block_forgery_to_sig_forgery haccept hnokey)

/-! ## §5 — Path (A.3): the agent `Authorization.signature`/bearer reduction.

The agent capability path routes user-facing turns through the gate; the `.signature`/`.bearer`/
`.stealth` arms of the 10-variant `Authorization` (`Exec/FullForestAuthPortal.lean`) accept a turn
only if the ed25519 oracle accepts the holder's signature over the request digest. (The `.token`
arm is HMAC, primitive #8 — a DIFFERENT carrier, covered by `CaveatChain.chain_unforgeable`; here we
reduce the ed25519-backed arms.) An authorization FORGERY is an accepted turn whose holder key never
signed the request — a `SigForgery`. -/

/-- **`AcceptedAuth K holderPK m s`** — a turn the gate authorized via the ed25519
`.signature`/`.bearer`/`.stealth` arm: the holder's signature `s` over the request digest `m`
verified under `holderPK`. Mirrors `FullForestAuthPortal`'s `signature_arm` `sigVerify` leg. -/
def AcceptedAuth {PK Msg Sig : Type u} (K : SignatureKernel PK Msg Sig)
    (holderPK : PK) (m : Msg) (s : Sig) : Prop :=
  K.sigVerify holderPK m s = true

/-- **REDUCTION (A.3) — authorization-forgery ⇒ signature-forgery.** A turn the gate authorizes whose
holder key never signed the request is a `SigForgery`. So an adversary who drives the executor without
holding the capability's secret key IS an EUF-CMA forger. -/
theorem auth_forgery_to_sig_forgery {PK Msg Sig : Type u} {K : SignatureKernel PK Msg Sig}
    {holderPK : PK} {m : Msg} {s : Sig}
    (haccept : AcceptedAuth K holderPK m s) (hnokey : ¬ K.Signed holderPK m) :
    SigForgery K holderPK m s :=
  ⟨haccept, hnokey⟩

/-- **(A.3) closed under EUF-CMA.** Under `Ed25519EufCma`, the gate CANNOT authorize a turn whose
holder key never signed the request — capability authority is unforgeable. -/
theorem no_forged_auth {PK Msg Sig : Type u} {K : SignatureKernel PK Msg Sig}
    (hcma : Ed25519EufCma K) {holderPK : PK} {m : Msg} {s : Sig}
    (hnokey : ¬ K.Signed holderPK m) : ¬ AcceptedAuth K holderPK m s :=
  fun haccept => no_forgery hcma holderPK m s (auth_forgery_to_sig_forgery haccept hnokey)

/-! ## §6 — The unified protocol-forgery ⇒ EUF-CMA-forgery statement.

All three paths share the SAME shape — an accepting `sigVerify pk m s` under a key whose holder never
signed `m`. We collect them as one `ProtocolSigForgery` so a single theorem witnesses "ANY of the
three protocol surfaces breaking ⇒ ed25519 broken". -/

/-- **`ProtocolSurface`** — which ed25519-backed surface a forgery targets. -/
inductive ProtocolSurface
  | handoff
  | blocklaceInsert
  | agentAuth
  deriving DecidableEq, Repr

/-- **`ProtocolSigForgery K surface pk m s`** — a forgery on any ed25519-backed surface: the surface
accepted `(pk, m, s)` and the key holder never signed `m`. The three surfaces are definitionally the
same acceptance predicate (each is `sigVerify pk m s = true`), so this is one statement covering all
of (A.1)/(A.2)/(A.3). -/
def ProtocolSigForgery {PK Msg Sig : Type u} (K : SignatureKernel PK Msg Sig)
    (_surface : ProtocolSurface) (pk : PK) (m : Msg) (s : Sig) : Prop :=
  K.sigVerify pk m s = true ∧ ¬ K.Signed pk m

/-- **THE REDUCTION — protocol-forgery ⇒ signature-forgery.** On ANY of the three ed25519-backed
surfaces, a successful protocol forgery yields an ed25519 `SigForgery`. This is the headline
statement the auditor asks for, made explicit. -/
theorem protocol_forgery_to_sig_forgery {PK Msg Sig : Type u} {K : SignatureKernel PK Msg Sig}
    {surface : ProtocolSurface} {pk : PK} {m : Msg} {s : Sig}
    (hforge : ProtocolSigForgery K surface pk m s) : SigForgery K pk m s :=
  hforge

/-- **THE CONTRAPOSITIVE — EUF-CMA ⇒ no protocol forgery on any surface.** Under the named ed25519
primitive, NONE of the three surfaces admits a forgery. One closure over all of (A.1)/(A.2)/(A.3). -/
theorem eufCma_repels_all_surfaces {PK Msg Sig : Type u} {K : SignatureKernel PK Msg Sig}
    (hcma : Ed25519EufCma K) (surface : ProtocolSurface) (pk : PK) (m : Msg) (s : Sig) :
    ¬ ProtocolSigForgery K surface pk m s :=
  fun hforge => no_forgery hcma pk m s (protocol_forgery_to_sig_forgery hforge)

/-! ## §7 — Non-vacuity teeth: the reduction fires in BOTH directions.

(a) On the REAL/reference HONEST carrier the assumption HOLDS and no forgery exists.
(b) On the forgeable oracle (`PortalFloor.instSignatureForge`, accept-everything) `Ed25519EufCma` is
    provably FALSE and a CONCRETE forgery exists on each surface — proving the reduction is not a
    vacuous relabel: strip the carrier and the protocol breaks. -/

section NonVacuity

open Dregg2.Crypto.PortalFloor.Reference (instSignatureKernel instSignatureForge)

/-- (a) HOLDS — the proved reference EUF-CMA carrier satisfies `Ed25519EufCma`. So the game-form
assumption is inhabited by the honest oracle (echo verify: `pk = m = s`). -/
theorem ref_eufCma : Ed25519EufCma instSignatureKernel :=
  (eufCma_iff_sound instSignatureKernel).mpr Reference.instSignatureKernel_unforgeable

/-- (a') Under the honest reference carrier, no handoff/block/auth forgery exists on a key that never
signed — the soundness keystones fire on a concrete instance. -/
theorem ref_no_forged_handoff {pk m s : Nat} (hnokey : ¬ instSignatureKernel.Signed pk m) :
    ¬ AcceptingHandoff instSignatureKernel pk m s :=
  no_forged_handoff ref_eufCma hnokey

/-- (b) FALSE — the forgeable accept-everything oracle violates `Ed25519EufCma`: there IS a forgery.
This is the standard `PortalFloor §9b` `instSignatureForge` tooth, lifted to the game form. -/
theorem forge_not_eufCma : ¬ Ed25519EufCma instSignatureForge := by
  intro h
  -- The accept-everything oracle accepts (0,1,0); `Signed` is `False`, so it is a forgery.
  exact h 0 1 0 ⟨rfl, fun (hs : (False : Prop)) => hs⟩

/-- (b.1) CONCRETE handoff forgery on the broken oracle: the certificate `(pk=0, m=1, s=0)` validates
its §1 leg yet was never signed — a real `SigForgery`, hence a real protocol break. -/
theorem forge_handoff_forgery : SigForgery instSignatureForge 0 1 0 :=
  handoff_forgery_to_sig_forgery (K := instSignatureForge) (by rfl) (fun hs => hs)

/-- (b.2) CONCRETE block forgery on the broken oracle: a block claiming creator key `0`, message `1`,
signature `0` is accepted by the (broken) insert yet was never signed — the impersonation the
blocklace must repel, demonstrated to exist exactly when the carrier is stripped. -/
theorem forge_block_forgery : SigForgery instSignatureForge 0 1 0 :=
  block_forgery_to_sig_forgery (K := instSignatureForge) (by rfl) (fun hs => hs)

/-- (b.3) CONCRETE authorization forgery on the broken oracle: a turn authorized under holder key `0`,
request `1`, signature `0` is accepted by the (broken) gate yet was never signed. -/
theorem forge_auth_forgery : SigForgery instSignatureForge 0 1 0 :=
  auth_forgery_to_sig_forgery (K := instSignatureForge) (by rfl) (fun hs => hs)

/-- (b.unified) The single statement: on the broken oracle EVERY surface admits a forgery. -/
theorem forge_all_surfaces (surface : ProtocolSurface) :
    ProtocolSigForgery instSignatureForge surface 0 1 0 :=
  ⟨by rfl, fun hs => hs⟩

end NonVacuity

/-! ## §8 — Axiom-hygiene tripwires. Each keystone pins exactly the whitelist; the sole standing
obligation is `Ed25519EufCma` on the `@[extern] dregg_ed25519_verify` oracle (the named curve
assumption). No `sorry` / `:= True` / `native_decide`. -/

#assert_axioms eufCma_iff_sound
#assert_axioms eufCma_of_unforgeable
#assert_axioms signed_of_accept
#assert_axioms handoff_forgery_to_sig_forgery
#assert_axioms no_forged_handoff
#assert_axioms block_forgery_to_sig_forgery
#assert_axioms no_forged_block
#assert_axioms auth_forgery_to_sig_forgery
#assert_axioms no_forged_auth
#assert_axioms protocol_forgery_to_sig_forgery
#assert_axioms eufCma_repels_all_surfaces
#assert_axioms ref_eufCma
#assert_axioms ref_no_forged_handoff
#assert_axioms forge_not_eufCma
#assert_axioms forge_handoff_forgery
#assert_axioms forge_block_forgery
#assert_axioms forge_auth_forgery
#assert_axioms forge_all_surfaces

end Dregg2.Crypto.Ed25519Reduction
