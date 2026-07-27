import Control.Ts2021Core
import Util.ByteArrayAlg
/-!
# Control.Ts2021Transcript — the two ends reach the SAME transcript, PROVEN

`Control/Channel.lean` §2b named this residual: the byte-exact ts2021 channel
FSM lands both peers in `.up`, but that the initiator's and the responder's
Noise transcripts *coincide* — same `Sym.h`, same `Sym.material` — was only
**demonstrated** by `control-ts2021-channel-kat` on one set of real keys, not
proven. This module discharges that residual as a real theorem over the
byte-exact core in `Control.Ts2021Core`, for ALL well-formed handshakes.

## What the proof rests on (all explicit, nothing hidden)

The transcript is `Wireguard.Blake2s.hash` folded over concatenated
`ByteArray`s, and the responder recovers the fields by `ByteArray.extract`.
Three things are needed, and each is stated where it can be seen:

1. **The byte algebra** — `Util.ByteArrayAlg` (plus Lean 4.30 core's own
   `ByteArray` `++`/`extract` lemmas): the responder's `extract` at the
   fixed offsets returns exactly the fields the initiator concatenated.
2. **AEAD correctness** — `Crypto.Assumptions.chacha_open_seal_roundtrip`, an
   EXISTING axiom of the crypto seam (HACL*/EverCrypt-discharged). No new axiom
   is introduced by this module.
3. **Explicit hypotheses**, carried in every statement below:
   * field sizes (`eiPub.size = 32`, `siPub.size = 32`, `erPub.size = 32`) —
     the X25519 public-key length;
   * `aeadExpands` — the ChaCha20-Poly1305 ciphertext-expansion law
     (`|ct| = |pt| + 16`). This is a true property of the AEAD but is NOT among
     the axioms in `Crypto.Assumptions`, so it is taken as an explicit
     hypothesis rather than silently added to the trust surface. The responder
     needs it to know the encrypted static field is 48 bytes and so to slice at
     offset 80;
   * the two Diffie-Hellman agreements per message. `§4` derives these from the
     EXISTING `Crypto.Assumptions.x25519_dh_agree` axiom given that each public
     key is the base-point image of its scalar, so on the real wire they are
     discharged, not assumed.

Nothing is assumed about BLAKE2s beyond it being a function: the transcripts
coincide because the two ends hash *the same byte sequences in the same order*,
which is what is proven. No collision-resistance is used or needed here.
-/

namespace Control.Ts2021Wire

open Control.Channel (bytesOf baOf)

/-! ## §1  The AEAD step coincides

Noise's `EncryptAndHash` on the sender and `DecryptAndHash` on the receiver
must leave the SAME symmetric state. They do, definitionally, once the AEAD
round-trips: both mix the *ciphertext* into `h` and both bump `n`. -/

/-- **The sender's `EncryptAndHash` and the receiver's `DecryptAndHash` agree.**
Given the ciphertext the sender produced, the receiver recovers the plaintext
AND lands in the identical symmetric state. -/
theorem decryptAndHash_encryptAndHash {s s' : Sym} {pt ct : ByteArray}
    (h : s.encryptAndHash pt = some (ct, s')) :
    s.decryptAndHash ct = some (pt, s') := by
  unfold Sym.encryptAndHash at h
  unfold Sym.decryptAndHash
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · split at h
    · rename_i c hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [Crypto.Assumptions.chacha_open_seal_roundtrip _ _ _ _ _ hc]
    · exact absurd h (by simp)

/-! ## §2  The initiation transcript coincides

The initiator emits `eiPub ‖ enc(siPub) ‖ enc(payload)` (32 ‖ 48 ‖ n). The
responder slices at 0/32/80 and runs the mirrored Noise steps. -/

/-- The ChaCha20-Poly1305 ciphertext-expansion law, as an explicit hypothesis.
See the module header: a true AEAD property, deliberately NOT added to
`Crypto.Assumptions`, so callers see the dependency. -/
abbrev AeadExpands : Prop :=
  ∀ (k n ad pt ct : ByteArray), Crypto.chachaSeal k n ad pt = some ct → ct.size = pt.size + 16

set_option maxHeartbeats 2000000 in
/-- **The responder reproduces the initiator's post-initiation transcript.**
Reading the initiation the initiator built recovers the initiator's ephemeral
public key, its static public key and the payload EXACTLY, and lands the
responder in the *identical* Noise symmetric state `sI` — same `ck`, same
transcript hash `h`, same key, same counter. -/
theorem readInitiation_noiseInitiation
    {prologue siPriv siPub eiPriv eiPub rsPub srPriv payload noiseMsg : ByteArray} {sI : Sym}
    (aeadExpands : AeadExpands)
    (hei : eiPub.size = 32) (hsi : siPub.size = 32)
    (hdhes : Crypto.x25519 srPriv eiPub = Crypto.x25519 eiPriv rsPub)
    (hdhss : Crypto.x25519 srPriv siPub = Crypto.x25519 siPriv rsPub)
    (hInit : noiseInitiation prologue siPriv siPub eiPriv eiPub rsPub payload
               = some (noiseMsg, sI)) :
    readInitiation prologue srPriv rsPub noiseMsg = some (eiPub, siPub, payload, sI) := by
  unfold noiseInitiation at hInit
  dsimp only at hInit
  split at hInit
  · exact absurd hInit (by simp)
  · rename_i dhes hes
    split at hInit
    · exact absurd hInit (by simp)
    · rename_i encS s2 hE1
      split at hInit
      · exact absurd hInit (by simp)
      · rename_i dhss hss
        split at hInit
        · exact absurd hInit (by simp)
        · rename_i encP s4 hE2
          simp only [Option.some.injEq, Prod.mk.injEq] at hInit
          obtain ⟨rfl, rfl⟩ := hInit
          -- the encrypted static field is 48 B: 32-byte key + 16-byte tag
          have hencS : encS.size = 48 := by
            unfold Sym.encryptAndHash at hE1
            split at hE1
            · rename_i hk; simp [Sym.mixKey] at hk
            · split at hE1
              · rename_i c hc
                simp only [Option.some.injEq, Prod.mk.injEq] at hE1
                obtain ⟨rfl, _⟩ := hE1
                rw [aeadExpands _ _ _ _ _ hc, hsi]
              · exact absurd hE1 (by simp)
          -- the byte algebra: the responder slices ARE the initiator fields
          unfold readInitiation
          rw [show (eiPub ++ encS ++ encP).extract 0 32 = eiPub from
                ByteArray.extract_split3_fst eiPub encS encP hei,
              ByteArray.extract_split3_snd' eiPub encS encP hei hencS (by omega),
              ByteArray.extract_split3_thd' eiPub encS encP hei hencS (by omega)]
          dsimp only
          rw [hdhes, hes]
          dsimp only
          rw [decryptAndHash_encryptAndHash hE1]
          dsimp only
          rw [hdhss, hss]
          dsimp only
          rw [decryptAndHash_encryptAndHash hE2]

/-! ## §3  The response transcript coincides

The responder emits `erPub ‖ enc(payload)` (32 ‖ n); the initiator slices at
0/32. No expansion law is needed here — the tail is the whole remainder. -/

set_option maxHeartbeats 2000000 in
/-- **The initiator reproduces the responder's post-response transcript.**
Reading the response the responder built recovers the payload EXACTLY and lands
the initiator in the *identical* final Noise state — hence the same
`Sym.material`, i.e. the same 64-byte `Split()` output. -/
theorem readResponse_noiseResponse
    {s0 sR : Sym} {erPriv erPub eiPriv eiPub siPriv siPub payload respMsg : ByteArray}
    (her : erPub.size = 32)
    (hdhee : Crypto.x25519 eiPriv erPub = Crypto.x25519 erPriv eiPub)
    (hdhse : Crypto.x25519 siPriv erPub = Crypto.x25519 erPriv siPub)
    (hResp : noiseResponse s0 erPriv erPub eiPub siPub payload = some (respMsg, sR)) :
    readResponse s0 eiPriv siPriv respMsg = some (payload, sR) := by
  unfold noiseResponse at hResp
  dsimp only at hResp
  split at hResp
  · exact absurd hResp (by simp)
  · rename_i dhee hee
    split at hResp
    · exact absurd hResp (by simp)
    · rename_i dhse hse
      split at hResp
      · exact absurd hResp (by simp)
      · rename_i encP s4 hE
        simp only [Option.some.injEq, Prod.mk.injEq] at hResp
        obtain ⟨rfl, rfl⟩ := hResp
        unfold readResponse
        rw [show (erPub ++ encP).extract 0 32 = erPub from
              ByteArray.extract_split2_fst erPub encP her,
            show (erPub ++ encP).extract 32 (erPub ++ encP).size = encP from
              ByteArray.extract_split2_snd erPub encP her]
        dsimp only
        rw [hdhee, hee]
        dsimp only
        rw [hdhse, hse]
        dsimp only
        rw [decryptAndHash_encryptAndHash hE]

/-! ## §4  Discharging the DH hypotheses from the EXISTING X25519 axiom

On the real wire each public key is the base-point image of its scalar. Then the
four DH agreements above are consequences of
`Crypto.Assumptions.x25519_dh_agree` — they are not extra assumptions. -/

theorem dh_es (hei : Crypto.x25519Base eiPriv = some eiPub)
    (hsr : Crypto.x25519Base srPriv = some rsPub) :
    Crypto.x25519 srPriv eiPub = Crypto.x25519 eiPriv rsPub :=
  (Crypto.Assumptions.x25519_dh_agree _ _ _ _ hei hsr).symm

theorem dh_ss (hsi : Crypto.x25519Base siPriv = some siPub)
    (hsr : Crypto.x25519Base srPriv = some rsPub) :
    Crypto.x25519 srPriv siPub = Crypto.x25519 siPriv rsPub :=
  (Crypto.Assumptions.x25519_dh_agree _ _ _ _ hsi hsr).symm

/-! ## §5  THE TRANSCRIPT COINCIDENCE — the §2b residual, discharged

The full handshake: the initiator builds the initiation, the responder reads it
and builds the response, the initiator reads that. Both ends end on the SAME
final symmetric state — hence the same transcript hash and the same 64-byte
split material, which is exactly the hypothesis
`Control.Channel.Ts2021.keys_agree_of_material` consumes. -/

set_option maxHeartbeats 2000000 in
/-- **THE TRANSCRIPT COINCIDENCE.** For ANY well-formed ts2021 handshake: the
responder's read of the initiation reproduces the initiator's post-initiation
Noise state *exactly* (`sI`), and the initiator's read of the response
reproduces the responder's FINAL state *exactly* (`sR`) — so both ends end on
the same transcript hash `Sym.h` and the same 64-byte `Sym.material`, which is
precisely what `Control.Channel.Ts2021.keys_agree_of_material` consumes.

Note what is NOT assumed: the two `read` results are **conclusions**, not
hypotheses. The only inputs are that the initiator built the initiation, that
the responder answered it, the AEAD expansion law, the X25519 public-key
lengths, and that each public key is its scalar's base-point image (from which
all four DH agreements are DERIVED via the existing `x25519_dh_agree` axiom). -/
theorem transcripts_coincide
    {prologue siPriv siPub eiPriv eiPub srPriv rsPub erPriv erPub : ByteArray}
    {plI plR noiseMsg respMsg : ByteArray} {sI sR : Sym}
    (aeadExpands : AeadExpands)
    -- public keys are the base-point images of their scalars
    (bEi : Crypto.x25519Base eiPriv = some eiPub)
    (bSi : Crypto.x25519Base siPriv = some siPub)
    (bSr : Crypto.x25519Base srPriv = some rsPub)
    (bEr : Crypto.x25519Base erPriv = some erPub)
    -- X25519 public keys are 32 bytes
    (hei : eiPub.size = 32) (hsi : siPub.size = 32) (her : erPub.size = 32)
    -- the initiator builds the initiation; the responder answers it
    (hInit : noiseInitiation prologue siPriv siPub eiPriv eiPub rsPub plI
               = some (noiseMsg, sI))
    (hResp : noiseResponse sI erPriv erPub eiPub siPub plR = some (respMsg, sR)) :
    -- (1) the responder lands in the initiator's EXACT post-initiation state
    readInitiation prologue srPriv rsPub noiseMsg = some (eiPub, siPub, plI, sI)
    -- (2) the initiator lands in the responder's EXACT final state
    ∧ readResponse sI eiPriv siPriv respMsg = some (plR, sR)
    -- (3) hence whatever final state the initiator reaches, its transcript hash
    --     and its 64-byte split material are the responder's
    ∧ ∀ sI', readResponse sI eiPriv siPriv respMsg = some (plR, sI') →
        sI' = sR ∧ sI'.h = sR.h ∧ sI'.material = sR.material := by
  have hR : readResponse sI eiPriv siPriv respMsg = some (plR, sR) :=
    readResponse_noiseResponse her
      (Crypto.Assumptions.x25519_dh_agree _ _ _ _ bEi bEr)
      (Crypto.Assumptions.x25519_dh_agree _ _ _ _ bSi bEr) hResp
  refine ⟨readInitiation_noiseInitiation aeadExpands hei hsi
            (dh_es bEi bSr) (dh_ss bSi bSr) hInit, hR, ?_⟩
  intro sI' hI'
  rw [hR] at hI'
  simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hI'
  subst hI'
  exact ⟨rfl, rfl, rfl⟩

/-! ## §6  Axiom ledger -/

#print axioms decryptAndHash_encryptAndHash
#print axioms readInitiation_noiseInitiation
#print axioms readResponse_noiseResponse
#print axioms transcripts_coincide

end Control.Ts2021Wire
