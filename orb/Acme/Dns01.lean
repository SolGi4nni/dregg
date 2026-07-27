/-
Acme.Dns01 — the DNS-01 challenge encoding tied to the real digest (RFC 8555 §8.4).

`Acme.Challenge` proves DNS-01 *value correctness* against an abstract `digest`
parameter: whatever the digest is, the responder publishes exactly
`digest(keyAuthorization)` at exactly `_acme-challenge.<domain>`. That is the
right shape for the path/record-name proofs (they must not rest on the crypto).

This module closes the remaining gap: it *instantiates* that abstract digest
with the concrete RFC 8555 §8.4 computation

      TXT value  =  base64url( SHA-256( keyAuthorization ) )

where `SHA-256` is the real, opaque `Crypto.sha256` (the verified crypto seam)
and `base64url` is a named abstract parameter `b64url : ByteArray → Bytes`
— honest, because base64url is a total bijective transcoding whose correctness is
not this module's obligation, and folding it in as a parameter keeps every
theorem here quantified over *every* encoder. The key-authorization octets are
the UTF-8 bytes of `token ‖ "." ‖ thumbprint`, matching what a CA hashes.

The validator recomputes the expected TXT value and compares it to the record it
read (§8.4: "The client... the server queries ... and verifies the TXT record").
This is the model's stand-in for the CA's DNS lookup, folded into the FSM's named
`validate : Challenge → Bool` interface from `Acme.Challenge`.

Theorems:
  * `dns01_txt_record` — the published TXT value *is* `base64url(SHA-256(keyAuth))`,
    with the real `Crypto.sha256`. The RFC §8.4 encoding, made concrete.
  * `dns01_hash_len` — the hashed value is exactly 32 bytes (uses the named crypto
    assumption `Crypto.Assumptions.sha256_len`; the digest fed to base64url is a
    genuine SHA-256 output).
  * `dns01_validates` — a *correct* published record (equal to the expected value)
    drives a processing challenge to `valid`.
  * `dns01_rejects_wrong` — a *wrong* published record (unequal) drives it to
    `invalid`; there is no acceptance of a record that is not the digest.
  * `dns01_mutant_alwaysAccept_unsound` — the mutant validator that accepts every
    record reaches `valid` on a record that is NOT the digest: a concrete witness
    that `dns01_rejects_wrong` is load-bearing (the real validator is not that
    mutant).
-/

import Acme.Challenge
import Crypto

namespace Acme

/-! ### The concrete DNS-01 digest (RFC 8555 §8.4)

`base64urlSha256 b64url` is the digest to plug into `Acme.Challenge`'s abstract
DNS-01 machinery. It hashes the UTF-8 octets of the key authorization with the
real `Crypto.sha256` and transcodes the 32-byte result with the supplied
base64url encoder. -/

/-- The RFC 8555 §8.4 DNS-01 digest: `base64url(SHA-256(keyAuthorization))`, with
`Crypto.sha256` the real opaque primitive and `b64url` the base64url encoder as a
named parameter. `ka` is the key-authorization byte string (`List Char`); its
UTF-8 octets are what gets hashed. -/
def base64urlSha256 (b64url : ByteArray → Bytes) (ka : Bytes) : Bytes :=
  b64url (Crypto.sha256 (String.mk ka).toUTF8)

/-- **The DNS-01 TXT value is `base64url(SHA-256(keyAuthorization))`.** Plugging
the concrete digest into `Acme.Challenge`'s `dns01TxtValue`, the value published
at `_acme-challenge.<domain>` is exactly the base64url of the SHA-256 of the key
authorization — RFC 8555 §8.4, with the actual `Crypto.sha256`. -/
theorem dns01_txt_record (b64url : ByteArray → Bytes) (token thumbprint : Bytes) :
    dns01TxtValue (base64urlSha256 b64url) token thumbprint
      = b64url (Crypto.sha256 (String.mk (keyAuthorization token thumbprint)).toUTF8) :=
  rfl

/-- **The hashed value is a genuine 32-byte SHA-256 output.** The bytes handed to
base64url are exactly a 32-byte digest — discharged by the named crypto
assumption `Crypto.Assumptions.sha256_len`, so the DNS-01 value is a real hash,
not an arbitrary blob. -/
theorem dns01_hash_len (token thumbprint : Bytes) :
    (Crypto.sha256 (String.mk (keyAuthorization token thumbprint)).toUTF8).size = 32 :=
  Crypto.Assumptions.sha256_len _

/-! ### The DNS-01 validator, tied into the challenge FSM

The CA validates DNS-01 by querying the TXT record and checking it equals the
expected `base64url(SHA-256(keyAuth))`. `dns01Validator` is that check, in the
shape of the `Acme.Challenge` `validate : Challenge → Bool` interface: it
recomputes the expected value from the challenge's own token and compares it to
the `published` record it read. -/

/-- The DNS-01 validation decision: the record `published` at
`_acme-challenge.<domain>` is accepted exactly when it equals the recomputed
expected value `base64url(SHA-256(keyAuthorization))`. -/
def dns01Validator (b64url : ByteArray → Bytes) (thumbprint published : Bytes)
    (c : Challenge) : Bool :=
  published == dns01TxtValue (base64urlSha256 b64url) c.token thumbprint

/-- **A correct DNS-01 record validates.** A `processing` challenge whose
published record equals the expected `base64url(SHA-256(keyAuth))` reaches
`valid`. -/
theorem dns01_validates {b64url : ByteArray → Bytes} {c : Challenge}
    {thumbprint published : Bytes}
    (hp : c.status = .processing)
    (hmatch : published = dns01TxtValue (base64urlSha256 b64url) c.token thumbprint) :
    (c.validateStep (dns01Validator b64url thumbprint published)).status = .valid := by
  have hval : dns01Validator b64url thumbprint published c = true := by
    simp only [dns01Validator, hmatch, beq_self_eq_true]
  simp only [Challenge.validateStep, hp, hval, Challenge.step]

/-- **A wrong DNS-01 record is rejected.** A `processing` challenge whose
published record differs from the expected value reaches `invalid` — the
validator accepts no record that is not the digest. -/
theorem dns01_rejects_wrong {b64url : ByteArray → Bytes} {c : Challenge}
    {thumbprint published : Bytes}
    (hp : c.status = .processing)
    (hne : published ≠ dns01TxtValue (base64urlSha256 b64url) c.token thumbprint) :
    (c.validateStep (dns01Validator b64url thumbprint published)).status = .invalid := by
  have hf : dns01Validator b64url thumbprint published c = false := by
    simp only [dns01Validator]
    cases h : published == dns01TxtValue (base64urlSha256 b64url) c.token thumbprint with
    | false => rfl
    | true => exact absurd (eq_of_beq h) hne
  exact validateStep_fail_invalid hp hf

/-! ### Mutant: the always-accept validator is unsound

`dns01_rejects_wrong` is not vacuous filler: swap the validator for one that
accepts every record and the DNS-01 check no longer proves domain control. The
witness below publishes a record that is *not* the digest, yet the mutant
validator drives the challenge to `valid`. -/

/-- **The always-accept mutant is unsound.** There is a processing DNS-01
challenge and a published record that is NOT `base64url(SHA-256(keyAuth))`, for
which the mutant validator `fun _ => true` still reaches `valid`. The real
`dns01Validator` (pinned by `dns01_validates` + `dns01_rejects_wrong`) is
therefore not this mutant. -/
theorem dns01_mutant_alwaysAccept_unsound :
    ∃ (b64url : ByteArray → Bytes) (c : Challenge) (thumbprint published : Bytes),
      c.status = .processing ∧
      published ≠ dns01TxtValue (base64urlSha256 b64url) c.token thumbprint ∧
      (c.validateStep (fun _ => true)).status = .valid := by
  refine ⟨fun _ => [], ⟨.dns01, [], [], .processing⟩, [], ['x'], rfl, ?_, rfl⟩
  simp [dns01TxtValue, base64urlSha256]

end Acme
