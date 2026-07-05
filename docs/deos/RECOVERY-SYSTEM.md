# The deos Recovery System

The human-layer recovery story for a sovereign identity: **you cannot lose your
own OS**. A person *is* a sovereign identity cell. When every device key is
lost, recovery is an M-of-N guardian quorum that **authorizes a key rotation to
a new key** — never a custodian, never a "reset my account" button, never the
reconstruction of a secret. Recovery is a witnessed, cap-gated turn through the
real executor, and its K-of-N authorization is verifiable by a light client that
runs only the verifier.

This document is the durable architecture. It is precise to the code: the proven
foundation is `sdk/tests/identity_social_recovery_e2e.rs`, which welds three
already-green parts into one flow.

---

## 1. The verdict: threshold-signature, not Shamir

deos social recovery uses **DKG'd weighted-threshold BLS (HINTS) + KERI
pre-rotation**. It does *not* use Shamir secret sharing. The distinction is not
cosmetic; it is the difference between a scheme with a single point of
compromise and one without.

**Shamir secret sharing RECONSTRUCTS a secret.**
- At recovery time the shares are combined and the original secret key *exists
  again* in plaintext, in one place, in one moment. That moment is a single
  point of compromise: whoever assembles the shares holds the key.
- The dealer who split the secret *knew it*. There is a moment in the scheme's
  history where one party held the whole secret. (Dealerless variants exist but
  are exactly DKG — see below.)
- It recovers the **OLD** key. The recovered identity speaks with the same
  secret that was lost. If the loss was a compromise, recovery hands the
  attacker's-era key right back.

**Threshold signature AUTHORIZES a rotation.**
- The guardians never reconstruct anything. Each holds a share of a *signing*
  key and emits a *partial signature*; the shares are aggregated into one
  constant-size quorum certificate (QC). The group secret `f(0)` exists only as
  a mathematical object — `Σ_{i∈QUAL} f_i(0)` — and is never materialized
  (`federation/src/dkg.rs`, the JF-DKG finalize).
- With DKG there is **no dealer** who ever held the group secret. Share issuance
  is joint-Feldman: no party ever holds `f(0)`.
- The quorum's job is to **bless a rotation to a NEW key the recovering user
  chooses now**. It is forward-secure: recovery installs a fresh key set,
  re-commits a fresh next-set, and advances the key-event chain. The lost
  (possibly compromised) key is retired, not restored.

So the comparison is:

| | Shamir | Threshold-sig + KERI (deos) |
|---|---|---|
| What happens at recovery | secret reconstructed | rotation **authorized** |
| Single point of compromise | yes (the reassembly) | no |
| Dealer ever holds the secret | yes (or it *is* DKG) | no (DKG: `f(0)` never exists) |
| Key recovered | the OLD key | a NEW key the user picks now |
| Forward-secure | no | yes |
| Is it a witnessed cap-gated turn | n/a (off-protocol) | yes — through the real executor |

**Shamir's one legitimate niche.** Splitting *your own seed across your own
devices* as a self-custody backup is orthogonal to social recovery: there is no
guardian quorum, no trust relationship, no other party. You are dealer and
reconstructor; the "single point of compromise at reassembly" is *you*, which is
acceptable because it was your secret all along. This is a personal backup
convenience, not the recovery protocol, and it never touches the executor or the
identity cell's authority.

---

## 2. The layer map: WHO × HOW × WHEN

Recovery factors into three **orthogonal** teeth. Each maps to real code; each
carries the no-amplification and forward-security properties.

### WHO — the HINTS guardian quorum (authorization)

The *who-may-rotate* decision is a weighted-threshold BLS quorum.

- **Primitive:** `dregg-federation`'s `FederationCommittee` wraps the `hints`
  crate (BLS12-381 + KZG): a quorum certificate is **one** aggregate signature
  regardless of committee size, carrying a SNARK that a weighted threshold
  signed (`federation/src/threshold.rs`). `ThresholdQC::to_bytes` is exactly the
  compressed `hints::Signature` the executor consumes.
- **Executor binding:** the identity cell's `set_state` permission demands
  `Authorization::Custom { vk_hash }`. The `ThresholdSigVerifier`
  (`turn/src/executor/membership_verifier.rs`) deserializes the QC, looks up the
  host-trusted committee for the predicate `commitment`, runs
  `hints::verify_aggregate` (SNARK + final BLS pairing) against the executor's
  recomputed `SigningMessage`, and pins the QC threshold `>= k`.
- **No amplification:** a sub-threshold quorum is *refused*. A 2-of-5 set below
  the 3-of-5 floor cannot even aggregate a certifying QC, and a coerced
  under-weight QC is rejected by the host-pinned floor
  (`sub_threshold_quorum_refused`). A valid QC from the *wrong* committee — an
  attacker who stood up their own guardians — is refused because the verifier
  checks against the host-trusted committee VK, not any committee the prover
  supplies (`wrong_committee_quorum_refused`). Recovery is **empowered, never
  amplified**.

### HOW — KERI pre-rotation (the rotation mechanics)

Independently of *who* authorizes, the `KeyRotationGate` enforces *how* a
rotation must be shaped (`StateConstraint::KeyRotationGate`, defined in
`cell/src/program/types.rs` and evaluated in `cell/src/program/eval.rs`;
kernel semantics in `metatheory/Dregg2/Apps/PreRotation.lean`).

Every key-state event commits to the **digest of the next, unexposed key set**
(`next_keys_digest`). A rotation must:
1. **Exhibit the preimage** of the *committed* next-keys digest against the
   pre-state register (`hash_preimage32(...) == old_fields[d]`). This is the
   forward-security keystone: a thief holding every *current* signing key still
   cannot rotate, because rotation requires the escrowed preimage, not the
   current keys.
2. **Install** the exhibited key-set commitment as current.
3. **Re-commit** a fresh nonzero next-keys digest in the same turn — the forward
   chain advances; the key-event log (KERI KEL) is the receipt stream over the
   two registers.

The gate **deliberately never reads the current key set**
(`rotate_current_keys_irrelevant`, an `rfl` theorem). Holding the current keys
contributes *nothing* toward rotating. This is exactly what lets a recovering
user who holds *no* old device key still rotate: they need only the escrowed
next-set preimage (the rotation credential the council holds) plus the quorum's
blessing. The custody rule is therefore explicit: escrow the next-set preimage
*with the recovery council*, not alongside the current keys.

WHO and HOW are orthogonal: the guardian quorum authorizes the cell's
`set_state` (`Authorization::Custom`); the `KeyRotationGate` independently
enforces the rotation mechanics. Both must pass.

### WHEN — the cooling time-lock (visibility)

The charter carries a `cooling_period`. The gate enforces
`old[last_rotated] + cooling_period <= height` and stamps the new rotation's own
height as the next window's anchor (`cell/src/program/eval.rs`, the
`KeyRotationGate` cooling step; Lean `TemporalAtom.cooledSince`). A rotation is therefore *visible to the
council the whole time*: a recovery cannot complete instantly and silently. The
window gives the genuine holder (or honest guardians) time to observe an
in-progress recovery and contest it. It is a time-lock, not a vote — orthogonal
again to WHO and HOW.

---

## 3. The frontier — what is being built

The proven foundation above is real and green. The following extend it.

- **Guardian-set rotation + proactive share-refresh.** `federation/src/dkg.rs`
  (`reshare_deal` / `ReshareParticipant`) re-shares the *same* `f(0)` to a new
  committee (new size `n'`, new threshold `t'`) via Lagrange-combined sub-shares,
  preserving the group public key. Under the proactive assumption that old
  members *erase* their old shares (a party-local act, requiring zeroization /
  memory hygiene at the holder — no protocol can force deletion), an adversary
  must corrupt `t` members within *one epoch window* rather than across the
  committee's whole lifetime. Honest caveat already in the code: resharing does
  not *revoke* old shares; old `t`-subsets remain valid Shamir points of the
  unchanged secret.

- **Device-pairing ceremony.** The DKG ceremony surface
  (`federation/src/dkg_ceremony.rs`: `RosterEntry`, `SignedCeremonyMsg`,
  `SealedShare`/`seal_share`/`open_share`, `EquivocationEvidence`) is the
  skeleton for adding/replacing a device. Private-share transport is *modeled*
  (HPKE-to-strand-key ciphertext is the placeholder); agreement on `QUAL` rides
  the blocklace's authenticated agreed broadcast (the ceremony-as-cell-app lane).

- **Binding the council commitment INTO the circuit state commitment** — the
  light-client superpower not yet closed. Today `StaticThresholdSigPolicy`
  (`turn/src/executor/membership_verifier.rs`) is **host-trusted**: the
  committee VK + threshold floor are pinned by the host and looked up by the
  predicate `commitment`, so a light client trusts the host's committee table.
  The identity cell *already* pins `charter.council.members_commitment()` into
  `COUNCIL_COMMIT_SLOT` at genesis (`sdk/src/identity.rs`,
  `starbridge-apps/polis/src/lib.rs` `members_commitment`) — a blake3 commitment
  over `(threshold, members…)` (v1) or additionally over member signing keys
  (v2 actor-bound). The frontier is to bind that pinned council commitment into
  the *circuit's* state commitment so the verifier checks the QC against the
  committee the **state itself attests**, removing the host as a trust anchor.

- **HINTS onboarding.** Real DKG genesis (no `generate_test_committee` silent
  setup): stand up a guardian committee through the ceremony, derive the
  `members_commitment`, and register the live committee VK.

---

## 4. The dregg superpower

Recovery is a **witnessed turn**. Its K-of-N authorization is a quorum
certificate that the executor verifies inline: a light client establishes that a
genuine guardian threshold authorized this exact rotation by **running only the
verifier** — `hints::verify_aggregate` over the executor-recomputed signing
message, against the host-pinned (and, at the frontier, state-bound) committee.

No custodian is trusted. No secret is reconstructed. No off-protocol "support
ticket" exists. The QC binds to *exactly* what the executor checks — the
federation id, the turn nonce (the cell's on-ledger replay counter), the
position, and the action's target/method/effects/predicate shape — so a recovery
cannot be replayed, retargeted, or re-shaped. The whole recovery is a single
cap-gated `set_state` whose authority is a verifiable threshold and whose
mechanics are a verifiable pre-rotation. That is what "you cannot lose your own
OS" means, made checkable by anyone with the verifier and none of the keys.

( ◕‿◕ )  *the quorum blesses, the chain advances, the old key sleeps.*
