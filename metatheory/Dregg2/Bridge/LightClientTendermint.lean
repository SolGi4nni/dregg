/-
# Dregg2.Bridge.LightClientTendermint — the VERIFIED Cosmos/Tendermint light-client RULES.

dregg verifies a Cosmos chain by PROOF: this file formalizes the Tendermint light-client
header-acceptance rules — the logic of `cosmos-lightclient/src/lib.rs:173`
(`verify_cosmos_header`, the informalsystems `ProdVerifier` rule set the crate delegates to,
`lib.rs:159-166`) — in Lean over the shared `Dregg2.Bridge.VerifiedLightClient` foundation,
and proves the three obligations `NoForgery` / `FailClosed` / `NonVacuous`.

THE RULES formalized (each cites the Rust it is the spec of):

  * **chain-id match** — a header from another chain is refused (cross-chain replay defense,
    `lib.rs:78-80`).
  * **adjacent-height advance + validator-set-hash binding** — the untrusted header is
    `trusted.height + 1` and the trusted `next_validators_hash` equals the hash of the
    untrusted validator-set encoding (`lib.rs:73-75, 85-88, 163-165`): the set that signs is
    EXACTLY the set the trusted header committed to. The header also self-binds
    (`header.validatorsHash = hash(valset)`), so the quorum is over the set the header names.
  * **stake-weighted ≥ 2/3 commit** — strictly MORE than 2/3 of the validator set's total
    voting power signed the commit, each signature verified against the header's canonical
    sign-bytes (`lib.rs:14-15, 99-102, 160-162`; Tendermint's `voting_power_needed = 2/3` is
    strict `>`). A missing (`none`) or invalid signature contributes ZERO power.
  * **time window** — untrusted time strictly after the trusted header time (monotonic), not
    from the future beyond `now + clock_drift`, and the trusted header still inside the
    trusting period (`lib.rs:15-16, 92-93, 162-166`).

TWO LAYERS, kept honest:

  * The rules layer (§2-§4) is PARAMETRIC over an arbitrary `CryptoLeaf` — for the real chain
    that leaf is ed25519 signature soundness (`sigSound`: a verifying commit signature means
    the validator genuinely signed those vote bytes — Ed25519 EUF-CMA, discharged by a
    verified crypto library) and SHA-256 collision resistance (`hashCR` — the validator-set
    hash binds one set). `tmNoForgery` is therefore literally "IF ed25519 + SHA-256 are sound
    THEN an accepted header carries a genuine >2/3-stake commit of its committed validator
    set" — the crypto assumptions are the `∀ L : CryptoLeaf` binder, minimal and visible,
    never a laundered `def FooValid`.
  * The demo instance (§5-§7) PROVES its leaf (like the foundation's toy), so the shipped
    file is genuinely axiom-clean end to end and the discriminators run on concrete data.

NON-VACUITY (the Nomad-law tooth, `tm_gate_discriminates`): under the SAME trusted state the
gate ACCEPTS a genuine 3-of-3 commit and REJECTS: an exactly-2/3 sub-quorum commit (Tendermint
requires strictly more), a forged third signature, a tampered `validatorsHash`, a self-consistent
update signed by a DIFFERENT validator set than the trusted epoch committed, a wrong chain-id,
a non-monotonic time, a future time, and the empty update.

ICS-23 membership (`verify_cosmos_membership`, `lib.rs:299`) is the named follow-up rung; here
its anchor appears as the adapter `inclusion` demo — an app-state fact is accepted only under a
verified header's `appHash` (`toAdapter` composition, §7).

Kernel-clean: `#assert_axioms` hard-gates every theorem; the only crypto assumptions are the
named `CryptoLeaf` fields, carried as VISIBLE hypotheses (`∀ L`), proven for the demo instance.
-/
import Dregg2.Bridge.VerifiedLightClient
import Metatheory.Bridge.InterchainAdapter
import Dregg2.Tactics

namespace Dregg2.Bridge.LightClientTendermint

open Dregg2.Bridge.VerifiedLightClient

/-! ## §1 — The Tendermint data shapes (`TrustedCosmosState` / `SignedHeader` analogs).

Heights and times are `Nat` (Tendermint's are u64 / nanosecond timestamps); pubkeys, signatures
and digests are the `CryptoLeaf`'s types, so the real chain plugs ed25519 keys and SHA-256
digests straight in. The commit is positional (`List (Option Sig)`) exactly like Tendermint's
per-validator `CommitSig` array — `none` is `BlockIdFlagAbsent`. -/

/-- A Tendermint block header, light-client view (`cosmos-lightclient/src/lib.rs:129-135`
`VerifiedHeader` fields + the `validators_hash` commitment the verifier checks). -/
structure TmHeader (Digest : Type) where
  chainId : Nat
  height : Nat
  time : Nat
  /-- The header's own commitment to the validator set that signs it. -/
  validatorsHash : Digest
  /-- The application state root — what ICS-23 membership opens into (`lib.rs:150-153`). -/
  appHash : Digest

/-- A validator: a public key + its stake-weighted voting power (`lib.rs:85-88`). -/
structure TmValidator (PubKey : Type) where
  pubkey : PubKey
  power : Nat

/-- The untrusted update: a header, the validator set claimed to have signed it, and the
positional commit (`lib.rs:156-199` `UntrustedBlockState`). -/
structure TmUpdate (L : CryptoLeaf) where
  header : TmHeader L.Digest
  validators : List (TmValidator L.PubKey)
  commit : List (Option L.Sig)

/-- The trusted state (`lib.rs:77-89` `TrustedCosmosState` + the verification-time clock and
`Options`): the weak-subjectivity anchor a verified advance extends. -/
structure TmTrustedState (L : CryptoLeaf) where
  chainId : Nat
  height : Nat
  headerTime : Nat
  /-- The verifier's clock (`now` in `verify_cosmos_header`). -/
  now : Nat
  /-- `DEFAULT_CLOCK_DRIFT` (`lib.rs:93`). -/
  clockDrift : Nat
  /-- The trusting period (`Options.trusting_period`). -/
  trustingPeriod : Nat
  /-- The trusted header's commitment to the NEXT validator set (`lib.rs:85-88`) — the
  adjacent-advance epoch binding. -/
  nextValidatorsHash : L.Digest

/-! ## §2 — Stake accounting: total power, verified-signature power, and the genuine signers. -/

/-- Total voting power of a validator list. -/
def totalPower {PubKey : Type} : List (TmValidator PubKey) → Nat
  | [] => 0
  | v :: vs => v.power + totalPower vs

/-- The voting power whose positional commit signature VERIFIES against `msg` (the header's
canonical sign-bytes). An absent (`none`) or non-verifying signature contributes ZERO — the
`lib.rs:99-102` rule that a forged/missing signature adds no power. -/
def signedPower (L : CryptoLeaf) (msg : L.Msg) :
    List (TmValidator L.PubKey) → List (Option L.Sig) → Nat
  | [], _ => 0
  | _ :: _, [] => 0
  | _ :: vs, none :: ss => signedPower L msg vs ss
  | v :: vs, some sig :: ss =>
      if L.sigVerify v.pubkey msg sig then v.power + signedPower L msg vs ss
      else signedPower L msg vs ss

/-- The sub-list of validators whose commit signature verifies — the witness list the
`NoForgery` proof exhibits as genuine signers. -/
def signers (L : CryptoLeaf) (msg : L.Msg) :
    List (TmValidator L.PubKey) → List (Option L.Sig) → List (TmValidator L.PubKey)
  | [], _ => []
  | _ :: _, [] => []
  | _ :: vs, none :: ss => signers L msg vs ss
  | v :: vs, some sig :: ss =>
      if L.sigVerify v.pubkey msg sig then v :: signers L msg vs ss
      else signers L msg vs ss

/-- The verified signers are a sub-list of the validator set (no invented validators, no
duplicated stake). -/
theorem signers_sublist (L : CryptoLeaf) (msg : L.Msg) :
    ∀ (vs : List (TmValidator L.PubKey)) (ss : List (Option L.Sig)),
      (signers L msg vs ss).Sublist vs
  | [], _ => by simp [signers]
  | _ :: _, [] => by simp [signers]
  | _ :: vs, none :: ss => by
      simp only [signers]; exact (signers_sublist L msg vs ss).cons _
  | v :: vs, some sig :: ss => by
      simp only [signers]
      by_cases hver : L.sigVerify v.pubkey msg sig = true
      · rw [if_pos hver]; exact (signers_sublist L msg vs ss).cons_cons v
      · rw [if_neg hver]; exact (signers_sublist L msg vs ss).cons v

/-- **The crypto leaf bites**: every verified signer GENUINELY signed the message — this is
where `L.sigSound` (ed25519 unforgeability for the real chain) turns a boolean verification
into the `Signed` denotation. -/
theorem signers_signed (L : CryptoLeaf) (msg : L.Msg) :
    ∀ (vs : List (TmValidator L.PubKey)) (ss : List (Option L.Sig)),
      ∀ v ∈ signers L msg vs ss, L.Signed v.pubkey msg
  | [], _ => by simp [signers]
  | _ :: _, [] => by simp [signers]
  | _ :: vs, none :: ss => by
      simp only [signers]; exact signers_signed L msg vs ss
  | v :: vs, some sig :: ss => by
      simp only [signers]
      by_cases hver : L.sigVerify v.pubkey msg sig = true
      · rw [if_pos hver]
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw'
        · exact L.sigSound _ msg sig hver
        · exact signers_signed L msg vs ss w hw'
      · rw [if_neg hver]; exact signers_signed L msg vs ss

/-- The verified signers carry EXACTLY the verified-signature power — so a quorum of
`signedPower` is a quorum of genuine signers' stake. -/
theorem signers_power (L : CryptoLeaf) (msg : L.Msg) :
    ∀ (vs : List (TmValidator L.PubKey)) (ss : List (Option L.Sig)),
      totalPower (signers L msg vs ss) = signedPower L msg vs ss
  | [], _ => by simp [signers, signedPower, totalPower]
  | _ :: _, [] => by simp [signers, signedPower, totalPower]
  | _ :: vs, none :: ss => by
      simp only [signers, signedPower]; exact signers_power L msg vs ss
  | v :: vs, some sig :: ss => by
      cases hver : L.sigVerify v.pubkey msg sig <;>
        simp [signers, signedPower, totalPower, hver, signers_power L msg vs ss]

/-! ## §3 — THE RULES: the Tendermint header-acceptance verdict, and its exact characterization. -/

section Rules

variable (L : CryptoLeaf) [DecidableEq L.Digest]
variable (sb : TmHeader L.Digest → L.Msg)
variable (enc : List (TmValidator L.PubKey) → L.Msg)

/-- **`tmVerify` — the Tendermint light-client RULES** (`verify_cosmos_header`,
`cosmos-lightclient/src/lib.rs:159-166`): chain-id match, adjacent height, monotonic time,
not-from-the-future (clock drift), trusting period, the trusted `nextValidatorsHash` binds the
untrusted validator set (epoch binding), the header self-binds its validator set, and strictly
more than 2/3 of the total voting power verifiably signed the header's sign-bytes.
`sb` is the canonical-vote sign-bytes encoder; `enc` the validator-set encoding fed to the
hash — both opaque parameters (the real chain plugs the protobuf encoders). -/
def tmVerify (ts : TmTrustedState L) (u : TmUpdate L) : Bool :=
  decide (u.header.chainId = ts.chainId)
  && decide (u.header.height = ts.height + 1)
  && decide (ts.headerTime < u.header.time)
  && decide (u.header.time ≤ ts.now + ts.clockDrift)
  && decide (ts.now < ts.headerTime + ts.trustingPeriod)
  && decide (L.hash (enc u.validators) = ts.nextValidatorsHash)
  && decide (L.hash (enc u.validators) = u.header.validatorsHash)
  && decide (2 * totalPower u.validators
              < 3 * signedPower L (sb u.header) u.validators u.commit)

/-- The exact propositional characterization of the verdict — every rejection/binding theorem
below is a projection of this iff. -/
theorem tmVerify_eq_true_iff (ts : TmTrustedState L) (u : TmUpdate L) :
    tmVerify L sb enc ts u = true ↔
      u.header.chainId = ts.chainId
      ∧ u.header.height = ts.height + 1
      ∧ ts.headerTime < u.header.time
      ∧ u.header.time ≤ ts.now + ts.clockDrift
      ∧ ts.now < ts.headerTime + ts.trustingPeriod
      ∧ L.hash (enc u.validators) = ts.nextValidatorsHash
      ∧ L.hash (enc u.validators) = u.header.validatorsHash
      ∧ 2 * totalPower u.validators
          < 3 * signedPower L (sb u.header) u.validators u.commit := by
  unfold tmVerify
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-! ## §4 — The three obligations, GENERIC in the crypto leaf.

`tmNoForgery` below is the honest theorem shape: `∀ L : CryptoLeaf, …` — instantiate `L` with
the real ed25519+SHA-256 leaf (whose `sigSound`/`hashCR` are the named verified-library
assumptions) and it reads: IF ed25519 and SHA-256 are sound THEN an accepted header genuinely
carries a >2/3-stake commit of its committed validator set. -/

/-- **The foreign-chain validity predicate** — what Tendermint itself calls a valid header:
the header's `validatorsHash` really commits its validator set, and there is a sub-list of
that set which GENUINELY signed the header's sign-bytes (the `Signed` denotation, not a
boolean) carrying strictly more than 2/3 of the total power. -/
def TmForeignValid (u : TmUpdate L) : Prop :=
  L.hash (enc u.validators) = u.header.validatorsHash
  ∧ ∃ S : List (TmValidator L.PubKey),
      S.Sublist u.validators
      ∧ (∀ v ∈ S, L.Signed v.pubkey (sb u.header))
      ∧ 2 * totalPower u.validators < 3 * totalPower S

/-- **NO FORGERY.** An update `tmVerify` accepts is foreign-valid: the genuine-signer sub-list
is `signers …`, its sublist-ness and power come from §2, and its GENUINENESS comes from the
crypto leaf's `sigSound` (via `signers_signed`) — the ed25519 assumption is consumed exactly
here, never assumed at the update level. -/
theorem tmNoForgery : NoForgery (tmVerify L sb enc) (TmForeignValid L sb enc) := by
  intro ts u h
  obtain ⟨_, _, _, _, _, _, hbind, hq⟩ := (tmVerify_eq_true_iff L sb enc ts u).mp h
  refine ⟨hbind, signers L (sb u.header) u.validators u.commit,
    signers_sublist L (sb u.header) u.validators u.commit,
    signers_signed L (sb u.header) u.validators u.commit, ?_⟩
  rw [signers_power]
  exact hq

/-- The empty / uninitialized update: zero header, NO validators, NO commit. -/
def tmEmptyUpdate (d0 : L.Digest) : TmUpdate L :=
  { header := ⟨0, 0, 0, d0, d0⟩, validators := [], commit := [] }

/-- **FAIL CLOSED (the Nomad-law tooth).** The empty update is rejected for EVERY trusted
state: with no validators the total power is 0 and `2·0 < 3·0` is false — an uninitialized
update can never ride a permissive default through the gate. -/
theorem tmFailClosed (d0 : L.Digest) :
    FailClosed (tmVerify L sb enc) (tmEmptyUpdate L d0) := by
  intro ts
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨_, _, _, _, _, _, _, hq⟩ :=
    (tmVerify_eq_true_iff L sb enc ts (tmEmptyUpdate L d0)).mp h
  simp [tmEmptyUpdate, totalPower, signedPower] at hq

/-- **SUB-QUORUM REJECTION, generic.** If the verified-signature power is ≤ 2/3 of the total
(including EXACTLY 2/3 — Tendermint's threshold is strict), the update is rejected. This is
the `Verdict::NotEnoughTrust` arm (`lib.rs:99-102, 212-214`) as a theorem. -/
theorem tm_subquorum_rejected (ts : TmTrustedState L) (u : TmUpdate L)
    (h : 3 * signedPower L (sb u.header) u.validators u.commit
           ≤ 2 * totalPower u.validators) :
    tmVerify L sb enc ts u = false := by
  rw [Bool.eq_false_iff]
  intro htrue
  obtain ⟨_, _, _, _, _, _, _, hq⟩ := (tmVerify_eq_true_iff L sb enc ts u).mp htrue
  exact absurd hq (Nat.not_lt.mpr h)

/-- **WRONG-EPOCH REJECTION, generic.** A validator set the trusted header did NOT commit to
(its encoding hashes to something other than `nextValidatorsHash`) is rejected — quorums by
foreign validator sets don't count (`lib.rs:163-165`). -/
theorem tm_wrong_epoch_rejected (ts : TmTrustedState L) (u : TmUpdate L)
    (h : L.hash (enc u.validators) ≠ ts.nextValidatorsHash) :
    tmVerify L sb enc ts u = false := by
  rw [Bool.eq_false_iff]
  intro htrue
  obtain ⟨_, _, _, _, _, hepoch, _, _⟩ := (tmVerify_eq_true_iff L sb enc ts u).mp htrue
  exact h hepoch

/-- **WRONG-VALIDATORS-HASH REJECTION, generic.** A header whose own `validatorsHash` does not
match its validator set is rejected (the self-binding leg). -/
theorem tm_wrong_valhash_rejected (ts : TmTrustedState L) (u : TmUpdate L)
    (h : L.hash (enc u.validators) ≠ u.header.validatorsHash) :
    tmVerify L sb enc ts u = false := by
  rw [Bool.eq_false_iff]
  intro htrue
  obtain ⟨_, _, _, _, _, _, hbind, _⟩ := (tmVerify_eq_true_iff L sb enc ts u).mp htrue
  exact h hbind

/-- **CHAIN-ID MISMATCH REJECTION, generic** — the cross-chain replay defense (`lib.rs:78-80`). -/
theorem tm_chain_mismatch_rejected (ts : TmTrustedState L) (u : TmUpdate L)
    (h : u.header.chainId ≠ ts.chainId) :
    tmVerify L sb enc ts u = false := by
  rw [Bool.eq_false_iff]
  intro htrue
  exact h ((tmVerify_eq_true_iff L sb enc ts u).mp htrue).1

/-- **ACCEPTANCE BINDS THE TRUST ANCHOR.** An accepted update carries the trusted chain-id, is
the adjacent height, and its validator set is the one the trusted header committed to. -/
theorem tm_accept_binds_trust (ts : TmTrustedState L) (u : TmUpdate L)
    (h : tmVerify L sb enc ts u = true) :
    u.header.chainId = ts.chainId
    ∧ u.header.height = ts.height + 1
    ∧ L.hash (enc u.validators) = ts.nextValidatorsHash := by
  obtain ⟨h1, h2, _, _, _, h6, _, _⟩ := (tmVerify_eq_true_iff L sb enc ts u).mp h
  exact ⟨h1, h2, h6⟩

/-- **THE HASH LEAF BITES (`hashCR`): the committed validator set is UNIQUE.** Any validator
set whose encoding hashes to the trusted `nextValidatorsHash` has the SAME encoding as an
accepted update's set — SHA-256 collision resistance is what makes the 32-byte epoch binding
bind. Consumed exactly here, never assumed globally. -/
theorem tm_committed_set_unique (ts : TmTrustedState L) (u : TmUpdate L)
    (h : tmVerify L sb enc ts u = true)
    (vs' : List (TmValidator L.PubKey))
    (h' : L.hash (enc vs') = ts.nextValidatorsHash) :
    enc vs' = enc u.validators := by
  obtain ⟨_, _, _, _, _, hepoch, _, _⟩ := (tmVerify_eq_true_iff L sb enc ts u).mp h
  exact L.hashCR _ _ (h'.trans hepoch.symm)

end Rules

/-! ## §5 — The demo crypto leaf (the ed25519 + SHA-256 SLOT), proved like the foundation's toy.

A real deployment replaces this with the ed25519 leaf whose `sigSound` is the named
verified-library unforgeability assumption and the SHA-256 leaf whose `hashCR` is the named
collision-resistance assumption (both VISIBLE as `CryptoLeaf` fields at the instance site —
`#assert_axioms` cannot see hypothesis-carried assumptions, so they are documented here, not
hidden). The demo PROVES both fields, keeping this file genuinely axiom-clean: registered keys
are `pk < 100`, the toy MAC is `s = pk + m`, the hash is the identity. -/

/-- Demo signature verifier: `pk` is a registered key AND `s` is the toy MAC `pk + m`. -/
def demoSigVerify (pk m s : Nat) : Bool := decide (pk < 100) && (s == pk + m)

/-- Demo hash — the identity (the SHA-256 slot; `hashCR` is injectivity). -/
def demoHash (m : Nat) : Nat := m

/-- Demo `Signed` denotation: a registered key (`pk < 100`) authorized the message. It
DISCRIMINATES: `demoSigned 777 m` is false. -/
abbrev demoSigned (pk : Nat) (_m : Nat) : Prop := pk < 100

/-- The demo signature-soundness leaf, PROVED (the ed25519 `sigSound` slot). -/
theorem demoSigSound (pk m s : Nat) (h : demoSigVerify pk m s = true) : demoSigned pk m := by
  simp only [demoSigVerify, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- The demo CR leaf, PROVED (the SHA-256 `hashCR` slot) — identity is injective. -/
theorem demoHashCR (m₁ m₂ : Nat) (h : demoHash m₁ = demoHash m₂) : m₁ = m₂ := h

/-- The demo `CryptoLeaf` — both soundness fields genuinely proved, so nothing below rests on
an unproven crypto assumption; the real chain swaps in ed25519 + SHA-256 here. -/
@[reducible] def demoLeaf : CryptoLeaf where
  PubKey := Nat
  Msg := Nat
  Sig := Nat
  Digest := Nat
  sigVerify := demoSigVerify
  hash := demoHash
  Signed := demoSigned
  sigSound := demoSigSound
  hashCR := demoHashCR

instance : DecidableEq demoLeaf.Digest := inferInstanceAs (DecidableEq Nat)

/-- Demo canonical-vote sign-bytes: an injective-enough packing of the header fields
(the protobuf `CanonicalVote` encoder slot). Covers the `validatorsHash` and `appHash`. -/
def demoSignBytes (h : TmHeader Nat) : Nat :=
  h.chainId + 1000 * h.height + 1000000 * h.time
    + 1000000000 * (h.validatorsHash + 1000000 * h.appHash)

/-- Demo validator-set encoding (the protobuf valset encoder slot): a positional fold. -/
def demoValSetEncode (vs : List (TmValidator Nat)) : Nat :=
  vs.foldl (fun acc v => acc * 97 + v.pubkey * 7 + v.power) 1

/-! ## §6 — Concrete chain data + the DISCRIMINATORS (the non-vacuity witnesses).

Three equal-power validators (keys 1, 2, 3 — total power 3), trusted state at height 10,
genuine adjacent header at height 11. With equal powers, a 2-of-3 commit is EXACTLY 2/3 —
Tendermint's strict `>` threshold rejects it: the boundary case is a discriminator leg. -/

/-- The trusted-epoch validator set: keys 1, 2, 3, power 1 each (total 3). -/
def demoValidators : List (TmValidator Nat) := [⟨1, 1⟩, ⟨2, 1⟩, ⟨3, 1⟩]

/-- The genuine adjacent header: right chain (5), right height (11), time inside the window,
`validatorsHash` really committing `demoValidators`. -/
def genuineHeader : TmHeader Nat :=
  { chainId := 5, height := 11, time := 55
    validatorsHash := demoHash (demoValSetEncode demoValidators)
    appHash := 4242 }

/-- A full 3-of-3 commit over a given header's sign-bytes (each validator's toy MAC). -/
def demoCommit (h : TmHeader Nat) : List (Option Nat) :=
  [some (1 + demoSignBytes h), some (2 + demoSignBytes h), some (3 + demoSignBytes h)]

/-- The trusted state: chain 5, height 10, header time 50, clock now 60 (drift 5, trusting
period 100), `nextValidatorsHash` committing `demoValidators`. -/
def ts0 : TmTrustedState demoLeaf :=
  { chainId := 5, height := 10, headerTime := 50, now := 60, clockDrift := 5
    trustingPeriod := 100
    nextValidatorsHash := demoHash (demoValSetEncode demoValidators) }

/-- The genuine update: the genuine header + the trusted-epoch set + a full 3-of-3 commit. -/
def genuineUpdate : TmUpdate demoLeaf :=
  ⟨genuineHeader, demoValidators, demoCommit genuineHeader⟩

/-- EXACTLY 2/3 signed (validator 3 absent): 2·3 < 3·2 is FALSE — the strict-threshold
boundary forgery. -/
def subQuorumUpdate : TmUpdate demoLeaf :=
  ⟨genuineHeader, demoValidators,
    [some (1 + demoSignBytes genuineHeader), some (2 + demoSignBytes genuineHeader), none]⟩

/-- Validator 3's signature FORGED (a wrong MAC): it contributes zero power → sub-quorum. -/
def forgedSigUpdate : TmUpdate demoLeaf :=
  ⟨genuineHeader, demoValidators,
    [some (1 + demoSignBytes genuineHeader), some (2 + demoSignBytes genuineHeader), some 0]⟩

/-- The header's own `validatorsHash` tampered to 999 (commit re-signed over the tampered
header, so ONLY the self-binding rule fires). -/
def tamperedValHashHeader : TmHeader Nat := { genuineHeader with validatorsHash := 999 }
def tamperedValHashUpdate : TmUpdate demoLeaf :=
  ⟨tamperedValHashHeader, demoValidators, demoCommit tamperedValHashHeader⟩

/-- A SELF-CONSISTENT update by a DIFFERENT (registered-key) validator set: key 9, power 3,
own header binding + a full quorum of itself — everything checks EXCEPT the trusted epoch
binding (`nextValidatorsHash`). The wrong-epoch tooth. -/
def foreignSetValidators : List (TmValidator Nat) := [⟨9, 3⟩]
def foreignSetHeader : TmHeader Nat :=
  { chainId := 5, height := 11, time := 55
    validatorsHash := demoHash (demoValSetEncode foreignSetValidators)
    appHash := 4242 }
def foreignSetUpdate : TmUpdate demoLeaf :=
  ⟨foreignSetHeader, foreignSetValidators, [some (9 + demoSignBytes foreignSetHeader)]⟩

/-- Wrong chain-id (6 ≠ 5), commit re-signed — only the replay defense fires. -/
def wrongChainHeader : TmHeader Nat := { genuineHeader with chainId := 6 }
def wrongChainUpdate : TmUpdate demoLeaf :=
  ⟨wrongChainHeader, demoValidators, demoCommit wrongChainHeader⟩

/-- Non-monotonic time (45 < trusted 50), commit re-signed. -/
def staleTimeHeader : TmHeader Nat := { genuineHeader with time := 45 }
def staleTimeUpdate : TmUpdate demoLeaf :=
  ⟨staleTimeHeader, demoValidators, demoCommit staleTimeHeader⟩

/-- From the future (99 > now 60 + drift 5), commit re-signed. -/
def futureTimeHeader : TmHeader Nat := { genuineHeader with time := 99 }
def futureTimeUpdate : TmUpdate demoLeaf :=
  ⟨futureTimeHeader, demoValidators, demoCommit futureTimeHeader⟩

/-- A validator set of one UNREGISTERED key (777): used to show `TmForeignValid` itself
discriminates — no genuine quorum can exist over it. -/
def unregisteredValidators : List (TmValidator Nat) := [⟨777, 3⟩]
def unregisteredHeader : TmHeader Nat :=
  { chainId := 5, height := 11, time := 55
    validatorsHash := demoHash (demoValSetEncode unregisteredValidators)
    appHash := 4242 }
def unregisteredUpdate : TmUpdate demoLeaf :=
  ⟨unregisteredHeader, unregisteredValidators, [some (777 + demoSignBytes unregisteredHeader)]⟩

/-- **THE DISCRIMINATOR, ASSEMBLED (non-vacuity teeth).** Under the SAME trusted state `ts0`
the gate accepts the genuine 3-of-3 update and REJECTS: the exactly-2/3 commit (strict
threshold), the forged signature, the tampered validators-hash, the self-consistent
wrong-epoch set, the wrong chain-id, the stale time, the future time, and the empty update.
The rules are not a `True`-carrier. -/
theorem tm_gate_discriminates :
    tmVerify demoLeaf demoSignBytes demoValSetEncode ts0 genuineUpdate = true
    ∧ tmVerify demoLeaf demoSignBytes demoValSetEncode ts0 subQuorumUpdate = false
    ∧ tmVerify demoLeaf demoSignBytes demoValSetEncode ts0 forgedSigUpdate = false
    ∧ tmVerify demoLeaf demoSignBytes demoValSetEncode ts0 tamperedValHashUpdate = false
    ∧ tmVerify demoLeaf demoSignBytes demoValSetEncode ts0 foreignSetUpdate = false
    ∧ tmVerify demoLeaf demoSignBytes demoValSetEncode ts0 wrongChainUpdate = false
    ∧ tmVerify demoLeaf demoSignBytes demoValSetEncode ts0 staleTimeUpdate = false
    ∧ tmVerify demoLeaf demoSignBytes demoValSetEncode ts0 futureTimeUpdate = false
    ∧ tmVerify demoLeaf demoSignBytes demoValSetEncode ts0
        (tmEmptyUpdate demoLeaf (0 : Nat)) = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **TRUE side of `TmForeignValid`.** The genuine update is foreign-valid: the full validator
list is its own >2/3 genuine-signer witness (all keys registered). -/
theorem tm_valid_holds :
    TmForeignValid demoLeaf demoSignBytes demoValSetEncode genuineUpdate :=
  ⟨by decide, demoValidators, List.Sublist.refl _, by decide, by decide⟩

/-- **FORGED-SIGNER DISCRIMINATOR on the validity predicate.** No update over the unregistered
set (key 777) is foreign-valid: any sub-list with >2/3 of its power is non-empty, hence
contains key 777, and `Signed 777 _` (registered-key) is false. The crypto denotation is what
separates them. -/
theorem tm_unregistered_signer_invalid :
    ¬ TmForeignValid demoLeaf demoSignBytes demoValSetEncode unregisteredUpdate := by
  rintro ⟨_, S, hsub, hsigned, hq⟩
  cases S with
  | nil => simp [unregisteredUpdate, unregisteredValidators, totalPower] at hq
  | cons v S' =>
    have hv : v ∈ unregisteredUpdate.validators :=
      hsub.subset (List.mem_cons_self ..)
    have hveq : v = ⟨777, 3⟩ := by
      simpa [unregisteredUpdate, unregisteredValidators] using hv
    have hs := hsigned v (List.mem_cons_self ..)
    rw [hveq] at hs
    simp [demoSigned] at hs

/-- **TAMPERED-VALIDATORS-HASH DISCRIMINATOR on the validity predicate.** The tampered header
(claimed hash 999) is not foreign-valid — the set-binding leg fails. -/
theorem tm_tampered_valhash_invalid :
    ¬ TmForeignValid demoLeaf demoSignBytes demoValSetEncode tamperedValHashUpdate := by
  rintro ⟨hbind, _⟩
  exact absurd hbind (by decide)

/-! ## §7 — The bundle + the `InterchainAdapter` composition: the finality hypothesis DISCHARGED.

`tendermintClient` cannot exist without the three obligations — they are fields. `toAdapter`
then produces the adapter whose `foreignFinal` is the light client's decidable verdict on the
`proof` rung: the `foreignFinal` hypothesis `Metatheory.Bridge.InterchainAdapter` assumes is
PRODUCED, not assumed. The inclusion demo is the ICS-23 anchor: an app-state fact (an
`appHash`-committed value, `lib.rs:299` `verify_cosmos_membership`'s anchor) is accepted only
under a verified header. -/

/-- **The Tendermint `ForeignLightClient`** — all three obligations discharged over the real
rule set (§3-§4), instantiated at the demo leaf. `nonVacuous` is witnessed by the genuine
3-of-3 update vs the exactly-2/3 sub-quorum update under the SAME trusted state. -/
def tendermintClient : ForeignLightClient where
  leaf := demoLeaf
  Update := TmUpdate demoLeaf
  TrustedState := TmTrustedState demoLeaf
  ForeignValid := TmForeignValid demoLeaf demoSignBytes demoValSetEncode
  verify := tmVerify demoLeaf demoSignBytes demoValSetEncode
  emptyUpdate := tmEmptyUpdate demoLeaf (0 : Nat)
  noForgery := tmNoForgery demoLeaf demoSignBytes demoValSetEncode
  failClosed := tmFailClosed demoLeaf demoSignBytes demoValSetEncode (0 : Nat)
  nonVacuous := ⟨ts0, genuineUpdate, subQuorumUpdate, by decide, by decide⟩

/-- The inclusion relation: a claimed app-state commitment matches the verified header's
`appHash` — the ICS-23 anchor (`lib.rs:333-336`: the proof's top root MUST equal the verified
`app_hash`). -/
def tmIncl : Nat → TmUpdate demoLeaf → Prop := fun ev u => ev = u.header.appHash

/-- The adapter the Tendermint client produces at `ts0` — `foreignFinal` is the verdict of the
verified rules, on the `proof` rung. -/
def tmAdapter : Metatheory.Bridge.InterchainAdapter (TmUpdate demoLeaf) Nat :=
  toAdapter tendermintClient ts0 tmIncl

/-- **END-TO-END DISCHARGE.** The adapter ACCEPTS the genuine app-state fact (4242 under the
genuine verified header), and that acceptance ENTAILS a foreign-VALID update including it —
the `InterchainAdapter` finality hypothesis is produced by the verified Tendermint rules. -/
theorem tm_adapter_accepts_and_discharges :
    tmAdapter.accepts 4242
    ∧ ∃ u, TmForeignValid demoLeaf demoSignBytes demoValSetEncode u ∧ tmIncl 4242 u := by
  have hacc : tmAdapter.accepts 4242 :=
    ⟨genuineUpdate,
      (by decide : tendermintClient.verify ts0 genuineUpdate = true), rfl⟩
  exact ⟨hacc, toAdapter_accepts_entails_valid tendermintClient ts0 tmIncl 4242 hacc⟩

/-- **The empty update is rejected at the adapter boundary** — `FailClosed`, lifted. -/
theorem tm_adapter_rejects_empty :
    ¬ tmAdapter.foreignFinal tendermintClient.emptyUpdate :=
  toAdapter_rejects_empty tendermintClient ts0 tmIncl

/-! ### It runs (`#guard`): the rules discriminate on concrete data. -/

#guard tmVerify demoLeaf demoSignBytes demoValSetEncode ts0 genuineUpdate == true
#guard tmVerify demoLeaf demoSignBytes demoValSetEncode ts0 subQuorumUpdate == false
#guard tmVerify demoLeaf demoSignBytes demoValSetEncode ts0 forgedSigUpdate == false
#guard tmVerify demoLeaf demoSignBytes demoValSetEncode ts0 tamperedValHashUpdate == false
#guard tmVerify demoLeaf demoSignBytes demoValSetEncode ts0 foreignSetUpdate == false
#guard tmVerify demoLeaf demoSignBytes demoValSetEncode ts0 wrongChainUpdate == false
#guard tmVerify demoLeaf demoSignBytes demoValSetEncode ts0 staleTimeUpdate == false
#guard tmVerify demoLeaf demoSignBytes demoValSetEncode ts0 futureTimeUpdate == false
#guard tmVerify demoLeaf demoSignBytes demoValSetEncode ts0 (tmEmptyUpdate demoLeaf (0 : Nat))
        == false
#guard demoSigVerify 1 42 43 == true
#guard demoSigVerify 777 42 819 == false

/-! ## §8 — Axiom hygiene: every theorem kernel-clean. The demo leaf is PROVED, so nothing here
rests on an unproven crypto assumption. A REAL deployment's `noForgery` rests on its VISIBLE,
named `leaf.sigSound` (ed25519) / `leaf.hashCR` (SHA-256) fields — carried as hypotheses,
which `#assert_axioms` cannot see, hence declared in this header, not hidden. -/

#assert_axioms signers_sublist
#assert_axioms signers_signed
#assert_axioms signers_power
#assert_axioms tmVerify_eq_true_iff
#assert_axioms tmNoForgery
#assert_axioms tmFailClosed
#assert_axioms tm_subquorum_rejected
#assert_axioms tm_wrong_epoch_rejected
#assert_axioms tm_wrong_valhash_rejected
#assert_axioms tm_chain_mismatch_rejected
#assert_axioms tm_accept_binds_trust
#assert_axioms tm_committed_set_unique
#assert_axioms tm_gate_discriminates
#assert_axioms tm_valid_holds
#assert_axioms tm_unregistered_signer_invalid
#assert_axioms tm_tampered_valhash_invalid
#assert_axioms tendermintClient
#assert_axioms tm_adapter_accepts_and_discharges
#assert_axioms tm_adapter_rejects_empty

#print axioms tmNoForgery
#print axioms tm_gate_discriminates

end Dregg2.Bridge.LightClientTendermint
