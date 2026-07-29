/-
# Dregg2.Bridge.LightClientTendermintSkip — the NON-ADJACENT (skipping) Tendermint light-client
decision, `@[export] dregg_tm_skip_verify`, and the trust-OVERLAP no-forgery theorem it renders.

## Why this module exists (the second half of the Cosmos accept surface)

`Dregg2.Bridge.LightClientTendermintGate` exports `dregg_tm_lc_verify`, which decides the
ADJACENT advance (`height = trusted.height + 1`, bound by the `next_validators_hash` epoch
binding). Its own header names the gap it leaves:

> `tmVerify` formalizes the ADJACENT-advance rule set. The Rust `verify_cosmos_header` also
> accepts the NON-ADJACENT / skipping shape (any higher height, bound by the trust-threshold
> overlap rule); the Lean re-authoring does not yet cover it.

That gap is not cosmetic — it is a **whole accept path**. `cosmos-lightclient` reaches a
`VerifiedHeader` by either shape (`cosmos-lightclient/tests/header_skipping.rs` carries a
genuine cosmoshub-4 ~95-block skip as an ACCEPT KAT), so gating only the adjacent shape would
leave the skipping shape un-gated and the crate's answer to "can a header be accepted without
the verified gate?" would still be YES. This module closes it: the two exports partition the
height axis and NOTHING is accepted outside them.

## What the skipping rule IS (read off the audited verifier, not invented)

`tendermint-light-client-verifier` 0.40.4 (`src/verifier.rs`,
`src/operations/voting_power.rs`, `tendermint/src/trust_threshold.rs`):

  * `validate_against_trusted` takes the `else` branch when
    `untrusted.height() != trusted.height + 1`, and there requires `is_monotonic_height`
    (`untrusted_height > trusted_height`). The two conditions together are exactly
    `trusted.height + 1 < untrusted.height` — which is why `tmSkipVerify`'s height conjunct is
    that STRICT form and not `≤`. The adjacent height is decided by the OTHER export; the two
    decisions cover DISJOINT height ranges (`tmSkip_height_disjoint_from_adjacent`).
  * `verify_commit_against_trusted` then calls `check_enough_trust_and_signers`, which is TWO
    threshold checks over the SAME commit against TWO validator sets:
      - the TRUSTED next-validator set at the configured `trust_threshold` (canonically 1/3),
      - the UNTRUSTED validator set at `TWO_THIRDS`.
  * `TrustThresholdFraction::is_enough_power signed total = signed * denominator > total *
    numerator` — **strict**. So the untrusted leg is `2 * total < 3 * signed` (identical to the
    adjacent gate's threshold, the same no-rounding multiply form) and the trusted-overlap leg
    is `trustNum * trustedTotal < trustDen * trustedSigned`. Exactly-1/3 overlap REJECTS, and
    `tmSkip_decision_discriminates` pins that boundary in the kernel.
  * The `next_validators_hash` epoch binding is ABSENT from this shape — that is the whole point
    of skipping — so `tmSkipVerify` does not carry it. What replaces it as the anchor is the
    overlap conjunct, and `tmSkipNoForgery` is what makes that replacement mean something.

## The crypto boundary (identical to the adjacent gate)

Only the LOGIC is exported; the crypto crosses as RESULTS. The per-validator Ed25519 commit
verification feeds BOTH power tallies (`signedPower` over the untrusted set with the untrusted
commit, and over the TRUSTED set with the same commit re-aligned to it — which is precisely what
`voting_power_in_sets` does when it walks each validator set looking that validator's vote up).
The SHA-256 validator-set hashing feeds `selfBindOk`. The gate re-derives no crypto.

`tendermint-rs`'s tally SHORT-CIRCUITS (`voting_power_in_impl` breaks as soon as
`power.check().is_ok()`), so the `tallied` it reports is a LOWER BOUND on the true signed power.
That is safe to put on the wire and is not an approximation of the decision: `check()` is the
same strict fraction test this gate re-decides, so a short-circuited tally satisfies the gate's
threshold exactly when the audited tally satisfied its own, and a tally that never met the
threshold was never short-circuited.

## The payoff: `tmSkipNoForgery` — an accepted skip is ANCHORED IN THE TRUSTED EPOCH

`TmSkipForeignValid` carries FOUR conjuncts, not three: the header's `validatorsHash` really
commits its validator set; that commitment BINDS (the `hashCR` carrier via `noCollision`); a
sub-list of the UNTRUSTED set carrying > 2/3 of its power GENUINELY signed; **and** a sub-list of
the TRUSTED next-validator set carrying more than `trustNum/trustDen` of THAT set's power
genuinely signed the same header. The last conjunct is the security content of skipping: at
1/3 it means at least one non-faulty validator the client already trusted signed the target, so
the client is not following a chain that its trusted epoch never touched. A stale anchor whose
power has moved away yields ZERO overlap, and `tmSkip_zero_overlap_rejected` refuses it with NO
crypto hypothesis at all.
-/
import Dregg2.Bridge.LightClientTendermint

set_option maxRecDepth 8192

namespace Dregg2.Bridge.LightClientTendermintSkip

open Dregg2.Bridge.VerifiedLightClient
open Dregg2.Bridge.LightClientTendermint

/- **Axiom hygiene**, same reason as the adjacent gate: `LightClientTendermint`'s
`instance : DecidableEq demoLeaf.Digest` is reducibly `DecidableEq Nat` and would otherwise be
picked up by every pure-`Nat` `decide` here, dragging `demoLeaf` → `demoSigSound` (a `by simp`
proof, hence `propext`) into theorems that contain no crypto. Dropping it locally makes the
`Nat` equality decides resolve to core `instDecidableEqNat`; it still resolves for the demo
instances below (via the reducible `demoLeaf.Digest ≡ Nat`), and every refinement stays `rfl`
because all `DecidableEq Nat` are definitionally equal. -/
attribute [-instance] Dregg2.Bridge.LightClientTendermint.instDecidableEqDigestDemoLeaf

/-! ## §1 — The skipping shapes: a trusted state that carries the OVERLAP TALLY BASE, and an
update that carries the commit in BOTH alignments. -/

/-- The trusted state for a NON-ADJACENT advance. It differs from `TmTrustedState` in exactly
the two places the rule differs: the `nextValidatorsHash` epoch commitment is gone (skipping
does not use it), and the trusted next-validator SET itself is present — it is the base the
trust-overlap tally is measured against — together with the configured trust-threshold
fraction (`Options.trust_threshold`; `trustNum/trustDen`, canonically `1/3`).

Carrying the SET rather than its hash is faithful to the deployed shape and is not a weakening:
`cosmos-lightclient`'s `verify_cosmos_header` refuses BEFORE any tally unless the caller's
`next_validators` hashes to the trusted header's committed `next_validators_hash`
(`HeaderVerifyError::TrustedStateCorrupt`), so the set the tally runs over is the committed one.
That check is the caller's responsibility per the audited verifier's own NOTE. -/
structure TmSkipTrusted (L : CryptoLeaf) where
  chainId : Nat
  height : Nat
  headerTime : Nat
  /-- The verifier's clock (`now` in `verify_cosmos_header`). -/
  now : Nat
  /-- `DEFAULT_CLOCK_DRIFT`. -/
  clockDrift : Nat
  /-- `Options.trusting_period`. -/
  trustingPeriod : Nat
  /-- The validator set the trusted header committed to sign the NEXT block — the OVERLAP TALLY
  BASE (`TrustedBlockState.next_validators`). -/
  nextValidators : List (TmValidator L.PubKey)
  /-- `Options.trust_threshold` numerator (canonically 1). -/
  trustNum : Nat
  /-- `Options.trust_threshold` denominator (canonically 3). -/
  trustDen : Nat

/-- The untrusted update for a skip. `commit` is the positional per-validator commit aligned to
`validators` (Tendermint's `CommitSig` array, `none` = `BlockIdFlagAbsent`); `trustedCommit` is
the SAME commit re-aligned to the TRUSTED next-validator set — position `i` holds the signature
the commit carries for `nextValidators[i]`, or `none` if that validator did not sign. This
mirrors `voting_power_in_sets`, which walks each validator set in turn and looks each
validator's vote up in the one commit. -/
structure TmSkipUpdate (L : CryptoLeaf) where
  header : TmHeader L.Digest
  validators : List (TmValidator L.PubKey)
  commit : List (Option L.Sig)
  /-- The same commit, positionally aligned to the trusted next-validator set. -/
  trustedCommit : List (Option L.Sig)

/-! ## §2 — THE RULES for a skip, and their exact characterization. -/

section Rules

variable (L : CryptoLeaf) [DecidableEq L.Digest]
variable (sb : TmHeader L.Digest → L.Msg)
variable (enc : List (TmValidator L.PubKey) → L.Msg)

/-- **`tmSkipVerify` — the Tendermint NON-ADJACENT (skipping) light-client RULES.** Chain-id
match; a STRICTLY non-adjacent height (`trusted.height + 1 < height`, the audited verifier's
`else` branch); monotonic time; not-from-the-future under clock drift; the trusted header still
inside the trusting period; the header self-binds its validator set; the TRUST-OVERLAP threshold
`trustNum · trustedTotal < trustDen · trustedSigned` (strictly more than `trustNum/trustDen` of
the TRUSTED set's power signed this header); and the full strict `> 2/3` over the UNTRUSTED set.

There is deliberately NO `nextValidatorsHash` conjunct — skipping's whole nature is that the
target's validator set was never committed by the trusted header. The overlap conjunct is what
takes its place, and `tmSkipNoForgery` is what makes that trade sound. -/
def tmSkipVerify (ts : TmSkipTrusted L) (u : TmSkipUpdate L) : Bool :=
  decide (u.header.chainId = ts.chainId)
  && decide (ts.height + 1 < u.header.height)
  && decide (ts.headerTime < u.header.time)
  && decide (u.header.time ≤ ts.now + ts.clockDrift)
  && decide (ts.now < ts.headerTime + ts.trustingPeriod)
  && decide (L.hash (enc u.validators) = u.header.validatorsHash)
  && decide (ts.trustNum * totalPower ts.nextValidators
              < ts.trustDen * signedPower L (sb u.header) ts.nextValidators u.trustedCommit)
  && decide (2 * totalPower u.validators
              < 3 * signedPower L (sb u.header) u.validators u.commit)

/-- The exact propositional characterization — every rejection/binding theorem below is a
projection of this iff. -/
theorem tmSkipVerify_eq_true_iff (ts : TmSkipTrusted L) (u : TmSkipUpdate L) :
    tmSkipVerify L sb enc ts u = true ↔
      u.header.chainId = ts.chainId
      ∧ ts.height + 1 < u.header.height
      ∧ ts.headerTime < u.header.time
      ∧ u.header.time ≤ ts.now + ts.clockDrift
      ∧ ts.now < ts.headerTime + ts.trustingPeriod
      ∧ L.hash (enc u.validators) = u.header.validatorsHash
      ∧ ts.trustNum * totalPower ts.nextValidators
          < ts.trustDen * signedPower L (sb u.header) ts.nextValidators u.trustedCommit
      ∧ 2 * totalPower u.validators
          < 3 * signedPower L (sb u.header) u.validators u.commit := by
  unfold tmSkipVerify
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-! ## §3 — NO FORGERY for a skip: the FOUR-conjunct foreign validity, overlap included. -/

/-- **What a verified skip buys.** The first three conjuncts are `TmForeignValid`'s (the header
commits its validator set, that commitment BINDS under the CR carrier, and a >2/3-stake sub-list
of that set GENUINELY signed). The fourth is the one skipping needs and adjacency does not: a
sub-list of the TRUSTED next-validator set, carrying strictly more than `trustNum/trustDen` of
THAT set's power, genuinely signed the same header. At the canonical 1/3 that is "at least one
validator the client already trusted, beyond the Byzantine third, endorses this target" — the
reason a skip is not a leap of faith. -/
def TmSkipForeignValid (ts : TmSkipTrusted L) (u : TmSkipUpdate L) : Prop :=
  L.hash (enc u.validators) = u.header.validatorsHash
  ∧ (∀ vs' : List (TmValidator L.PubKey),
      L.hash (enc vs') = u.header.validatorsHash → enc vs' = enc u.validators)
  ∧ (∃ S : List (TmValidator L.PubKey),
      S.Sublist u.validators
      ∧ (∀ v ∈ S, L.Signed v.pubkey (sb u.header))
      ∧ 2 * totalPower u.validators < 3 * totalPower S)
  ∧ (∃ T : List (TmValidator L.PubKey),
      T.Sublist ts.nextValidators
      ∧ (∀ v ∈ T, L.Signed v.pubkey (sb u.header))
      ∧ ts.trustNum * totalPower ts.nextValidators < ts.trustDen * totalPower T)

/-- **NO FORGERY, SKIPPING.** GIVEN the SHA-256 CR carrier, a skip `tmSkipVerify` accepts is
skip-foreign-valid. Both genuine-signer witnesses are `signers …` — over the untrusted set with
the untrusted-aligned commit, and over the TRUSTED set with the trusted-aligned commit — and
their sublist-ness, genuineness and power all come from `LightClientTendermint` §2 unchanged
(`signers_sublist` / `signers_signed` / `signers_power`), so the ed25519 `sigSound` assumption is
consumed in exactly one place and the CR carrier in exactly one other. A chain whose hash
collapses gets no conclusion here either. -/
theorem tmSkipNoForgery (hcr : L.hashCR) (ts : TmSkipTrusted L) (u : TmSkipUpdate L)
    (h : tmSkipVerify L sb enc ts u = true) :
    TmSkipForeignValid L sb enc ts u := by
  obtain ⟨_, _, _, _, _, hbind, hoverlap, hq⟩ := (tmSkipVerify_eq_true_iff L sb enc ts u).mp h
  refine ⟨hbind, ?_, ?_, ?_⟩
  · -- the CR carrier bites: any set encoding hashing to the header's commitment IS the set's
    intro vs' h'
    exact L.noCollision hcr _ _ (h'.trans hbind.symm)
  · exact ⟨signers L (sb u.header) u.validators u.commit,
      signers_sublist L (sb u.header) u.validators u.commit,
      signers_signed L (sb u.header) u.validators u.commit,
      by rw [signers_power]; exact hq⟩
  · exact ⟨signers L (sb u.header) ts.nextValidators u.trustedCommit,
      signers_sublist L (sb u.header) ts.nextValidators u.trustedCommit,
      signers_signed L (sb u.header) ts.nextValidators u.trustedCommit,
      by rw [signers_power]; exact hoverlap⟩

/-! ## §4 — THE TEETH. Each of these refuses with NO crypto hypothesis — they are consequences
of the rule shape alone, so no assumption about ed25519 or SHA-256 can be blamed for them. -/

/-- The empty skip: zero header, NO validators, NO commit, NO trusted-aligned commit. -/
def tmSkipEmptyUpdate (d0 : L.Digest) : TmSkipUpdate L :=
  { header := ⟨0, 0, 0, d0, d0⟩, validators := [], commit := [], trustedCommit := [] }

/-- **FAIL CLOSED (the Nomad-law tooth).** The empty skip is rejected for EVERY trusted state:
with no validators the untrusted total power is 0 and `2·0 < 3·0` is false. An uninitialized
update can never ride a permissive default through this gate either. -/
theorem tmSkipFailClosed (d0 : L.Digest) (ts : TmSkipTrusted L) :
    tmSkipVerify L sb enc ts (tmSkipEmptyUpdate L d0) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨_, _, _, _, _, _, _, hq⟩ :=
    (tmSkipVerify_eq_true_iff L sb enc ts (tmSkipEmptyUpdate L d0)).mp h
  simp [tmSkipEmptyUpdate, totalPower, signedPower] at hq

/-- **THE STALE-ANCHOR TOOTH: zero trust overlap is refused UNCONDITIONALLY.** If no validator
of the trusted next-validator set has a verifying signature in the commit, the overlap tally is
0 and the conjunct `trustNum · trustedTotal < trustDen · 0` is `_ < 0`, false in `Nat` for every
threshold and every trusted set. This is `cosmos-lightclient`'s
`reject_skip_below_trust_overlap_threshold` as a theorem: a light client whose trusted voting
power has moved away MUST bisect, and cannot skip on trust it no longer has. No crypto
hypothesis is used. -/
theorem tmSkip_zero_overlap_rejected (ts : TmSkipTrusted L) (u : TmSkipUpdate L)
    (h : signedPower L (sb u.header) ts.nextValidators u.trustedCommit = 0) :
    tmSkipVerify L sb enc ts u = false := by
  rw [Bool.eq_false_iff]
  intro htrue
  obtain ⟨_, _, _, _, _, _, hoverlap, _⟩ := (tmSkipVerify_eq_true_iff L sb enc ts u).mp htrue
  rw [h, Nat.mul_zero] at hoverlap
  exact absurd hoverlap (Nat.not_lt_zero _)

/-- **A DEGENERATE TRUST THRESHOLD FAILS CLOSED, it does not open the door.** A trusted state
carrying `trustDen = 0` (a malformed `Options.trust_threshold`, which the fraction constructor
rejects but which nothing stops a caller from fabricating in the state) makes the overlap
conjunct `_ < 0` — false. The refusal direction is the safe one, and it is proved rather than
argued. -/
theorem tmSkip_zero_denominator_rejected (ts : TmSkipTrusted L) (u : TmSkipUpdate L)
    (h : ts.trustDen = 0) :
    tmSkipVerify L sb enc ts u = false := by
  rw [Bool.eq_false_iff]
  intro htrue
  obtain ⟨_, _, _, _, _, _, hoverlap, _⟩ := (tmSkipVerify_eq_true_iff L sb enc ts u).mp htrue
  rw [h, Nat.zero_mul] at hoverlap
  exact absurd hoverlap (Nat.not_lt_zero _)

/-- **SUB-QUORUM REJECTION on the UNTRUSTED set** — including EXACTLY 2/3 (the threshold is
strict). Same tooth the adjacent gate has, over the skip rule set. -/
theorem tmSkip_subquorum_rejected (ts : TmSkipTrusted L) (u : TmSkipUpdate L)
    (h : 3 * signedPower L (sb u.header) u.validators u.commit
           ≤ 2 * totalPower u.validators) :
    tmSkipVerify L sb enc ts u = false := by
  rw [Bool.eq_false_iff]
  intro htrue
  obtain ⟨_, _, _, _, _, _, _, hq⟩ := (tmSkipVerify_eq_true_iff L sb enc ts u).mp htrue
  exact absurd hq (Nat.not_lt.mpr h)

/-- **SUB-OVERLAP REJECTION** — including the EXACTLY-`trustNum/trustDen` boundary, which
rejects because `is_enough_power` is strict. -/
theorem tmSkip_suboverlap_rejected (ts : TmSkipTrusted L) (u : TmSkipUpdate L)
    (h : ts.trustDen * signedPower L (sb u.header) ts.nextValidators u.trustedCommit
           ≤ ts.trustNum * totalPower ts.nextValidators) :
    tmSkipVerify L sb enc ts u = false := by
  rw [Bool.eq_false_iff]
  intro htrue
  obtain ⟨_, _, _, _, _, _, hoverlap, _⟩ := (tmSkipVerify_eq_true_iff L sb enc ts u).mp htrue
  exact absurd hoverlap (Nat.not_lt.mpr h)

/-- **CHAIN-ID MISMATCH REJECTION** — the cross-chain replay defense, on the skip path too. -/
theorem tmSkip_chain_mismatch_rejected (ts : TmSkipTrusted L) (u : TmSkipUpdate L)
    (h : u.header.chainId ≠ ts.chainId) :
    tmSkipVerify L sb enc ts u = false := by
  rw [Bool.eq_false_iff]
  intro htrue
  exact h ((tmSkipVerify_eq_true_iff L sb enc ts u).mp htrue).1

/-- **THE TWO EXPORTS PARTITION THE HEIGHT AXIS.** An accepted skip is STRICTLY non-adjacent, so
it can never be the shape `dregg_tm_lc_verify` decides — no header is decided twice, and (with
the routing's height dispatch) none is decided by neither. This is what makes "gate both exports
and every accept path is covered" a real statement rather than a hope. -/
theorem tmSkip_height_disjoint_from_adjacent (ts : TmSkipTrusted L) (u : TmSkipUpdate L)
    (h : tmSkipVerify L sb enc ts u = true) :
    u.header.height ≠ ts.height + 1 := by
  obtain ⟨_, hh, _⟩ := (tmSkipVerify_eq_true_iff L sb enc ts u).mp h
  omega

/-- **ACCEPTANCE BINDS THE TRUST ANCHOR.** An accepted skip carries the trusted chain-id, lands
strictly beyond the adjacent height, and its validator set is the one its own header commits to.
-/
theorem tmSkip_accept_binds_trust (ts : TmSkipTrusted L) (u : TmSkipUpdate L)
    (h : tmSkipVerify L sb enc ts u = true) :
    u.header.chainId = ts.chainId
    ∧ ts.height + 1 < u.header.height
    ∧ L.hash (enc u.validators) = u.header.validatorsHash := by
  obtain ⟨h1, h2, _, _, _, h6, _, _⟩ := (tmSkipVerify_eq_true_iff L sb enc ts u).mp h
  exact ⟨h1, h2, h6⟩

end Rules

/-! ## §5 — THE EXPORTED SCALAR DECISION + the refinement tie, over the projections a deployed
node computes. Grouped to match `tmSkipVerify`'s `&&`-chain EXACTLY so the refinement is `rfl`. -/

/-- **`tmSkipVerifyDecision`** — THE composed non-adjacent decision over the sixteen
scalar/boolean projections. `selfBindOk` carries the SHA-256 validator-set hash-and-compare
result; `trustedSignedPow` and `signedPow` carry the two Ed25519-verified stake tallies. This is
the object `@[export] dregg_tm_skip_verify` renders and `tmSkipNoForgery` is (via
`tmSkipVerifyDecision_refines`) proven over. -/
def tmSkipVerifyDecision (chainId tsChainId height tsHeight headerTime time now clockDrift
    trustingPeriod : Nat) (selfBindOk : Bool)
    (trustNum trustDen trustedTotalPow trustedSignedPow totalPow signedPow : Nat) : Bool :=
  decide (chainId = tsChainId)
  && decide (tsHeight + 1 < height)
  && decide (headerTime < time)
  && decide (time ≤ now + clockDrift)
  && decide (now < headerTime + trustingPeriod)
  && selfBindOk
  && decide (trustNum * trustedTotalPow < trustDen * trustedSignedPow)
  && decide (2 * totalPow < 3 * signedPow)

/-- **`tmSkipProjectedDecision`** — the projections a node hands the gate for a skip `u` under
trusted state `ts`: the scalars, the SHA-256 self-binding RESULT, the threshold fraction, and the
two power sums for each of the two validator sets. The crypto carriers appear here and NOWHERE
else in the gate, as their boolean / `Nat` results. -/
def tmSkipProjectedDecision (L : CryptoLeaf) [DecidableEq L.Digest]
    (sb : TmHeader L.Digest → L.Msg) (enc : List (TmValidator L.PubKey) → L.Msg)
    (ts : TmSkipTrusted L) (u : TmSkipUpdate L) : Bool :=
  tmSkipVerifyDecision u.header.chainId ts.chainId u.header.height ts.height
    ts.headerTime u.header.time ts.now ts.clockDrift ts.trustingPeriod
    (decide (L.hash (enc u.validators) = u.header.validatorsHash))
    ts.trustNum ts.trustDen
    (totalPower ts.nextValidators)
    (signedPower L (sb u.header) ts.nextValidators u.trustedCommit)
    (totalPower u.validators)
    (signedPower L (sb u.header) u.validators u.commit)

/-- **THE TRANSLATION-VALIDATION THEOREM.** Fed a skip's true projections, the exported scalar
decision is DEFINITIONALLY `tmSkipVerify L sb enc ts u`. Gating a deployed node on
`dregg_tm_skip_verify` gates it, definitionally, on the decision `tmSkipNoForgery` is proven
over. -/
theorem tmSkipVerifyDecision_refines (L : CryptoLeaf) [DecidableEq L.Digest]
    (sb : TmHeader L.Digest → L.Msg) (enc : List (TmValidator L.PubKey) → L.Msg)
    (ts : TmSkipTrusted L) (u : TmSkipUpdate L) :
    tmSkipProjectedDecision L sb enc ts u = tmSkipVerify L sb enc ts u := rfl

/-- **THE PAYOFF through the EXPORTED decision.** Acceptance by the projected scalar decision
entails skip-foreign-validity — including the trust-OVERLAP conjunct. -/
theorem tmSkipVerifyDecision_no_forgery (L : CryptoLeaf) [DecidableEq L.Digest]
    (sb : TmHeader L.Digest → L.Msg) (enc : List (TmValidator L.PubKey) → L.Msg)
    (hcr : L.hashCR) (ts : TmSkipTrusted L) (u : TmSkipUpdate L)
    (h : tmSkipProjectedDecision L sb enc ts u = true) :
    TmSkipForeignValid L sb enc ts u :=
  tmSkipNoForgery L sb enc hcr ts u ((tmSkipVerifyDecision_refines L sb enc ts u) ▸ h)

/-! ## §6 — THE WIRE + `@[export]`. Same `String → String` C-ABI shape as `dregg_tm_lc_verify`.
Fail-closed on any malformed wire (`"ERR"` ⇒ the node treats it as REJECT). -/

/-- Parse a `key=value` field, fail-closed on a key mismatch or a missing `=`. -/
def parseField? (key part : String) : Option String :=
  match part.splitOn "=" with
  | [k, v] => if k == key then some v else none
  | _ => none

/-- Parse a single boolean flag (`"1"` / `"0"`), fail-closed on anything else. -/
def parseBit? (s : String) : Option Bool :=
  if s == "1" then some true else if s == "0" then some false else none

/-- **`decodeTmSkipWire`** — parse the full `INPUT` grammar into the sixteen projections.
Fail-closed (`none`) on any deviation.

```
INPUT := "ci=" Nat ";tci=" Nat ";h=" Nat ";th=" Nat ";ht=" Nat ";t=" Nat
       ";nw=" Nat ";cd=" Nat ";tp=" Nat ";vb=" BIT ";tn=" Nat ";td=" Nat
       ";ttot=" Nat ";tsp=" Nat ";tot=" Nat ";sp=" Nat
BIT   := "0" | "1"
```
(`ci`=untrusted chain-id, `tci`=trusted chain-id, `h`=untrusted height, `th`=trusted height,
`ht`=trusted header time, `t`=untrusted time, `nw`=now, `cd`=clock drift, `tp`=trusting period,
`vb`=header-self-binding SHA-256 result, `tn`/`td`=trust-threshold numerator/denominator,
`ttot`=TRUSTED next-validator set total power, `tsp`=Ed25519-verified overlap power in that set,
`tot`=untrusted total voting power, `sp`=Ed25519-verified signed power in the untrusted set.)

The grammar is deliberately NOT a superset of `decodeTmWire`'s: a wire meant for the adjacent
gate has 13 fields and decodes to `none` here, and vice versa, so a mis-routed wire is `"ERR"`
(REJECT) rather than a verdict about the wrong rule set. -/
def decodeTmSkipWire (s : String) :
    Option (Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Bool
            × Nat × Nat × Nat × Nat × Nat × Nat) :=
  match s.splitOn ";" with
  | [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15] => do
      let ci   ← (parseField? "ci"   p0).bind String.toNat?
      let tci  ← (parseField? "tci"  p1).bind String.toNat?
      let h    ← (parseField? "h"    p2).bind String.toNat?
      let th   ← (parseField? "th"   p3).bind String.toNat?
      let ht   ← (parseField? "ht"   p4).bind String.toNat?
      let t    ← (parseField? "t"    p5).bind String.toNat?
      let nw   ← (parseField? "nw"   p6).bind String.toNat?
      let cd   ← (parseField? "cd"   p7).bind String.toNat?
      let tp   ← (parseField? "tp"   p8).bind String.toNat?
      let vb   ← (parseField? "vb"   p9).bind parseBit?
      let tn   ← (parseField? "tn"   p10).bind String.toNat?
      let td   ← (parseField? "td"   p11).bind String.toNat?
      let ttot ← (parseField? "ttot" p12).bind String.toNat?
      let tsp  ← (parseField? "tsp"  p13).bind String.toNat?
      let tot  ← (parseField? "tot"  p14).bind String.toNat?
      let sp   ← (parseField? "sp"   p15).bind String.toNat?
      some (ci, tci, h, th, ht, t, nw, cd, tp, vb, tn, td, ttot, tsp, tot, sp)
  | _ => none

/-- **`tmSkipVerifyGate`** — THE GATE. Decode the wire, run the VERIFIED `tmSkipVerifyDecision`
(refined to `tmSkipVerify`, over which `tmSkipNoForgery` is proven), and encode `"1"` (ACCEPT) /
`"0"` (REJECT). A malformed wire returns `"ERR"` (fail-closed: the node treats it as REJECT). -/
def tmSkipVerifyGate (s : String) : String :=
  match decodeTmSkipWire s with
  | some (ci, tci, h, th, ht, t, nw, cd, tp, vb, tn, td, ttot, tsp, tot, sp) =>
      if tmSkipVerifyDecision ci tci h th ht t nw cd tp vb tn td ttot tsp tot sp then "1" else "0"
  | none => "ERR"

/-- **THE EXPORT.** `@[export dregg_tm_skip_verify]` — the C-ABI entry the node's FFI bridge
(`dregg-lean-ffi`) calls for a NON-ADJACENT advance. `cosmos-lightclient`'s verify path computes
the two Ed25519 tallies + the SHA-256 validator-set hash and passes the projections; the archive
renders the verdict. -/
@[export dregg_tm_skip_verify]
def dregg_tm_skip_verify (s : String) : String := tmSkipVerifyGate s

/-- **The gate string IS the verified decision, by construction.** For any wire that decodes,
the exported gate's output is `"1"`/`"0"` off `tmSkipVerifyDecision` on the decoded projections
— so gating a node on this export gates it, definitionally, on `tmSkipVerify`. -/
theorem tmSkipVerifyGate_eq_decision (s : String)
    (ci tci h th ht t nw cd tp : Nat) (vb : Bool) (tn td ttot tsp tot sp : Nat)
    (hd : decodeTmSkipWire s
            = some (ci, tci, h, th, ht, t, nw, cd, tp, vb, tn, td, ttot, tsp, tot, sp)) :
    tmSkipVerifyGate s
      = (if tmSkipVerifyDecision ci tci h th ht t nw cd tp vb tn td ttot tsp tot sp
         then "1" else "0") := by
  unfold tmSkipVerifyGate
  rw [hd]

/-! ## §7 — NON-VACUITY: the DECISION DISCRIMINATES, kernel-clean.

Pure `Nat`/`Bool`, so `decide` reduces it in the kernel. The accepting row is a genuine skip
(trusted set of total power 3 with overlap 2 at threshold 1/3; untrusted set of total power 3
fully signed). Every other row is a ONE-FIELD deviation that must reject. -/

theorem tmSkip_decision_discriminates :
    -- ACCEPT: chain 5, skip 10 → 105, overlap 2 of trusted 3 at 1/3, 3 of 3 untrusted
    tmSkipVerifyDecision 5 5 105 10 50 55 60 5 100 true 1 3 3 2 3 3 = true
    -- overlap EXACTLY 1/3 (1 of 3): `1·3 < 3·1` is false — strict threshold
    ∧ tmSkipVerifyDecision 5 5 105 10 50 55 60 5 100 true 1 3 3 1 3 3 = false
    -- ZERO overlap: the stale-anchor tooth
    ∧ tmSkipVerifyDecision 5 5 105 10 50 55 60 5 100 true 1 3 3 0 3 3 = false
    -- ADJACENT height (11 = 10+1): NOT this decision's shape
    ∧ tmSkipVerifyDecision 5 5 11 10 50 55 60 5 100 true 1 3 3 2 3 3 = false
    -- BACKWARD height (9 < 10)
    ∧ tmSkipVerifyDecision 5 5 9 10 50 55 60 5 100 true 1 3 3 2 3 3 = false
    -- untrusted sub-quorum EXACTLY 2/3 (2 of 3): strict `> 2/3` rejects
    ∧ tmSkipVerifyDecision 5 5 105 10 50 55 60 5 100 true 1 3 3 2 3 2 = false
    -- wrong chain-id
    ∧ tmSkipVerifyDecision 6 5 105 10 50 55 60 5 100 true 1 3 3 2 3 3 = false
    -- stale (non-monotonic) time: 45 < trusted 50
    ∧ tmSkipVerifyDecision 5 5 105 10 50 45 60 5 100 true 1 3 3 2 3 3 = false
    -- from the future: 99 > now 60 + drift 5
    ∧ tmSkipVerifyDecision 5 5 105 10 50 99 60 5 100 true 1 3 3 2 3 3 = false
    -- trusting period expired: now 200 ≥ 50 + 100
    ∧ tmSkipVerifyDecision 5 5 105 10 50 55 200 5 100 true 1 3 3 2 3 3 = false
    -- header does not self-bind its validator set
    ∧ tmSkipVerifyDecision 5 5 105 10 50 55 60 5 100 false 1 3 3 2 3 3 = false
    -- degenerate threshold denominator 0: fails CLOSED
    ∧ tmSkipVerifyDecision 5 5 105 10 50 55 60 5 100 true 1 0 3 2 3 3 = false
    -- a threshold of 1/1 (unanimity of the trusted set) is not met by 2 of 3
    ∧ tmSkipVerifyDecision 5 5 105 10 50 55 60 5 100 true 1 1 3 2 3 3 = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §8 — The MODEL skip, end-to-end through the projection pipeline (crypto results included).

The trusted epoch is `demoValidators` (keys 1,2,3 — total power 3). The skip target at height
105 is signed by a ROTATED set (keys 1,2,7 — total power 3), i.e. validator 3 has left and 7 has
joined. The trusted-aligned commit therefore holds signatures for 1 and 2 and `none` for 3:
overlap power 2 of trusted total 3, which clears 1/3 strictly. The target's own set fully signs,
clearing 2/3 strictly. No `nextValidatorsHash` is consulted anywhere — that is the skip. -/

/-- The rotated validator set that signs the skip target: validator 3 has left, 7 has joined.
Two of the three trusted-epoch keys remain, which is what makes the overlap 2. -/
def skipValidators : List (TmValidator Nat) := [⟨1, 1⟩, ⟨2, 1⟩, ⟨7, 1⟩]

/-- The skip-target header: right chain (5), height 105 (95 blocks past the trusted 10), time
inside the window, `validatorsHash` really committing `skipValidators`. -/
def skipHeader : TmHeader Nat :=
  { chainId := 5, height := 105, time := 55
    validatorsHash := demoHash (demoValSetEncode skipValidators)
    appHash := 4242 }

/-- The trusted state for the skip: the same anchor as `ts0` but carrying the trusted SET as the
overlap base and the canonical 1/3 threshold. -/
def skipTs0 : TmSkipTrusted demoLeaf :=
  { chainId := 5, height := 10, headerTime := 50, now := 60, clockDrift := 5
    trustingPeriod := 100
    nextValidators := demoValidators
    trustNum := 1, trustDen := 3 }

/-- The genuine skip: the rotated set fully signs the target, and the SAME commit re-aligned to
the trusted set holds 1's and 2's signatures with `none` for the departed validator 3. -/
def genuineSkip : TmSkipUpdate demoLeaf :=
  { header := skipHeader
    validators := skipValidators
    commit := [some (1 + demoSignBytes skipHeader), some (2 + demoSignBytes skipHeader),
               some (7 + demoSignBytes skipHeader)]
    trustedCommit := [some (1 + demoSignBytes skipHeader), some (2 + demoSignBytes skipHeader),
                      none] }

/-- The STALE-ANCHOR skip: the target is signed by a set that shares NOTHING with the trusted
epoch (keys 8, 9, 10), so the trusted-aligned commit is all-`none` and the overlap is 0. This is
`reject_skip_below_trust_overlap_threshold`'s scenario, and it must refuse. -/
def staleAnchorValidators : List (TmValidator Nat) := [⟨8, 1⟩, ⟨9, 1⟩, ⟨10, 1⟩]
def staleAnchorHeader : TmHeader Nat :=
  { chainId := 5, height := 105, time := 55
    validatorsHash := demoHash (demoValSetEncode staleAnchorValidators)
    appHash := 4242 }
def staleAnchorSkip : TmSkipUpdate demoLeaf :=
  { header := staleAnchorHeader
    validators := staleAnchorValidators
    commit := [some (8 + demoSignBytes staleAnchorHeader),
               some (9 + demoSignBytes staleAnchorHeader),
               some (10 + demoSignBytes staleAnchorHeader)]
    trustedCommit := [none, none, none] }

/-- A skip whose overlap is EXACTLY 1/3 (only validator 1 remains from the trusted epoch): the
strict threshold rejects it, and the light client must bisect. -/
def thinOverlapSkip : TmSkipUpdate demoLeaf :=
  { genuineSkip with
    trustedCommit := [some (1 + demoSignBytes skipHeader), none, none] }

/-- **THE ASSEMBLED DISCRIMINATOR over the RULES.** Under the same trusted state the skip rules
accept the genuine rotated-set skip and reject: the stale anchor (zero overlap), the
exactly-1/3 overlap (strict), and the empty update. -/
theorem tmSkip_rules_discriminate :
    tmSkipVerify demoLeaf demoSignBytes demoValSetEncode skipTs0 genuineSkip = true
    ∧ tmSkipVerify demoLeaf demoSignBytes demoValSetEncode skipTs0 staleAnchorSkip = false
    ∧ tmSkipVerify demoLeaf demoSignBytes demoValSetEncode skipTs0 thinOverlapSkip = false
    ∧ tmSkipVerify demoLeaf demoSignBytes demoValSetEncode skipTs0
        (tmSkipEmptyUpdate demoLeaf (0 : Nat)) = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **THE EXPORTED DECISION ACCEPTS THE MODEL GOOD SKIP, end-to-end** — obtained by refining to
`tmSkipVerify` and reusing `tmSkip_rules_discriminate`, so the whole projection pipeline (both
crypto tallies included) is exercised. By `tmSkipVerifyDecision_no_forgery` that acceptance
entails `TmSkipForeignValid`. -/
theorem tmSkip_gate_accepts_model_good :
    tmSkipProjectedDecision demoLeaf demoSignBytes demoValSetEncode skipTs0 genuineSkip = true :=
  (tmSkipVerifyDecision_refines demoLeaf demoSignBytes demoValSetEncode skipTs0 genuineSkip).trans
    tmSkip_rules_discriminate.1

/-- **THE OVERLAP CONJUNCT IS INHABITED, not decoration.** The genuine skip really is
skip-foreign-valid: `[⟨1,1⟩, ⟨2,1⟩]` is a sub-list of the TRUSTED epoch set whose members
genuinely signed the skip target and whose power clears 1/3 strictly. Discharged through the
theorem, with `demoLeaf_hashCR` supplying the CR carrier — so the fourth conjunct is witnessed
by a real object rather than asserted. -/
theorem tmSkip_valid_holds :
    TmSkipForeignValid demoLeaf demoSignBytes demoValSetEncode skipTs0 genuineSkip :=
  tmSkipNoForgery demoLeaf demoSignBytes demoValSetEncode demoLeaf_hashCR skipTs0 genuineSkip
    tmSkip_rules_discriminate.1

/-- A trusted anchor whose epoch set is a single UNREGISTERED key (777 — the demo's `Signed`
denotation is `pk < 100`, so no signature by it can ever be genuine). Used to falsify the
OVERLAP conjunct specifically: `genuineSkip` satisfies the other three, so a refutation here
isolates the fourth. -/
def unregisteredTrustedTs : TmSkipTrusted demoLeaf :=
  { skipTs0 with nextValidators := [⟨777, 3⟩] }

/-- **THE OVERLAP CONJUNCT IS FALSIFIABLE (the other polarity — it is not decoration).** Against
a trusted epoch made of an unregistered key, `genuineSkip` is NOT skip-foreign-valid even though
it satisfies the three conjuncts `TmForeignValid` already had: any witness sub-list carrying
more than 1/3 of that set's power is non-empty, hence contains key 777, and `Signed 777 _` is
false. So the fourth conjunct genuinely separates updates — a skip's trust anchor has to have
really signed, and the crypto denotation is what says so. -/
theorem tmSkip_unregistered_overlap_invalid :
    ¬ TmSkipForeignValid demoLeaf demoSignBytes demoValSetEncode
        unregisteredTrustedTs genuineSkip := by
  rintro ⟨_, _, _, T, hsub, hsigned, hov⟩
  cases T with
  | nil => simp [unregisteredTrustedTs, skipTs0, totalPower] at hov
  | cons v T' =>
    have hv : v ∈ unregisteredTrustedTs.nextValidators :=
      hsub.subset (List.mem_cons_self ..)
    have hveq : v = ⟨777, 3⟩ := by
      simpa [unregisteredTrustedTs, skipTs0] using hv
    have hs := hsigned v (List.mem_cons_self ..)
    rw [hveq] at hs
    simp [demoSigned] at hs

/-- **AND THE SAME ANCHOR IS REJECTED BY THE RULES**, so the falsifier above is not describing
a state the gate would have accepted: the overlap tally over `[⟨777, 3⟩]` is 0 (the commit
carries no signature for it), and `tmSkip_zero_overlap_rejected` refuses. Both halves —
"the predicate fails" and "the gate refuses" — are pinned. -/
theorem tmSkip_unregistered_anchor_rejected :
    tmSkipVerify demoLeaf demoSignBytes demoValSetEncode unregisteredTrustedTs genuineSkip
      = false := by decide

/-! ### It runs (`#guard`): the wire gate + the scalar decision discriminate on concrete data. -/

#guard tmSkipVerifyGate
  "ci=5;tci=5;h=105;th=10;ht=50;t=55;nw=60;cd=5;tp=100;vb=1;tn=1;td=3;ttot=3;tsp=2;tot=3;sp=3"
  == "1"
#guard tmSkipVerifyGate
  "ci=5;tci=5;h=105;th=10;ht=50;t=55;nw=60;cd=5;tp=100;vb=1;tn=1;td=3;ttot=3;tsp=1;tot=3;sp=3"
  == "0"
#guard tmSkipVerifyGate
  "ci=5;tci=5;h=105;th=10;ht=50;t=55;nw=60;cd=5;tp=100;vb=1;tn=1;td=3;ttot=3;tsp=0;tot=3;sp=3"
  == "0"
#guard tmSkipVerifyGate
  "ci=5;tci=5;h=11;th=10;ht=50;t=55;nw=60;cd=5;tp=100;vb=1;tn=1;td=3;ttot=3;tsp=2;tot=3;sp=3"
  == "0"
#guard tmSkipVerifyGate "garbage" == "ERR"
-- The ADJACENT gate's 13-field wire is NOT a valid skip wire: mis-routing is `"ERR"`, never a
-- verdict about the wrong rule set.
#guard tmSkipVerifyGate "ci=5;tci=5;h=11;th=10;ht=50;t=55;nw=60;cd=5;tp=100;eb=1;vb=1;tot=3;sp=3"
  == "ERR"
#guard dregg_tm_skip_verify
  "ci=5;tci=5;h=105;th=10;ht=50;t=55;nw=60;cd=5;tp=100;vb=1;tn=1;td=3;ttot=3;tsp=2;tot=3;sp=3"
  == "1"

/-! ## §9 — Axiom hygiene. The crypto carriers are the visible `CryptoLeaf` fields / the `hcr`
hypothesis, invisible to `#assert_axioms` exactly because they are the audit surface (see
`LightClientTendermint.lean` §8). -/

#assert_axioms tmSkipVerify_eq_true_iff
#assert_axioms tmSkipNoForgery
#assert_axioms tmSkipFailClosed
#assert_axioms tmSkip_zero_overlap_rejected
#assert_axioms tmSkip_zero_denominator_rejected
#assert_axioms tmSkip_subquorum_rejected
#assert_axioms tmSkip_suboverlap_rejected
#assert_axioms tmSkip_chain_mismatch_rejected
#assert_axioms tmSkip_height_disjoint_from_adjacent
#assert_axioms tmSkip_accept_binds_trust
#assert_axioms tmSkipVerifyDecision_refines
#assert_axioms tmSkipVerifyDecision_no_forgery
#assert_axioms tmSkipVerifyGate_eq_decision
#assert_axioms tmSkip_decision_discriminates
#assert_axioms tmSkip_rules_discriminate
#assert_axioms tmSkip_gate_accepts_model_good
#assert_axioms tmSkip_valid_holds
#assert_axioms tmSkip_unregistered_overlap_invalid
#assert_axioms tmSkip_unregistered_anchor_rejected

#print axioms tmSkipVerifyDecision_refines
#print axioms tmSkipNoForgery
#print axioms tmSkip_zero_overlap_rejected

end Dregg2.Bridge.LightClientTendermintSkip
