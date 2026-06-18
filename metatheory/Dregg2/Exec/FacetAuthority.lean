/-
# Dregg2.Exec.FacetAuthority — the FAITHFUL deployed authority model (`AuthRequired` tier × `EffectMask` facet).

## Why this module exists (the kernel-fidelity correction, decision #2(A))

The kernel's `Dregg2.Exec.authorizedB` (`Kernel.lean`) authorizes a turn over `src` by a TOY
test: the actor owns `src`, OR holds a `Cap.node src`, OR an `endpoint src` cap whose abstract
`List Auth` rights `contains Auth.write`. The DEPLOYED system the kernel is supposed to refine
authorizes by TWO axes, BOTH committed in the 7-field cap leaf (`circuit/src/cap_root.rs`,
`DeployedCapTree.CapLeaf`):

  * an **`AuthRequired` tier** — `auth_tag` (`cell/src/permissions.rs::AuthRequired`:
    `None`/`Signature`/`Proof`/`Either`/`Impossible`/`Custom{vk_hash}`) — the auth METHOD a
    holder must satisfy to exercise the cap (a signature, a proof, either, never, or a
    custom-verifier witness);
  * an **`EffectMask` facet** — `mask_lo`/`mask_hi` (`cell/src/facet.rs`: a `u32` bitmask, one
    bit per effect KIND) — which effect kinds the cap permits, checked by
    `is_effect_permitted(mask, EFFECT_<kind>) = EFFECT_<kind> & mask != 0` (with
    `Some(0) = deny-all`, the P2-1 fix), and attenuated bitwise-subset by
    `is_facet_attenuation(parent, child) = child & parent == child` (the E-language non-amp).

This module models that deployed cap FAITHFULLY and defines `authorizedFacetB`: the actor holds
a cap over `turn.src` whose FACET permits the turn's effect-kind AND whose TIER is satisfied by
the authorization the turn provides. It is PURELY ADDITIVE — the toy `authorizedB`/`List Auth`
machinery is untouched (the cutover that retires it is `§10`, run by the main loop).

## What is faithful to what (the field-by-field contract)

  * `AuthTier` ≡ `AuthRequired` (`permissions.rs:5`): the SIX constructors, byte order
    None=0…Custom=5 (`cap_root.rs:46` `auth_tag`). `AuthProvided` ≡ `AuthKind`
    (`permissions.rs:76`). `AuthTier.isSatisfiedBy` ≡ `AuthRequired::is_satisfied_by`
    (`permissions.rs:33`, incl. `Custom`/`Impossible` fail-closed). `AuthTier.narrowerOrEqual`
    ≡ `AuthRequired::is_narrower_or_equal` (`permissions.rs:52`).
  * `EffectMask := Nat` (the deployed `u32`). `EFFECT_<kind>` ≡ `facet.rs:36-77` bit positions.
    `isEffectPermitted` ≡ `is_effect_permitted` (`facet.rs:123`, incl. `some 0 = deny-all`).
    `isFacetAttenuation` ≡ `is_facet_attenuation` (`facet.rs:107`, bitwise subset).
  * `FacetCap` carries `target`, `tier`, `facet` (= the deployed `CapabilityRef`'s
    `{target, permissions, allowed_effects}`, the authority-bearing core), and an `effectKind`
    accessor maps a turn's intent to its `EFFECT_<kind>` bit. `authorizedFacetB` welds to the
    `AuthModes.facetOk` Bool the abstract six-mode dispatcher already reads.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. No `sorry`, no `native_decide`,
no `:= True`, no faked constants. Pure, `#guard`-able. NEW names only; imports read-only.
-/
import Dregg2.Exec.Kernel
import Dregg2.Tactics

namespace Dregg2.Exec.FacetAuthority

open Dregg2.Authority (Label Caps)

set_option autoImplicit false

/-! ## §1 — the `AuthRequired` TIER axis (faithful to `cell/src/permissions.rs`).

The auth METHOD a cap holder must satisfy. The deployed `auth_tag` felt is the tier byte
(`None=0…Custom=5`). We keep the six constructors and the two order-theoretic operations the
deployed system uses: `is_satisfied_by` (does a provided `AuthKind` discharge the tier?) and
`is_narrower_or_equal` (the attenuation order on tiers). -/

/-- **`AuthTier`** ≡ `cell/src/permissions.rs::AuthRequired`. The auth method required to exercise
a cap. `custom vkHash` carries the verification-key hash (folded to a felt in `auth_tag`). -/
inductive AuthTier where
  /-- (0) `None` — always allowed, no authorization needed. -/
  | none
  /-- (1) `Signature` — an Ed25519 signature from the cell's key. -/
  | signature
  /-- (2) `Proof` — a ZK proof matching the cell's verification key. -/
  | proof
  /-- (3) `Either` — a signature OR a proof suffices. -/
  | either
  /-- (4) `Impossible` — permanently locked; this action can never be performed. -/
  | impossible
  /-- (5) `Custom vkHash` — app-defined: requires a `Custom` witness whose `vk_hash` matches. -/
  | custom (vkHash : Nat)
  deriving DecidableEq, Repr

/-- The deployed `auth_tag` tier BYTE (`cap_root.rs:46`: `None=0…Custom=5`). The `custom` case
absorbs `vkHash` in the deployed leaf; here the byte is the discriminant `5` (the leaf's
`auth_tag` felt additionally mixes `vkHash`, modelled by `CapLeaf.auth_tag` carrying it). -/
def AuthTier.tierByte : AuthTier → Nat
  | .none       => 0
  | .signature  => 1
  | .proof      => 2
  | .either     => 3
  | .impossible => 4
  | .custom _   => 5

/-- **`AuthProvided`** ≡ `cell/src/permissions.rs::AuthKind` — the auth a turn actually supplies. -/
inductive AuthProvided where
  /-- An Ed25519 signature was provided. -/
  | signature
  /-- A ZK proof was provided. -/
  | proof
  /-- An app-defined `Custom` witness with the named `vk_hash` was provided + verified. -/
  | custom (vkHash : Nat)
  deriving DecidableEq, Repr

/-- **`AuthTier.isSatisfiedBy`** ≡ `AuthRequired::is_satisfied_by` (`permissions.rs:33`), EXTENDED
faithfully to the `Custom` provided witness: `None` is always satisfied; `Signature`/`Proof`
match the provided kind; `Either` accepts a sig OR a proof; `Impossible` is never satisfied; a
`Custom vk` tier is satisfied ONLY by a `Custom vk'` provided witness with `vk = vk'` (the
executor's per-variant `vk_hash` check — the `AuthKind` lattice alone can NOT discharge it, so a
plain `Signature`/`Proof` does not satisfy `Custom`, exactly as the Rust documents). -/
def AuthTier.isSatisfiedBy : AuthTier → AuthProvided → Bool
  | .none,         _              => true
  | .signature,    .signature     => true
  | .signature,    _              => false
  | .proof,        .proof         => true
  | .proof,        _              => false
  | .either,       .signature     => true
  | .either,       .proof         => true
  | .either,       _              => false
  | .impossible,   _              => false
  | .custom vk,    .custom vk'    => decide (vk = vk')
  | .custom _,     _              => false

/-- **`AuthTier.narrowerOrEqual self other`** ≡ `AuthRequired::is_narrower_or_equal`
(`permissions.rs:52`): `self` is at least as restrictive as `other`. `Impossible` is the bottom
(narrowest); `None` is the top (broadest); `Proof`/`Signature` are narrower than `Either`; two
`Custom`s are comparable only on `vk_hash` equality; `Custom` is incomparable with the IPC
tiers. Faithful to the Rust match arm-for-arm. -/
def AuthTier.narrowerOrEqual : AuthTier → AuthTier → Bool
  | .impossible,  _            => true                 -- Impossible most restrictive
  | _,            .impossible  => false                -- (_, Impossible): only Impossible ≤ Impossible
  | _,            .none        => true                 -- None least restrictive
  | .none,        _            => false                -- None ≤ x only when x = None (handled above)
  | .proof,       .either      => true                 -- Proof narrower than Either
  | .signature,   .either      => true                 -- Signature narrower than Either
  | .custom a,    .custom b     => decide (a = b)       -- equal vk_hash only
  | .custom _,    _            => false                -- Custom vs Sig/Proof/Either: incomparable
  | _,            .custom _     => false
  | a,            b            => decide (a = b)        -- same level

/-! ## §2 — the `EffectMask` FACET axis (faithful to `cell/src/facet.rs`).

`EffectMask = u32`, one bit per effect KIND. We model the felt mask as a `Nat` (the deployed
`u32`); the deployed leaf splits it `mask_lo`/`mask_hi`. The two load-bearing operations are
`is_effect_permitted` (does the mask carry this effect's bit?) and `is_facet_attenuation`
(bitwise subset = the non-amp narrowing). -/

/-- The deployed `EffectMask` (`facet.rs:31`, a `u32`); here `Nat` (deployment is `u32`). -/
abbrev EffectMask := Nat

/-- Effect-kind bit positions, EXACTLY `cell/src/facet.rs:36-77` (`EFFECT_<kind> = 1 << n`). -/
def EFFECT_SET_FIELD          : EffectMask := 1 <<< 0
def EFFECT_TRANSFER           : EffectMask := 1 <<< 1
def EFFECT_GRANT_CAPABILITY   : EffectMask := 1 <<< 2
def EFFECT_REVOKE_CAPABILITY  : EffectMask := 1 <<< 3
def EFFECT_EMIT_EVENT         : EffectMask := 1 <<< 4
def EFFECT_INCREMENT_NONCE    : EffectMask := 1 <<< 5
def EFFECT_CREATE_CELL        : EffectMask := 1 <<< 6
def EFFECT_SET_PERMISSIONS    : EffectMask := 1 <<< 7
def EFFECT_SET_VERIFICATION_KEY : EffectMask := 1 <<< 8

/-- `EFFECT_ALL` = `0xFFFF_FFFF` (`facet.rs:80`, all kinds permitted = unrestricted-when-`Some`). -/
def EFFECT_ALL : EffectMask := 0xFFFF_FFFF

/-- **`isEffectPermitted mask effectBit`** ≡ `cell/src/facet.rs:123` `is_effect_permitted`:
`none ⇒ unrestricted` (all permitted); `some 0 ⇒ deny-all` (the P2-1 fix: a zero mask denies,
NOT widens); `some m ⇒ effectBit &&& m ≠ 0`. -/
def isEffectPermitted : Option EffectMask → EffectMask → Bool
  | .none,       _        => true
  | .some 0,     _        => false
  | .some m,     bit      => decide (bit &&& m ≠ 0)

/-- **`isFacetAttenuation parent child`** ≡ `cell/src/facet.rs:107` `is_facet_attenuation`:
`child` is a bitwise SUBSET of `parent` (`child &&& parent = child`) — the E-language
non-amplification: facets only restrict, never widen. -/
def isFacetAttenuation (parent child : EffectMask) : Bool :=
  decide (child &&& parent = child)

/-! ## §3 — `FacetCap`: the deployed cap's authority-bearing core (faithful to `CapabilityRef`).

`cell/src/capability.rs::CapabilityRef` carries `{target, slot, permissions: AuthRequired,
allowed_effects: Option<EffectMask>, breadstuff, expires_at, stored_epoch}`. The AUTHORITY core
— what gates exercise — is `(target, permissions, allowed_effects)`. `FacetCap` models exactly
that triple. (`slot`/`breadstuff`/`expires_at`/`stored_epoch` are c-list / freshness metadata,
orthogonal to the tier×facet authority decision modelled here; freshness is the
`AuthContext.freshOk` bit in `AuthModes`.) -/

/-- **`FacetCap`** — the deployed cap's authority core (`capability.rs::CapabilityRef`):
the connectivity `target`, the `AuthRequired` `tier`, and the `Option EffectMask` `facet`
(`allowed_effects` — `none` = unrestricted). -/
structure FacetCap where
  /-- The capability's target cell (`CapabilityRef::target`). -/
  target : Label
  /-- The required-auth tier (`CapabilityRef::permissions : AuthRequired`). -/
  tier   : AuthTier
  /-- The facet mask (`CapabilityRef::allowed_effects : Option EffectMask`; `none` = all). -/
  facet  : Option EffectMask
  deriving DecidableEq, Repr

/-- The c-list face: a cell's held `FacetCap`s, keyed by holder label (the deployed
`CapabilitySet` per cell). -/
abbrev FacetCaps := Label → List FacetCap

/-! ## §4 — the EFFECT KIND of a turn (which `EFFECT_<bit>` it requires).

A `Kernel.Turn` is a value MOVEMENT `src ⇒ dst` — the deployed `Effect::Transfer`, so it
requires the `EFFECT_TRANSFER` bit. We expose the mapping as a function so the cutover and other
effect families (set-field, grant, …) extend it; the transfer turn pins `EFFECT_TRANSFER`. -/

/-- The effect-kind bit a balance-movement `Turn` requires: `EFFECT_TRANSFER` (`facet.rs:37`).
A transfer's facet gate is `isEffectPermitted cap.facet (turnEffectBit _) = EFFECT_TRANSFER`. -/
def turnEffectBit (_ : Turn) : EffectMask := EFFECT_TRANSFER

/-! ## §5 — `authorizedFacetB`: the FAITHFUL two-axis authority gate.

The deployed authority decision over a turn: the actor holds a `FacetCap` over `turn.src` whose
FACET permits the turn's effect-kind (`isEffectPermitted`) AND whose TIER is satisfied by the
authorization the turn provides (`isSatisfiedBy`). Owning `src` (`actor = src`) is the intra-vat
l4v `troa_lrefl` short-circuit (own-it ⇒ arbitrary change), exactly as the toy `authorizedB`. -/

/-- A held `FacetCap` AUTHORIZES the turn iff it targets `src`, its facet permits the turn's
effect bit, and its tier is satisfied by `provided`. The per-cap leg of the two-axis gate. -/
def capAuthorizesFacet (provided : AuthProvided) (turn : Turn) (c : FacetCap) : Bool :=
  decide (c.target = turn.src)
    && isEffectPermitted c.facet (turnEffectBit turn)
    && c.tier.isSatisfiedBy provided

/-- **`authorizedFacetB caps provided turn`** — THE faithful deployed authority gate. The actor
owns `src` (intra-vat), OR holds some `FacetCap` over `src` that authorizes the turn on BOTH
axes (facet permits the effect-kind AND the tier is satisfied by `provided`). This is the
tier×facet replacement for the kernel's toy `authorizedB`. -/
def authorizedFacetB (caps : FacetCaps) (provided : AuthProvided) (turn : Turn) : Bool :=
  decide (turn.actor = turn.src)
    || (caps turn.actor).any (capAuthorizesFacet provided turn)

/-! ## §5.G — `authorizedFacetEffB`: the GENERAL two-axis gate over the turn's ACTUAL effect bit.

`authorizedFacetB`/`capAuthorizesFacet` above hardwire `turnEffectBit turn = EFFECT_TRANSFER`, so the
facet axis only ever checks the TRANSFER bit — the cap-open then authorizes ANY effect's transfer-facet
cap regardless of the effect being performed (the residual-(a) under-binding). The general gate takes
the turn's ACTUAL effect-kind bit `effectBit : EffectMask` as a parameter and checks the held cap's
facet against THAT bit (`isEffectPermitted c.facet effectBit`), so a cap permitting a DIFFERENT effect
than the turn performs is REJECTED. `authorizedFacetB` is the `EFFECT_TRANSFER` instance recovered when
`effectBit := turnEffectBit turn`. -/

/-- A held `FacetCap` AUTHORIZES the turn FOR a specific effect-kind `effectBit` iff it targets `src`,
its facet permits THAT effect bit, and its tier is satisfied. The general (effect-parameterized) per-cap
leg; `capAuthorizesFacet` is the `turnEffectBit turn` instance. -/
def capAuthorizesFacetEff (provided : AuthProvided) (effectBit : EffectMask) (turn : Turn)
    (c : FacetCap) : Bool :=
  decide (c.target = turn.src)
    && isEffectPermitted c.facet effectBit
    && c.tier.isSatisfiedBy provided

/-- **`authorizedFacetEffB caps provided effectBit turn`** — THE general two-axis authority gate, over
the turn's ACTUAL effect-kind bit. The actor owns `src` (intra-vat), OR holds some `FacetCap` over `src`
whose facet permits `effectBit` AND whose tier is satisfied by `provided`. The facet axis now checks the
turn's GENUINE effect (NOT the constant `EFFECT_TRANSFER`), so a cap permitting a different effect is
rejected. `authorizedFacetB = authorizedFacetEffB … (turnEffectBit turn)`. -/
def authorizedFacetEffB (caps : FacetCaps) (provided : AuthProvided) (effectBit : EffectMask)
    (turn : Turn) : Bool :=
  decide (turn.actor = turn.src)
    || (caps turn.actor).any (capAuthorizesFacetEff provided effectBit turn)

/-- `capAuthorizesFacet` is the `turnEffectBit turn` instance of the general per-cap leg. -/
theorem capAuthorizesFacet_eq_eff (provided : AuthProvided) (turn : Turn) (c : FacetCap) :
    capAuthorizesFacet provided turn c
      = capAuthorizesFacetEff provided (turnEffectBit turn) turn c := rfl

/-- **`authorizedFacetB` is the `turnEffectBit turn` instance of `authorizedFacetEffB`.** The general
effect-parameterized gate at the transfer bit IS the transfer-pinned gate — so every theorem about
`authorizedFacetB` is a specialization of one about `authorizedFacetEffB`. -/
theorem authorizedFacetB_eq_eff (caps : FacetCaps) (provided : AuthProvided) (turn : Turn) :
    authorizedFacetB caps provided turn
      = authorizedFacetEffB caps provided (turnEffectBit turn) turn := rfl

/-- **`authorizedFacetEffB_owner`** — owning `src` short-circuits to authorized (intra-vat), for ANY
effect bit (the owner leg is effect-agnostic — own-it ⇒ arbitrary change). -/
theorem authorizedFacetEffB_owner (caps : FacetCaps) (provided : AuthProvided) (effectBit : EffectMask)
    (turn : Turn) (h : turn.actor = turn.src) :
    authorizedFacetEffB caps provided effectBit turn = true := by
  unfold authorizedFacetEffB
  simp [h]

/-- **`authorizedFacetEffB_holds_cap`** — a non-owner holding a `FacetCap` over `src` whose facet
permits the turn's ACTUAL `effectBit` under a satisfied tier IS authorized for that effect (the general
two-axis admit). -/
theorem authorizedFacetEffB_holds_cap
    (caps : FacetCaps) (provided : AuthProvided) (effectBit : EffectMask) (turn : Turn) (c : FacetCap)
    (hmem : c ∈ caps turn.actor)
    (htgt : c.target = turn.src)
    (hfacet : isEffectPermitted c.facet effectBit = true)
    (htier : c.tier.isSatisfiedBy provided = true) :
    authorizedFacetEffB caps provided effectBit turn = true := by
  unfold authorizedFacetEffB
  simp only [Bool.or_eq_true, List.any_eq_true]
  right
  exact ⟨c, hmem, by unfold capAuthorizesFacetEff; simp [htgt, hfacet, htier]⟩

/-- **`wrong_effect_unauthorized` — the GENERAL facet axis BITES (witness FALSE).** A non-owner holding
a cap whose facet permits ONLY `permitted` is NOT authorized for a turn performing a DIFFERENT
single-bit effect `wanted` (with `permitted ≠ 0`, `wanted ≠ 0`, and `wanted &&& permitted = 0` — the two
effect bits are disjoint). The facet axis rejects the cap because the turn's actual effect is outside the
cap's mask — exactly the under-binding `authorizedFacetB` could not catch. -/
theorem wrong_effect_unauthorized
    (actor src dst : Label) (amt : ℤ) (tier : AuthTier) (provided : AuthProvided)
    (permitted wanted : EffectMask)
    (hsat : tier.isSatisfiedBy provided = true) (hne : actor ≠ src)
    (hdisjoint : wanted &&& permitted = 0) :
    authorizedFacetEffB
        (fun a => if a = actor then [{ target := src, tier := tier, facet := some permitted }] else [])
        provided wanted { actor := actor, src := src, dst := dst, amt := amt } = false := by
  unfold authorizedFacetEffB
  have howner : (decide (({ actor := actor, src := src, dst := dst, amt := amt } : Turn).actor
      = ({ actor := actor, src := src, dst := dst, amt := amt } : Turn).src)) = false := by
    simp [hne]
  rw [howner, Bool.false_or]
  -- the actor's only held cap rejects `wanted` on the facet axis: wanted &&& permitted = 0.
  have hperm : isEffectPermitted (some permitted) wanted = false := by
    unfold isEffectPermitted
    by_cases hz : permitted = 0
    · subst hz; rfl
    · -- some (permitted ≠ 0): decide (wanted &&& permitted ≠ 0) = false since wanted &&& permitted = 0.
      cases permitted with
      | zero => exact absurd rfl hz
      | succ n => simp [hdisjoint]
  simp only [if_true, List.any_cons, List.any_nil, Bool.or_false, capAuthorizesFacetEff,
    hperm, Bool.and_false, Bool.false_and]

/-! ## §6 — the FAITHFUL teeth (both polarities, non-vacuous).

(1) NON-AMP = the facet bitwise-narrowing is a real subset gate;
(2) a wrong-facet, unauthorized, or wrong-tier action is REJECTED. -/

/-! ### §6.1 — non-amplification: `isFacetAttenuation` is the bitwise-subset non-amp. -/

/-- **`facet_attenuation_self`** — the identity facet narrowing passes (`mask ⊑ mask`). -/
theorem facet_attenuation_self (mask : EffectMask) : isFacetAttenuation mask mask = true := by
  unfold isFacetAttenuation
  simp [Nat.and_self]

/-- **`facet_attenuation_subset_admitted`** — narrowing `{TRANSFER, SET_FIELD}` to `{TRANSFER}`
is an honest attenuation: the child is a bitwise subset of the parent (the E-language
"facets only restrict"). -/
theorem facet_attenuation_subset_admitted :
    isFacetAttenuation (EFFECT_TRANSFER ||| EFFECT_SET_FIELD) EFFECT_TRANSFER = true := by
  unfold isFacetAttenuation EFFECT_TRANSFER EFFECT_SET_FIELD
  decide

/-- **`facet_attenuation_amplify_rejected` — the NON-AMP tooth (witness FALSE).** Widening
`{SET_FIELD}` to `{SET_FIELD, TRANSFER}` is NOT an attenuation: TRANSFER is not in the parent,
so the bitwise-subset gate REJECTS it. A facet can only narrow, never amplify. -/
theorem facet_attenuation_amplify_rejected :
    isFacetAttenuation EFFECT_SET_FIELD (EFFECT_SET_FIELD ||| EFFECT_TRANSFER) = false := by
  unfold isFacetAttenuation EFFECT_SET_FIELD EFFECT_TRANSFER
  decide

/-! ### §6.2 — the facet permits the right effect, rejects the wrong one. -/

/-- A transfer-only facet PERMITS a transfer turn's effect bit. -/
theorem transferFacet_permits_transfer :
    isEffectPermitted (some EFFECT_TRANSFER) EFFECT_TRANSFER = true := by
  unfold isEffectPermitted EFFECT_TRANSFER
  decide

/-- **The WRONG-FACET tooth (witness FALSE).** A SET_FIELD-only facet does NOT permit a transfer
turn's effect bit — the facet axis rejects an effect outside the mask. -/
theorem setFieldFacet_rejects_transfer :
    isEffectPermitted (some EFFECT_SET_FIELD) EFFECT_TRANSFER = false := by
  unfold isEffectPermitted EFFECT_SET_FIELD EFFECT_TRANSFER
  decide

/-- **The DENY-ALL tooth (the P2-1 fix).** A `some 0` (zero) facet denies EVERY effect — a
zero mask is deny-all, NOT unrestricted. -/
theorem zeroFacet_denies_all (bit : EffectMask) : isEffectPermitted (some 0) bit = false := rfl

/-- An UNRESTRICTED facet (`none`) permits every effect. -/
theorem noneFacet_permits_all (bit : EffectMask) : isEffectPermitted none bit = true := rfl

/-! ### §6.3 — the tier is satisfied by the right auth, rejects the wrong / impossible. -/

/-- `Signature` tier is satisfied by a provided signature. -/
theorem signatureTier_satisfied_by_signature :
    AuthTier.isSatisfiedBy .signature .signature = true := rfl

/-- **The WRONG-TIER tooth (witness FALSE).** A `Signature` tier is NOT satisfied by a bare
proof — the tier axis rejects the wrong auth method. -/
theorem signatureTier_rejects_proof :
    AuthTier.isSatisfiedBy .signature .proof = false := rfl

/-- `Either` is satisfied by either a signature or a proof. -/
theorem eitherTier_satisfied_by_both :
    AuthTier.isSatisfiedBy .either .signature = true
    ∧ AuthTier.isSatisfiedBy .either .proof = true := ⟨rfl, rfl⟩

/-- **The IMPOSSIBLE tooth (witness FALSE).** An `Impossible` tier is satisfied by NOTHING —
a permanently-locked action never authorizes, no matter what auth is provided. -/
theorem impossibleTier_never_satisfied (p : AuthProvided) :
    AuthTier.isSatisfiedBy .impossible p = false := by cases p <;> rfl

/-- **The CUSTOM tooth.** A `Custom vk` tier is satisfied ONLY by a `Custom vk'` witness with
matching `vk_hash` — a plain signature/proof does NOT discharge it, and a mismatched vk fails. -/
theorem customTier_matches_vk_only :
    AuthTier.isSatisfiedBy (.custom 7) (.custom 7) = true
    ∧ AuthTier.isSatisfiedBy (.custom 7) (.custom 8) = false
    ∧ AuthTier.isSatisfiedBy (.custom 7) .signature = false := by
  refine ⟨?_, ?_, rfl⟩ <;> decide

/-! ### §6.4 — tier-narrowing non-amp (the attenuation order on the auth method). -/

/-- `Signature`/`Proof` are narrower than `Either`; `Impossible` is narrowest; `None` is broadest
— the honest tier attenuations are admitted. -/
theorem tier_narrowing_admitted :
    AuthTier.narrowerOrEqual .signature .either = true
    ∧ AuthTier.narrowerOrEqual .proof .either = true
    ∧ AuthTier.narrowerOrEqual .impossible .signature = true
    ∧ AuthTier.narrowerOrEqual .signature .none = true := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- **The TIER-AMPLIFY tooth (witness FALSE).** `Either` is NOT narrower-or-equal to `Signature`
(it is BROADER — it also accepts proofs), so widening a `Signature` cap to `Either` is rejected
by the tier attenuation order. -/
theorem tier_amplify_rejected :
    AuthTier.narrowerOrEqual .either .signature = false := rfl

/-! ### §6.5 — the end-to-end gate: admits the right cap, rejects the rest. -/

/-- **`authorizedFacetB_owner`** — owning `src` short-circuits to authorized (intra-vat). -/
theorem authorizedFacetB_owner (caps : FacetCaps) (provided : AuthProvided) (turn : Turn)
    (h : turn.actor = turn.src) :
    authorizedFacetB caps provided turn = true := by
  unfold authorizedFacetB
  simp [h]

/-- **`authorizedFacetB_holds_transfer_cap`** — a non-owner holding a `FacetCap` over `src` that
permits TRANSFER under a tier the provided auth satisfies IS authorized (the two-axis admit). -/
theorem authorizedFacetB_holds_transfer_cap
    (caps : FacetCaps) (provided : AuthProvided) (turn : Turn) (c : FacetCap)
    (hmem : c ∈ caps turn.actor)
    (htgt : c.target = turn.src)
    (hfacet : isEffectPermitted c.facet (turnEffectBit turn) = true)
    (htier : c.tier.isSatisfiedBy provided = true) :
    authorizedFacetB caps provided turn = true := by
  unfold authorizedFacetB
  simp only [Bool.or_eq_true, List.any_eq_true]
  right
  exact ⟨c, hmem, by unfold capAuthorizesFacet; simp [htgt, hfacet, htier]⟩

/-- **`empty_facetCaps_unauthorized` — the gate is REAL (witness FALSE).** Over the empty
cap-table, a non-owner is NOT authorized — the two-axis gate is not vacuously always-true. -/
theorem empty_facetCaps_unauthorized (provided : AuthProvided)
    (turn : Turn) (hne : turn.actor ≠ turn.src) :
    authorizedFacetB (fun _ => []) provided turn = false := by
  unfold authorizedFacetB
  simp [hne]

/-- **`wrong_facet_unauthorized` — the facet axis BITES end-to-end (witness FALSE).** A non-owner
holding a SET_FIELD-only cap over `src` is NOT authorized for a TRANSFER turn: the facet axis
rejects it even though the cap targets `src` and the tier is satisfied. -/
theorem wrong_facet_unauthorized
    (actor src dst : Label) (amt : ℤ) (tier : AuthTier) (provided : AuthProvided)
    (hsat : tier.isSatisfiedBy provided = true) (hne : actor ≠ src) :
    authorizedFacetB
        (fun a => if a = actor then [{ target := src, tier := tier, facet := some EFFECT_SET_FIELD }] else [])
        provided { actor := actor, src := src, dst := dst, amt := amt } = false := by
  unfold authorizedFacetB
  -- the owner leg is false (actor ≠ src); the cap leg is false (facet rejects TRANSFER).
  have howner : (decide (({ actor := actor, src := src, dst := dst, amt := amt } : Turn).actor
      = ({ actor := actor, src := src, dst := dst, amt := amt } : Turn).src)) = false := by
    simp [hne]
  rw [howner, Bool.false_or]
  -- the actor's only held cap rejects the TRANSFER on the facet axis.
  simp only [if_true, List.any_cons, List.any_nil, Bool.or_false, capAuthorizesFacet,
    turnEffectBit, setFieldFacet_rejects_transfer, Bool.and_false, Bool.false_and]

/-- **`wrong_tier_unauthorized` — the tier axis BITES end-to-end (witness FALSE).** A non-owner
holding an `Impossible`-tier cap over `src` (facet wide-open) is NOT authorized: the tier axis
rejects every provided auth, so a permanently-locked cap never authorizes. -/
theorem wrong_tier_unauthorized
    (actor src dst : Label) (amt : ℤ) (provided : AuthProvided) (hne : actor ≠ src) :
    authorizedFacetB
        (fun a => if a = actor then [{ target := src, tier := .impossible, facet := none }] else [])
        provided { actor := actor, src := src, dst := dst, amt := amt } = false := by
  unfold authorizedFacetB
  have howner : (decide (({ actor := actor, src := src, dst := dst, amt := amt } : Turn).actor
      = ({ actor := actor, src := src, dst := dst, amt := amt } : Turn).src)) = false := by
    simp [hne]
  rw [howner, Bool.false_or]
  -- the actor's only held cap has tier Impossible ⇒ isSatisfiedBy false ⇒ rejected.
  simp only [if_true, List.any_cons, List.any_nil, Bool.or_false, capAuthorizesFacet,
    impossibleTier_never_satisfied, Bool.and_false]

/-! ## §7 — non-vacuity: the gate FIRES on a concrete two-axis edge (`#guard`-executed).

Concrete edge: actor 5 holds a TRANSFER-facet, `Signature`-tier cap over src 9; a transfer turn
`⟨5, 9, 0, 30⟩` providing a signature is authorized. A SET_FIELD-only cap, or an `Impossible`
tier, or the empty table — all reject. -/

namespace Demo

/-- Actor 5 holds a transfer-facet, signature-tier cap over src 9; nobody else holds anything. -/
def caps5to9 : FacetCaps := fun a =>
  if a = 5 then [{ target := 9, tier := .signature, facet := some EFFECT_TRANSFER }] else []

/-- A transfer turn from actor 5 over src 9 (non-owned: 5 ≠ 9). -/
def transferTurn : Turn := { actor := 5, src := 9, dst := 0, amt := 30 }

/-- The two-axis gate ADMITS: facet permits TRANSFER, tier (Signature) is satisfied by a sig. -/
example : authorizedFacetB caps5to9 .signature transferTurn = true := by decide

/-- A PROOF does NOT discharge the `Signature` tier ⇒ rejected (the tier axis bites). -/
example : authorizedFacetB caps5to9 .proof transferTurn = false := by decide

/-- A SET_FIELD-only cap does NOT permit a transfer ⇒ rejected (the facet axis bites). -/
example :
    authorizedFacetB (fun a => if a = 5 then [{ target := 9, tier := .signature, facet := some EFFECT_SET_FIELD }] else [])
      .signature transferTurn = false := by decide

/-- The empty cap-table rejects the non-owner. -/
example : authorizedFacetB (fun _ => []) .signature transferTurn = false := by decide

/-- The OWNER (actor = src) is authorized regardless of caps. -/
example : authorizedFacetB (fun _ => []) .signature { actor := 9, src := 9, dst := 0, amt := 30 } = true := by
  decide

#guard authorizedFacetB caps5to9 .signature transferTurn                    -- true
#guard authorizedFacetB caps5to9 .proof transferTurn == false               -- false (wrong tier)
#guard authorizedFacetB (fun _ => []) .signature transferTurn == false      -- false (no cap)
#guard isFacetAttenuation (EFFECT_TRANSFER ||| EFFECT_SET_FIELD) EFFECT_TRANSFER  -- true (subset)
#guard isFacetAttenuation EFFECT_SET_FIELD (EFFECT_SET_FIELD ||| EFFECT_TRANSFER) == false  -- false (amplify)
#guard AuthTier.isSatisfiedBy .impossible .signature == false               -- false (locked)

end Demo

/-! ## §8 — the bridge to `Kernel.authorizedB` (the cutover's refinement target).

The faithful gate REFINES the toy gate on the shape they share: a cap conferring write over `src`
under a satisfied tier and a transfer-permitting facet. The cutover (§10) swaps the kernel's
authority guard to `authorizedFacetB`; this lemma is the refinement direction the cutover
preserves — owning `src` authorizes under BOTH gates, so the conservation/integrity proofs that
read `authorizedB = true` (`exec_authorized`, `BalanceMovementSpec.admitGuardA`) carry over
verbatim once the guard is the faithful one. -/

/-- **`facet_refines_owner`** — the OWNER short-circuit agrees across both gates: when `actor =
src`, both the toy `authorizedB` and the faithful `authorizedFacetB` admit. The shared spine the
cutover preserves (the intra-vat l4v `troa_lrefl` leg is identical in both). -/
theorem facet_refines_owner (caps : Caps) (fcaps : FacetCaps) (provided : AuthProvided)
    (turn : Turn) (h : turn.actor = turn.src) :
    Dregg2.Exec.authorizedB caps turn = true
    ∧ authorizedFacetB fcaps provided turn = true := by
  refine ⟨?_, authorizedFacetB_owner fcaps provided turn h⟩
  unfold Dregg2.Exec.authorizedB
  simp [h]

/-! ## §9 — Axiom hygiene. -/

#assert_axioms facet_attenuation_self
#assert_axioms facet_attenuation_subset_admitted
#assert_axioms facet_attenuation_amplify_rejected
#assert_axioms setFieldFacet_rejects_transfer
#assert_axioms zeroFacet_denies_all
#assert_axioms signatureTier_rejects_proof
#assert_axioms impossibleTier_never_satisfied
#assert_axioms customTier_matches_vk_only
#assert_axioms tier_amplify_rejected
#assert_axioms authorizedFacetB_owner
#assert_axioms authorizedFacetB_holds_transfer_cap
#assert_axioms authorizedFacetB_eq_eff
#assert_axioms authorizedFacetEffB_owner
#assert_axioms authorizedFacetEffB_holds_cap
#assert_axioms wrong_effect_unauthorized
#assert_axioms empty_facetCaps_unauthorized
#assert_axioms wrong_facet_unauthorized
#assert_axioms wrong_tier_unauthorized
#assert_axioms facet_refines_owner

/-! ## §10.5 — THE FAITHFUL KERNEL GATE (§10(A) landed additively, here below `Kernel`).

`Kernel.lean` cannot reference `authorizedFacetB` (it is imported BY this module — a cycle), so the
additive faithful kernel state + executor live here. `FacetKernelState` carries the deployed FACET
caps (`fcaps : FacetCaps`) alongside the same finite ledger; `execFaithful` is `Kernel.exec` with the
authority conjunct repointed from the toy `authorizedB` onto the faithful two-axis `authorizedFacetB`,
reading the auth the turn `provided`. The conservation/availability/distinctness/liveness legs are
UNCHANGED (orthogonal to authority) — only the authority gate is faithful. The re-stated teeth
(`execFaithful_authorized`/`execFaithful_unauthorized_fails`) are the §10(A) `exec_authorized`/
`exec_unauthorized_fails` over the faithful gate. -/

open Dregg2.Exec (KernelState transferBal)

/-- **`FacetKernelState`** — the kernel state with the DEPLOYED FACET caps (the §10(A) `fcaps`
parallel field, made a faithful state here): the finite `accounts`, the ℤ balance, and the
`FacetCaps` table (NOT the toy `Caps`). -/
structure FacetKernelState where
  /-- The finite set of live cells whose balances are conserved. -/
  accounts : Finset CellId
  /-- Resource balance per cell. -/
  bal      : CellId → ℤ
  /-- The DEPLOYED facet capability table (tier × facet per held cap). -/
  fcaps    : FacetCaps

/-- **`execFaithful k provided turn`** — the FAITHFUL executable kernel transition (§10(A)).
Identical to `Kernel.exec` EXCEPT the authority conjunct is the deployed two-axis `authorizedFacetB
k.fcaps provided turn` (NOT the toy `authorizedB`). Fail-closed; commits only when the actor is
authorized on BOTH axes (facet permits TRANSFER ∧ tier satisfied by `provided`), the amount is
non-negative and available, `src ≠ dst`, and both cells are live. -/
def execFaithful (k : FacetKernelState) (provided : AuthProvided) (turn : Turn) :
    Option FacetKernelState :=
  if authorizedFacetB k.fcaps provided turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ k.bal turn.src
      ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts then
    some { k with bal := transferBal k.bal turn.src turn.dst turn.amt }
  else
    none

/-- **`execFaithful_authorized`** (§10(A) `exec_authorized`, faithful) — no state change without the
faithful authority: every committed turn passed the deployed two-axis `authorizedFacetB` gate. -/
theorem execFaithful_authorized (k k' : FacetKernelState) (provided : AuthProvided) (turn : Turn)
    (h : execFaithful k provided turn = some k') :
    authorizedFacetB k.fcaps provided turn = true := by
  unfold execFaithful at h
  by_cases hg : authorizedFacetB k.fcaps provided turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ k.bal turn.src
      ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts
  · exact hg.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`execFaithful_unauthorized_fails`** (§10(A) `exec_unauthorized_fails`, faithful) — a turn the
deployed two-axis gate REJECTS does NOT commit. -/
theorem execFaithful_unauthorized_fails (k : FacetKernelState) (provided : AuthProvided) (turn : Turn)
    (h : authorizedFacetB k.fcaps provided turn = false) :
    execFaithful k provided turn = none := by
  unfold execFaithful
  rw [if_neg]
  rintro ⟨ha, _⟩
  rw [h] at ha; exact absurd ha (by simp)

/-- **`execFaithful_conserves`** — the faithful gate preserves total supply over the live accounts
(authority is orthogonal to conservation; the debit/credit cancel exactly as in `Kernel`). -/
theorem execFaithful_conserves (k k' : FacetKernelState) (provided : AuthProvided) (turn : Turn)
    (h : execFaithful k provided turn = some k') :
    (∑ c ∈ k'.accounts, k'.bal c) = ∑ c ∈ k.accounts, k.bal c := by
  unfold execFaithful at h
  by_cases hg : authorizedFacetB k.fcaps provided turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ k.bal turn.src
      ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨_, _, _, hne, hsrc, hdst⟩ := hg
    exact Dregg2.Exec.transfer_sum_conserve k.accounts k.bal turn.src turn.dst turn.amt hsrc hdst hne
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ### §10.5 demo — the faithful kernel runs (`#guard`). -/

namespace FacetDemo

/-- Actor 0 owns 100, cell 1 owns 5; actor 0 holds NO facet cap (authority is by ownership). -/
def fs0 : FacetKernelState :=
  { accounts := {0, 1}
    bal := fun c => if c = 0 then 100 else if c = 1 then 5 else 0
    fcaps := fun _ => [] }

/-- Actor 0 transfers 30 to cell 1 (owns src 0 ⇒ authorized intra-vat). -/
def ft1 : Turn := { actor := 0, src := 0, dst := 1, amt := 30 }
/-- Actor 2 attempts the same — unauthorized (no facet cap over src 0, and 2 ≠ 0). -/
def ftBad : Turn := { actor := 2, src := 0, dst := 1, amt := 30 }

#guard (execFaithful fs0 .signature ft1).isSome              -- true (owner)
#guard (execFaithful fs0 .signature ftBad).isSome == false   -- false (unauthorized)

end FacetDemo

#assert_axioms execFaithful_authorized
#assert_axioms execFaithful_unauthorized_fails
#assert_axioms execFaithful_conserves

/-! ## §10 — THE CUTOVER PLAN (file-by-file swaps; what `List Auth` retires).

This module is ADDITIVE. The kernel still authorizes by the toy `authorizedB`. The cutover
(run by the main loop, NOT here) swaps the authority decision to `authorizedFacetB` reading the
cap leaf's COMMITTED `auth_tag` (tier) + `mask_lo`/`mask_hi` (facet). Precisely:

### (A) The kernel gate — `Dregg2/Exec/Kernel.lean`
  * `KernelState.caps : Caps` (= `Label → List Cap`) becomes `FacetCaps` (= `Label → List
    FacetCap`), OR the kernel grows a parallel `fcaps : FacetCaps` field (additive-then-cutover,
    to keep `exec_conserves` untouched while the authority leg migrates).
  * `Turn` grows a `provided : AuthProvided` field (the auth the turn supplies — the deployed
    `Authorization` the executor verified). Default-construct it `.signature` at the legacy
    call sites until they thread the real provided kind.
  * `def authorizedB (caps) (turn) := …` is REPLACED at its single call site (the `exec` `if`,
    `Kernel.lean:70`) by `authorizedFacetB k.fcaps turn.provided turn`. The OLD `authorizedB`
    and its `Cap.node`/`Cap.endpoint`/`Auth.write`/`List Auth` machinery STAY (other modules
    still reference them) but become DEAD for the kernel gate — retire them in a later sweep
    once no `import` reads them (grep: `authorizedB`, `Auth.write`, `rights.contains`).
  * `exec_authorized`/`exec_unauthorized_fails` re-state over `authorizedFacetB` (the proofs are
    structurally identical: read the guard conjunct off the `if`).

### (B) The full-state spec guard — `Dregg2/Circuit/Spec/balancemovement.lean`
  * `admitGuardA` conjunct (1) `authorizedB k.caps t = true` becomes
    `authorizedFacetB k.fcaps t.provided t = true`. Every downstream theorem
    (`recCexecAsset_iff_spec`, `execFullA_balanceA_iff_spec`, the `…_rejects_*` non-vacuity
    teeth) re-derives unchanged in shape — `balanceMovement_rejects_unauthorized`'s hypothesis
    becomes `authorizedFacetB … = false`. The executor `recKExecAsset`/`recCexecAsset`
    (`RecordKernel.lean:719`) must read the new guard at its `if`; the spec follows.

### (C) The cap-leaf bridge — `Dregg2/Circuit/DeployedCapTree.lean`
  * `confersWriteLeaf l := l.mask_lo = rightsMaskOf (endpoint 0 [read, write])` becomes the
    TWO-AXIS predicate `confersTransferLeaf l := isEffectPermitted (some (maskOfLimbs l.mask_lo
    l.mask_hi)) EFFECT_TRANSFER ∧ tierSatisfied (tierOfTag l.auth_tag) provided` — i.e. the leaf
    confers authority iff its FACET (decoded from `mask_lo`/`mask_hi` per `cap_root.rs::
    split_effect_mask`) permits the turn's effect AND its TIER (decoded from `auth_tag`,
    None=0…Custom=5) is satisfied. The current `mask_lo == write-mask` check is the abstract
    `Auth` rights shadow (the NAMED HORIZONLOG fork the cap-open emit already flagged); the
    cutover REPLACES it with the genuine `EffectMask` facet bit + the `auth_tag` tier.
  * `DeployedFaithful.backed` rewrites: a member opening whose facet permits the effect AND whose
    tier is satisfied is backed by a `FacetCap` over `src` admitting the turn — and
    `deployedCapOpen_implies_authorizedB` concludes `authorizedFacetB`, NOT the toy
    `authorizedB`. The body REUSES `authorizedFacetB_holds_transfer_cap` (this module) verbatim:
    exhibit the held `FacetCap`, discharge the two legs.
  * `Dregg2/Circuit/DeployedCapOpen.lean::capOpen_authorizes` and
    `Dregg2/Circuit/Emit/CapOpenEmit.lean::transferCapOpenEffV3_authorizes` then conclude
    `authorizedFacetB` through the rewritten bridge — the `writeMaskGate` becomes a
    `transferFacetGate` (decode `mask_lo`/`mask_hi`, check `EFFECT_TRANSFER` bit) PLUS an
    `authTagGate` (decode `auth_tag`, check the tier), both already-faithful-to-`facet.rs`
    column gates.

### (D) What `List Auth` machinery RETIRES (the toy model deletion)
  * `Kernel.authorizedB`'s `Cap.node`/`Cap.endpoint t rights`/`rights.contains Auth.write` test
    (the toy authority) — once (A) lands and no kernel gate reads it.
  * The `confersWriteLeaf` write-mask shadow in `DeployedCapTree` — replaced by the two-axis
    facet+tier leaf predicate in (C).
  * The `Auth.write`-bit `rightsMaskOf` write encoding (`EffectVmEmitCapReshape.rightsMaskOf`
    over `Auth`) STAYS for the cap-RESHAPE non-amp lattice (that is the genuine `Finset Auth`
    delegation order, orthogonal to the per-effect facet); only the kernel-GATE's use of the
    `Auth.write` shadow retires.

### Residuals (genuine, NAMED — not deferred silently)
  * **The `auth_tag` ↔ tier-byte encoding.** The deployed `auth_tag` is the tier byte
    (None=0…Custom=5) with the 8 `vk_hash` limbs absorbed for `Custom` (`cap_root.rs:46`). The
    cutover's `tierOfTag : ℤ → AuthTier` decode must reproduce that absorb for `Custom` (two
    distinct `vk_hash`es ⇒ distinct `auth_tag` felts). For the IPC tiers (None…Impossible) the
    byte is the discriminant; `AuthTier.tierByte` (§1) already pins it. The `Custom` felt-decode
    is the one genuinely-crypto residual (a Poseidon2 absorb, named — not a gap).
  * **A plain transfer's required tier.** Open question the cutover must settle:
    `cell/src/permissions.rs::default_user()` sets `send: Signature` — so a plain
    holder-initiated transfer's tier is `Signature` (a sig discharges it), NOT `None`. But the
    deployed `Effect::Transfer` is exercised via a CAP whose `permissions` field is the tier the
    GRANTOR set on the cap (could be `None` for an open-bearer transfer cap, `Signature` for a
    sig-gated one, `Proof` for a zkApp). So the tier is NOT fixed per-effect; it is the
    `auth_tag` the cap leaf commits. The cutover reads it off the leaf (no per-effect default);
    `turnEffectBit` fixes only the FACET bit, the tier comes from the cap. (For the OWNER
    short-circuit there is no tier — owning `src` is intra-vat, l4v `troa_lrefl`, gated by
    neither axis, as both gates agree per `facet_refines_owner`.)
-/

end Dregg2.Exec.FacetAuthority
