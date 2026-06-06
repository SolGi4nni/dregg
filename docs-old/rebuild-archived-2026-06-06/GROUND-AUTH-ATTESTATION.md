# GROUND-AUTH-ATTESTATION — the authorization + attestation dimension, Rust as ground truth

> ⚑ **GROUND-CHECKED vs live Lean 2026-06-02 (post-2-compaction drift-repair); REAL/DECORATIVE/ASPIRATIONAL tags carry file:line receipts.**
>
> **The headline of this doc has been SUPERSEDED in the GOOD direction.** When this
> was written it was a READ-ONLY audit concluding the Lean *overlooks* four advanced
> Rust features. **All four of those carry-forward modules have since LANDED in Lean,
> fully term-proved, kernel-clean, and imported into `Dregg2.lean` (lines 186–189).**
> The four "O"/"S→O" verdicts in §1.6 are now **CLOSED-WITH-TEETH**; the Part-2
> "genuinely new theory" — a verifier-indexed `Discharged` — is **BUILT**:
> - `Authority/CaveatChain.lean` — REAL HMAC append-only caveat chain (was: "**O**, inexpressible"). [REAL]
> - `Authority/ThirdPartyDischarge.lean` — REAL ticket/VID/bind/freshness 3P protocol (was: "**S→O**, a `Bool` flip"). [REAL]
> - `Authority/SelectiveDisclosure.lean` — selective disclosure + predicate proofs + multi-show unlinkability wired to the credential path (was: "**O** + **S, disconnected**"). [REAL]
> - `Authority/DesignatedVerifier.lean` — verifier-indexed `DischargedFor` + the transferability DIAL (public ⇒ non-repudiable; designated ⇒ deniable via the simulator) (was Part-2: "a genuinely new piece of theory" needed). [REAL]
>
> Each is a §8-honest *reduction* (the underlying HMAC/AEAD/STARK soundness stays an
> explicit Prop-portal — see the per-module "§8 portal" sections), NOT a fake "we
> proved the crypto" claim. The Rust-grounding (Part 1 §1.1–§1.5) and the anonymity
> findings (Part 2 §2.2a) remain accurate as written. What is *still* genuinely OPEN
> is narrower and named at the bottom (the BASE `Credential.lean` is still
> all-or-nothing; ring/chameleon repudiation is still unbuilt in Rust; the §8 crypto
> soundness itself is — correctly — never discharged in Lean). Original BLUF kept
> below for the record, then corrected inline.

READ-ONLY grounding pass *as originally written* (the audit half is now history; the
carry-forward landed). Every claim cites `file:line`. The mission: establish the
**Rust** semantics of dregg's authorization/attestation layer as ground truth, audit
the Lean's fidelity against it, and analyze the
repudiation/deniability/designated-verifier concern. This is the dimension an
effect-VM-centric view under-weights: caveats *gate* effects and attestation is
the turn *output*, so the real turn vocabulary is **effects ⊕ caveat-gates ⊕
attestation**, not effects alone.

Bottom line up front (ORIGINAL — see the ⚑ banner above for the corrections):
- The Rust is **substantially richer** than the Lean on this axis. The Lean
  Authority modules model the *algebraic discipline* (attenuation-only,
  discharge-monotone, issued-and-not-revoked, six-mode dispatch soundness) at a
  high level of faithfulness — and in one place (CapTP non-amplification) the
  Lean models the *correct* semantics the Rust is *missing*. ~~But the Lean
  **overlooks** the cryptographic substance of the most advanced Rust features:
  the HMAC caveat chain, the third-party discharge protocol (encrypted
  ticket/VID, bind-to-parent, freshness), credential selective-disclosure +
  predicate proofs + blinded multi-show, the stealth one-time-key auth mode, and
  the StarkDelegation anonymous-delegation public-input binding.~~ **CORRECTION
  (2026-06-02):** all of these EXCEPT stealth/StarkDelegation-at-the-auth-mode-layer
  are now modeled in Lean with term-proved reductions (§1.6 table re-tagged below).
  The remaining true overlook is just **stealth + StarkDelegation as first-class
  *auth modes* in `AuthModes.lean`** — the credential-layer anonymity (BlindedSet
  multi-show) now IS modeled (`SelectiveDisclosure.lean`).
- On Part 2: dregg's proofs/attestations are **hardwired to maximal
  transferability** in the *running Rust* (publicly-verifiable STARK + Ed25519
  signatures ⇒ non-repudiable) — still true of the code. dregg HAS strong
  **anonymity** (who-hiding) and has it modeled in Lean. ~~it has **zero
  deniability** and **zero designated-verifier** machinery in either Rust or
  Lean.~~ **CORRECTION (2026-06-02):** the *Rust* still has zero DV machinery, but
  the **Lean now MODELS the missing axis** — `DesignatedVerifier.lean` builds the
  verifier-indexed discharge + the transferability dial + the simulator-based
  deniability theorems. The dial is now *specified*; the Rust impl is the
  ASPIRATIONAL remainder (§2.4).

---

# PART 1 — THE CAVEAT / TOKEN / ATTESTATION SYSTEM (Rust first)

## 1.1 The macaroon core (HMAC caveat chain) — `macaroon/`

The macaroon implementation is **real and complete**, not a stub.

- **HMAC chain construction**: `macaroon/src/macaroon.rs:118-142` — `Macaroon::new`
  seeds `T₀ = HMAC(root_key, nonce_bytes)`; the chain extends per caveat. The
  invariant is stated in the module header `macaroon/src/macaroon.rs:14-21`:
  `Tᵢ = HMAC(Tᵢ₋₁, encode(Cᵢ))`.
- **Attenuation = append-only caveat add**: `add_first_party`
  (`macaroon.rs:151-156`) advances the tail. Caveats can only *restrict*
  (`caveat.rs:2-9`, `caveat.rs:47-49`). This is the cryptographic realization of
  "a key may only narrow."
- **Verification replays the chain** (`macaroon.rs:204-262`): re-derives the tail
  from the root key, collects first-party caveats for clearing, dispatches 3P
  caveats to discharges, and does a **constant-time** final-tail compare
  (`macaroon.rs:257`). Tests prove tamper/removal/wrong-key all fail
  (`macaroon.rs:455-506`).
- **Caveat type space** (`caveat.rs:24-45`): platform `0..31`, user-registerable
  `32..47`, user-defined `48..253`, `254`=third-party, `255`=bind-to-parent.
- **Typed dregg grant vocabulary** (`token/src/dregg_caveats.rs:137-169`):
  `App{id,actions}`, `Service`, `Feature`, `ValidityWindow{not_before,not_after}`,
  `ConfineUser`, `OAuthProvider`, `OAuthScope`, `FeatureGlob{include,exclude}`,
  `Budget{...}`, and an `Unknown` passthrough. The `Attenuation → WireCaveat`
  lowering is `dregg_caveats.rs:299`.

### Advanced feature: THIRD-PARTY CAVEATS + DISCHARGE PROTOCOL — `macaroon/src/caveat_3p.rs`

This is a full Schnorr-style discharge protocol, not a flag:
- `ThirdPartyCaveat::new` (`caveat_3p.rs:71-102`): generates an ephemeral
  discharge key `r`; encrypts `{r, caveats_for_3p}` under the issuer↔3P shared key
  `KA` → **Ticket (CID)**; encrypts `r` under the *current HMAC tail* →
  **VerifierKey (VID)**. So only the verifier (who can replay the chain to that
  tail) recovers `r`, and only the 3P (who holds `KA`) recovers the ticket.
- **Discharge issuance**: `create_discharge` (`macaroon.rs:383-404`) — the 3P
  signs a fresh discharge macaroon under `r`, stamping a `created_at` timestamp.
- **bind-to-parent**: `bind_discharge` (`macaroon.rs:341-347`) adds a caveat
  carrying `SHA256(root_tail)`. `verify_discharge` (`macaroon.rs:267-332`)
  **requires** this binding (fail-closed at `macaroon.rs:324-329`, even for empty
  discharges — test `macaroon.rs:578`), preventing replay of a discharge against a
  less-attenuated root.
- **Freshness / replay protection**: discharges older than `MAX_DISCHARGE_AGE =
  300s` (`macaroon.rs:35`) are rejected; `created_at == 0` is rejected fail-closed
  (`macaroon.rs:275-289`).
- AEAD is **XChaCha20-Poly1305** (`macaroon/src/crypto.rs:5-8, 59-61`); the
  192-bit nonce removes collision concerns.
- **Cross-vat split is real**: a macaroon's root secret is held only by its
  scoping cell; a biscuit is Ed25519 public-key verifiable. (Token backends:
  `token/src/macaroon_backend.rs`, `token/src/biscuit_backend.rs`, datalog
  verification `token/src/datalog_verify.rs` 2708 lines.)

### The discharge gateway — `discharge-gateway/` + `macaroon/src/discharge_gateway.rs`

A 1096-line server (`macaroon/src/discharge_gateway.rs`) implementing the 3P that
decrypts tickets, checks the embedded caveats, and mints bound discharges. This is
the running counterpart to `Caveat.thirdParty` / `Discharge.settle` in Lean.

## 1.2 Credentials (predicate / membership / anonymous multi-show) — `credentials/`

This is the **most advanced** and most under-modeled feature. Per the module doc
(`credentials/src/lib.rs:1-57`), `dregg-credentials` promotes `bridge::present`
to the credential primitive. It provides:
- `Credential` backed by a real signed macaroon (`credentials/src/issuance.rs`).
- `Presentation` = a STARK proof of "authorization derives from a valid
  credential" **without** revealing the credential (`presentation.rs:84-109`).
- **Selective disclosure**: `PresentationOptions.disclose`
  (`presentation.rs:36-37`); only disclosed attributes are transmitted, with a
  Poseidon2 `revealed_facts_commitment` (`presentation.rs:256-270`,
  `presentation.rs:365-372`).
- **Predicate proofs** (`Gte/Lte/InRange`) over hidden attributes:
  `presentation.rs:307-351` via `prove_predicate_for_fact`.
- **Anonymous presentation / unlinkable multi-show**: `present_anonymous`
  (`presentation.rs:176-182`). The anonymous path (a) **omits the holder
  `confine_user` binding** (`presentation.rs:231-244`) and (b) uses a **real
  STARK with a fresh per-presentation blinding factor** so the public
  `blinded_leaf` differs across shows (`presentation.rs:292-299`). The
  unlinkability rationale is documented inline (`presentation.rs:204-212`).
- The wire form strips the private `AuthorizationTrace` before transmission
  (`presentation.rs:133-152`; the trace is "SECURITY: MUST NOT be transmitted",
  `bridge/src/present.rs:171-179`).
- Verification: `credentials/src/verification.rs` (`verify` / `verify_anonymous`),
  revocation via federation-attested non-revocation root
  (`credentials/src/revocation.rs`).

The underlying ZK engine is `bridge::present::BridgePresentationBuilder`
(`bridge/src/present.rs:103-137`) producing a `BridgePresentationProof`
(`bridge/src/present.rs:149-202`) — a real STARK over issuer-membership Merkle
path + fold chain, verifiable against the **public** `federation_root`
(`bridge/src/present.rs:269-308`).

## 1.3 Anonymous-auth at the turn layer — `turn/`

The `Authorization` sum (`turn/src/action.rs`) is the real per-action auth
carrier. Its `to_auth_kind` map (`action.rs:504-533`) enumerates the variants:
`Signature`, `Proof`, `Breadstuff`, `Bearer`, `Unchecked`, `CapTpDelivered`,
`Custom`, `OneOf`, **`Stealth`**, **`Token`**. Two are anonymity-bearing:

### Stealth one-time-key auth — `turn/src/executor/authorize.rs:1337-1417+`, `cell/src/stealth.rs`

- `cell/src/stealth.rs` is a **complete** Monero/EIP-5564-style stealth-address
  implementation: X25519 DH for the view exchange, Ed25519 point addition for the
  one-time key, `P = H(r·V)·G + S` (`stealth.rs:271-292`), spend key
  `k = H(shared) + s` (`stealth.rs:298-314`), view tags for fast scanning
  (`stealth.rs:220-253`). Tested end-to-end (`stealth.rs:347-533`).
- The executor verifies a stealth auth by recomputing `P' = c·G + S` where `S` is
  the *target cell's persistent key* (never on the wire) and checking an Ed25519
  signature under `P` over a domain-separated message binding federation/nonce/
  position/action-hash (`authorize.rs:1337-1417`,
  `action.rs:606-635`). Unlinkability + replay are argued inline
  (`authorize.rs:1358-1368`).

### StarkDelegation anonymous bearer delegation — `turn/src/action.rs:481-502`, `authorize.rs:1252-1333`

`DelegationProofData` has two arms (`action.rs:483-502`):
- `SignedDelegation{delegator_pk, signature, bearer_pk}` — Ed25519, **identifies**
  the delegator (verified at `authorize.rs:1150-1250`).
- `StarkDelegation{proof_bytes, root_issuer_commitment}` — a STARK proving the
  derivation chain **without** the delegator online and **deliberately hiding**
  delegator/bearer pubkeys behind `root_issuer_commitment`
  (`authorize.rs:1270-1277`). Only the public scope (perm tier, expiry,
  federation id, target) is bound into the proof's public inputs
  (`authorize.rs:1267-1321`), then `stark::verify` runs (`authorize.rs:1322-1332`).
  This is genuine anonymous delegation.

`BlindedSet` membership is the credentials-layer anonymity predicate (see §1.2);
its predicate-kind plumbing lives in `cell/src/predicate.rs` (kind enumerated
`predicate.rs:274`, real-but-soundness-gated verifier `predicate.rs:730, 797`).

## 1.4 Attestation = the turn OUTPUT (the badge) — `turn/src/witnessed_receipt.rs`

The attestation half of the dimension is the **WitnessedReceipt**
(`turn/src/witnessed_receipt.rs:245-267`): a `TurnReceipt` enriched with STARK
`proof_bytes`, flat `public_inputs`, and an optional `WitnessBundle` (inline trace
±recursive proof). It is **verifiable stand-alone** via
`verifier::verify_effect_vm_proof` (`witnessed_receipt.rs:250-251`) and carries a
witness-hash binding so a gossiped scope-2 artifact cannot detach its trace
(`witnessed_receipt.rs:289-325`). The cross-cell bilateral-chain verifier is
`verify_bilateral_chain` (`witnessed_receipt.rs:482-529`). Receipts also carry an
`executor_signature` (`witnessed_receipt.rs:571`).

## 1.5 The right turn vocabulary: effects ⊕ caveat-gates ⊕ attestation

Yes. The effect VM is only one of three faces:
1. **Effects** — what the turn *does* (the VM trace).
2. **Caveat-gates** — what the turn is *allowed* to do: the six-mode
   `verify_authorization` dispatch gates each action *before* effects run
   (`turn/src/executor/authorize.rs`), with token caveats (`Token.admits`)
   and discharge among the gates.
3. **Attestation** — what the turn *emits*: the WitnessedReceipt/STARK badge that
   travels and is independently checkable.

An effect-VM-only model captures (1), shadows part of (2) via the predicate
registry, and treats (3) as a hash. The authorization + attestation dimension is
co-equal with the effect dimension and must be carried as such.

---

## 1.6 LEAN FIDELITY AUDIT (faithful / shadow / overlooked) — RE-TAGGED 2026-06-02

Legend: **F** faithful (semantics match), **S** simplified-shadow (the shape is
present but the cryptographic/semantic substance is abstracted to an oracle or a
`Bool`), **O** overlooked-absent (no Lean counterpart).

**2026-06-02 re-tag:** each row now also carries a structural tag with a file:line
receipt — **[REAL]** = a term-proved Lean object with teeth (often `#assert_axioms`-
or `#print axioms`-pinned to the kernel whitelist `{propext, Classical.choice,
Quot.sound}`); **[DECORATIVE]** = vocabulary only, no Lean object (grep-confirmed
absent); **[ASPIRATIONAL]** = honestly-named OPEN, unbuilt. The four rows that were
**O**/**S→O**/**S** at audit time (HMAC chain, 3P discharge, selective disclosure,
multi-show) are now **[REAL]** — their carry-forward modules landed
(`Dregg2.lean:186-189`). `#assert_axioms` certifies *kernel-clean*, NOT
faithful/non-vacuous — the non-vacuity teeth are the separately-cited
`*_has_teeth` / `*_rejected` / `disclosed_slot_is_revealed` / `dial_endpoints_distinct`
theorems.

| Rust feature (file:line) | Lean counterpart (file:line) | Verdict | Note |
|---|---|---|---|
| Attenuation = append caveat, narrowing-only (`macaroon.rs:151`, `caveat.rs:47`) | `Token.attenuate` + `attenuate_narrows` (`Authority/Caveat.lean:81-101`) | **F** | The keystone law is genuinely proved; matches Rust discipline exactly. |
| Token admits iff ALL caveats hold (`token/src/dregg_caveats.rs:388`) | `Token.admits` = `List.all` (`Authority/Caveat.lean:76`) | **F** | Conjunction/meet semantics match. |
| HMAC chain `Tᵢ=HMAC(Tᵢ₋₁,Cᵢ)`, tamper/removal detection (`macaroon.rs:204-262`) | **`CaveatChain.lean`** — `Chain`/`replayTag`/`Chain.verify` + `verify_iff_wellTagged` (`:168`), `forgery_requires_mac_query` (`:305`), `removal_breaks_tail` (`:328`); HMAC = §8 `MacKernel.unforgeable` portal (`:78-87`) | ~~**O**~~ → **F (REAL, term-proved reduction)** | **DRIFT FIXED (2026-06-02).** The old "Lean has NO chain integrity / cannot even express it" is **superseded**: `CaveatChain.lean` models the macaroon as the REAL append-only HMAC chain (`Chain.append` = `add_first_party`, `:153`), the replay-and-compare verifier (`Chain.verify`, `:160`), and proves the integrity *reduction* with teeth: a forged-but-accepted chain yields a MAC collision over differing link-lists (`forgery_requires_mac_query`, `:305-320`), and dropping a caveat without re-signing forces a no-op MAC step (`removal_breaks_tail`, `:328-351`). The HMAC's *security* stays an honest §8 `Prop`-carrier (`MacKernel.unforgeable`) — never faked as proved. Bridges back to `Caveat.lean` via `verifiedChainGate`/`chainToken` (`:244-262`). [REAL] |
| Biscuit (pubkey, cross-vat) vs macaroon (HMAC, intra-vat) split (`token/src/{biscuit,macaroon}_backend.rs`) | `TokenKind` + `crossVatVerifiable` + `macaroon_not_crossvat` (`Authority/Caveat.lean:57-126`) | **F** (shape) / **S** (crypto) | The *policy* (macaroon not off-island) is proved; the *reason* (HMAC secret) is an unmodeled premise. |
| 3P caveat: encrypted ticket/VID, ephemeral key `r` (`caveat_3p.rs:71-102`) | **`ThirdPartyDischarge.lean`** — `ThirdPartyCaveat{vid,ticket,predicate}` (`:124`), `recoverKey = aeadUnseal parentTail vid` (`:213`), `accepts_iff` (`:246`); AEAD = §8 `DischargeCrypto` portal (`:74-90`) | ~~**S→O**~~ → **F (REAL, term-proved gate)** | **DRIFT FIXED (2026-06-02).** The old "cryptographic ticket/VID protocol is entirely absent — a gateway is a `Bool`" is **superseded**: `ThirdPartyDischarge.lean` models the VID (`seal(parentTail, r)`) and ticket (`seal(K_A, …)`) and proves acceptance is EXACTLY the four-conjunct gate `accepts_iff` (`:246-267`): recover `r` from the VID under the replayed parent-tail ∧ keyed-by-`r` ∧ fresh ∧ chain-valid ∧ bound ∧ predicate. "Only the chain-replayer recovers `r`" is the `recoverKey` semantics (`unseal parentTail vid`) — only a verifier who replayed to `parentTail` decrypts it. AEAD/keyed-hash *soundness* stays the §8 `DischargeCrypto.cryptoSound` carrier. [REAL] |
| bind-to-parent + freshness (`macaroon.rs:267-332`) | **`ThirdPartyDischarge.lean`** — `boundTo`/`bindCaveat`/`fresh` (`:170-209`), `unbound_discharge_rejected` (`:318`), `cross_bound_rejected` (`:333`), `stale_discharge_rejected` (`:304`); `maxDischargeAge = 300` (`:104`) | ~~**O**~~ → **F (REAL, teeth)** | **DRIFT FIXED (2026-06-02).** Discharge↔root binding and the 300s freshness window are now modeled WITH TEETH: a discharge minted for parent A presented against a different parent B is REJECTED (`cross_bound_rejected`, `:333-354`, honest `bindingHash tailB ≠ bindingHash tailA`), and a stale/replayed discharge (`fresh = false`, beyond `maxDischargeAge`, or `createdAt = 0`) is REJECTED (`stale_discharge_rejected`, `:304-311`). The honest round-trip closes the loop (`honest_discharge_accepted`, `:275`). Not "an unconditional flip" anymore. [REAL] |
| Discharge accumulates / resolves forward (`discharge-gateway/`) | `admits_mono_discharge`, `resolve_forward`, `settle_le` (`Authority/Discharge.lean:77-174`) | **F** | Strong, faithful: the await-authority monotonicity keystone. |
| Credential issue/present/verify/revoke (`credentials/src/{issuance,presentation,verification,revocation}.rs`) | `VC`, `issue/present/verify/revoke`, `credential_verifies_iff_issued_and_not_revoked` (`Authority/Credential.lean:55-209`) | **F** (lifecycle) | The issued-and-not-revoked discipline is faithful; revocation reuses the nullifier G-Set with real I-confluence (`Credential.lean:226-244`). |
| **Selective disclosure** (revealed-facts commitment) (`presentation.rs:256-270`) | **`SelectiveDisclosure.lean`** — `Credential{attr : Fin n → Nat}` (`:134`), `disclosedView`/`observerView` (`:204-222`), `presentation_hides_undisclosed` (`:239`) + non-vacuity `disclosed_slot_is_revealed` (`:260`) | ~~**O**~~ → **F (REAL, view-collapse, #assert_axioms-pinned)** | **DRIFT FIXED (2026-06-02).** The Lean credential now carries a *vector* of attributes and can disclose a SUBSET: `presentation_hides_undisclosed` (`:239-253`) proves two credentials agreeing on the disclosed slots + proven predicates produce the SAME observer-view (so the view is independent of hidden attributes), and `disclosed_slot_is_revealed` (`:260-272`) gives the non-vacuity teeth (distinct disclosed values ⇒ distinct views). Pinned `#assert_axioms` (`:409-410`). The Poseidon2 commitment's *computational* binding stays §8. NOTE: this is a NEW credential object (`SelectiveDisclosure.Credential`); the BASE `Credential.lean` `claim:Nat` is still all-or-nothing (see "still OPEN"). [REAL] |
| **Predicate proofs** Gte/Lte/InRange on hidden attrs (`presentation.rs:307-351`) | `WitnessedKind` dispatch + `registry_sound` (`Predicate.lean:106`) **AND** **`SelectiveDisclosure.lean`** — `Predicate` enum + `evalPred` (`:95-121`), `ProvenPredicate{holds}` (`:153`), `proven_predicate_holds` (`:287`) + teeth `predicate_proof_has_teeth` (`:298`) | ~~**S**~~ → **F (REAL, the relation is now characterized)** | **DRIFT FIXED (2026-06-02).** The "range-proof relation itself … never characterized" is **superseded**: `SelectiveDisclosure.evalPred` (`:115-121`) IS the decidable arithmetic of Gte/Lte/Gt/Lt/Neq/InRange, and a `ProvenPredicate` is *uninhabitable* for a false predicate (`predicate_proof_has_teeth`: no proof of `.gte 18` over value `17`, `:298-306`). `registry_sound` (the dispatch keystone) remains. Circuit *binding* of the value stays §8. [REAL] |
| **Anonymous multi-show unlinkability** (fresh blinding ⇒ different `blinded_leaf`) (`presentation.rs:176-212, 292-299`) | **`SelectiveDisclosure.lean`** — `multishow_unlinkable` (`:326`) + `multishow_blinding_invisible` (`:341`), wired to the credential `Presentation` object; plus `Privacy.blinded_membership_hides_element` (`Privacy.lean:489`) | ~~**S** (split, disconnected)~~ → **F (REAL, NOW WIRED to the credential path)** | **DRIFT FIXED (2026-06-02).** The "modeled in the wrong place, disconnected" verdict is **resolved**: `multishow_unlinkable` (`:326-334`) states unlinkability *about the credential `Presentation`* — two shows of the SAME credential with DIFFERENT fresh blinding (`p₁.blinding ≠ p₂.blinding`) have EQUAL observer-views, because the blinding is not in the view. `multishow_blinding_invisible` (`:341-345`) gives the concrete non-vacuity (blinding 0 vs 1 collapse). This is exactly `Privacy.unlinkable`'s view-collapse landed on the credential multi-show path the audit said it governed. `#assert_axioms`-pinned (`:413-414`). [REAL] |
| Six-mode `verify_authorization` dispatch (`authorize.rs`) | `AuthMode` + `authModeAdmits` + per-mode `*_sound` (`Exec/AuthModes.lean:135-410`) | **F+** | Faithful to OneOf recursion rules, Custom registry, Bearer/Token caveats, Unchecked-no-escalation. **And superior**: it models the *correct* CapTP `granted ≤ held` non-amplification that the Rust `verify_captp_delivered` is documented to be MISSING (`AuthModes.lean:20-25, 268-296`). |
| **Stealth one-time-key auth** (`authorize.rs:1337+`, `cell/src/stealth.rs`) | `CatalogInstances.lean:236-240` (a verify-seam stub) + `Privacy.unlinkable` (`Privacy.lean:457-461`) | **S→O** | `AuthModes.lean`'s "six modes" **omit Stealth entirely** (it lists OneOf/Custom/CapTpDelivered/Bearer/Token/Unchecked). `CatalogInstances` reduces stealth to a generic `Discharged`. The `P = c·G + S` relation and its unlinkability are *not* the same object as the `Privacy.unlinkable` payment-graph law; the auth-mode unlinkability is unmodeled. |
| **StarkDelegation** anonymous bearer (hidden delegator/bearer, scope-bound PI) (`authorize.rs:1252-1333`) | `AuthMode.bearer` carries `held/granted` *in the clear* (`AuthModes.lean:152, 305-314`) | **O** | The Lean bearer models the *non-amplification* edge but **not the anonymous variant**: there is no notion that delegator/bearer can be hidden behind a `root_issuer_commitment` while only public scope is bound. The anonymity of the delegation path is overlooked. |
| WitnessedReceipt attestation badge + bilateral chain (`witnessed_receipt.rs`) | `Exec/Receipt.lean`, `Exec/ProofForest.lean`, `Exec/TurnForest.lean` (badge/forest spine) **+** transferability now formalized in **`DesignatedVerifier.lean`** (`public_convinces_any_third_party`, `:176`; `publicMode_collapses_to_universal`, `:186`) | ~~**S**~~ → **S (structure) / F (transferability-as-property now STATED)** | **PARTIAL DRIFT FIXED (2026-06-02).** The forest/receipt *structure* is modeled and the STARK binding stays a §8 oracle (correctly). The old "transferability/non-repudiation as a *property* is not stated" is now **superseded**: `DesignatedVerifier.lean` formalizes exactly that — the current universal `Discharged` (`Laws.lean:41`, `CryptoKernel.lean:75`) IS the `public` endpoint `∀V` (`publicMode_collapses_to_universal`, `:186-190`), hence non-repudiable (`public_convinces_any_third_party`, `:176-180`). [REAL for the property; the receipt↔dial *wiring* is still ASPIRATIONAL.] |
| Pedersen committed conservation (value tier) (`wasm/src/privacy.rs:283-475`, cell commitments) | `Exec/CellPrivacy.lean` `committed_transfer_conserves` (`CellPrivacy.lean:161-169`) | **F** | Genuinely faithful homomorphic-sum conservation over hidden amounts, via the `commit_hom` interface law. |

### Where the Lean WAS a FICTION or an OVERLOOK (the load-bearing flags) — STATUS 2026-06-02

**Items 1–4 are now CLOSED-WITH-TEETH** (the four carry-forward modules landed,
`Dregg2.lean:186-189`); only item 5 remains genuinely open. Original findings kept
for the record, each tagged with its resolution:

1. ~~**No HMAC chain integrity** (O).~~ **CLOSED [REAL].** `CaveatChain.lean` makes
   "caveats can only be added, the tail proves it" expressible AND proved: removal
   without re-signing forces a MAC no-op (`removal_breaks_tail`, `:328`), forgery
   reduces to a MAC collision (`forgery_requires_mac_query`, `:305`). The §8 obligation
   is now *explicit* (`MacKernel.unforgeable`, `:78-87`), exactly as the original asked.
2. ~~**The 3P discharge protocol is a `Bool` flip** (S→O).~~ **CLOSED [REAL].**
   `ThirdPartyDischarge.lean` carries the ticket/VID encryption (`recoverKey`, `:213`),
   the `r`-recovery-only-by-chain-replayer property (`unseal parentTail vid`), and
   bind-to-parent + freshness with rejection teeth (`cross_bound_rejected` `:333`,
   `stale_discharge_rejected` `:304`). `Discharge.lean`'s monotonicity is now the
   *await-face* of a fully crypto-grounded protocol, not the whole story.
3. ~~**Selective disclosure is missing from the credential model** (O).~~ **CLOSED
   [REAL]** at the new credential object: `SelectiveDisclosure.lean`'s
   `Credential{attr : Fin n → Nat}` + `presentation_hides_undisclosed` (`:239`) disclose
   an attribute subset with view-collapse hiding. *Residual:* the BASE `Credential.lean`
   (`claim:Nat`, all-or-nothing) is unchanged — the two are not yet unified (still OPEN,
   below).
4. ~~**Multi-show unlinkability is modeled but disconnected** (S).~~ **CLOSED [REAL].**
   `SelectiveDisclosure.multishow_unlinkable` (`:326`) states "the same credential is
   unlinkable across shows" *about the credential `Presentation` object* — the exact wiring
   the original said was missing.
5. **Stealth and StarkDelegation anonymity are STILL overlooked at the auth-mode layer**
   (O) — **GENUINELY OPEN.** `AuthModes.lean` remains the best module on the axis but still
   models only OneOf/Custom/CapTpDelivered/Bearer/Token/Unchecked — it drops the two
   `Authorization` variants that carry *actor*-anonymity. (Grep-confirmed 2026-06-02: no
   `Stealth`/`StarkDelegation` constructor in `AuthModes.lean`'s `AuthMode` inductive,
   `:135`.) NOTE the *credential-layer* anonymity (BlindedSet multi-show) is now covered by
   `SelectiveDisclosure.lean`; what is missing is specifically the stealth `P = c·G + S`
   one-time-key relation and the StarkDelegation hidden-delegator/bearer binding *as auth
   modes*. [ASPIRATIONAL — honestly-named open; no Lean object yet.]

### Where the Lean LEADS the Rust (carry the Lean semantics forward)

- **CapTP non-amplification** [REAL] (`AuthModes.lean` — `captp_granted_le_held`
  `:273`, `captp_sound` `:289`): the Lean proves `granted ≤ held`, which the Rust
  `verify_captp_delivered` is documented to omit (it checks signatures + facet masks
  but not the authority lattice). This is a *real bug surfaced by the Lean*. Carry the
  Lean's `captp_granted_le_held` gate into the verified kernel and **fix the Rust to
  match it**, per the improve-don't-degrade rule. (Cross-check: this is the FID-ESCROW
  pattern in reverse — here the Lean is the *better* spec.) Verified live 2026-06-02:
  both theorems present and term-proved (the dispatcher gate `authModeAdmits` for
  `CapTpDelivered` requires `decide (cert.granted.rights ≤ cert.held.rights)`,
  `AuthModes.lean:199`).

---

# PART 2 — REPUDIATION / DENIABILITY / DESIGNATED-VERIFIER

The severe privacy question: a publicly-verifiable STARK / WitnessedReceipt is
**transferable** ⇒ **non-repudiable**. Anyone holding the artifact can later prove
to *any* third party that a turn was authorized. Grounded in the code:

## 2.1 Confirmation: dregg's attestations ARE transferable / publicly-verifiable

Every attestation primitive is maximally transferable:

- **WitnessedReceipt** verifies stand-alone against a global VK with no verifier
  secret: `verifier::verify_effect_vm_proof` (`turn/src/witnessed_receipt.rs:250-251`);
  the artifact is explicitly designed to *travel as gossip*
  (`witnessed_receipt.rs:287-307`) and serialize to a durable
  `DWR1` envelope (`witnessed_receipt.rs:341-373`). Public inputs are extracted
  in the clear (`witnessed_receipt.rs:253-256`).
- **Credential presentation STARK** verifies against the **public**
  `federation_root` (`bridge/src/present.rs:269-308`,
  `present.rs:284-308`). No designated verifier; anyone with the federation root
  is convinced.
- **StarkDelegation** binds only public scope and verifies with the global Effect
  VM AIR (`turn/src/executor/authorize.rs:1322-1332`) — transferable.
- **SignedDelegation / HandoffCertificate** are **Ed25519 signatures**
  (`turn/src/action.rs:486-494`; `captp/src/handoff.rs:115-191, 251-257`). An
  Ed25519 signature is the canonical *non-repudiable, universally-verifiable*
  object: `verify_signature` (`handoff.rs:255-257`) convinces anyone. The
  recipient also signs (`handoff.rs:314-348`), so the presentation is a
  two-signature transferable transcript.
- **Stealth auth** is *also* a transferable Ed25519 signature under the one-time
  key `P` (`authorize.rs:1337-1417`): it hides *who* but the signature is still a
  transferable proof that *whoever holds S* authorized the action.

**Verdict: the system is hardwired to maximal transferability.** Every "yes, this
was authorized" badge is a portable, third-party-convincing object. There is no
verifier-bound nonce, no chameleon/trapdoor, no interactive ZK, anywhere.

## 2.2 What dregg HAS vs LACKS across the three properties

### (a) ANONYMITY (hide *who*) — STRONG, and partly proved

| Mechanism | Rust (file:line) | What it hides | Real? |
|---|---|---|---|
| Stealth addresses | `cell/src/stealth.rs:136-214`; auth `authorize.rs:1337-1417` | the recipient/actor's persistent key `S`; per-turn one-time `P` | Yes — real Monero/EIP-5564 construction; `S` never on the wire. |
| StarkDelegation | `authorize.rs:1252-1333` | delegator + bearer pubkeys (behind `root_issuer_commitment`) | Yes — only public scope is bound. |
| Anonymous credential present (BlindedSet) | `credentials/src/presentation.rs:176-299` | which credential / which issuer-tree leaf; multi-show unlinkable | Yes — fresh per-show blinding factor. |
| Pedersen value commitments | `wasm/src/privacy.rs:283-475`; `cell` commitments | the amount | Yes — homomorphic, range-proven. |
| Nullifiers | `cell` nullifier path; `Privacy.lean:520-556` | which note/holder spent | Yes. |

Lean coverage of anonymity is genuinely good: `Privacy.unlinkable`
(`Privacy.lean:457-461`), `stealth_anonymity_set_large` (k-anonymity, `:467-472`),
`blinded_membership_hides_element` (`:489-494`), `nullifier_hides_identity`
(`:538-541`), all stated as *view-indistinguishability* with non-vacuous
`Reference` witnesses (`:558-567`). So **anonymity is the one Part-2 property the
Lean already models honestly.**

### (b) DENIABILITY / REPUDIATION — ABSENT

A search of the entire Rust tree for `deniab|repudiat|disavow|chameleon|
RingSignature|ring.signature` returns **no implementation** (only an unrelated
mention in `turn/src/action.rs` doc and `audit/src/tests.rs`). The Lean tree has
**nothing**.

- There is **no ring signature** anywhere (the closest, "anonymity set", is the
  BlindedSet *membership* proof, which proves "I am one of the set" — it hides
  *which* member but the proof is still a transferable, publicly-verifiable STARK,
  so it gives anonymity, **not** deniability). A ring signature's deniability
  flavor ("one of us signed, you can't prove which, and any of us could have
  forged my apparent participation") is not present.
- There is no chameleon hash / trapdoor commitment that would let an authorizer
  later claim "I could have produced that for any message."
- **Net: the authorizer can NEVER deny to a suspecting verifier.** Once a
  WitnessedReceipt / signed delegation / stealth signature exists, it is a
  permanent, transferable fact. Anonymity hides *who among a set*, but for the
  *actual* signer there is no plausible-deniability mechanism.

### (c) DESIGNATED-VERIFIER / non-transferable proof — ABSENT IN RUST, **NOW MODELED IN LEAN**

- ~~No "proof valid only to holder of verifier-sk" construction exists in Rust or
  Lean.~~ **CORRECTION (2026-06-02):** still **absent in the running Rust**
  (verified: `circuit/src/presentation.rs::verify` takes only `&self` + public root,
  no verifier-secret — a grep finds none), but the **Lean now MODELS the axis**:
  `Authority/DesignatedVerifier.lean` builds the verifier-indexed discharge
  `DischargedFor : Verifier → Statement → Proof → Prop` (`:113`) and the
  transferability dial. [Lean: REAL. Rust: ASPIRATIONAL.]
- Every *running* verifier path (`verifier::*`, `verify_issuer_stark`,
  `verify_signature`, `stark::verify`) takes only *public* inputs + a *global* VK and
  returns a universal accept/reject — none takes a verifier secret key. (Still true;
  the §8 `DVKernel.verifyFor` oracle that DOES take a verifier index is Lean-only,
  awaiting a DV-NIZK/chameleon Rust impl.)
- The one place that *strips* private data — `Presentation::to_wire` removing the
  `AuthorizationTrace` (`presentation.rs:133-152`) — protects the *prover's*
  witness from leaking; it does **not** make the resulting proof non-transferable.
  The stripped proof is still universally verifiable.
- **What the Lean now proves about the absent-in-Rust mode:** the *designated* mode
  convinces a specific `V₀` and is NOT transferable (`designated_not_transferable`,
  `DesignatedVerifier.lean:206` — extracts a concrete unconvinced verifier), and it is
  *deniable* via the simulator (`designated_is_deniable`, `:224` — `V₀` could have
  produced the convincing transcript itself, so it carries zero third-party evidence).
  The two endpoints are a *witnessed* separation, not a vacuous `True`
  (`dial_endpoints_distinct`, `:346`). The DV-ZK crypto stays the §8 `DVKernel` portal.

**Summary table (corrected 2026-06-02):**

| Property | dregg status | Mechanism / absence (file:line) |
|---|---|---|
| Anonymity (hide who) | **HAS, strong, partly proved** | stealth `cell/src/stealth.rs`; StarkDelegation `authorize.rs:1252`; BlindedSet `credentials/src/presentation.rs:176`; Lean `Privacy.lean:457-541`; credential-layer now also `SelectiveDisclosure.lean:326` (multi-show unlinkable) |
| Deniability / repudiation | **Rust LACKS; Lean MODELS the dial** | Rust: no ring sig / chameleon / disavowal (grep-confirmed). Lean: `DesignatedVerifier.designated_is_deniable` (`:224`, simulator repudiation) — the *property* is specified; a ring/chameleon Rust impl is the ASPIRATIONAL remainder |
| Designated-verifier / non-transferable | **Rust LACKS; Lean MODELS the axis** | Rust: all verifiers take public PI + global VK, no verifier-sk path. Lean: `DesignatedVerifier.DischargedFor` (`:113`) + `Transferable`/`DesignatedFor` dial + `designated_not_transferable` (`:206`) |

## 2.3 The tension: verifiability ⊥ deniability — and is there a dial?

The tension is real and dregg sits at one pole:
- **Verifiability (transferable proof)** is *required* by dregg's distributed
  core: consensus/finality (`blocklace/`), the proof-carrying forest
  (`circuit/src/proof_forest.rs`, `Exec/ProofForest.lean`), bilateral cross-cell
  consistency (`witnessed_receipt.rs:482-529`), and dispute resolution
  (`app-framework/src/dispute.rs`) all need a third party to *independently
  re-verify* a turn. A non-transferable proof cannot serve these.
- **Deniability (non-transferable)** is what private bilateral interaction wants:
  "I'll prove to *you* I'm authorized, but you can't show it to anyone else."

dregg's *running Rust* today has **no transferability dial**: the existing
disclosure controls (`FieldVisibility::{Public, Committed, SelectivelyDisclosable}`
at `cell/src/state.rs:16-25`; presentation `disclose` at `presentation.rs:36-37`;
fully-private vs selective-disclosure `revealed_facts_commitment` at
`bridge/src/present.rs:131-136`) all dial **what is revealed** — never **to whom
the proof is convincing**. Even "fully private" is *universally* verifiable; it
just reveals fewer facts. The transferability axis is orthogonal to the disclosure
axis and is, in the Rust, still pinned at "maximal."

**CORRECTION (2026-06-02):** the *Lean specification* of the dial now EXISTS —
`Authority/DesignatedVerifier.lean`'s `TransferDial` (`:146`) is exactly the second
axis this paragraph said was missing, beside the disclosure dials. Its `.transferable`
endpoint provably collapses to dregg's current universal verdict
(`publicMode_collapses_to_universal`, `:186`), and its `.designated V₀` endpoint is
the non-transferable/deniable mode (`DesignatedFor`, `:138`). So the dial is no longer
un-conceived; it is *specified and proved-coherent in Lean*, and the gap is now purely
the Rust DV-NIZK/chameleon implementation (§2.4).

## 2.4 What a designated-verifier / deniable MODE would take (sketch)

This is a *new* capability, not a tweak. It composes *orthogonally* to the
existing disclosure dials (`acceptanceOnly`/`selective`/`fullDisclosure`): add a
third axis **transferability ∈ {public, designated, deniable}** alongside
**disclosure ∈ {acceptance-only, selective, full}**.

1. **Designated-verifier ZK (DVZK).** Replace the universally-sound STARK badge,
   *on the private path only*, with a proof of the disjunction
   `(turn is authorized) ∨ (I know verifier's secret key)`. The intended verifier
   knows their own sk so the proof is worthless to relay (they could have forged
   it); to the verifier the first disjunct is the only credible one. Compose:
   keep the public WitnessedReceipt for consensus, mint a DVZK *companion* for the
   private channel. Cost: a new circuit (an OR-composition over the existing
   presentation AIR + a Schnorr-knowledge clause); the federation-root membership
   stays as-is.
2. **Deniable authentication.** Use a SIGMA/OTR-style interactive (or
   ring-MAC) authenticator on the captp channel so the *recipient* is convinced
   live but holds no transferable transcript. This belongs at the
   `captp/handoff` layer (`handoff.rs`), replacing the Ed25519 recipient signature
   on the *private* path with a deniable MAC keyed to the session. The
   *introducer* signature (needed for authority provenance) would stay
   non-repudiable — only the *presentation* becomes deniable.
3. **Ring-based repudiation.** A true ring signature over the authorizer's
   anonymity set gives the weak deniability "one of us, you can't prove which."
   The BlindedSet machinery (`credentials/src/presentation.rs`,
   `cell/src/predicate.rs:274`) already commits an anonymity *set*; what is missing
   is making the *signature itself* (not just a membership proof) ring-structured
   and **non-transferable**. This is the smallest delta to get *some* repudiation,
   and it is the natural extension of the existing anonymity story.

In every case the **consensus/forest path keeps the transferable badge** (it must;
finality depends on it); the new mode is a *parallel private artifact* on the
bilateral channel.

~~The Lean model would need a new `Transferable` vs `Designated` distinction on the
verify seam (`Laws.Verifiable`): today `Discharged` is a single universal predicate;
deniability requires indexing it by *which verifier* is convinced — a genuinely new
piece of theory.~~ **DONE (2026-06-02) — the theory landed:**
`Authority/DesignatedVerifier.lean` builds exactly the `Transferable` vs `Designated`
distinction (`:129`/`:138`) over a verifier-indexed `DischargedFor` (`:113`),
recovering the single universal `Laws.Discharged` (`Laws.lean:41`) as the `∀V`
collapse (`publicMode_collapses_to_universal`, `:186`). The Lean half of all three
§2.4 sketches now has its *specification*:
- (1) **DVZK** — `DesignatedFor` + the simulator law `DVKernel.simulate_verifies`
  (`:102`) is the Lean-side statement of "the verifier could have forged it" (the
  OR-with-Schnorr disjunction's effect); the *circuit* is the Rust remainder. [Lean spec REAL; Rust circuit ASPIRATIONAL.]
- (2) **deniable auth** — `designated_is_deniable` (`:224`) is the "convinced live,
  no transferable transcript" property; the SIGMA/OTR `captp/handoff` impl is the Rust remainder.
- (3) **ring repudiation** — `repudiation_no_third_party_evidence` (`:246`) captures
  the "carries zero evidence to W" bite; the ring *signature* (vs membership proof) is the Rust remainder.

So the *new piece of theory* exists and is proved-coherent over a reference DV-kernel
(`dial_endpoints_distinct`, `:346`); what remains is **three Rust crypto
implementations**, not a missing Lean concept.

---

# CARRY-FORWARD VERDICT

## Rust semantics that MUST be carried forward faithfully — STATUS 2026-06-02

**Items 1–3 are DONE in Lean** (term-proved reductions, `Dregg2.lean:186-189`); item
4 remains open. This is the section the work actually closed.

1. ~~**HMAC caveat-chain integrity**~~ — **DONE [REAL].** `CaveatChain.lean` carries
   the replay-and-compare verifier and the integrity reduction
   (`forgery_requires_mac_query` `:305`, `removal_breaks_tail` `:328`); the HMAC is now
   an *explicit* §8 obligation (`MacKernel.unforgeable`, `:78-87`) — exactly "explicit,
   not unstated," as asked.
2. ~~**The 3P discharge protocol's cryptographic core**~~ — **DONE [REAL].**
   `ThirdPartyDischarge.lean` pairs the discharge monotonicity with the binding
   obligation: ticket/VID `r`-recovery (`recoverKey`, `:213`), bind-to-parent +
   freshness with teeth (`cross_bound_rejected` `:333`, `stale_discharge_rejected`
   `:304`), AEAD as §8 `DischargeCrypto.cryptoSound`.
3. ~~**Credential selective disclosure + predicate proofs + anonymous multi-show**~~ —
   **DONE [REAL]** at the new credential object: `SelectiveDisclosure.lean`
   (`presentation_hides_undisclosed` `:239`, `proven_predicate_holds` `:287` with teeth
   `:298`, `multishow_unlinkable` `:326`). *Residual:* unify with the BASE
   `Credential.lean` (still all-or-nothing `claim:Nat`).
4. **Stealth + StarkDelegation actor-anonymity** as first-class auth modes
   (`authorize.rs:1252-1417`, `cell/src/stealth.rs`) — **STILL OPEN [ASPIRATIONAL].**
   `AuthModes.lean`'s `AuthMode` inductive (`:135`) still omits both. The
   *credential-layer* anonymity is now covered; the *auth-mode-layer* stealth
   `P = c·G + S` relation and StarkDelegation hidden-delegator binding are not yet
   Lean objects (grep-confirmed absent 2026-06-02).

## Where the Lean WAS a FICTION / OVERLOOK — STATUS 2026-06-02
- ~~**Fiction-adjacent:** a reader of `Authority/Caveat.lean` + `Discharge.lean` would
  believe the token layer is fully captured; in fact *all* of the cryptographic
  substance … is absent and unflagged.~~ **RESOLVED.** The cryptographic substance now
  lives in `CaveatChain.lean` + `ThirdPartyDischarge.lean`, each with an *explicit* §8
  portal section flagging precisely what is assumed (`MacKernel`/`DischargeCrypto`).
  `Caveat.lean`/`Discharge.lean` are now correctly understood as the *algebraic faces*
  (narrowing, await-monotonicity) of crypto-grounded protocols, not the whole truth.
  The FID-ESCROW failure mode is averted: shape AND substance are present, and the
  assumption boundary is named.
- **Remaining overlook:** Stealth + StarkDelegation in `AuthModes.lean` (item 4 above).
  Selective disclosure and multi-show unlinkability are NO LONGER overlooks — they are
  in `SelectiveDisclosure.lean`, wired to the credential `Presentation` object.
- **Counter-note (Lean is BETTER), UNCHANGED:** CapTP non-amplification
  (`AuthModes.lean` — `captp_granted_le_held` `:273`, `captp_sound` `:289`) is the
  *correct* spec; the Rust `verify_captp_delivered` is the buggy side. Carry the Lean
  forward and fix Rust. [REAL — this finding still stands.]

## Ranked advanced token/auth features — STATUS 2026-06-02 (most → least load-bearing)
1. ~~**HMAC caveat-chain integrity**~~ — **MODELED** (`CaveatChain.lean`). [REAL]
2. ~~**Third-party discharge crypto** (ticket/VID/bind/freshness)~~ — **MODELED**
   (`ThirdPartyDischarge.lean`). [REAL]
3. ~~**Credential selective disclosure + predicate proofs**~~ — **MODELED**
   (`SelectiveDisclosure.lean`). [REAL]
4. ~~**Anonymous multi-show unlinkability bound to the credential object**~~ —
   **MODELED & WIRED** (`SelectiveDisclosure.multishow_unlinkable`). [REAL]
5. **Stealth one-time-key auth mode** — STILL dropped from the auth-mode model. [ASPIRATIONAL]
6. **StarkDelegation anonymous delegation** (hidden delegator/bearer) — bearer STILL
   modeled only in the clear (`AuthModes.bearer`). [ASPIRATIONAL]
7. ~~**bind-to-parent + discharge freshness/replay**~~ — **MODELED**
   (`ThirdPartyDischarge`: `cross_bound_rejected`, `stale_discharge_rejected`). [REAL]

**Net: 5 of 7 missed features are now closed; the residual frontier is the two
auth-mode actor-anonymity variants (5, 6).**

## Part-2 verdict — STATUS 2026-06-02
The *running Rust* is **deliberately, structurally non-repudiable**: transferable
proofs are load-bearing for its distributed core, so this is not an oversight but an
architectural commitment, and the running code still has **zero deniability and zero
designated-verifier** capability. **CORRECTION:** the *Lean* is no longer silent on
this — `Authority/DesignatedVerifier.lean` now MODELS the missing axis: the
verifier-indexed `DischargedFor` (`:113`), the transferability dial (`:146`), and the
simulator-based deniability theorems (`designated_is_deniable` `:224`,
`designated_not_transferable` `:206`, `dial_endpoints_distinct` `:346`). The
private-interaction mode is *transferability* orthogonal to the existing *disclosure*
dials, and its **theory is now built and proved-coherent in Lean**; what remains is the
**three Rust crypto implementations** (DVZK circuit / deniable-auth SIGMA-MAC / ring
signature) — see §2.4. The anonymity-set commitment is still the only *running* stepping
stone, and it gets you the weakest (ring) form.

---

```
( ⌐■_■ )  the badge travels — and now, in Lean, we have also written down the badge
          that DOESN'T. the running code still answers "the badge always travels";
          the kernel now knows how to say "only to you." the Rust crypto is the
          remaining mile.   ( the spec caught up; the silicon hasn't yet )
```
