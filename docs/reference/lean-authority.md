# Lean: authority & the production law

What the `metatheory/Dregg2/Authority/` subsystem is at HEAD. The thesis it
encodes — stated in `metatheory/CONSTRUCTIVE-KNOWLEDGE.md:18-50` — is that **a
principal's authority over a resource is exactly its ability to constructively
exhibit a witness the kernel accepts**: authority is *production under
non-forgeability*, not affine descent. This subsystem is the Lean realization of
that thesis for credentials/macaroons/biscuits: the attenuation algebra, the
verify/find seam, the credential lifecycle, and the bridge that welds the
macaroon caveat-chain narrowing onto the kernel capability gate.

Every module here is a `Dregg2.lean`-imported library target (`lakefile.toml:12`
declares the un-globbed `Dregg2` lib; the imports are listed at
`Dregg2.lean:23,80,100,103,451,453,700`), so all of it is compiled under
`lake build`. The modules are pure and `#eval`/`#guard`-runnable, and the
load-bearing theorems pin their axiom footprint with `#assert_axioms`.

---

## The verify/find seam: soundness-by-verification

`Dregg2.Authority.Predicate` models dregg1's `WitnessedPredicateRegistry`
(`cell/src/predicate.rs`) as a map from a witness-bearing kind to a decidable
verifier plugin.

- `WitnessedKind` (`Predicate.lean:35`) — the seven built-in kinds
  (`dfa | temporal | merkleMembership | nonMembership | pedersen | blindedSet |
  bridge`) plus the open, content-addressed extension `custom (vk : Nat)`.
- `registryVerify` (`Predicate.lean:72`) — the dispatch: look up the verifier
  for a kind and run it; an unregistered kind fails closed (`false`,
  `Predicate.lean:74-76`).
- The keystone `registry_sound` (`Predicate.lean:99`): a witness the registry
  accepts for a kind discharges that kind's predicate. The prover/matcher is the
  *untrusted* `find` side — `registry_sound_find` (`Predicate.lean:111`) carries
  the producer's `some wit` as documentation but proves soundness from the
  accept bit alone (the gate decides, not the producer).
- The asymmetry is the point: `find_untrusted` (`Predicate.lean:126`) exhibits a
  prover that gives up where a witness exists (no completeness/termination), and
  `adversarial_find_cannot_forge` (`Predicate.lean:139`) proves that against *any*
  prover, an honest verifier that rejects `(stmt, wit)` cannot be made to accept.
- Crypto kinds route their verifier through the §8 `CryptoKernel.verify` oracle
  (`cryptoVerifier`, `Predicate.lean:196`; `crypto_kind_routes_to_oracle`,
  `Predicate.lean:204`) — the Lean law models dispatch and
  soundness-by-verification, never reasoning into the crypto.

This is the `Predicate ⊣ Witness` adjunction made operational: checking is
cheap and in-TCB; search is undecidable and untrusted.

---

## The caveat algebra: attenuation narrows

`Dregg2.Authority.Caveat` is the keys-as-caps token layer (a caveat as a
`Ctx → Bool` admit gate plus a third-party gateway arm).

- A token admits a request iff **all** its caveats are satisfied — the
  conjunction/meet `Token.admits` (`Caveat.lean:149`, mirroring
  `token/src/dregg_caveats.rs`'s `List.all`).
- `Token.attenuate` (`Caveat.lean:154`) appends a caveat, and `attenuate_narrows`
  (`Caveat.lean:162`) proves it can only shrink the admitted set: anything the
  attenuated token admits, the parent already admitted.
- `CaveatPred` (`Caveat.lean:66`) reifies the temporal floor/ceiling predicates
  (`validAfter`/`validUntil`/`heightLt`/⊤/⊥) so the content-level refinement order
  `CaveatPred.refines` (`Caveat.lean:271`) can be decided structurally over all
  contexts (`caveatPred_refines`, `Caveat.lean:278`), with non-vacuity teeth
  (`#assert_axioms` list at `Caveat.lean:380-387`).
- `TokenKind` distinguishes biscuit vs. macaroon transport: a macaroon is *not*
  cross-vat verifiable, a biscuit is (`macaroon_not_crossvat`/`biscuit_crossvat`,
  `Caveat.lean:191,196`).

---

## The macaroon: an HMAC-authenticated append-only chain

`Dregg2.Authority.CaveatChain` carries the real `macaroon/src/macaroon.rs`
semantics — the running-tag chain `T₀ = HMAC(root, nonce)`,
`Tᵢ = HMAC(Tᵢ₋₁, encode(Cᵢ))` — that a bare `Ctx → Bool` list cannot express:
chain integrity (you cannot remove, reorder, or forge a caveat).

- `MacKernel` (`CaveatChain.lean:76`) is the §8 keyed-hash portal: an
  uninterpreted `mac`, an abstract `Tagged` "genuine MAC" relation, a runnable
  recompute-and-compare `verifyTag`, and the **`unforgeable : Prop`** EUF-CMA
  carrier. The carrier is welded to the semantics by `verifyTag_sound`
  (`CaveatChain.lean:95`): it is *not* a `True`-fillable label — a collapsing
  oracle makes `unforgeable` provably false.
- The chain is built/verified exactly as Rust computes the tail
  (`Chain.append`/`Chain.verify`, `CaveatChain.lean:162,169`);
  `verify_iff_wellTagged` (`CaveatChain.lean:177`) is the replay-and-compare
  equivalence, and `append_narrows` (`CaveatChain.lean:230`) lifts the caveat
  algebra's narrowing onto the chain.
- Structural integrity (holds even on a toy `mac`, reducing forgery to a MAC
  collision): `integrity_tail_binds` (`CaveatChain.lean:292`),
  `forgery_requires_mac_query` (`CaveatChain.lean:302`), `removal_breaks_tail`
  (`CaveatChain.lean:324`).
- The de-vacuified result `chain_unforgeable` (`CaveatChain.lean:402`)
  **consumes** `unforgeable` via `verifyTag_sound` and concludes the genuine
  `Tagged` relation for a verifying non-empty chain's stored tail — the reduction
  "forge a verifying chain ⇒ break HMAC", with HMAC security left as the named §8
  portal. Non-vacuity is witnessed both ways: a positive honest-kernel witness
  and a negative collapse-refutation in the in-file `Demo` namespace
  (referenced at `CaveatChain.lean:359,399-402`).

`Dregg2.Authority.BiscuitGraph` is the public-key analogue: a biscuit is a signed
block chain (`Block`, `BiscuitGraph.lean:55`) enabling **offline** attenuation,
with `WellFormed` (`BiscuitGraph.lean:88`) demanding both that each block verifies
under its parent's `vkey` and that it attenuates (`child.authority ⊆ parent`).
The keystone `biscuit_narrows` (`BiscuitGraph.lean:96`) proves the leaf confers
⊆ the root; signature unforgeability is the §8 `SigChecker` oracle, never a Lean
law.

---

## The structured clearance lattice: `attenuate` is a meet

`Dregg2.Authority.CredentialAttenuation` models the thing the real Rust
credential stack computes — the multi-dimensional `token/src/traits.rs::Attenuation`
that tightens several independent axes at once — which the flat-set modules do
not (`CredentialAttenuation.lean:1-76` states this explicitly and imports the
others read-only).

- A `Clearance` (`CredentialAttenuation.lean:164`) is the product of an action
  mask (`Mask`, a `Finset Action`), a validity `Window` (`[lo,hi]` over
  `WithBot/WithTop Int`), and a user-confinement set. `Clearance.admits`
  (`CredentialAttenuation.lean:183`) is the meet-semantics fail-closed
  conjunction — the runnable golden oracle.
- `attenuate` (`CredentialAttenuation.lean:209`) applies one restriction as a
  **meet**: intersect the mask, intersect the window, AND the confinement. Each
  axis's meet is a subinterval/subset (`Window.meet_le_left`,
  `CredentialAttenuation.lean:294`).
- The order `Clearance.le` (`≼`, `CredentialAttenuation.lean:231`) is genuine,
  not a `() ≤ ()` collapse: masks order by `⊆` (so `{read,write}` and `{read}`
  are properly comparable; `order_discriminates`, `CredentialAttenuation.lean:351`,
  proves a wider mask is *not* `≼` a narrower one), and `admits` is monotone in it
  (`admits_mono` KEYSTONE, `CredentialAttenuation.lean:270`).
- The headline **`attenuate_le`** (`CredentialAttenuation.lean:302`): the
  attenuated clearance is `≼` the parent across all axes simultaneously — Rust's
  "can only narrow, never expand" (`token/src/traits.rs:178-181`) as a theorem.
  Its operational form `attenuate_admits_subset` (`CredentialAttenuation.lean:322`)
  and the contrapositive tooth `amplification_impossible`
  (`CredentialAttenuation.lean:341`) say no restriction can add back authority the
  parent withheld.
- **Multi-party (n>1)**: `attenuateChain` applies a delegation chain left to right;
  `chain_narrows` (`CredentialAttenuation.lean:389`) proves the leaf admits ⊆ the
  root for arbitrary chain length (via `chain_le` + `Clearance.le_trans`), and
  `chain_le_prefix` (`CredentialAttenuation.lean:401`) that every additional
  hand-off narrows further.

### Connection to the verified executor

`clearance_attenuation_is_exec_nonamplifying` (`CredentialAttenuation.lean:450`)
projects the mask axis through `maskToAuth` onto the executor's
`Exec.EffectsAuthority.IsNonAmplifying` over the real `ECap`/`List Auth` lattice
— so credential attenuation here lands on the *same* `is_attenuation(held, granted)`
gate the kernel enforces, not a parallel toy.

### The §8 integrity boundary

The narrowing algebra is unconditional. The thing that needs the carried crypto
assumption is **integrity**: that a presented derived credential really is an
`attenuate` of the issuer root (not forged with a wider clearance). That binding
is reused, not re-proved: `presented_attenuation_is_genuine`
(`CredentialAttenuation.lean:491`) takes the same `MacKernel.unforgeable` carrier
and routes through `CaveatChain.chain_unforgeable`. Every keystone here pins
clean — `#assert_axioms` over the headline list at
`CredentialAttenuation.lean:574-586` (`{propext, Classical.choice, Quot.sound}`),
with the integrity theorem taking `unforgeable` as an explicit hypothesis rather
than an `axiom`.

---

## The credential lifecycle: issue / present / verify / revoke

`Dregg2.Authority.Credential` is the keys-as-caps verifiable credential: a
`VC = {issuer, schema, subject, claim, attestation}` (`Credential.lean:47`) with
a content-addressed `id`.

- `verify` (`Credential.lean:145`) admits iff the §8 `CryptoKernel.verify` accepts
  the attestation against the issuer statement (it was *issued*) **and** the id is
  not in the revocation set (the negative discharge) — a fail-closed `&&`.
- The keystone `credential_verifies_iff_issued_and_not_revoked`
  (`Credential.lean:155`) proves both directions.
- Revocation **reuses** the nullifier G-Set wholesale (`RevocationSet :=
  NullifierCell.Cell`, `Credential.lean:111`): `revoke` is a nullifier spend
  (`Credential.lean:125`), `revoke_blocks_verify` (`Credential.lean:180`) fires
  the negative discharge, and `revocation_is_iconfluent` (`Credential.lean:212`) +
  `revocation_tier1_eligible` (`Credential.lean:220`) prove revocation is the
  *narrowest* consensus seam — grow-only, partition-tolerant, needing only
  root-epoch agreement. Non-vacuity: `revocation_invariant_nontrivial`
  (`Credential.lean:227`).

---

## The convergence arrow: macaroon caveat-chain ⇒ kernel cap gate

The credential is meant to be *one authority seen four ways* (biscuit · macaroon ·
kernel cap · zk), all refining `granted ⊆ held`. `Dregg2.Authority.CaveatCapBridge`
is where the macaroon caveat-chain narrowing is welded onto the kernel capability
gate `capAuthorityG` over the shared `ExecAuth := Finset Auth` lattice.

- `caveatChainAuthority` (the shared narrowing) and `caveatChainAuthority_le_held`
  (`CaveatCapBridge.lean:77`) render the macaroon's `append_narrows` directly on
  the rights lattice (`granted ⊆ held` by construction), with
  `delegationVerb_authority_eq` (`CaveatCapBridge.lean:108`) giving equality when
  `keep ≤ held`.
- `chainGateG_implies_capAuthorityG` (`CaveatCapBridge.lean:168`) shows the
  macaroon chain gate implies the kernel cap gate on a *coherently-built* node —
  but the module flags (`CaveatCapBridge.lean:232-253`) that this keystone's
  conclusion holds *regardless* of the hypothesis, because `granted` is hardwired
  to `caveatChainAuthority held keeps` (≤ held by construction). That is honest
  defense-in-depth but does not make the macaroon gate load-bearing.
- The de-vacuified bridge closes that gap over a node with a **free**
  `(granted, held)` pair read by one shared quantity:
  - `chainGateG_emits_granted_le_held` (`CaveatCapBridge.lean:337`) — the macaroon
    caveat-chain gate passing **forces** `granted ≤ held` (the proof consumes the
    hypothesis, reading the admit leg which *is* `decide (granted ≤ held)`);
  - `chainGateG_implies_capAuthorityG_devac` (`CaveatCapBridge.lean:357`) — that
    same forced atom drives the kernel `capAuthorityG` gate, so the `gateOK` `&&`
    of the two legs is a proven identity carried by one quantity;
  - `capAuthorityG_reads_same_atom` (`CaveatCapBridge.lean:374`) — the converse
    leg: the kernel gate's content is the identical `granted ≤ held`.
  - Non-vacuity is two-polarity: a non-amplifying pair makes **both** gates pass
    and an amplifying pair makes **both** fail (`deleg_nonAmp_*`/`deleg_amp_*`,
    `CaveatCapBridge.lean:408-418` and the `#guard`s at `:396-404`).

This is the live convergence point named in `CONSTRUCTIVE-KNOWLEDGE.md:485-511`
as the macaroon↔cap arrow — and at HEAD the `Authority/` bridge carries a
non-vacuous `chainGateG → capAuthorityG` arrow over a shared rights pair, going
beyond that section's (kernel-file-scoped) "no such theorem" framing. The whole
file is `#assert_axioms`-clean (`CaveatCapBridge.lean:584-609`).

`Dregg2.Authority.TokenCapBridge` carries the companion four-leg story — macaroon
token, biscuit chain, and the cell-program crown all reducing to the same
`granted ⊆ held` over `Finset Auth` (`caveatChainToken_admits_capCrown`
`TokenCapBridge.lean:183`, `biscuitVerify_implies_capCrown_admits`
`TokenCapBridge.lean:206`, with the structural forged-token bound
`forged_token_cannot_forge_capCrown` `TokenCapBridge.lean:251`).

---

## How it composes

The four facets of "authority = production under non-forgeability"
(`CONSTRUCTIVE-KNOWLEDGE.md:34-41`) appear here as:

1. **non-forgeability** — the §8 portals (`CryptoKernel.verify`,
   `MacKernel.unforgeable`, biscuit `SigChecker`): the ability to produce a
   witness is uncounterfeitable; the Lean law proves the *reduction*, never the
   crypto.
2. **monotone attenuation (`granted ⊆ held`)** — `attenuate_le` /
   `chain_narrows` (clearance), `append_narrows` / `chain_unforgeable` (macaroon),
   `biscuit_narrows` (biscuit), all landing on the executor's `IsNonAmplifying`.
3. **kernel enforcement** — `capAuthorityG`, reached via the de-vacuified bridge
   so the macaroon narrowing forces the kernel atom.
4. **zk-checkability** — the §8 oracles are exactly the carriers the deployed
   circuit discharges (named, not proved in Lean).

The discipline throughout: **narrowing is a theorem; non-forgeability is a named
assumption** discharged by the real keyed-hash/signature and provably false on a
collapsing oracle.
