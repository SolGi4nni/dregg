# The Dual Multi-Aspect Authorization Model

*A study + design. Four aspects (biscuit · macaroon · capability · zk) as facets
of ONE credential — the map as built, the recovered intent, the integration
seams, and the design that welds them onto one proven arrow.*

Status of this document: **study + design**, read-heavy. No big change is
implemented here. Every claim is file:line'd; where a build was used to verify, it
is noted.

---

## 0. Executive summary

The credential is meant to be a **dual multi-aspect** object — one authority,
seen four ways:

- **biscuit** (Datalog policy — *what the credential permits*): `dregg-token`'s
  `biscuit` feature (`token/src/biscuit_backend.rs`, `token/src/dregg.rs`),
  wrapped at the rim by `dregg-auth`'s `Grant`/`Token` surface
  (`dregg-auth/src/grant.rs`). Real `biscuit_auth::Authorizer::authorize()`
  Datalog, call-bound. **Live** via the executor + node-MCP gate + SDK sub-agent
  spawn.
- **macaroon** (caveat-chain attenuation transport — *how authority narrows on
  the wire, hop by hop*): the HMAC `dregg-macaroon` crate
  (`macaroon/src/macaroon.rs`) behind `dregg-token`'s `MacaroonToken`, carried by
  the SDK's `AgentCipherclerk`/`HeldToken` (`sdk/src/cipherclerk.rs`); and a
  *second, cleaner* ed25519+BLAKE3 implementation, `dregg_auth::credential`
  (`dregg-auth/src/credential/`), built to mirror the Lean theory line-for-line.
- **capability** (object-cap c-list — *what the running kernel actually
  enforces*): the kernel `caps : Label → List Cap` side-table
  (`metatheory/Dregg2/Exec/Caps.lean`), its Rust c-list
  (`cell/src/capability.rs`), the openable `capability_root`
  (`cell/src/commitment.rs`, `circuit/src/cap_root.rs`), and the Granovetter
  delegate edge `recKDelegateAtten` with proven `granted ≤ held`
  (`metatheory/Dregg2/Exec/AuthTurn.lean:439`).
- **zk** (proof of honest narrowing — *proving the kernel narrowed correctly so a
  light client can't be fooled*): the Argus turn proof — `portalVerify` (the
  credential-validity §8 leg, `metatheory/Dregg2/Exec/FullForestAuth.lean:138`)
  plus the **in-circuit `granted ⊆ held`** against the authenticated openable
  cap-root (`circuit/tests/effect_vm_attenuate_non_amp.rs`,
  `circuit/tests/effect_vm_grant_non_amp.rs`, cap Phase A/B/B2/D — landed).

**What was missing, in one sentence:** *the four aspects each narrow authority,
but only the capability aspect's narrowing (`granted ⊆ held`) is bound to the
kernel state and proven in-circuit — biscuit's Datalog decision, the macaroon
caveat chain, and the cap-subset are evaluated as **independent conjuncts** over
**independent record fields** (`gateOK na s = credentialValidG na && capAuthorityG
na && caveatsDischarged na s && revocationGate na s`,
`FullForestAuth.lean:490`), with no proven arrow that the macaroon/biscuit
narrowing **equals** the kernel cap narrowing, so non-amplification is told as
three informally-agreeing stories rather than one.*

**The smallest first integration step:** make the macaroon/biscuit caveat that
narrows a *capability-bearing* verb **emit the same `(granted, held)` pair the
kernel cap leg already consumes** — i.e. give `NodeAuth` a single shared
"narrowed authority" field that BOTH `chainGateG` and `capAuthorityG` read, and
prove the one-line bridge `chainGateG na = true → granted(na) ⊆ held(na)` on the
verb where they overlap (delegation). That is one Lean lemma plus one SDK field;
it turns the existing `&&` from defense-in-depth into a *proven identity* on the
overlap, without deleting any aspect.

**GREEN / YELLOW / RED — is the dual multi-aspect model coherently integrated
today?**

> **RED → YELLOW.** RED on *coherent integration*: the four aspects are real and
> individually sound, but they are four parallel authority surfaces welded by
> conjunction, not one proven authority — the macaroon/biscuit narrowing is not
> bound to the kernel cap, and biscuit's decision touches neither the cap c-list
> nor the circuit. YELLOW is the honest grade for the *capability+zk pair alone*:
> cap Phase A/B/B2/D have landed, so the kernel cap narrowing **is** authenticated
> and proven in-circuit (`circuit/tests/effect_vm_attenuate_non_amp.rs`). The
> design below moves the *whole model* to GREEN by routing all four aspects onto
> that one proven `granted ⊆ held` arrow.

---

## 1. The four aspects as they exist (file:line'd)

### 1.1 biscuit — Datalog policy

**Where it lives.** Two layers over one engine:

- The engine: `dregg-token`'s `biscuit` feature. `BiscuitToken`
  (`token/src/biscuit_backend.rs:28`) wraps `biscuit_auth::Biscuit`. `mint_dregg`
  (`:69`) emits authority Datalog via `dregg::authority_datalog`
  (`token/src/dregg.rs:91`); `verify` (`:141`) builds an `Authorizer` from
  `authorizer_datalog(request)` (`token/src/dregg.rs:239`) and calls
  `authorizer.authorize()` (`:145`) — **genuine biscuit Datalog evaluation**, not
  a stub. `attenuate` (`:230`) appends a real biscuit block; `seal` (`:268`)
  blocks further attenuation.
- The rim: `dregg-auth`'s `Root`/`Grant`/`Token` (`dregg-auth/src/lib.rs:91,140`;
  `dregg-auth/src/grant.rs:67`). `Grant::issue_with` (`grant.rs:130`) emits
  `app(tool, actions)` / `user(subject)` / `feature("rate:…")`. `verify_offline`
  (`lib.rs:346`) is the one-line offline check; `mcp::OfflineGate`
  (`dregg-auth/src/mcp.rs:130`) is the tool-gate middleware.

**What it expresses.** Datalog facts `app(id,actions)`, `service(name,actions)`,
`feature(name)`, `oauth_provider/oauth_scope`, `user(uid)`, `unrestricted(true)`
(only when zero app+service grants, `dregg.rs:150`); attenuation as confining
checks `check if request_app($t), allowed_tool($t)` (genuine no-amplify,
`grant.rs:201`) and time bounds. Raw Datalog is never accepted — every value is
allowlist-`sanitize`d (`grant.rs:183`, `dregg.rs:43`), with injection tests
(`dregg.rs:380`).

**Is it on a live path?** **YES — but only the engine, not the rim.** The
executor's `verify_token_authorization`
(`turn/src/executor/authorize.rs:1678`) dispatches the
`(TokenFormat::Biscuit, TokenKeyRef::BiscuitIssuer)` arm (`:1714`), trust-anchors
the issuer against the target cell's key (`:1718`), decodes (`:1747`, real sig
check), and calls `token.verify(&request)` (`:1812`) — the real `Authorizer`. The
`AuthRequest` is call-bound: `action=hex(method)`, `service=hex(target)`,
`app_id=hex(federation_id)`, `now=block_height` (`:1639`). Live producers: the
node MCP cap-gate `mint_tool_cap`/`enforce_tool_cap`
(`node/src/mcp.rs:2084,2221`, called on every `tools/call` at `:7809`) and the SDK
sub-agent spawn `mint_subagent_cap_token` (`sdk/src/runtime.rs:108`). The polished
`dregg-auth` `Grant`/`OfflineGate` product face is **NOT** wired into the node —
it is reached only by its own CLI/tests + `pg-dregg`. The node built its own
parallel biscuit gate directly on `dregg-token` + the executor, leaving
`dregg-auth::ToolGate` unimplemented.

### 1.2 macaroon — caveat-chain attenuation + third-party discharge

**TWO implementations (confirmed), serving different layers:**

1. **`dregg-macaroon`** (`macaroon/src/`): canonical HMAC-SHA256 chain,
   XChaCha20-Poly1305 sealing, `em2_` wire prefix. `Macaroon` (`macaroon.rs:93`),
   `add_first_party` (append caveat, `:151`, `new_tail = HMAC(old_tail,
   caveat)`), `add_third_party` (`:175`), `bind_discharge` (`:341`), `verify`
   (`:204`). Gateway side: `DischargeGateway::process_request`
   (`macaroon/src/discharge_gateway.rs:530`) holds `K_A`, decrypts the ticket,
   runs `ConditionEvaluator`s, mints+signs the discharge (`create_discharge`,
   `macaroon.rs:383`). **The third-party authoring + signing path is fully
   present** here — the prior audit's "can a gateway author a discharge?" is YES.
   The one soft spot: `MacaroonToken::attenuate`
   (`token/src/macaroon_backend.rs:140`) only appends *first-party* caveats; to
   add a third-party caveat you must drop to the raw `Macaroon`.

2. **`dregg_auth::credential`** (`dregg-auth/src/credential/`): a SECOND,
   structurally-macaroon credential — ed25519 block-chain + BLAKE3, `dga1_`/`dgd1_`
   wire prefixes, **NOT HMAC**. `Caveat = FirstParty(Pred) | ThirdParty{gateway,
   caveat_id, hint}` (`caveat.rs:24`); `Pred` is a full Boolean algebra
   (`pred.rs:46`: `AttrEq/AttrPrefix/NotBefore/NotAfter/Within/AllOf/AnyOf/Not`),
   fail-closed under partial context (`Unbound ≠ false`, `pred.rs:28`).
   `Credential` (`chain.rs:214`), `attenuate` (the only mutation, `:246`), `tail()`
   = BLAKE3 of last sig (`:267`), `verify` (`:293`). `Discharge` (`chain.rs:425`)
   has a **mandatory** binding (`GatewayKey::discharge` *requires* `bound_to` —
   the unbound discharge is unconstructible, `chain.rs:176`). This module's doc
   comments (`mod.rs:19`) are a theorem-by-theorem map to the Lean. **It is the
   cleaner, Lean-faithful reference, but it is NOT the one carried by the live
   SDK** (the SDK uses the HMAC crate).

**The caveat vocabulary** (`token/src/dregg_caveats.rs:94`, enforced
`verify_caveats:388`, though canonical semantics is now Datalog
`MacaroonToken::verify → datalog_verify`, `macaroon_backend.rs:137`):

| ID | Name | Enforces |
|----|------|----------|
| 1 | App | app_id + action-mask containment |
| 2 | Service | service-name + action-mask containment |
| 4 | Feature | request features ⊆ granted |
| 5 | ValidityWindow | `not_before`/`not_after` |
| 8 | ConfineUser | request user_id ∈ confined set |
| 9 | OAuthProvider | provider match-any |
| 10 | OAuthScope | request scopes ⊆ granted |
| 13 | FeatureGlob | include/exclude glob |
| 14 | Budget | local budget-state check |
| 254 | ThirdParty | requires gateway discharge (HMAC layer, `caveat.rs:42`) |
| 255 | BindToParent | discharge binding (`caveat.rs:45`) |
| — | Unknown | **fail-closed DENY** (`dregg_caveats.rs:419`) |

**What backs the SDK's `HeldToken`.** The **federation-membership Merkle tree**
(`dregg_commit::merkle::MerkleTree`), leaves = **BLAKE3-derived proof keys**
(`derive_proof_key(root_key)`, `sdk/src/cipherclerk.rs:1570`; the leaf field is
`issuer_key = blake3::derive_key("dregg-proof-key-v1", root_key)`,
`cipherclerk.rs:469`). The ZK proof here proves "issuer ∈ federation tree." The
`HeldToken` (`cipherclerk.rs:361`) carries `encoded`/`root_key`/`issuer_key`/
`membership_proof`/`caveat_chain_hash`/`delegation_binding` — and **no kernel
`CapId`/c-list slot**. It is standalone at the agent layer.

**Lean model** (`metatheory/Dregg2/Authority/`): `Caveat.lean` (the narrowing
algebra: `attenuate_narrows:84`, `attenuate_subset:92`); `CaveatChain.lean` (HMAC
chain + `MacKernel` portal, integrity teeth); `MacaroonDischarge.lean`
(`unbound_discharge_rejected:153`, `binding_not_replayable_to_other_root:179`,
`#assert_axioms`-clean); `ThirdPartyDischarge.lean` (the ticket/VID two-key seal).
Rust differentials tie back: `macaroon/src/caveat_chain_diff.rs`,
`discharge_diff.rs`.

### 1.3 capability — object-cap c-list, kernel-enforced

**The c-list (Lean).** `Caps := Label → List Cap` (imported from
`Authority/Positional.lean`); `Cap = endpoint target (rights : List Auth) | node
target | null`; rights lattice `ExecAuth := Finset Auth` ordered by `⊆`, `⊤ =
univ` (`Exec/Caps.lean:60`). Ops: `grant`/`attenuate`/`derive`/`revoke`/`invoke`
(`Caps.lean:72-99`). The genuine `granted ≤ held`:
`attenuate_confRights_le` (`Caps.lean:133`, over `Finset Auth`, NOT a `()≤()`
collapse). The kernel-op face `recKDelegateAtten` (`Exec/AuthTurn.lean:97`) with
`recKDelegateAtten_non_amplifying` (`:439`). The circuit-IR primitive
`checkSubset` (`Circuit/Argus/Stmt.lean:83`) decides over the genuine partial
order (`{read}` vs `{write}` incomparable, `:380`).

**The c-list (Rust).** `CapabilityRef` (`cell/src/capability.rs:44`:
`target/slot/permissions/breadstuff/expires_at/allowed_effects/stored_epoch`),
`CapabilitySet` (`:126`, `refs: Vec<CapabilityRef>`). Non-amplification gate:
`is_attenuation(held, granted) := granted.is_narrower_or_equal(held)` (`:539`),
enforced in `attenuate`/`attenuate_in_place`. The openable root:
`compute_canonical_capability_root_felt` (`cell/src/commitment.rs:504`), leaf
`cap_ref_to_leaf` (`:458`).

**The 10-variant `Authorization`** (Rust `turn/src/action.rs:221`; Lean
`FullForestAuth.lean:103`): (1) Signature, (2) Proof (zk, vk-bound), (3)
Breadstuff (bearer token-hash, c-list read), (4) Bearer (delegation chain), (5)
Unchecked (genesis only), (6) CapTpDelivered (two-sig handoff), (7) Custom
(app-defined predicate), (8) OneOf (disjunction), (9) Token (biscuit/macaroon),
(10) Stealth (one-time-key). The Lean dispatcher `authModeAdmits`
(`Exec/AuthModes.lean:182`) proves per-mode soundness, including
`captp_granted_le_held` (`:271`) — and **notes the dregg1 Rust gap**
(`AuthModes.lean:20`): Rust `verify_captp_delivered` checks sigs + masks but does
**NOT** re-check the authority lattice; the Lean models the *correct* semantics.

### 1.4 zk — proof of honest narrowing

**What the turn proof witnesses about authorization** — three witnesses, cap
Phase A/B/B2/D landed (the cap-reshape memory is stale; **Phase D is in the
code**):

1. **`granted ⊆ held` in-circuit, authenticated.** `AttenuateCapability`:
   `circuit/tests/effect_vm_attenuate_non_amp.rs` — a verifying p3 proof implies
   `granted ⊑ held` on both the 16+16 effect-mask submask gate AND the
   `AuthRequired` partial-order lattice, with `held` **membership-opened against
   the actor's seeded `old_cap_root`** (four forgeries each rejected by a specific
   gate). `GrantCapability` (Phase B2): `circuit/tests/effect_vm_grant_non_amp.rs`
   — same gates cross-cell.
2. **The openable cap-root value (Phase A).** `circuit/src/cap_root.rs`
   (sorted-Poseidon2 Merkle, depth 16, 7-field leaf); seeded from the cell's
   canonical root, **not `BabyBear::ZERO`** — this closes the "circuit starts at
   ZERO" disjointness. Differential: `circuit/tests/cap_root_cell_circuit_differential.rs`.
3. **The Phase-D authority binding (landed).** `CapMembershipWitness`
   (`sdk/src/full_turn_proof.rs:120,207`): the CONSUMED capability's full 7-field
   leaf, proven member of the holder's pre-state `capability_root`; routing in
   `node/src/turn_proving.rs:429` seeds the EffectVM with the canonical pre-state
   root (`:530`) and rejects a witness whose `cap_root` ≠ canonical (`:475`). The
   former authority-gap blocker doc is retired (`turn_proving.rs:96`).

**The credential-validity leg.** `portalVerify`
(`FullForestAuth.lean:138`) reduces `credentialValid` over a `CryptoKernel`: the
crypto-floor arms (signature/proof/bearer/capTpDelivered/custom/stealth/token)
route through `CryptoKernel.verify`; the Lean arms (breadstuff/unchecked/oneOf)
are pure structural reads. It witnesses *the credential is valid* (sig/HMAC/proof
verifies), distinct from the cap-subset leg.

**Designed-but-unbuilt (Phase E).** `EffectVmEmitCapRoot.lean:89` is explicit: the
per-effect new-root advance is still **pinned-as-digest** in the Lean model; the
in-row sorted-tree-update recompute (membership-open + sorted-key range-checks)
and the Lean soundness lift `checkSubset → satisfiedVm ⇒ granted ⊆ held` are
Phase E, out of scope of the landed work.

---

## 2. The recovered INTENDED design

The designers articulated the integration across several documents; the through-line
is a **division of labor where all four aspects refine ONE worthwhile semantics —
the `granted ⊆ held` narrowing relation** — each proving a different facet.

- **`dregg-auth/README.md`** is the rim statement. It names the two codecs
  deliberately (`README.md:132`): *"The biscuit surface and the credential core
  are two codecs (`eb2_` / `dga1_`). The credential core is the proven one; the
  grant surface remains for the CLI/MCP wedge **until it is re-based on the
  core**."* — i.e. biscuit was always meant to bottom out in the proven caveat
  algebra, not float beside it.
- **`docs/REFINEMENT-DESIGN.md` Decision 6** (the deepest statement, proved in
  `Dregg2/Substrate/VerbCompression.lean`): grant compresses to a guarded write
  *only with an order-relational guard* — *"non-amplification reads a different
  key than it writes and compares values under the rights order… The guard IS the
  guarantee (`grant_non_amplifying`); the real `attenuate` always passes it."* The
  kernel authority **is** the `granted ⊆ held` order-comparison atom. This is the
  semantics the other three aspects are supposed to transport / prove.
- **`docs/REFINEMENT-DESIGN.md` Decision 5** (the #166 SDK design, landed
  `sdk/src/lib.rs:163`): *"You cannot express an unauthorized act.
  `Authorization::Unchecked` leaves the public API… Two user-facing nouns:
  `Receipt` and `AttestedHistory`."* — authorization-inescapable: every public
  turn carries a credential.
- **The dregg4 guarded-comodel/lens** (`project-dregg4-vision.md`): the three
  faces — *EFFECTS ⊕ CAVEATS ⊕ ATTESTATION* — are the get/put/guard of a lens.
  "One object, one soundness theorem." Attestation lives in a **Disclosure ×
  Transferability × Agreement dial-cube**: Disclosure (acceptanceOnly / selective
  / full), Transferability (public ∀V vs designated-verifier deniable,
  `Authority.DV`), Agreement (single-machine ↔ distributed). The *zk honesty
  proof* is one setting of the attestation dial; the *caveat* face is the
  authorization (put-guard) leg.
- **The standing discipline** (`feedback-seams-are-work-not-walls.md`,
  `feedback-dont-launder-vacuity-as-honest.md`): the four aspects must **converge
  to ONE worthwhile semantics, not stay parallel codecs**. A labeled seam is a
  severe problem, not a wall — drive every divergence to one semantics (decide
  which layer holds it, pull the others to it).

**Synthesis — the intended one credential, four facets:**

```
            ┌─────────────────── ONE CREDENTIAL ───────────────────┐
            │                                                        │
  biscuit ──┤  policy face      "what is permitted" (Datalog)        │
            │       │  compiles-to / re-bases-on ↓                   │
  macaroon ─┤  transport face   "how it narrows, hop by hop"         │  all four
            │       │  each hop appends a caveat that ↓              │  refine the
  cap     ──┤  kernel face      granted ⊆ held  (the guard atom)     │  SAME
            │       │  the verb commits against ↓                    │  granted⊆held
  zk      ──┤  honesty face     proves the kernel narrowed,          │  relation
            │                    authenticated cap-root, no-amp        │
            └────────────────────────────────────────────────────────┘
```

biscuit *states* the policy, macaroon *transports* the narrowing on the wire, cap
*enforces* it in kernel state, zk *proves* the enforcement to a light client — all
four are readings of the single relation `granted ⊆ held`.

---

## 3. The integration seams — where it "never worked out" (ranked)

The single executor admission gate is `gateOK`
(`FullForestAuth.lean:490`):

```
gateOK na s = credentialValidG na   -- WHO  (portal: sig/HMAC/proof verifies)
           && capAuthorityG na       -- WHAT (kernel granted ⊆ held)
           && caveatsDischarged na s  -- macaroon chain + tiered caveats
           && revocationGate na s
```

These read **independent `NodeAuth` fields** (`FullForestAuth.lean:272`):
`cred` (WHO), `capMode`+`capCtx` (kernel cap), `caveats`+`chain`+`chainCtx`+
`chainDis` (macaroon). They are AND-ed — fail-closed, defense-in-depth, good — but
**no theorem forces them to describe the same authority.** Verified: there is no
lemma `chainGateG na → capAuthorityG na` anywhere in `metatheory/Dregg2/` (the
only co-occurrence, `GatedForestCfg.lean:827`, is a test config asserting both
legs true independently — not an arrow).

**Ranked by load-bearing-ness (most-load-bearing-unintegrated first):**

1. **macaroon ↔ cap — the central seam.** *(load-bearing: this is the delegation
   path; it is where non-amplification is told twice.)* The macaroon caveat chain
   narrows authority at the agent/federation layer (`HeldToken`'s federation-tree
   leaf, `cipherclerk.rs:469`); the kernel cap narrows at the c-list
   (`recKDelegateAtten`, `granted ⊆ held`). `gateOK` conjoins `chainGateG`
   (`FullForestAuth.lean:452`) and `capAuthorityG` (`:443`) over disjoint fields,
   with **no proven arrow** that the macaroon `Token.admits`/`attenuate_subset`
   narrowing IS the kernel `granted ⊆ held` narrowing. The kernel files
   (`Exec/{AuthTurn,Caps,AuthModes}.lean`) do **not import** `CaveatChain`/
   `MacaroonDischarge` at all. *Refinement of the prior audit:* at the executor
   they are a genuine fail-closed conjunction (a macaroon can never widen past the
   kernel cap), so it is slightly stronger than "two informally-agreeing stories"
   — but the substance holds: two separately-modeled lattices welded by `&&`, not
   one proven arrow.

2. **biscuit ↔ cap — no binding.** *(load-bearing: biscuit is the LIVE token gate
   on every MCP `tools/call`.)* A passing biscuit
   (`verify_token_authorization`, `authorize.rs:1714`) is an **admission gate in
   front of** a call; it does **NOT** install, derive, or reference a kernel
   cap-leaf. The biscuit's `service(cell, verb)` grant and the kernel
   `capability_root` are checked independently; the biscuit never opens against
   the c-list. `Authorization::Token` returns `Ok(())` to admit (`:222`) without
   touching `CapabilitySet`.

3. **biscuit/macaroon ↔ zk — no circuit binding.** *(load-bearing: the turn proof
   is the light-client artifact; if the token decision is off-circuit, a light
   client can't see it.)* Only the **cap** narrowing is witnessed in-circuit
   (`effect_vm_attenuate_non_amp.rs`). The biscuit decision
   (`biscuit_auth::Authorizer::authorize()`) is opaque to the circuit — there is
   no biscuit→FactSet conversion (`factset.rs` handles macaroon caveats only) and
   no biscuit witness in the turn circuit. The macaroon HMAC replay
   (`chainGateG`) is evaluated against wire-supplied `na.chain`, **not** an
   in-circuit constraint. So the zk proof witnesses *the kernel narrowed* but not
   *the macaroon/biscuit narrowed*.

4. **biscuit ↔ macaroon — two codecs, one unrealized re-basing.** They are sibling
   `AuthToken` backends selected by wire prefix (`eb2_`/`em2_`,
   `TokenFormat::detect`, `authorize.rs:1701`), on disjoint evaluators (biscuit:
   `biscuit_auth::Authorizer`; macaroon: in-house `datalog_verify.rs` 18-rule
   engine). The README's intended "biscuit re-based on the proven core"
   (`README.md:135`) is **not built** — biscuit floats beside the caveat algebra.

5. **CapTP `granted ≤ held` — modeled in Lean, NOT in Rust.** *(named, lower rank:
   the Lean models the fix; Rust lags.)* `captp_granted_le_held`
   (`AuthModes.lean:271`) is proved; Rust `verify_captp_delivered` checks sigs +
   masks but not the authority lattice (`AuthModes.lean:20`). A labeled divergence
   between the worthwhile Lean semantics and deployed Rust.

6. **dregg-auth product face unreached.** *(named, low rank: ergonomic, not
   soundness.)* The `Grant`/`OfflineGate`/`ToolGate` surface is not wired into the
   node (`dregg-auth/src/mcp.rs:22` `ToolGate` trait unimplemented node-side); the
   node built a parallel biscuit gate. And the two macaroon implementations
   (HMAC `dregg-macaroon` vs ed25519 `dregg_auth::credential`) are unreconciled —
   the live SDK uses the HMAC one; the Lean-faithful one is the reference.

---

## 4. The integration design — four facets, one proven arrow

The goal: make biscuit / macaroon / cap / zk **FACETS of one proven authority**,
each still doing its job, with the cipherclerk-as-sovereign-executor preserved.
The unifying object is the relation already proven and in-circuit:
`granted ⊆ held` over `ExecAuth = Finset Auth` (`Caps.lean:133`,
`recKDelegateAtten_non_amplifying`, `effect_vm_attenuate_non_amp.rs`).

### 4.1 Target architecture — the "narrowed-authority spine"

Add **one shared quantity** that every aspect emits or consumes: the
*narrowed-authority pair* `(granted, held)` for the verb being authorized, where
`granted, held : ExecAuth` (the kernel rights lattice).

- **cap** already produces it (`recKDelegateAtten`, `capability_root`
  membership). It is the **anchor** — the semantics the others refine to.
- **macaroon**: each caveat that narrows a capability-bearing verb must *project*
  to an `ExecAuth` narrowing. The caveat chain's cumulative meet defines a
  `granted_macaroon ⊆ held_macaroon`; the bridge obligation is
  `granted_macaroon = granted_kernel` (or `⊆`) on the overlap verbs.
- **biscuit**: the Datalog `app(id, actions)` / `service(name, actions)` grant
  *compiles to* the same `ExecAuth` (actions → `Finset Auth`), so a biscuit
  `check if request_app($t), allowed_tool($t)` becomes a `checkSubset` over the
  same lattice. This is the README's "re-base biscuit on the proven core,"
  realized as: biscuit → caveat-algebra → `ExecAuth`.
- **zk**: already witnesses the cap narrowing in-circuit. To bind the others, the
  turn proof additionally witnesses that *the credential's narrowed authority
  (macaroon/biscuit) equals the kernel `granted`* — one extra equality constraint,
  not a new tree.

The four trees do **not** collapse to one tree. They remain four trees (federation
membership / biscuit blocks / kernel c-list / cap-root Merkle), but they are
**joined by one proven relation** at the verb where they overlap.

### 4.2 Precise binding points — what each aspect must emit/consume

| aspect | emits | consumes | binding obligation |
|---|---|---|---|
| **cap** | `(granted, held) : ExecAuth`, `cap_root` membership | the verb's slot | (anchor — already proven `granted⊆held`) |
| **macaroon** | a projection `caveatChainAuthority : Chain → ExecAuth` | the verb's `held` | `chainGateG na → caveatChainAuthority(na.chain) ⊇ granted(na)` (Lean lemma) |
| **biscuit** | `biscuitAuthority : Biscuit → ExecAuth` (actions→Finset Auth) | the request | `verify_offline ⇒ biscuitAuthority ⊇ granted` (Rust + a Lean refinement of the Datalog) |
| **zk** | one equality constraint `granted_witnessed == granted_kernel` | the existing cap-membership witness | extend `CapMembershipWitness` with the credential's narrowed authority leaf |

The single new structural change: `NodeAuth` (`FullForestAuth.lean:272`) gains a
shared field `narrowed : ExecAuth` that BOTH `capAuthorityG` and `chainGateG`
read, replacing the two independent `capMode`/`chain` authority read-outs on the
overlap. `gateOK`'s `&&` then becomes a proven identity on that field.

### 4.3 Staged implementation plan (smallest end-to-end first)

**Stage 0 — the one-lemma bridge (Lean only, no Rust change).** On the
*delegation* verb (where macaroon attenuation and kernel `recKDelegateAtten`
overlap), prove `chainGateG na = true → capAuthorityG na = true` by defining
`caveatChainAuthority` and the projection `granted_macaroon ⊆ granted_kernel`.
This is the smallest step that turns seam #1 from `&&` into a proven arrow. *No
data structure changes; it is a theorem over existing `NodeAuth` fields plus one
projection definition.* **This is the first integration step.**

**Stage 1 — shared `narrowed` field.** Add `NodeAuth.narrowed : ExecAuth`;
have both `capAuthorityG` and `chainGateG` read it; prove `gateOK` unchanged
(keystone-survival via the existing `eraseG` discipline,
`FullForestAuth.lean:34`). SDK: `HeldToken` carries the `ExecAuth` projection of
its caveat chain alongside `caveat_chain_hash` (`cipherclerk.rs:428`).

**Stage 2 — biscuit re-basing.** Define `biscuitAuthority : Biscuit → ExecAuth`
(actions string → `Finset Auth`); route `verify_token_authorization`'s biscuit arm
(`authorize.rs:1714`) to emit the same `granted` the cap leg consumes; prove the
Datalog `check if request_app, allowed_tool` refines `checkSubset`. Realizes
README's "re-base biscuit on the core."

**Stage 3 — zk binding.** Extend `CapMembershipWitness`
(`full_turn_proof.rs:120`) with the credential's narrowed-authority leaf; add the
one in-circuit equality `granted_witnessed == granted_kernel`. Now the turn proof
witnesses that the macaroon/biscuit narrowing equals the kernel narrowing — all
four bind on one real path.

**Stage 4 — close the named lags.** Rust `verify_captp_delivered` re-checks
`granted ≤ held` (lift `captp_granted_le_held` to Rust); Phase E (the in-row
sorted-tree recompute + `checkSubset → satisfiedVm` Lean lift,
`EffectVmEmitCapRoot.lean:89`); reconcile the two macaroon implementations (route
the live SDK onto the Lean-faithful `dregg_auth::credential`, or prove the HMAC
crate refines it).

**The cipherclerk stays a sovereign executor throughout.** Nothing here splits the
clerk or removes its dual role. The integration *adds* a shared `narrowed`
projection the clerk emits when it mints/attenuates/delegates; the clerk remains
the credential-holder-IS-sovereign-executor by design.

---

## 5. The ember-decisions the integration needs

1. **Which `granted_macaroon` ↔ `granted_kernel` relation:** equality (the
   macaroon narrowing *is* the kernel narrowing) or refinement `⊆` (the macaroon
   may narrow strictly further)? Equality is the strongest "one authority" claim;
   `⊆` keeps the agent layer free to over-narrow. *Recommend `⊆` with equality on
   the delegation verb.*
2. **Which macaroon implementation is canonical** — the live HMAC `dregg-macaroon`
   or the Lean-faithful ed25519 `dregg_auth::credential`? The integration is
   cleaner if the SDK routes onto the proven core; that is a larger SDK change.
3. **Does biscuit re-base, or stay a separate-but-bound codec?** README intends
   re-basing; a lighter option is to keep biscuit's Datalog but prove its decision
   refines `checkSubset` (Stage 2 as a refinement, not a rewrite).
4. **Phase E priority** — is the in-circuit `checkSubset → satisfiedVm` lift
   (`EffectVmEmitCapRoot.lean:89`) on the critical path for this integration, or
   does Stage 3's equality constraint suffice for "all four bind on one path"?
5. **CapTP Rust lag (#)** — lift `granted ≤ held` into Rust
   `verify_captp_delivered` now (closing seam #5), or defer behind the shared
   `narrowed` field (which would subsume it)?

---

## 6. Verification notes

- Structural claims (§1–§3) are read directly from the cited files at the line
  numbers given. The `gateOK` four-leg conjunction over independent `NodeAuth`
  fields (`FullForestAuth.lean:272,490`) and the absence of any
  `chainGateG → capAuthorityG` arrow were confirmed by reading the file and by
  a tree-wide grep (only `GatedForestCfg.lean:827`, a test config, co-mentions
  both, and not as an implication).
- The cap-reshape memory (`project-cap-reshape-plan.md`) lists Phase D as
  "remaining"; the code shows **Phase D landed** (`CapMembershipWitness`,
  `node/src/turn_proving.rs:96` retiring the blocker doc). The genuinely-open
  in-circuit work is **Phase E** (`EffectVmEmitCapRoot.lean:89`).
- `cargo check -p dregg-auth` was started as light verification; it triggers a
  dependency rebuild and auto-backgrounds in this sandbox — not blocked on for
  this study. The `dregg-auth` crate's structure and the `dregg_auth::credential`
  module were read directly.
```
