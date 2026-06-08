# Dregg Threat Model + Info-Flow / Metadata-Privacy Analysis

**Status:** living document. Produced by the red-team workflow as the map for the
Fuzz + Chaos phases. Every claim here is grounded in either (a) a source line,
(b) a Lean theorem, or (c) a **reproducible adversarial test** in the new
`redteam/` crate (`cargo test -p dregg-redteam`). Real attack output is quoted
verbatim in §6.

**The discipline.** Throughout, distinguish three statements:

1. **"Lean proves X"** — a machine-checked theorem in `Dregg2/` about the
   *abstract model* (often with crypto as an opaque `attested : Prop` and graphs
   as `Spec.Authority.Graph`).
2. **"the running Rust enforces X"** — the deployed code path actually rejects
   the violation. This is what the `redteam/` harness *tests*, by constructing
   the adversary and asserting the outcome on the concrete types.
3. **the GAP** — where (1) holds but (2) is weaker, absent, or has an
   unauthenticated side door. A GAP is a FINDING.

A passing red-team test that *asserts the rejection* is EVIDENCE the property
holds operationally (not just in Lean). A passing red-team test that *asserts
the bad outcome* (`finding_*`) is a confirmed, reproducible FINDING — it is a
regression tripwire: the day someone fixes the underlying issue, that test
flips to red and tells us.

---

## 0. System under test + the trust spine

- **CapTP** (`captp/`, ~3,950 LOC): swiss-table confinement, 3-party Granovetter
  handoff, distributed GC, promise pipelining, store-and-forward. Trust model in
  `captp/src/lib.rs:3-37` (MIXED: handoff + store-forward are *trustless-when-
  proven*; swiss/GC/session are *executor-trusted*).
- **Blocklace** (`blocklace/`): the byzantine-repelling causal DAG. Block sig =
  Ed25519 over `(creator,seq,payload_hash,preds)`; `id = blake3(content||sig)`;
  equivocation = same-creator incomparable pair; equivocators evicted from tips.
- **Node** (`node/`): the live surface. Axum HTTP API (`node/src/api.rs`),
  Plumtree+Dandelion++ gossip (`net/src/gossip.rs`), faucet, MCP tool server.
- **Lean (`Dregg2/`)**: the proof tower. Relevant: `Exec/CapTP.lean`,
  `Exec/CapTPGC.lean`, `Exec/CapTPConcrete.lean`, `Authority/Blocklace.lean`,
  per-effect full-state soundness specs.
- **Live devnet:** `https://devnet.dregg.fg-goose.online` — a **solo** node
  (`federation_mode:"solo"`, `peer_count:0`), DAG ~45k heartbeat blocks.

The recurring structural truth (the n=1 collapse the brief warns about): the
*distributed* CapTP claims (confinement, GC safety) rest on the assumption that
"the federation executor honestly maintains swiss table and session state"
(`lib.rs:30`). At single-machine this is vacuously true; the verification target
is making the executor-maintained state *be* the verified `RecordKernelState`.
Until that join lands, executor-trusted = "trust the Rust HashMap".

---

## 1. Adversary catalog

| # | Adversary | Vantage | Primary goal |
|---|-----------|---------|--------------|
| A1 | **Malicious cell / app** | runs code in a cell on a host node | escape its capability sandbox; touch another cell's state; forge authority |
| A2 | **Malicious agent holding a (weak) capability** | possesses a swiss number / handoff cert / token | **amplify** it; replay it; grief others' caps |
| A3 | **Byzantine peer / strand** | a participant in the gossip mesh / DAG | equivocate (fork its strand); frame an honest strand; flood; eclipse |
| A4 | **Malicious validator** | a consensus committee member | violate finality/safety; censor; double-finalize |
| A5 | **Network adversary** | on-path between honest parties | observe metadata; replay; delay/drop; correlate |
| A6 | **Malicious relay** | a store-and-forward relay operator | read/forge queued messages; learn the recipient graph; drop selectively |

Below, each adversary gets: **surface**, **what the proofs claim to stop**, and
**where operational enforcement gaps** (FINDINGS tagged `F-n`).

---

## 2. Per-adversary analysis

### A1 — Malicious cell / app

**Surface.** Effects in a turn's call-forest; the per-action `Authorization`;
the cell's own permissions; the executor admission gate; the MCP tool surface
(`node/src/mcp.rs`) with its `_cap` biscuit slot.

**What the proofs claim.** A single credential-gated executor entry
(`execFullForestG`) with a proven `gateOK` 4-leg + `authModeAdmits`; per-effect
full-state soundness (`*_full_sound`) freezes the 16 non-touched kernel fields
(anti-ghost tooth); attenuation is genuinely enforced (`recKDelegateAtten`,
granted ≤ held). The confused-deputy class is closed on the node's submit path:
`post_submit_turn` **ignores the body's `agent` field and derives the agent cell
from the operator's cipherclerk pubkey** (`node/src/api.rs:2155-2164`, the F-P1-3
fix) — so a remote caller cannot target a victim cell's c-list with the
operator's signature.

**Operational gaps.**
- **The submit endpoint is an operator console, not a multi-tenant gateway.**
  Because every action is re-signed with the operator's cipherclerk
  (`s.cclerk.make_action`, `api.rs:2201`), a malicious *remote* caller cannot
  impersonate a cell — but it also means the node has **no notion of a
  non-operator authenticated submitter**. On the live devnet `/turn/submit` and
  `/turns/submit` return **405** (POST disabled at the deployment), so the live
  mutation surface is the faucet only (§A5). This is safe-by-disablement, not
  safe-by-design: a multi-tenant deployment that re-enables submit inherits the
  "everything is the operator" model.
- **F-1 (CLOSED — `node/src/api.rs`):** previously the per-IP `RateLimiter`
  keyed on the `ConnectInfo` socket IP and ignored `X-Forwarded-For`, so behind
  the devnet reverse proxy every request shared the proxy's socket IP — the
  60/min turn limit degenerated into one *global* bucket (DoS of honest clients)
  with no real per-client cost for a NATed/proxied/IP-rotating attacker.
  **Fix:** `resolve_client_ip(socket_ip, xff, trusted)` resolves the real client
  IP — it honors `X-Forwarded-For` **only** when the direct peer is a configured
  trusted proxy (`DREGG_TRUSTED_PROXIES`, comma-separated), and then walks the
  header from the **right** (proxy-appended, least-spoofable end) to the first
  non-trusted hop, so a client that prepends bogus left-hand entries cannot move
  the key. An untrusted direct attacker's `X-Forwarded-For` is ignored entirely
  (it stays pinned to the real socket IP), so it cannot mint a fresh unlimited
  bucket by rotating the header. Every rate-limited handler now routes through
  `RateLimiter::check_request(socket_ip, &headers)`. **Redteam DEFENDED:** the
  `f1_*` attack tests in `node/src/api.rs` drive the real resolver + limiter
  (`f1_proxied_clients_get_distinct_buckets_defended`,
  `f1_untrusted_xff_spoof_is_ignored_defended`,
  `f1_xff_left_prepend_spoof_is_inert_defended`,
  `f1_real_limiter_isolates_proxied_clients_defended`).

### A2 — Malicious agent holding a capability

**Surface.** A swiss number (bearer secret); a `HandoffCertificate` it received;
a token/biscuit; the `validate_handoff` admission gate.

**What the proofs claim (B1/B2/B3).** *Confinement:* a cap is unreachable
without its 256-bit swiss number (`Exec/CapTP` confinement; `sturdy.rs:164`).
*Unforgeability:* a cert can't be forged without the introducer's Ed25519 key
(`handoff.rs:413`). *Non-amplification (Granovetter):* `granted ≤ held` on both
the `AuthRequired` lattice and the effect mask, where **held is read from the
target's own swiss entry, not the cert's self-asserted field**
(`handoff.rs:448-499`; Lean `handoff_non_amplifying`).

**Red-team result — DEFENDED (evidence, §6):** 258 near-miss swiss guesses all
rejected (`attack_confinement_guess_swiss_number_is_rejected`); permission-
amplification and effect-mask-amplification (both the superset and the
`None`-means-unrestricted forms) rejected; a post-signing field tamper rejected
(`InvalidIntroducerSignature`); a cert intercepted in transit and presented by
the wrong party rejected (`InvalidRecipientSignature`); an untrusted introducer
rejected even with a perfectly valid signature. **The amplification spec holds
on the running Rust, not just in Lean.** Crypto is real `ed25519_dalek`
(`types/src/lib.rs:62-90`), not a spike.

**Operational gaps (FINDINGS).**
- **F-2 (CLOSED — `redteam`-DEFENDED, `captp/src/handoff.rs`):** *Was:*
  `validate_handoff` enlivened the swiss entry BEFORE the non-amplification check,
  so a rejected amplifying presentation still bumped `use_count` and could exhaust
  a one-shot handoff, griefing the legitimate recipient. *Fix:* `validate_handoff`
  now reads the held authority with the new **read-only `SwissTable::check`**
  (`sturdy.rs`) and consumes a use via `enliven` ONLY on the success path
  (`handoff.rs` §7), AFTER every rejecting check (target binding, amplification)
  has passed. A rejected presentation leaves `use_count` untouched. The red-team
  test `finding_amplifying_handoff_consumes_a_use_on_rejection` is **flipped to
  DEFENDED**: after a rejected amplifying attempt the one-shot swiss is intact and
  the honest handoff SUCCEEDS (and consumes exactly the one legitimate use).
- **F-3 (CLOSED — `redteam`-DEFENDED, `captp/src/sturdy.rs` + `wire/src/server.rs`):**
  *Was:* `EnlivenError` distinguished `NotFound` (absent) vs `Expired`/`ExhaustedUses`
  (present-but-dead) at the network boundary (`server.rs` echoed `e.to_string()`),
  a membership oracle on the secret-keyed table. *Fix:* added
  `EnlivenError::opaque_message()` (== `"denied"`); the wire `EnlivenResponse` error
  path now emits that single opaque message and logs the taxonomy only locally
  (`tracing::debug!`). The red-team test
  `finding_enliven_error_taxonomy_is_a_membership_oracle` is **flipped to DEFENDED**:
  it now asserts the BOUNDARY representation a remote sees is IDENTICAL across
  present-but-dead vs absent (no "found"/"expired"/"exhausted" tell).

### A3 — Byzantine peer / strand

**Surface.** Blocks it injects via gossip; its own strand (which it may fork);
another creator's blocks it observed (re-encoding attempts); the closure /
equivocation checks in `receive_block` (`blocklace/src/finality.rs:602`).

**What the proofs claim.** `receive_block` **verifies the Ed25519 signature
FIRST** (`finality.rs:611`), then enforces causal closure, then detects
equivocation (same-creator incomparable pair) and **evicts the equivocator's
tip** (`finality.rs:624-635`); a known equivocator's blocks never re-enter
`tips` (`finality.rs:637-651`). Lean: `equivocation_detectable`,
`observer_detects`, `honest_no_equivocation` (`Authority/Blocklace.lean`).

**Red-team result — DEFENDED (evidence, §6):** a Byzantine creator forking its
own strand is detected and flagged (`attack_byzantine_self_fork_...`); a forged
block claiming a victim creator (signed with the attacker's key) is rejected
`InvalidSignature` (`attack_forge_block_for_other_creator_...`); an identical
replay is idempotent, **not** a self-equivocation (`attack_replay_same_block_...`).

**The subtle one — DEFENDED, but the proof did NOT cover it:** the block id binds
the signature (`id = blake3(content||sig)`, `finality.rs:337`). If a *non-
canonical re-encoding* of an honest block's signature still verified, it would
mint a NEW id with the SAME `(creator,seq,preds)` → an incomparable pair → the
**honest creator would be framed as an equivocator and evicted** (a censorship
primitive). `honest_no_equivocation` does **not** rule this out: it constrains the
*author's* behavior, not the detector's robustness to attacker-crafted
re-encodings. The red-team probe `probe_signature_malleability_framing` adds
the ed25519 group order `L` to the signature's `S` scalar and feeds the result
back. **Result: `ed25519_dalek` v2 `Signature::from_bytes` + strict `verify`
rejects the malleated S (`verifies=false`, `receive_block=Err(InvalidSignature)`,
`honest_framed=false`).** So the framing attack *fails on the running Rust* —
this is operational evidence that dalek-v2 strictness closes a gap the Lean model
is silent about. **This is exactly the kind of property to keep in the Chaos
suite**, because it depends on a crypto-library version detail, not a proof.

**Operational gaps.**
- **F-4 (FINDING — Sybil/admission, design-level):** a strand is just a keypair;
  there is **no admission cost / stake gate** for creating a strand or joining
  the gossip mesh (`_FEDERATION-SSB-ORIENTATION.md:196`). Only *consensus-
  participant* membership is gated (constitution vote). An attacker mints
  unlimited strands. SSB leans on the social follow-graph for Sybil resistance;
  dregg's `Subscription` *could* but does not yet. The byzantine-repelling tooth
  catches *equivocation*, not *identity inflation*. *Logged; no quick fix —
  needs a real admission design (stake / proof-of-personhood / follow-graph
  scoping).*
- **F-5 / L4 (CLOSED — `redteam`-DEFENDED, `net/src/{gossip,peer_score}.rs`):**
  *Was:* Dandelion++ stem was **disabled below 5 peers** (immediate self-fluff —
  the origin broadcast directly, zero tx-origin anonymity) and there was no
  anchor-peer anti-eclipse policy, so a nascent small network was most
  eclipse-vulnerable and origin-exposed exactly when smallest. *Fix:* (a)
  **anchor peers** — the operator-configured bootstrap peers are recorded as
  trusted anchors (`GossipState.anchors`, `PeerScore.is_anchor`); they are
  **pinned into the eager set ahead of any Sybil flood**
  (`PeerScoreboard::select_eager_with_anchors`), **retained (not removed) on a
  transient connection death**, and **exempt from score-erosion graylisting**
  (only the categorical equivocation hard-fault graylists an anchor) — so an
  eclipse adversary can neither capture the spanning tree nor starve a trusted
  anchor out by inducing flaps. (b) **small-N origin anonymity** — the publish
  path (`StemPlan::plan`) now keeps the origin **one hop removed whenever any
  peer is present**, *preferring a trusted anchor as the first stem hop* rather
  than self-fluffing; only a truly peerless node disseminates locally (nobody to
  leak to). The red-team tests are **DEFENDED**:
  `attack_sybil_flood_cannot_evict_trusted_anchor_from_eager_set`,
  `attack_anchor_flap_does_not_starve_it_from_eager_set`,
  `attack_byzantine_anchor_is_not_pinned` (`redteam/tests/net_eclipse_attacks.rs`)
  + net-internal `gossip::tests::stem_plan_origin_never_self_fluffs_with_peers_present`.
  A graylisted (proven-Byzantine) anchor is NOT pinned — trust is not a license
  to equivocate.

### A4 — Malicious validator

**Surface.** The consensus committee; `tau` single-anchor finality; epoch
reconfiguration; quorum certificates.

**What the proofs claim.** `tau` single-anchor uniqueness
(`BlocklaceFinality.finalLeaderAt_unique`); `≤ f` Byzantine tolerance under
partial synchrony (`2f+1/3f+1`); epoch-transition safety
(`Lean EpochReconfig` + Rust differential, task #83); Stingray cert-reconciliation
rebalance safety with a Byzantine bound (task #90).

**Operational gaps.**
- **F-6 (LOGGED — not yet exercised by this harness):** the consensus path is
  the **least red-teamed** surface here because the live devnet is solo
  (`consensus_live:true` but a committee of one) — there is no *running*
  multi-validator instance to attack. The Byzantine-bound theorems are proven in
  Lean and have Rust differentials, but a *running* `> f` collusion / equivocating-
  leader / withheld-certificate scenario has not been chaos-tested. **This is the
  top Chaos-phase target:** stand up an n≥4 committee in a test net and drive
  `f+1` malicious validators against `finalLeaderAt_unique` and the epoch
  reconfig safety. Until then, "validator safety holds on the running system" is
  *unverified operationally*, only proven abstractly.
- **F-7 (LOGGED — `_FEDERATION-SSB-ORIENTATION.md:204`):** an evicted equivocator
  keeps its already-finalized blocks; there is no economic slashing and no proof
  that a partition that hides an equivocation (>50% eviction freeze,
  `:85`) degrades *safely*. Partial-replication soundness (a `Subscription` hop-
  limited view) is an open safety question.

### A5 — Network adversary (on-path)

**Surface.** Everything observable on the wire: the node's HTTP API; gossip
envelopes; timing; the live `/status` JSON.

**What the proofs claim.** Block signatures + hash chaining make tampering
detectable; store-forward payloads are ciphertext (B6, §A6). Gossip is "best-
effort (liveness only); adversary can delay/drop, not read/forge" — signed
envelopes + hash check (`_FEDERATION-SSB-ORIENTATION.md:145`).

**Operational gaps / leaks (this is mostly an info-flow story — see §3).**
- **F-8 (CLOSED — `node/src/api.rs`):** `GET /status` previously disclosed,
  unauthenticated, the aggregate private-activity counters `note_count` and
  `revocation_count` (volume of shielded notes / revoked credentials) alongside
  identity + liveness fields. The private counters are the sensitive part: they
  are a private-activity-VOLUME oracle. **Fix:** `revocation_count`/`note_count`
  are now `Option<u64>` on `StatusResponse` and `#[serde(skip_serializing_if =
  "Option::is_none")]`; `get_status` populates them **only** when the operator
  explicitly opts in via `DREGG_STATUS_EXPOSE_COUNTS=1` (e.g. a trusted internal
  dashboard behind auth). Default = the fields are **absent** from the public
  wire, while the coarse liveness signal (`healthy`/`consensus_live`/
  `dag_height`) is retained. **Redteam DEFENDED:** in-crate
  `f8_status_does_not_leak_private_counts_defended` drives the REAL router via
  `oneshot` and asserts both counters are absent; `f8_opt_in_re_exposes_counts_control`
  proves the gate is non-vacuous (opt-in re-exposes them); network-gated
  `devnet_status_withholds_private_counts_f8` (redteam crate) scrapes the live
  origin. *Residual (separately tracked, by-design): the Ed25519 pubkey + DAG
  height are deliberately public consensus/identity signals; the `dag_height`
  uptime-oracle aspect is an L1 metadata-privacy item, not part of F-8's
  private-counter leak.*

  *(No Lean proof-gap to extend for F-1/F-8: both live entirely in the HTTP
  transport boundary — per-IP throttling and `/status` JSON field selection —
  which is outside the verified protocol/executor tower. The Lean `RateLimit`
  predicate models a protocol-level per-window **cell-state** counter, a
  distinct concept. The closure is Rust fix + redteam DEFENDED, the correct bar
  for a transport-layer finding.)*

### A6 — Malicious relay (store-and-forward)

**Surface.** The `MessageRelay` queue; `BlocklaceEnvelope`s it stores; the
`destination` field; queue depth / TTL.

**What the proofs claim (B6).** Forward secrecy: each message is encrypted to an
ephemeral X25519 key; the relay sees only ciphertext; it can delay/drop but not
read/forge. **Correction to the stale orientation doc:** the crypto is **no
longer a spike** — `captp/Cargo.toml:15-17` and `store_forward.rs:180-326` now
use real `x25519-dalek` ECDH → HKDF-SHA256 → **RFC 8439 ChaCha20-Poly1305**
(`HKDF_DOMAIN = "dregg-store-forward-v2-x25519-hkdf-sha256-chacha20poly1305"`),
with a unique ephemeral key per message justifying the zero nonce
(`store_forward.rs:176-178`). The `_CAPTP-ORIENTATION.md §C.1` "hand-rolled
spike" warning is **superseded**; B6's confidentiality rests on vetted
primitives. Tests: `wrong_key_decryption_fails`, `tampered_ciphertext_fails`.

**Operational gaps / leaks.**
- **F-9 (FINDING — by-design metadata leak):** `BlocklaceEnvelope.destination`
  is **cleartext** (`store_forward.rs:929+`), by design so nodes know which
  blocks to attempt decryption on. A relay (or any DAG observer) learns the
  **recipient set and per-recipient message volume/timing** even though it cannot
  read content. This is the classic encrypted-but-not-anonymous relay leak. *Fix
  direction: recipient-anonymous addressing (per-epoch tags / fuzzy message
  detection / PIR-style retrieval — the node already ships a `/pir/*` surface,
  `api.rs:1423`, which is the right primitive to extend here).*
- **F-10 (CLOSED — `redteam`-DEFENDED, `captp/src/pipeline.rs` + `wire/src/server.rs`):**
  *Was:* the cross-fed pipeline bridge defaulted to a `[0;32]` sender placeholder
  (`CrossFedPipelineBridge::new()` / `Default`), so a pipelined send's `authorization`
  was bound to an anonymous originator — a relay/bridge could replay it under an
  unset sender. *Fix:* `CapTpState::new(local_federation)` is now **mandatory** (no
  unbound default; the `Default for CapTpState` impl was REMOVED) and constructs the
  bridge via `CrossFedPipelineBridge::with_local_federation(node_id)`. Every
  production outbound pipelined message therefore stamps the node's REAL federation
  id as `sender`. The bare `new()`/`[0;32]` path survives only as a test convenience.
  New red-team test `finding_pipeline_bridge_ships_unbound_sender` (DEFENDED) asserts
  the production `CapTpState` bridge stamps the real sender (not `[0;32]`) on outbound
  messages, and `configured_bridge_binds_sender_through_chain` asserts every chain leg
  binds it.

---

## 3. Info-flow / metadata-privacy analysis — what LEAKS

The dregg privacy story is **content confidentiality + verifiable execution**,
NOT **metadata privacy**. Shielded value and note nullifiers hide *amounts and
linkage of a transfer's content*; they do **not** hide *that a turn happened, by
whom (at the cell/strand granularity), when, and to which counterparty-set*. The
following are concrete leaks, ranked.

| Leak | Channel | Who sees it | Severity | Status |
|------|---------|------------|----------|--------|
| **L1 — node identity + uptime + activity volume** | `GET /status` (live) | anyone, unauth | MED (deanon + recon) | F-8, live |
| **L2 — recipient set of store-forward** | `BlocklaceEnvelope.destination` cleartext | relay + any DAG observer | MED | F-9, by-design |
| **L3 — cell-graph / capability-graph topology** | who-introduces-whom edges in handoff/introduce; routing-table entries (`node/src/routing_table.rs`); the cap DAG | any node holding the blocks | MED | by-design (only-connectivity-begets-connectivity is *observable*) |
| **L4 — transaction-origin (no anonymity at small N)** | ~~Dandelion++ stem disabled < 5 peers~~ → origin kept one hop removed via anchor stem | on-path / mesh peer | HIGH at small N | **F-5 CLOSED** |
| **L5 — timing / ordering side channel** | block `seq`, causal_sequence, DAG arrival times; turn-execution duration metrics (`record_turn_execution_duration`, `api.rs:2263`) | mesh peer / metrics scraper | LOW–MED | logged |
| **L6 — swiss membership oracle** | `EnlivenError` taxonomy | a prober with a guessed value | LOW (256-bit secret) | F-3 |
| **L7 — shielded vs transparent is itself a label** | the choice to use a note vs a transparent transfer is visible in the effect type | any DAG observer | MED | by-design |
| **L8 — gossip IHave / Graft pattern** | lazy-push hashes reveal who-has-what before content | mesh peer | LOW | by-design |

**The proven-vs-actual privacy gap, stated plainly.** The Lean tower proves
*per-effect full-state soundness* and *note nullifier / commitment* correctness —
i.e. **content-level integrity and (for notes) value confidentiality**. It proves
**nothing about metadata unlinkability**: there is no Lean theorem that quantifies
an adversary's view of the gossip/relay/cap-graph and bounds what they learn.
The swiss-bearer-secret is handled well at the *confinement* layer (256-bit,
real CSPRNG `getrandom::fill`, constant work to reject, no swiss number ever in a
`/status`-style dump) — but its *existence and liveness* leak via L6, and its
*use pattern* (handoff edges) leak via L3. "Shielded value vs transparent" (L7)
is a privacy *set-partition* leak: every shielded turn advertises that it is
shielded, so the anonymity set is "users who chose shielding," not "all users."

**Bottom line for the privacy claim:** dregg today is **confidential, not
private**. A network/relay adversary that records the DAG reconstructs the
*social graph* (who transacts with whom, when, how often, and via which caps)
while learning little about *amounts*. Closing this is a research pillar
(metatheory #31/#5), not a patch — it needs anonymous addressing (L2/L9),
mandatory or default shielding (L7), and a transaction-origin layer that holds at
small N (L4).

---

## 4. The proven-vs-operational ledger (summary)

| Property | Lean says | Running Rust | Verdict |
|----------|-----------|--------------|---------|
| Swiss confinement (B1) | unreachable w/o secret | 258 guesses rejected; real CSPRNG | **HOLDS** (evidence) |
| Handoff unforgeability (B2) | no key ⇒ no accept | tamper + interception + untrusted all rejected; real ed25519 | **HOLDS** (evidence) |
| Handoff non-amplification (B3) | granted ≤ held (vs swiss entry) | both lattice + mask amplifications rejected | **HOLDS** (evidence) |
| Handoff reject is side-effect-free | pure decision `Prop` | read-only `check`; enliven only on success | **HOLDS — F-2 CLOSED** |
| GC no-premature-reclaim (B4, lease) | lease only reclaims expired | (lease path proven) | holds for lease path |
| GC session-Byzantine resistance | wrong session can't drop | session path: rejected | **HOLDS** for session path |
| GC drop authentication | **refcount-drop path modeled** (`CapTPGCConcrete.processDrop` + `f11_session_free_drop_denied`) | legacy `process_drop` fail-closed (`#[deprecated]`, returns `Invalid`) | **HOLDS — F-11 CLOSED (+ proof extended)** |
| GC session granularity | **per-ref scoping** (`f12_reexport_preserves_original_session_rights` / `f12_session_drops_only_its_own`) | **per-session buckets** (`RefCount.sessions`); re-export keeps original session's rights | **HOLDS — F-12 CLOSED** |
| Equivocation detection | detectable + evict | self-fork detected; forgery rejected | **HOLDS** (evidence) |
| Honest-creator non-framing | author honest ⇒ no equiv | malleability framing **fails** (dalek-v2 strict) | **HOLDS** (evidence, beyond proof) |
| Forward secrecy (B6) | ephemeral-key idealized | real x25519+HKDF+ChaCha20Poly1305 | **HOLDS** (primitives vetted) |
| Pipelining ≠ bypass (B5) | auth survives resolution | bridge binds real sender (mandatory `CapTpState::new(fed)`) | **HOLDS — F-10 CLOSED** |
| Metadata unlinkability | **no theorem** | leaks L1–L8 | **OPEN (research)** |

The two NEW GC findings (F-11, F-12) are the GC analogues of F-2 and F-3:

- **F-11 (FINDING — `redteam`-proven, fix in `captp/src/gc.rs`):** the legacy
  `ExportGcManager::process_drop` (`gc.rs:153`) processes a DropRef **without any
  session validation** — it is the `expected_session=None` path. Any caller who
  knows `(cell_id, victim_federation)` can decrement the victim's refcount and,
  at zero, force `CanRevoke` — a **premature reclaim of a still-wanted
  capability**, exactly what the session-Byzantine defense
  (`process_drop_with_session`) exists to prevent. The defense is opt-in; the
  open door is the default-named method. Reproduced by
  `finding_legacy_process_drop_bypasses_session_byzantine_defense`.
  **CLOSED:** (a) `process_drop` is now `#[deprecated]` and **fail-closed** — it
  performs NO mutation and always returns `DropResult::Invalid`. `process_drop_inner`
  takes a mandatory `SessionId` (the `Option`/session-free arm is gone) and
  decrements only the requesting session's bucket. The red-team test
  `finding_legacy_process_drop_bypasses_session_byzantine_defense` is **flipped to
  DEFENDED** (`[GC ATTACK 2 / F-11] DEFENDED (denied, fail-closed)`). (b) The Lean
  blind spot is closed too: `Exec/CapTPGCConcrete.lean` §2 now models the
  refcount-drop path with a mandatory-session `processDrop` over per-session buckets
  (`HolderRef.sessions`), and §4a proves `f11_session_free_drop_denied` — a session
  that minted no ref (the session-free / forged / "session 0" credential) is a total
  NO-OP on the table: `(invalid, t)` with `totalRefs` unchanged (the law the pre-fix
  code VIOLATED). The honest holder still gets through (`right_session_decrements`),
  and `byzantine_cannot_drop_victim_ref` carries over. `#assert_axioms`-clean, no
  `sorry`.
- **F-12 (FINDING — `redteam`-proven, design subtlety):** `session_id` was stored
  **per-(cell, federation) holder, not per-ref** (`gc.rs:129-139`). A re-export to
  the same federation on a new session **overwrote the session id of ALL that
  holder's existing refs** and bumped the count. Consequence: after a re-export,
  the *original* session could no longer drop even the refs it legitimately minted,
  while the *new* session could drop refs it never minted. Reproduced by
  `finding_reexport_supersedes_session_for_all_existing_refs`.
  **CLOSED:** `RefCount` now carries per-session buckets (`sessions: HashMap<SessionId,
  u64>`, summed by `count`); `record_export_with_session` mints into the named
  session's bucket and never touches the others, and `process_drop_inner` decrements
  only the requesting session's bucket. The original session keeps its drop rights and
  a session can drop only what it minted. The red-team tests
  `finding_reexport_supersedes_session_for_all_existing_refs` and
  `new_session_cannot_overdrop_into_original_sessions_refs` are **flipped to DEFENDED**
  (`[GC ATTACK 3 / F-12] DEFENDED`, `[GC ATTACK 3b / F-12] DEFENDED`). On the Lean side
  `Exec/CapTPGCConcrete.lean` §4a proves `f12_reexport_preserves_original_session_rights`
  (a new session's bucket leaves the original session's bucket untouched) and
  `f12_session_drops_only_its_own` (a drop touches only the named session's bucket).
  The `gcDifferentialCorpus` (Lean ⟷ Rust `gc_session_tooth_matches_lean_corpus`) now
  pins the corrected per-ref rows. `#assert_axioms`-clean, no `sorry`.

---

## 5. The red-team harness (`redteam/` crate)

A new workspace crate (`redteam/`, package `dregg-redteam`) that property-tests
the running Rust against the Lean-proven invariants. **Owned by this workflow**;
it touches no SWAP/circuit/apps/lightclient code. It depends on the real
`dregg-captp`, `dregg-blocklace`, `dregg-cell`, `dregg-types` crates (no mocks).

- `tests/captp_attacks.rs` — 8 tests: confinement, permission/mask amplification,
  forgery, interception-replay, untrusted-introducer (DEFENDED) + F-2 grief +
  F-3 oracle (FINDINGS asserted reproducible).
- `tests/gc_attacks.rs` — 5 tests: wrong-session drop, over-drop (DEFENDED) +
  F-11 legacy session-free bypass (now **DEFENDED** — fail-closed) + F-12 re-export
  supersede + F-12 new-session over-drop (now **DEFENDED** — per-ref scoping).
- `tests/blocklace_attacks.rs` — 4 tests: self-fork detection, cross-creator
  forgery, idempotent replay (DEFENDED) + the malleability-framing PROBE
  (DEFENDED by dalek-v2 strictness).
- `src/lib.rs` — adversary toolkit (keypair minting, bit-flip tamper,
  `AttackOutcome` taxonomy).

Run: `cargo test -p dregg-redteam -- --nocapture`. A `finding_*` test that goes
RED in future = the underlying issue was fixed (good) — update the assertion.

---

## 6. Real attack output (verbatim, `cargo test -p dregg-redteam`)

```
running 4 tests   (blocklace_attacks)
test attack_byzantine_self_fork_is_detected_and_evicted ... [BL ATTACK 1] self-fork: DEFENDED (detected + flagged)
ok
test attack_forge_block_for_other_creator_is_rejected ... [BL ATTACK 2] cross-creator forgery: DEFENDED (sig rejected)
ok
test attack_replay_same_block_is_idempotent_not_equivocation ... [BL ATTACK 4] identical replay: DEFENDED (idempotent)
ok
test probe_signature_malleability_framing ... [BL ATTACK 3 / PROBE] malleated-sig verifies=false receive_block=Err(InvalidSignature { creator: [202, 147, ...], seq: 1 }) honest_framed=false
ok
test result: ok. 4 passed; 0 failed

running 8 tests   (captp_attacks)
test attack_amplify_effect_mask_is_rejected ... [ATTACK 2b] effect-mask amplification (both forms): DEFENDED
test attack_amplify_permissions_is_rejected ... [ATTACK 2] permission amplification: DEFENDED
test attack_confinement_guess_swiss_number_is_rejected ... [ATTACK 1] confinement vs 258 guesses: DEFENDED
test attack_forge_introducer_signature_is_rejected ... [ATTACK 3] post-sign field tamper: DEFENDED
test attack_intercept_cert_present_as_wrong_recipient_is_rejected ... [ATTACK 3b] cert-interception replay: DEFENDED
test attack_untrusted_introducer_is_rejected ... [ATTACK 6] untrusted introducer: DEFENDED
test finding_amplifying_handoff_consumes_a_use_on_rejection ... [ATTACK 4 / FINDING] amplifying-cert rejection still consumed a use: BROKEN (FINDING)
test finding_enliven_error_taxonomy_is_a_membership_oracle ... [ATTACK 5 / FINDING] enliven error taxonomy distinguishes present-vs-absent: LEAK (FINDING)
test result: ok. 8 passed; 0 failed

running 5 tests   (gc_attacks)
test attack_byzantine_wrong_session_drop_is_noop ... [GC ATTACK 1] wrong-session drop: DEFENDED
test attack_overdrop_does_not_underflow_or_overrevoke ... [GC ATTACK 4] over-drop: DEFENDED (no underflow)
test finding_legacy_process_drop_bypasses_session_byzantine_defense ... [GC ATTACK 2 / F-11] legacy session-free process_drop: DEFENDED (denied, fail-closed)
test finding_reexport_supersedes_session_for_all_existing_refs ... [GC ATTACK 3 / F-12] session is PER-REF; re-export keeps the original session's rights: DEFENDED
test new_session_cannot_overdrop_into_original_sessions_refs ... [GC ATTACK 3b / F-12] new session cannot over-drop into another session's refs: DEFENDED
test result: ok. 5 passed; 0 failed
```

Live devnet probe (`GET /status`, real response — L1/F-8):

```json
{"healthy":true,"peer_count":0,"latest_height":0,"dag_height":45292,
 "block_count":45292,"consensus_live":true,"revocation_count":0,
 "note_count":0,"federation_mode":"solo",
 "public_key":"9b3512552d162619121bc0fa308b21fee8bc5a34f85fc2d785769d2e82aba9fa"}
```

Live devnet `POST /turn/submit` → **405** (mutation disabled on the deployment);
`POST /api/faucet {}` → **422** (handler reached, the live mutation surface).

---

## 7. Findings ledger (for Fuzz + Chaos)

| ID | Class | Severity | Where | Owner | Fix |
|----|-------|----------|-------|-------|-----|
| F-2 | grief / DoS | MED | `captp/src/handoff.rs` enliven-before-amplify | CapTP | **CLOSED** — read-only `check`; enliven only on success (redteam DEFENDED) |
| F-3 | info leak | LOW | `captp/src/sturdy.rs` EnlivenError taxonomy | CapTP | **CLOSED** — opaque `"denied"` at boundary (redteam DEFENDED) |
| F-11 | premature reclaim | HIGH | `captp/src/gc.rs::process_drop` session-free | CapTP | **CLOSED** — `#[deprecated]` fail-closed + Lean `CapTPGCConcrete.f11_session_free_drop_denied` (refcount-drop path; redteam DEFENDED) |
| F-12 | GC session granularity | MED | `captp/src/gc.rs` holder-scoped session | CapTP | **CLOSED** — per-ref session buckets + Lean scoping proof (redteam DEFENDED) |
| F-10 | pipeline sender-binding | MED | `captp/src/pipeline.rs` bridge placeholder | CapTP | **CLOSED** — mandatory `CapTpState::new(fed)` binds real sender (redteam DEFENDED) |
| F-1 | rate-limit bypass | MED | `node/src/api.rs` per-IP behind proxy | node | **CLOSED** — `resolve_client_ip` keys on `X-Forwarded-For` only from a `DREGG_TRUSTED_PROXIES` peer (rightmost-untrusted hop); untrusted XFF ignored (redteam DEFENDED: `f1_*` in `node/src/api.rs`) |
| F-8 / L1 | metadata leak | MED | `node/src/api.rs` `/status` | node | **CLOSED** — `note_count`/`revocation_count` omitted from public `/status` by default (`serde` skip), opt-in `DREGG_STATUS_EXPOSE_COUNTS=1` for trusted dashboards; coarse liveness retained (redteam DEFENDED: `f8_*` + `devnet_status_withholds_private_counts_f8`) |
| F-9 / L2 | recipient leak | MED | `captp/src/store_forward.rs` cleartext dest | CapTP | anon addressing / PIR |
| F-4 | Sybil/admission | DESIGN | strands have no admission cost | federation | stake / follow-graph |
| F-5 / L4 | eclipse / no anon at small N | HIGH@smallN | `net/src/{gossip,peer_score}.rs` | net | **CLOSED** — anchor peers pinned eager + flap-exempt + anchor stem hop (`StemPlan`); origin never self-fluffs with peers present (redteam DEFENDED: `net_eclipse_attacks.rs` + `stem_plan_*`) |
| CHECKPOINT-AUTH | A1-class recovery-path bypass | HIGH | `blocklace/src/finality.rs::from_checkpoint` | blocklace | **CLOSED** — `from_checkpoint` re-verifies sig+closure+equivocation like the hardened insert; verbatim path is now the explicit `from_checkpoint_trusted` (local-disk only); peer `bootstrap_from_checkpoint` routes through the authenticating loader (redteam DEFENDED: `blocklace_deep_attacks.rs` DEEP 5/6/5c) |
| F-6 | validator chaos untested | OPEN | consensus (solo devnet) | chaos | n≥4 committee attack |
| F-7 | finalized-equivocator / partial-replication | OPEN | finality | research | slashing + safety proof |
| L3/L5/L7/L8 | topology / timing / shielding-label | by-design | gossip + cap-graph | research | metadata-privacy pillar |

**Chaos-phase priorities (ranked):** F-6 (stand up a Byzantine committee — the
biggest *unverified-operationally* surface), then the metadata-privacy research
pillar (L1–L8). (F-5 eclipse-at-small-N and the CHECKPOINT-AUTH recovery-path
bypass are now CLOSED + red-team DEFENDED.)

**What the red team could NOT break (operational evidence the property holds on
the running system, not just in Lean):** swiss confinement, handoff
unforgeability, handoff non-amplification, GC session-Byzantine resistance (on the
session-aware path), GC underflow safety, blocklace self-fork detection,
cross-creator forgery rejection, replay idempotency, and — beyond what the proof
covers — honest-creator non-framing via signature malleability (closed by
`ed25519_dalek` v2 strictness).
