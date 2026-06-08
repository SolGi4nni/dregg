# CapTP Orientation — heritage protocol, trust model, and the dregg2 verification targets

**Scope.** The `captp/` crate (~5395 LOC across 8 modules) is dregg's object-capability
transport protocol: the network-layer machinery that moves capabilities between vats/strands
(sturdy refs, 3-party handoff, promise pipelining, distributed GC, store-and-forward). This
doc orients the **CapTP-verification wave**: what the protocol *is* per module, what security
properties it *claims*, where the heritage is honest-but-incomplete, and — the payload —
**what dregg2 (Lean) must model + prove to make CapTP a VERIFIED protocol, not just verified
effect-arms**, ranked by criticality with concrete Lean beachheads wired to the *existing*
verified cap effects.

**One correction to the brief's premise up front.** The brief states Lean has "ZERO model of
the CapTP PROTOCOL machinery." That is no longer true — and the exact shape of what *does*
exist is the key to the verification targets. There are **three** Lean layers already:

1. **Abstract protocol theorems** — `Dregg2/Exec/CapTP.lean` (516 LOC) + `Dregg2/Exec/CapTPGC.lean`
   (226 LOC). These prove the Granovetter handoff IS an `Introduce`, pipelining preserves the
   authorization seam, the pipeline chain IS a dataflow DAG, and distributed-GC reclaim is
   lease-based (closing the cross-vat-cycle leak honestly). They are **abstract**: crypto is an
   opaque `attested : Prop`, rights are an abstract `[SemilatticeInf Rights]`, the cap graph is
   `Spec.Authority.Graph`.
2. **Abstract→concrete lattice bridge** — `Dregg2/Exec/CapTPConcrete.lean` (372 LOC). Pins the
   concrete `AuthRequired` 6-element attenuation lattice, proves it's a genuine bounded
   meet-semilattice, instantiates `handoff_non_amplifying` at that carrier, and exposes a
   `#guard`-pinned 49-bit decision table with a **live Rust differential**
   (`captp/tests/handoff_lattice_differential.rs`).
3. **Full-state-verified concrete effect instances** on `RecordKernelState` — `swissExportA`,
   `swissEnliven`, `swissDropA` (touch `swiss : List SwissRecord` carrying `refcount`),
   `introduceA`/`dropRefA` (touch `caps : Label → List Cap`). Each has a per-effect full-state
   circuit⟺spec soundness proof (`*_full_sound`) plus an executor⟺spec corner.

So the real gap is **not absence** — it's that **these three layers are not joined into
protocol-level security theorems**. The abstract protocol theorems (layer 1) carry crypto/state
as opaque `Prop`s and abstract graphs; the verified effect specs (layer 3) prove faithful
record transitions but model **no protocol-level adversary** (no forged-cert rejection, no
cross-session GC interference, no confinement-by-secret). The verification wave is precisely the
work of **connecting layer 1's adversary-shaped claims to layer 3's verified state tables**, plus
modeling the facets that have **no Lean counterpart at all** (session epochs, store-forward
forward-secrecy). Distinguish throughout: *"has an effect arm in Lean"* (true for ~all cap
effects) vs *"has the protocol property proved against an adversary"* (≈absent — say so loudly).

---

## A. The CapTP protocol model, per module

### A.1 — `sturdy.rs` + `uri.rs`: the swiss table (bearer-secret confinement)

- **State.** `SwissTable { entries : HashMap<[u8;32], SwissEntry> }` (`sturdy.rs:68`). A
  `SwissEntry` (`sturdy.rs:42`) carries `cell_id`, `permissions : AuthRequired`,
  `allowed_effects : Option<EffectMask>`, `expires_at`, `created_at`, `max_uses`, `use_count`.
- **The swiss number = bearer secret.** A 32-byte random secret (`sturdy.rs:92`,
  `getrandom::fill`). The map key IS the secret: **possession is authorization**. There is no
  separate auth check at the table layer — knowing the swiss number IS the credential
  (`lib.rs:11` "possession IS authorization").
- **Message flow.** `export`/`export_with_options` (`sturdy.rs:85`,`113`) mint an entry and
  return the swiss number; `make_uri` (`sturdy.rs:143`) wraps it in a `dregg://<fed>/<cell>/<swiss>`
  URI (`uri.rs:89` parse, base58 segments, each exactly 32 bytes). `enliven` (`sturdy.rs:159`)
  presents a swiss number → checks `expires_at`/`max_uses`, bumps `use_count`, returns the entry
  (the live ref). `revoke` (`sturdy.rs:188`) removes the entry.
- **Trust assumption.** Executor-trusted (`lib.rs:11`): the federation node must faithfully
  maintain the map. The confinement property (a cap is unreachable without its swiss number) is
  **only as strong as the secrecy of the 32-byte number** + the table's honesty.
- **Confinement property (claimed, not proved).** Without the swiss number, `enliven` returns
  `EnlivenError::NotFound` (`sturdy.rs:164`); the only way in is to *guess* a 256-bit secret. The
  tests cover not-found / expired / exhausted / revoke (`sturdy.rs:238`–`315`) but there is **no
  adversarial unguessability statement** — it's a `HashMap` lookup, secured by entropy.

### A.2 — `handoff.rs`: the 3-party introduction (Granovetter)

This is the richest, most security-load-bearing module. It implements Miller's
*only-connectivity-begets-connectivity* across vats.

- **`HandoffCertificate`** (`handoff.rs:128`): `introducer : FederationId`,
  `introducer_signature : Signature`, `target_federation`, `target_cell : CellId`,
  `recipient_pk : [u8;32]`, `permissions : AuthRequired`, `allowed_effects`, `expires_at`,
  `max_uses`, `nonce : [u8;32]`, `swiss : [u8;32]`.
- **What is signed.** `signing_message` (`handoff.rs:207`) is domain-separated
  (`b"dregg-handoff-cert-v1"`) and covers **every field except the signature**: introducer,
  target_federation, target_cell, recipient_pk, a permissions tag byte (+ the 32-byte vk_hash
  inline for `Custom`, so `Custom{A}` can't be replayed as `Custom{B}`, `handoff.rs:227`),
  allowed_effects, expires_at, max_uses, nonce, swiss. The introducer Ed25519-signs it
  (`handoff.rs:198`, `sign`).
- **The recipient binding.** `HandoffPresentation` (`handoff.rs:327`) wraps the cert + a
  `recipient_signature`. The recipient signs `presentation_message` =
  `b"dregg-handoff-present-v1" || nonce || target_cell || target_federation` (`handoff.rs:353`),
  proving they own `recipient_pk` — an interceptor of the cert in transit cannot present it.
- **`validate_handoff`** (target side, `handoff.rs:413`) — the **6-check admission gate**:
  1. introducer signature valid (`verify_signature`, `handoff.rs:423`);
  2. recipient signature valid (`verify_recipient_signature`, `handoff.rs:428`);
  3. introducer ∈ `known_federations` (trust path, `handoff.rs:433` → `UntrustedIntroducer`);
  4. not expired (`is_valid`, `handoff.rs:438`);
  5. swiss number present & enliven it — the returned `SwissEntry` is the **authoritative HELD
     authority** the target recorded for the introducer (`handoff.rs:448`); the cert's own
     `permissions` are introducer-asserted and **must not** be trusted as an upper bound on
     themselves;
  6a. **target binding** (`handoff_same_target`): `cert.target_cell == held.cell_id` else
      `TargetMismatch` (`handoff.rs:463`) — a forged cert can't redirect a swiss entry for cell
      X to confer access to cell Y;
  6b. **non-amplification** (`handoff_non_amplifying`, Granovetter): the granted
      `AuthRequired` must be `is_narrower_or_equal` to the **held** entry's
      (`handoff.rs:475`), AND the granted effect mask must be a bitwise subset of held
      (`is_facet_attenuation`, `handoff.rs:487`–`499`). `granted ⊄ held` ⇒ `Amplification`.
  On success, mints a random `routing_token` and returns `HandoffAcceptance` with the **granted**
  (attenuated) authority (`handoff.rs:505`).
- **Trust assumption.** **Trustless-when-proven** (`lib.rs:18`): the cert's Ed25519 signature is
  independently verifiable by anyone with the introducer's public key, *without trusting the
  executor*. The swiss-entry lookup and trust-path membership remain executor-trusted.
- **Security tests** (`handoff.rs:567`–`1009`): `create_and_verify_signature`,
  `wrong_recipient_rejected`, `untrusted_introducer_rejected`, `expired_certificate_rejected`,
  `max_uses_exhausted`, `target_mismatch_rejected`, the full non-amplification battery
  (`attenuating_handoff_passes`, `amplifying_handoff_rejected`,
  `amplifying_handoff_from_impossible_rejected`, the effect-mask variants), and an
  `out_of_band_scenario` (cert → compact string → much-later present).

### A.3 — `gc.rs`: distributed reference counting

- **State, two sides.** `ExportGcManager` (`gc.rs:78`) tracks who holds refs to *our* caps:
  `ExportEntry { cell_id, holders : HashMap<FederationId, RefCount>, total_refs, exported_at }`,
  where `RefCount { count, last_activity, session_id }` (`gc.rs:39`). `ImportGcManager`
  (`gc.rs:334`) tracks what *we* hold and generates `DropMessage`s.
- **Drop/keep protocol.** Export side: `record_export_with_session` (`gc.rs:112`) increments;
  `process_drop_with_session` (`gc.rs:162`) decrements and returns `StillHeld` / `CanRevoke` /
  `Invalid`. Import side: `record_import` (`gc.rs:350`) increments `local_refs`;
  `local_ref_dropped` (`gc.rs:369`) decrements and, at zero, emits a `DropMessage` to the remote.
- **The session-epoch defense (capability-Byzantine resistance).** A `SessionId : u64`
  (`gc.rs:35`) tags every export. `process_drop_with_session` rejects a drop whose `session_id`
  ≠ the export's (`gc.rs:193`). Re-export on a new session *supersedes* the old session id
  (`gc.rs:139`). This is the load-bearing invariant: **a Byzantine node on a different session
  cannot drop another holder's refs** (`byzantine_node_different_session_cannot_drop_others_refs`,
  `gc.rs:670`).
- **Invariant (claimed).** Never reclaim a live ref (each holder's count is independent;
  `CanRevoke` only at `total_refs == 0`); never leak (idle sweep via `stale_exports`,
  `gc.rs:219`, + `gc_sweep`, `gc.rs:235`). The leak side is genuinely hard across vats (see §D.2).
- **Trust assumption.** Executor-trusted (`lib.rs:14`) — incorrect GC leaks (won't release) or
  prematurely revokes (kills a live ref). The session-id check is the one *adversary-resistant*
  piece and it's tested, not proved.

### A.4 — `pipeline.rs`: promise pipelining

- **State.** `PipelineRegistry { queued : HashMap<u64, Vec<PipelinedMessage>>, promises :
  HashMap<u64, PipelinePromiseState>, next_id }` (`pipeline.rs:137`). A `PipelinedMessage`
  (`pipeline.rs:54`) targets an unresolved promise and carries a `PipelinedAction { method, args,
  authorization }` (`pipeline.rs:68`) — the `authorization` bytes are load-bearing for soundness.
- **Message flow.** `create_promise` → `pipeline_message` queues against a `Pending` promise
  (`pipeline.rs:174`); `resolve_promise` flips it `Fulfilled` and **drains the queue in order**
  for delivery (`pipeline.rs:204`); `break_promise` flips it `Broken` and **cascades** failure to
  every queued message's `result_promise_id`, recursively (`pipeline.rs:223`). `pipeline_chain`
  (`pipeline.rs:269`) wires step k+1's target to step k's result promise — a dependency DAG.
- **Cross-fed bridge.** `CrossFedPipelineBridge` (`pipeline.rs:425`) keeps a per-peer registry +
  a local registry + an `outbox` of `PipelineWireMessage`s (`PipelineToPromise` /
  `PromiseResolved` / `PromiseBroken` / `PipelineResult`, `pipeline.rs:350`). A `PipelineResultValue::Success`
  carries a `receipt_hash : [u8;32]` for auditability (`pipeline.rs:405`).
- **Ordering.** Queued messages deliver in insertion order on resolution (`concurrent_pipelines_to_same_promise`,
  `pipeline.rs:871`); chains cascade in sequence (`pipeline_chain_resolves_in_sequence`, `pipeline.rs:787`).
- **Trust assumption.** Executor-trusted bookkeeping; the **authorization survives resolution**
  — pipelining is a latency win, not an authority bypass.

### A.5 — `store_forward.rs`: encrypted offline queue

- **Encryption.** `encrypt_for_destination` (`store_forward.rs:165`): ephemeral X25519 keypair →
  DH shared secret with `dest_pk` → BLAKE3-derived symmetric key (`derive_symmetric_key`,
  domain `"dregg-store-forward-v1-key"`, `store_forward.rs:235`) → AEAD encrypt. Returns
  `(ephemeral_pk, ciphertext||tag)`. `decrypt_from_sender` (`store_forward.rs:201`) reverses it.
- **⚠ The crypto is a hand-rolled spike, NOT vetted primitives.** The X25519 is a bespoke
  Montgomery-ladder over a 5×51-bit field (`store_forward.rs:255`, "for production use this should
  be replaced by a vetted library (x25519-dalek, etc.)"). The "ChaCha20-Poly1305" is **not
  actual ChaCha20-Poly1305** — it's `ciphertext = plaintext XOR BLAKE3_keystream(key, counter)` +
  `tag = BLAKE3_MAC(key, ciphertext)` (`store_forward.rs:572`, explicitly "NOT standard
  ChaCha20-Poly1305"). Nonce is zero, justified by unique-key-per-message.
- **Relay.** `MessageRelay` (`store_forward.rs:653`) is a per-destination `VecDeque` with
  per-queue + total depth caps (DoS) and `expire` TTL sweeps (`store_forward.rs:723`).
  `StoreForwardClient` (`store_forward.rs:782`) assigns per-destination causal sequence numbers,
  tracks unacknowledged, and `process_incoming` decrypts + **sorts by causal_sequence**
  (`store_forward.rs:891`). Also a `BlocklaceEnvelope` path (`store_forward.rs:929`) that stores
  ciphertext as block payloads so DAG sync IS the store-forward layer.
- **Trust assumption.** **Trustless-when-proven** (`lib.rs:21`): the relay sees only ciphertext;
  it can delay or drop but not read or forge. Forward secrecy comes from the ephemeral key per
  message. Tests: `wrong_key_decryption_fails`, `tampered_ciphertext_fails`,
  `blocklace_wrong_key_fails`.

### A.6 — `session.rs`: bilateral session state

- **State.** `CapSession { peer_id, peer_strand : Option<StrandId>, epoch : u64, exports :
  HashMap<CellId, ExportEntry>, imports, promises, next_promise_id }` (`session.rs:24`).
- **Epoch.** Monotonic generation counter; messages carrying a stale epoch are rejected
  (`session.rs:39`, `session_epoch_prevents_stale_message_processing`, `session.rs:315` — note
  this test actually exercises the GC `session_id`, not a separate epoch gate on the session
  struct itself). `export` ref-counts + narrows permissions (`session.rs:134`); `import`,
  `disconnect_import`, and the promise table mirror `pipeline.rs` at the session granularity.
- **Unified-lace migration.** Sessions are *bilateral between strands* in the new model
  (`peer_strand`); `peer_id` is legacy group/federation id. The migration is **mid-flight** —
  see §C.

---

## B. The security properties CapTP claims (`lib.rs` Soundness, precisely stated)

| # | Property | Precise statement | Where |
|---|----------|-------------------|-------|
| B1 | **Capability confinement** | A cap is unreachable without its swiss number; `enliven` on an unknown swiss → `NotFound`. The swiss number is a 256-bit bearer secret; possession = authorization. | `lib.rs:25`, `sturdy.rs:164` |
| B2 | **Handoff unforgeability** | A `HandoffCertificate` cannot be forged without the introducer's Ed25519 private key; `validate_handoff` rejects on bad introducer sig, bad recipient sig, untrusted introducer, target mismatch, or amplification. | `lib.rs:26`, `handoff.rs:413` |
| B3 | **Handoff non-amplification** | The conferred (`granted`) authority is `⊆` the introducer's *target-recorded held* authority on both the `AuthRequired` lattice and the effect mask — across vats (Granovetter). | `handoff.rs:467`, Lean `handoff_non_amplifying` |
| B4 | **GC correctness** | No premature reclaim (revoke only at `total_refs == 0`); no leak (idle sweep). Plus **session-scoped Byzantine resistance**: a drop is accepted only from the session that created the export. | `lib.rs:14`, `gc.rs:193`,`670` |
| B5 | **Pipelining ≠ authority bypass** | A queued pipelined call's `authorization` obligation survives promise resolution unchanged; resolution delivers but does not discharge. | `pipeline.rs:73`, Lean `pipelining_preserves_seam` |
| B6 | **Forward secrecy** | Store-forward messages are encrypted to an ephemeral X25519 key per message; the relay sees only ciphertext; a compromised long-term key does not retro-decrypt past messages. | `lib.rs:27`, `store_forward.rs:165` |
| B7 | **Session-epoch replay resistance** | Stale messages from an old session/epoch are rejected; re-establishment supersedes. | `session.rs:39`, `gc.rs:139` |

---

## C. HONEST gaps (heritage incomplete / tested-not-proved / loose ends)

1. **Store-forward crypto is a spike, not production crypto.** The X25519 and the "AEAD" are
   hand-rolled (`store_forward.rs:248`,`569`), explicitly flagged "replace with a vetted library."
   The AEAD is BLAKE3-XOR-keystream + BLAKE3-MAC, **not** ChaCha20-Poly1305. **B6 forward
   secrecy is only as good as this bespoke construction** — any verified forward-secrecy claim
   must either (a) name the swap to `x25519-dalek`/`chacha20poly1305` first, or (b) be honest that
   it models an *idealized* AEAD/DH seam, not this code. Do not launder the spike as proven.

2. **Nearly every B-property is TESTED, not PROVED-against-an-adversary.** B1/B2/B4/B6/B7 have
   unit tests exercising the happy path + a handful of negative cases, but no statement that
   *quantifies over an adversary*. E.g. B2 has `untrusted_introducer_rejected` but no theorem "for
   all byte-strings that are not a valid signature under the introducer's key, validation
   rejects." The negative tests are existential witnesses, not universal soundness.

3. **The trust model's "executor-trusted" core is unbounded.** `lib.rs:30` assumes "the
   federation executor honestly maintains swiss table and session state." This is the n=1 collapse
   the brief warns against: at single-machine it's fine, but the *distributed* claim (B1, B4) rests
   entirely on this assumption with no mechanism enforcing it. A verified CapTP needs the
   executor-maintained state itself to be the **verified `RecordKernelState` `swiss` table** (which
   layer 3 already gives us) — closing this is most of target D3.

4. **Unified-lace migration is mid-flight.** Six `TODO(unified-lace)` markers
   (`handoff.rs:30`, `gc.rs:14`, `pipeline.rs:40`, `store_forward.rs:24`, `uri.rs:66`,
   `session.rs:31`): GC keys, pipeline sessions, and SF destinations are *supposed* to be
   `StrandId` (bilateral) but are still `FederationId` (group). `GroupId = FederationId`
   (`lib.rs:112`) papers over it. `record_export_by_strand` wraps a `StrandId` into a
   `FederationId([u8;32])` (`gc.rs:276`) — a structural pun. **Any GC-safety theorem must pin
   whether the key is the group or the strand**; the pun means "different session" and "different
   strand" are conflated.

5. **Session epoch is half-wired.** `CapSession.epoch` exists (`session.rs:39`) but the test that
   *claims* to exercise epoch replay-resistance actually exercises the GC `session_id`
   (`session.rs:315`–`343`). There is no code path that rejects a `CapSession`-level message by
   its `epoch` field — the real replay defense lives only in `gc.rs`'s `process_drop_with_session`.
   B7 is **weaker than the doc claims** at the session layer.

6. **`PipelineRegistry.pipeline_message` to an already-*fulfilled* promise re-queues silently**
   (`pipeline.rs:187`), relying on the caller to re-drain. The `CrossFedPipelineBridge`'s
   chain-to-remote uses a fragile convention ("the remote creates a promise whose ID equals the
   result_promise_id," `pipeline.rs:512`) and a `local_federation_placeholder() = [0;32]`
   (`pipeline.rs:689`) — sender identity on pipelined calls is **unset in the bridge**, so the
   `authorization` field's binding to a real sender is not enforced at the bridge layer.

7. **Two distinct "drop" effects in Lean, easy to conflate.** `swissDropA` decrements the
   `swiss` refcount table (the real GC, `Inst/swissDropA.lean:5`); `dropRefA` touches `caps` and is
   the *authority-revocation* family (`recCRevoke`, `Inst/dropRefA.lean:8`). The `gc.rs`
   ref-drop maps to `swissDropA`, **not** `dropRefA`. A GC-safety theorem must target the `swiss`
   table.

8. **No Lean model at all for: session epochs, store-forward (crypto, relay, causal ordering),
   and the `known_federations` trust path.** These are the genuinely-absent facets (the `epoch`
   hits in Lean are the *relay rate-limit* epoch in `RelayOperator.lean`, unrelated).

---

## D. dregg2 VERIFICATION TARGETS (ranked by criticality)

These are the properties that **hold as the system scales** — not n=1 collapses. Each names the
property, the gap, and (for the top 3) a concrete Lean beachhead wired to the existing verified
cap effects. The existing abstract theorems (`CapTP.lean`) are the *shape*; the work is connecting
them to layer-3 verified state and adding the adversary.

### D1 — Handoff-certificate unforgeability, wired to verified introduce/handoff effects ★★★ TOP

- **Property (B2).** `validate_handoff` accepts ⇒ a cert signed by the named introducer's Ed25519
  key exists. Contrapositive (the load-bearing direction): **no party lacking the introducer's
  private key can produce a presentation that `validate_handoff` accepts** for a fresh
  (introducer, recipient, target) — and acceptance installs *exactly* the non-amplifying granted
  cap into the verified `caps` table, nothing more.
- **Current state.** `handoff.rs` is the trustless-when-proven jewel (Ed25519 + domain
  separation + recipient binding, A.2). Lean `handoff_is_introduce` / `handoff_non_amplifying`
  prove the *graph* discipline but fold the entire signature/trust/swiss check into one opaque
  `attested : Prop` (`CapTP.lean:255`). `CapTPConcrete` pins the non-amplification *lattice*
  decision with a live Rust differential — but the **signature unforgeability seam is unmodeled**.
- **Beachhead.** A new `Dregg2/Exec/CapTPHandoffSound.lean` that:
  (1) makes `attested` in `HandoffValid` (`CapTP.lean:244`) **concrete** as a `Spec.Verifiable`
  discharge over the cert's `signing_message` bytes — reuse the SAME `Verifiable Statement
  Witness` / `Laws.Discharged` seam the rest of dregg2 uses for Ed25519 (the
  `Authority/ThirdPartyDischarge.lean` credential seam is the precedent), so unforgeability is "no
  witness ⇒ no discharge ⇒ `validate_handoff` rejects," not new crypto;
  (2) prove `validate_handoff_accepts → introduceA_full_sound`'s precondition — i.e. a validated
  handoff is exactly the verified `introduceE` transition on `caps` (`Inst/introduceA.lean:235`),
  so acceptance installs `recDelegateCaps s.kernel.caps intro rec t` and **freezes the other 16
  kernel fields** (the anti-ghost tooth already proved there). This *joins layer 1 to layer 3*:
  the abstract `Introduce` becomes the concrete full-state `DelegateSpec`.
- **Wired to existing effects:** `introduceA` (`caps` table, `Inst/introduceA.lean`),
  `handoff_non_amplifying_concrete` (`CapTPConcrete.lean:286`), the `swiss`-table `enliven`
  (`Spec/swissenliven.lean`) that produces the authoritative `held`.

### D2 — Distributed-GC safety over the verified refcount table ★★★ TOP

- **Property (B4, the safety half).** **No premature reclaim**: the runtime never revokes an
  export while *some* strand still holds a ref — formalized over the verified `swiss : List
  SwissRecord` refcount, AND against the session-Byzantine adversary (a drop from the wrong
  session cannot decrement another holder's count).
- **Current state.** `CapTPGC.lean` proves the **liveness** half honestly (lease-based reclaim,
  `captp_gc_by_lease`, + the cross-vat-cycle leak is the *proved price* of `dead_undecidable`,
  `CapTPGC.lean:143`). But it operates on the abstract `ImportHandle` + `Liveness.Lease`, **not**
  on the concrete `swiss` refcount table, and it does **not** model the session-id Byzantine
  defense (`gc.rs:670`) at all. Layer 3 has `swissDropA` proving the refcount-decrement/GC-at-zero
  full-state transition (`Spec/swissdrop.lean:24`–`37`) but no *no-premature-reclaim invariant
  across multiple holders/sessions*.
- **Beachhead.** A new `Dregg2/Exec/CapTPGCConcrete.lean` that:
  (1) models the multi-holder refcount as the verified `SwissRecord.refcount` summed over holders
  (the brief's "never reclaim a ref some strand still holds"); state the safety invariant
  `total_refs > 0 → entry ∈ swiss` and prove `swissDropA` preserves it (reuse the
  `swissDropA_full_sound` full-state transition — GC removal happens **iff** `refcount` hits 0,
  `Spec/swissdrop.lean:27`);
  (2) add the **session-id tooth**: model `RefCount.session_id` and prove `process_drop` from a
  non-matching session is a *no-op* on the refcount (the `byzantine_node_different_session...`
  test as a theorem). This is the anti-ghost tooth for GC: tampering the drop's session ⇒ the
  refcount table is unchanged ⇒ no premature reclaim.
- **Wired to existing effects:** `swissDropA` (`swiss` table, `Inst/swissDropA.lean`),
  `swissEnliven` (`refcount + 1`, the keep side, `Spec/swissenliven.lean:18`), `swissExportA`
  (`refcount := 1` mint, `Spec/swissexport.lean:79`). The lease-liveness side stays in
  `CapTPGC.lean` (already proved); this target adds the **concrete safety + Byzantine** half.

### D3 — Swiss-table confinement: a cap is unreachable without its swiss number ★★★ TOP

- **Property (B1).** For the verified `swiss : List SwissRecord` table, `enliven sw` succeeds ⇒
  `sw` was minted by a prior `swissExportA` (or its derived handoff). Adversarially: a party who
  has not been given a swiss number cannot, except with negligible probability (256-bit secret),
  produce one that `enliven` accepts — and absent a successful enliven, the target cap's authority
  is **not** added to the adversary's `caps` slot.
- **Current state.** `swissExportA`/`swissEnliven` prove the full-state *transitions* (mint with
  fresh `sw`, find-then-bump), and `swissExportA`'s guard already encodes **freshness** ("the
  swiss number is not already in use") + **non-amplification** (`Inst/swissExportA.lean` header).
  But there is **no confinement theorem**: nothing states "enliven on a swiss not in the table
  fails AND yields no authority," and the unguessability is an entropy argument, not a Lean
  statement.
- **Beachhead.** Extend `Spec/swissenliven.lean` with `enliven_requires_mint`: `enlivenSwissUpdate
  ss sw = some _ → findSwiss ss sw = some _` (already half-there: `enlivenSwissUpdate` returns
  `none` on `findSwiss = none`, `Spec/swissenliven.lean:53`) — promote to an explicit
  **confinement lemma** and connect it to the `caps` side: a failed enliven leaves the caller's
  `caps` slot frozen (reuse the `RestIffNoCaps` frame from `Inst/introduceA.lean:80` — a no-enliven
  turn touches neither `swiss` nor `caps`). The unguessability of `sw` itself is carried as a named
  entropy assumption (like the Ed25519 seam), **honestly labeled** — not proved, but isolated.
- **Wired to existing effects:** `swissEnliven` (`Spec/swissenliven.lean`), `swissExportA`
  freshness guard, the `RestIffNoSwiss`/`RestIffNoCaps` frames (anti-ghost: a non-presenting party
  changes nothing).

### D4 — Promise-resolution correctness / ordering ★★ (shape mostly proved)

- **Property (B5).** Pipelining preserves the authorization seam (proved: `pipelining_preserves_seam`,
  `CapTP.lean:129`); the chain is a dataflow DAG and broken promises cascade transitively (proved:
  `pipeline_chain_is_dataflow_edge`, `pipeline_break_cascades`, `CapTP.lean:175`,`186`). **Gap:**
  in-order delivery (`resolve_promise` drains FIFO, `pipeline.rs:204`) and the cross-fed bridge's
  sender-identity binding (the `[0;32]` placeholder, §C.6) are **not** modeled. A target: prove the
  delivered-message sequence is a permutation-preserving drain AND that the `authorization` is bound
  to a *concrete* sender (closing the bridge placeholder).
- **Beachhead (lower priority):** extend `CapTP.lean §1` with a `List`-level FIFO-drain lemma and a
  sender-bound `PipelinedCall`; reuse `Spec.Await.PromiseGraph` for the DAG (already connected).

### D5 — Store-forward forward-secrecy ★ (blocked on crypto swap)

- **Property (B6).** Ephemeral-key-per-message ⇒ a compromised long-term key does not retro-decrypt.
  **Gap:** *no* Lean model, and the underlying crypto is a spike (§C.1). A verified forward-secrecy
  theorem should be deferred until the crypto is swapped to vetted primitives, OR stated explicitly
  as an *idealized AEAD/DH* seam (a `Verifiable`-style discharge over an opaque encrypt/decrypt
  pair) — honestly labeled as modeling the protocol shape, not this bespoke code. Lowest priority;
  do not let it block D1–D3.

### D6 — Session-epoch replay resistance ★ (half-wired in Rust first)

- **Property (B7).** Stale-epoch messages rejected. **Gap:** the session-layer epoch is half-wired
  even in Rust (§C.5); the real defense is the GC `session_id` (folded into D2). Recommend: fix the
  Rust session-epoch gate first, then model it as a monotonic-generation guard reusing the same
  `session_id` machinery as D2 — don't model the broken-in-Rust path.

---

## Sequencing for the wave

D1 → D2 → D3 are the **crown** (each joins layer-1 abstract protocol claims to layer-3 verified
state + adds an adversary, and each holds as the system scales). They share the same move:
*de-vacuify an opaque `attested`/abstract-graph into the concrete verified `swiss`/`caps` table
transition, then add the anti-ghost tooth* (tamper the signature / the drop-session / the swiss
number ⇒ verified state unchanged). D4 is mostly shape-proved (finish ordering + sender binding).
D5/D6 are gated on Rust-side fixes (crypto swap, session-epoch gate) and must be honestly labeled
as idealized seams until then — never laundered as proven.
