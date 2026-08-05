# The Galley layer contract — the PoA organ template

Traced end to end 2026-08-05 against HEAD. Every claim below is anchored to `file:line`.
Galley is the only PoA kernel with a complete Lean → player path, so it is the template.
This document states what each hop is allowed to decide and — just as important — the
places where the template is Galley-specific and a second organ would have to generalize.

**Read the correction in §0 before you copy anything.** The Lean object that reaches the
player is *not* the Galley kernel.

---

## 0. The correction: two Galleys, and only one of them ships

There are two independent Lean state machines with "Galley" in the name.

| | `GalleyMaintenanceDaily.lean` (1906 ln) | `GalleyMaintenanceDailyRuntime.lean` (1412 ln) |
|---|---|---|
| Reducer | `reduce` (`GalleyMaintenanceDaily.lean:350`), private | `reduce` (`…Runtime.lean:684`), public |
| State | `State` (`:162`) — phases `ballot / maintenance / completed / outputRecorded` | `ProjectionWire` (`:160`) — no phases, one `sequence` counter |
| Actions | `participant / openMaintenance / perform / visitCommons / recordFinalizedOutput` (`:185`) | payload kinds `"public-play"` / `"holder-sponsor"` (`:688`, `:698`) |
| Concepts | HolderMechanics two-chamber ballot, authored procedure steps, commons rotations + capacity + neighborly alternative, finalized-run output + deployment-global nullifier registry, CAS persistence contracts | one visit per player, a bounded `localService` accumulator against `serviceTarget`, three inert anchor roots |
| `@[export]` | **none** | `dregg_poa_galley_daily_judge` (`:975`) |
| Reached by Rust | **never** | always |

`…Runtime.lean` imports `GalleyMaintenanceDaily` for **exactly one identifier** —
`abbrev MAX_LOCAL_SERVICE := GalleyMaintenanceDaily.MAX_LOCAL_SERVICE` (`…Runtime.lean:46`).
Nothing else. Verified by `grep -n "GalleyMaintenanceDaily\." …Runtime.lean` → one hit.

**There is no refinement theorem, no simulation, and no shared type between them.**
`GalleyMaintenanceDailyBoundary.lean` (145 ln) is a privacy ratchet over the *kernel*
(`fail_if_success (have _ := State.mk)` etc., 13 `True`-valued theorems) — it proves the
kernel's constructors are private, which is worth having, but it says nothing about the
runtime and the runtime has no boundary module of its own.

`GalleyCommons.lean` (2760 ln) is a third, separate kernel — settled-credit commons play —
with **zero `@[export]`**. It is reachable from `GalleyMaintenanceDaily.provisionCapabilities`
(`GalleyMaintenanceDaily.lean:1329`) as a type parameter and from nothing else. It does not
ship either.

So: **≈4,700 lines of proved Lean Galley kernel are dark, and the ~1,400-line Runtime that
does ship is the whole shipped semantics.** Every other organ's Runtime/Wire layer (the
~9,880 lines named in the brief) is in the same position by default. When a lane says
"the kernel reaches the node", the check is: *does the `@[export]`'d function's call graph
reach the kernel's reducer?* For Galley the answer is no.

This is not a reason to stop. It is the first item of work for any organ that wants its
kernel to be load-bearing — but it must be **said out loud** rather than inherited silently.

---

## 1. The seven hops

```
authored policy JSON (a manifest component)
   │  poa.galley-maintenance-daily.policy.v1                    ActivatedContent.lean:54
   ▼
[1] Lean ActivatedContentRuntime   @[export dregg_poa_activated_content_authorize]
   │  emits policy_json (verbatim) + genesis_projection_json     ActivatedContentRuntime.lean:104
   ▼
[2] persist  poa_activated_content.rs — sealed redb frame, replayed on every read
   ▼
[3] persist  poa_galley_authority.rs  — builds POA-GALLEY-DAILY-IN-1, calls Lean, re-checks
   │            ↕ dregg-lean-ffi/src/poa_galley_ffi.rs → lean_init.c:1539 → Lean judgeFFI
   ▼
[4] node     poa_galley_api.rs        — 3 HTTP routes, reshapes; prepares an UNSIGNED Turn
   ▼
[5] browser  galley-runtime.js        — transport + strict shape gate
   │  galley-controller.js            — DOM only
   ▼
[6] wallet extension  signTurnV3(postcard, federationId)  — replaces authorization, signs
   ▼
[7] node blocklace_sync → persist commit_log — classify, preflight, execute, RE-JUDGE, stage
   │  the staged event becomes the next `history` entry for hop [3]
   └──────────────────────────────────────────────────────────────────────► back to [3]
```

---

## 2. What Lean exports

### 2.1 The one symbol

```lean
-- metatheory/Dregg2/Games/PathOfAngels/GalleyMaintenanceDailyRuntime.lean:975
@[export dregg_poa_galley_daily_judge]
def judgeFFI (bytes : String) : String :=
  (judgeBytesWithAuthority? bytes 0 none).getD ""
```

`String → String`. **Empty string is the only refusal channel** — no error code, no reason.
`now` is pinned to `0` and `authority` to `none`, so `commandPayload?` can never take the
`"holder-sponsor"` branch (`…Runtime.lean:984` `no_authority_cannot_form_holder_payload`).
Holder sponsorship is structurally unreachable from the export, not policy-disabled.

Two more Lean exports are on the Galley path but owned by other modules:
`dregg_poa_activated_content_authorize` (`ActivatedContentRuntime.lean:117`) and
`dregg_poa_event_batch_runtime_plan` / `…_initial_heads_digest` (`EventBatchRuntime.lean`).

### 2.2 The export must be listed in the FFI decision table

`dregg-lean-ffi/build.rs:255` lists `"dregg_poa_galley_daily_judge"` among the *decision
exports*. build.rs probes the built archive for the symbol and emits
`cfg(dregg_poa_galley_daily_judge_present)`. **If the symbol is absent the Rust bridge
compiles to a refusal, not a Rust reimplementation** (`poa_galley_ffi.rs:110-119`).
An organ that adds an export and forgets this list gets a silently-absent authority.

### 2.3 The C shim

`dregg-lean-ffi/src/lean_init.c:1539` `dregg_poa_galley_daily_judge_str(in, out, cap) -> size_t`,
guarded by `#ifdef DREGG_POA_GALLEY_DAILY_JUDGE`. Returns `(size_t)-1` on transport refusal,
otherwise the full length (caller re-calls with a bigger buffer if `full >= cap`).
Module init at `lean_init.c:1363` calls
`initialize_Dregg2_Dregg2_Games_PathOfAngels_GalleyMaintenanceDailyRuntime(1)`.

### 2.4 Wire formats and bounds, all Lean-owned

| constant | value | site |
|---|---|---|
| `INPUT_FORMAT` | `POA-GALLEY-DAILY-IN-1` | `…Runtime.lean:38` |
| `OUTPUT_FORMAT` | `POA-GALLEY-DAILY-OUT-1` | `:39` |
| `BETA_HOLDER_FORMAT` | `POA-GALLEY-BETA-HOLDER-1` | `:40` |
| `STREAM_KIND` | `9` | `:41` |
| `STREAM_VERSION` | `1` | `:42` |
| `MAX_EVENTS` | `64` | `:45` |
| `MAX_LOCAL_SERVICE` | `100` | `:46` (via kernel) |
| `WIRE_BYTE_LIMIT` | `1 MiB` | `:44` |
| action-token preimage format | `POA-GALLEY-ACTION-TOKEN-1` | `:788` |

Seven domain-separated digest tags, all `digestString` = 8 BabyBear sponge lanes
(`CommitmentTreeWide.hashTo8`) serialized as 8 little-endian u32 (`…Runtime.lean:607`):
`PAYLOAD 0x50474150 · EVENT 0x…45 · INPUT 0x…49 · POLICY 0x…4c · PROJECTION 0x…52 ·
ACTION_TOKEN 0x…54 · AUTHORITY 0x…41` (`:612-618`).

⚠ These digests are **not SHA-256 and not BLAKE3**. They are the 8-lane BabyBear
construction — the same one carrying the 247.26-bits-into-256 injectivity wound recorded in
`project-circuit-soundness-apex`. `semantic_head`, `projection_digest` and every
`action_token` a player signs against are values of this hash. Say that at that resolution;
do not describe an action token as "a 256-bit commitment".

### 2.5 Canonicality is the decoder's contract

`canonicalDecode` (`…Runtime.lean:541`) parses, then **re-encodes and demands byte
equality**. Proved: `decodeInput_reencodes` (`:584`), `decodeOutput_reencodes` (`:1154`),
`decodePolicy_reencodes` (`:578`), all `#assert_axioms`-clean. Consequences the callers
depend on:

- the exact JSON **key order** of every `*.toJson` is the wire;
- a trailing space refuses (`hostile_trailing_byte_refused`, `:1372`);
- an unknown field refuses (`:1375`);
- `exactKeys` (`:56`) demands the key set *exactly*, not a superset.

`decodePolicy` is deliberately exposed (`:575`) so the activated-content installer uses the
**same parser** as the game — there is no second policy grammar.

### 2.6 What the judge actually decides

`judgeInput?` (`…Runtime.lean:951`):

1. `validatedPrefix?` (`:858`) — `policy.validB`, `history.length ≤ 64`,
   `EventSourcing.rebuild` from `initialProjection policy` over the whole history,
   then **three equalities**: rebuilt projection `=` `claimed_projection`,
   cursor sequence `=` claimed sequence, cursor sequence `=` history length.
   *Lean replays from genesis on every single call.* There is no incremental trust.
2. mode `"view"` → `action.kind = "none"` and `action.token = 0…0`, else refuse.
3. mode `"command"` → `commandPayload?` (`:920`) requires the requested `(kind, token)` to
   be **found in the list this same judge would have offered** (`requestedAction?`, `:914`),
   then `EventSourcing.applyEvent` with the deployment-fixed `digestBoundary` (`:660`).

Output (`OutputWire`, `:229`): `input_digest`, `policy_digest`, `replay{6}`, `projection`,
`view`, `event?`, `receipt?` — `event` and `receipt` are both-or-neither (`:1145`).

Proved facts a consumer may rely on:
- `reduce_preserves_advantage_anchors` (`:716`) — `powerRoot/lootRoot/canonRoot/canonRevision`
  are identical across any accepted transition.
- `reduce_holder_sponsor_bounded` (`:725`) — sponsor service ≤ 100 and anchors unchanged.
- `receiptOf_has_no_advantage_delta` (`:979`) — the three deltas are literally `0`.
- `no_authority_cannot_form_holder_payload` (`:984`).

### 2.7 Action-token semantics — read this before copying

```lean
-- …Runtime.lean:804
private def publicAction … : ActionTokenWire := {
  token := digestString ACTION_TOKEN_DOMAIN
    (tokenPreimage policy state.cursor viewer "public-play" viewer.player
       zeroDigest zeroDigest (state.cursor.sequence + 1))
  expiresAfterSequence := state.cursor.sequence          -- ← the CURRENT head
}
```

The preimage binds `deployment_id, federation_id, daily_id, content_epoch, rules_digest,
expected_predecessor (= cursor.head), event_sequence (= cursor.sequence + 1), action_kind,
player, player_cell, beneficiary, authority_commitment, nonce, expires_after_sequence`
(`:785-802`). It is a **pure function of state** — it is not a secret, not a MAC, and any
party with the history can recompute it. Its only job is to make the client's request
*exactly nameable*; the server re-derives and re-matches at every hop.

`expiresAfterSequence` equals the head the token was minted at, and every downstream check
is `current ≤ expires`, so **a public token is valid at exactly one sequence and is dead the
instant any event lands.** `poa_galley_authority.rs:641` requires
`expires_after_sequence == snapshot.sequence`; `galley-runtime.js:435` implements the same
predicate. That is the concurrency model: one in-flight player command per daily, full stop.

---

## 3. The wire, byte for byte

### 3.1 Input — `POA-GALLEY-DAILY-IN-1`

Rust builds it as a **string template**, not with serde
(`persist/src/poa_galley_authority.rs:1277`):

```
{"format":"POA-GALLEY-DAILY-IN-1","mode":"<view|command>","policy":<POLICY VERBATIM>,
 "history":[<EVENT JSON>,…],"claimed_projection":<PROJECTION VERBATIM>,
 "viewer":{"player":"<hex64>","player_cell":"<hex64>","sponsor_beneficiary":"<hex64>"},
 "action":{"kind":"<none|public-play|holder-sponsor>","token":"<hex64>"}}
```

Two of those slots are **bytes that Lean itself produced and persistence stored verbatim**:

- `policy` is `policy.policy_json` (`:1266`), the sealed manifest component, never
  re-serialized by Rust;
- `claimed_projection` is `snapshot.projection` (`:1268`), the durable head projection,
  which is either Lean's `initialProjection` from the activated-content bind or a previous
  judge output.

This is why the round-trip check passes. **Copy this discipline exactly: keep Lean-authored
bytes as bytes; never re-serialize them through a Rust struct on the way back in.**

`history` entries *are* re-serialized (`:1119` `serde_json::to_vec(&event)`) from
`GalleyEventWire`, so for the history alone, Rust struct field order is load-bearing.

### 3.2 Output — `POA-GALLEY-DAILY-OUT-1`

Decoded by `strict_json` (`:1528`): serde parse with `deny_unknown_fields`, then
**re-serialize and demand byte equality** against the Lean bytes. Same idea as Lean's
`canonicalDecode`, implemented independently.

### 3.3 The mirror, and its drift surface

`GalleyPolicyWire :1599 · GalleyProjectionWire :1625 · GalleyReplayWire :1641 ·
GalleyActionWire :1652 · GalleyViewWire :1662 · GalleyStatementWire :1675 ·
GalleyPayloadWire :1687 · GalleyEventWire :1699 · GalleyReceiptWire :1707 ·
GalleyOutputWire :1722` — all in `persist/src/poa_galley_authority.rs`, all
`#[serde(deny_unknown_fields)]`.

These are **not a semantic twin** — they carry no transition rule; the reducer is only in
Lean. But they *are* a syntactic twin, and **their Rust struct declaration order is the
canonical key order**. Nothing mechanically pins it to Lean's encoders. The policy key
order currently exists in four places:

1. `PolicyWire.toJson` — `…Runtime.lean:260`
2. `struct GalleyPolicyWire` — `poa_galley_authority.rs:1599`
3. `fn live_policy_json` — `node/src/poa_galley_api.rs:553` (test)
4. the same `format!` again in `persist/src/poa_activated_content.rs:558`,
   `persist/src/commit_log.rs:4454`, `persist/src/poa_galley_authority.rs:1987` (tests)

A field added to `PolicyWire` in Lean and not to `GalleyPolicyWire` in Rust does not fail
to compile — it fails at runtime as `"Galley policy is not strict typed JSON"`, and only on
a box that has the archive linked. **Generalization item G1** below.

---

## 4. What the node serves

`node/src/poa_galley_api.rs`. Mounted at `node/src/api.rs:2227`
(`.merge(crate::poa_galley_api::routes())`), base path `/api/poa/galley/v1` (`:25`).
The browser calls `/node/api/poa/galley/v1/*`; Caddy strips `/node` (`galley-runtime.js:17`).
⚠ `sdk/src/poa_galley.rs:17` advertises `GALLEY_API_PATH_V1 = "/node/api/poa/galley/v1"` —
the Caddy-side path, disagreeing with the node's own constant. Two spellings of one route.

| route | method | body | response |
|---|---|---|---|
| `…/session` | GET | — | `POA-GALLEY-SESSION-V1` |
| `…/status` | GET | — | `POA-GALLEY-STATUS-V1` (session + `events[]`) |
| `…/command` | POST | `{format: POA-GALLEY-COMMAND-PREPARE-V1, action_token}` | `POA-GALLEY-UNSIGNED-TURN-V1` |

Every route requires header `X-Dregg-Actor: <64 lowercase hex, nonzero>`, exactly once
(`:211-234`). It is allowed through CORS preflight at `node/src/api.rs:1858`, and there is a
test that asserts that (`poa_galley_api.rs:632`). Body limit 16 KiB (`:32`).

**Authority of the actor header: personalization only.** `observe_active_poa_galley_v1`'s
own doc says so (`poa_galley_authority.rs:864`) and it is true — the header selects which
player's actions Lean is asked to offer, and nothing else. The write path derives identity
solely from the verified `SignedTurn` envelope.

### 4.1 Reads

`get_session` / `get_status` → `observe(…)` → `store.observe_active_poa_galley_v1(actor)`
(`poa_galley_authority.rs:867`), which in **one redb write-txn that is always aborted**:

1. `prepare_active_poa_galley_policy_v1_in` — audit the signed active world, load the sealed
   content frame, **re-run Lean's `authorize`** on the stored manifest (`poa_activated_content.rs:150`);
2. `AuthenticatedPoaGalleyPolicyV1::from_activated_content` (`:440`) — re-check that the
   policy binds the world (`federation_id`, `content_epoch`) and that the genesis projection
   is genuinely all-zero-with-policy-anchors (`:482-497`);
3. `load_galley_snapshot_in` (`:1052`) — rebuild the exact event history from the V2 batch
   store, refusing on any stream/world/genesis/length disagreement;
4. build the IN-1 view request, `call_galley` (`:1291`), `validate_view` (`:1301`);
5. `load_galley_receipts_in` (`:1169`) — resolve each event's canonical receipt frame by
   scanning `RECEIPT_CHAIN`, checking postcard canonicality, `turn_hash`, `pre_state_hash`,
   agent cell, federation and `Finality::Final`. Bounded at 65 536 rows (`:65`); over that
   it **refuses observability** rather than returning unverifiable receipts.

`validate_view` (`:1301`) then re-derives, independently of Lean: history length, before/after
sequence, before/after head, projection byte-equality against the durable projection,
action count ≤ 2, and — in `validate_output_shape` (`:1415`) — that the three roots and the
canon revision equal the policy's, that action tokens are unique, and that **every offered
action is `public-play` with `actor == signer`**. `observe_…` narrows again at `:906`:
any action that is not `public-play`, self-beneficiary, expiring exactly at the head is an
integrity error.

**So the node does not trust Lean's output; it re-checks every field it will act on.**
That is the template's most copyable property.

### 4.2 The one vocabulary rename

`GalleyActionResponse { kind: "perform", … }` (`poa_galley_api.rs:329`) — hardcoded. Lean
says `"public-play"`; the HTTP surface says `"perform"`; the browser requires `"perform"`
(`galley-runtime.js:233`); the signed carrier uses `PERFORM_TAG_V1 = 2`
(`turn/src/poa_galley_carrier.rs:27`). One concept, four spellings. **G2.**

### 4.3 Node-invented fields (not Lean, not durable)

- `aggregate_id = format!("galley:{}", hex(daily_id))` (`:359`)
- `schema_version: 1` — a literal, not `GALLEY_STREAM_VERSION` (`:361`)
- `replay { audited: true, … }` (`:367`) — **a literal `true`.** It is not a claim the node
  computes; it is the shape of "we got this far". The browser gates its entire player loop
  on it (`galley-controller.js:401`), which is honest only because a failed audit returns
  an error instead of `audited: false`. There is no code path that emits `audited: false`.
  A lane copying this should either compute it or delete it. **G3.**
- `intent_id` — `blake3::derive_key("dregg-poa-galley-intent-v1")` over
  `federation_id ‖ daily_id ‖ sequence_le ‖ semantic_head ‖ actor ‖ token ‖ preparation_digest`
  (`:493-500`). Client-opaque correlation id only.

### 4.4 Prepare (`post_command`, `:432`)

Re-observes, requires **exactly one** offered action matching the token *and*
`expires_after_sequence == observed.sequence` (`:451-460`) → otherwise `409 StaleAction`.
Then reads the player cell: if it exists, `public_key()` must equal the actor
(`ActorCellMismatch`) and `pq_identity()` must be present (`ActorPqIdentityMissing`) — a
cold player with no cell is allowed at `(nonce 0, no previous receipt)`.

Builds an **unsigned** `Turn` with `galley_player_command_turn(actor, nonce,
previous_receipt_hash, Perform { action_token, action_content_id })`
(`turn/src/poa_galley_carrier.rs:252`), materializes call hashes, postcards it, and returns
base64 + `preparation_digest = SHA-256(postcard)`.

⚠ `preparation_digest` is **not** the turn hash. The wallet replaces
`Authorization::Unchecked` with a hybrid signature and re-hashes, so the final turn hash
differs. The node test asserts exactly this (`poa_galley_api.rs:985`
`assert_ne!(event.turn_hash, prepared.preparation_digest)`). Any organ copying the prepare
step must keep those two names distinct in every layer, or the browser's reconciliation
silently never matches.

### 4.5 Error vocabulary (`:159-169`)

`poa-galley-actor-required` 401 · `-actor-malformed` 400 · `-command-malformed` 400 ·
`-action-stale` 409 · `-actor-cell-mismatch` 409 · `-actor-pq-identity-missing` 409 ·
`-observation-unavailable` 503. Body is `{code, message}`.

Note that **an uninstalled Galley world is a 503**, and the browser renders it as
"GALLEY SEALED // galley-http: … (503)". See §7.

---

## 5. The signed carrier

`turn/src/poa_galley_carrier.rs`, deliberately *below* the SDK so persistence and finality
classify the same bytes without an SDK dependency (`:1-8`). `sdk/src/poa_galley.rs` is a
26-line re-export plus one route constant.

- topic `pathofangels.network/galley-command/v1` (`:20`), method `poa-galley` (`:23`)
- tags: `PublicVote 0 · OpenMaintenance 1 · Perform 2 · VisitCommons 3 · HolderSponsorship 4`
  (`:25-29`)
- `galley_player_cell(pk) = CellId::derive_raw(pk, blake3("default"))` (`:244`) — the
  deployed default-agent derivation, **not** a Galley identity domain
- `command_from_exact_galley_turn` (`:303`) rejects any turn carrying memo, `valid_until`,
  `depends_on`, conservation/execution/custom proofs, witness index maps, more than one
  root, children, non-default preconditions, delegation, partial commitment, balance change,
  witness blobs, more or fewer than one `EmitEvent`, a foreign emitter cell, or a fee that
  is not `galley_command_hybrid_fee(turn)` (`:284`)
- `classify_galley_event` (`:407`) — **`OpenMaintenance` is `Err(OperatorOnlyOpenMaintenance)`**;
  a malformed reserved marker is an error, never `Ordinary`

Of the five tags, **only `Perform` has a writer.** `classify_finalized_galley`
(`poa_galley_api.rs:75`) maps `PublicVote / VisitCommons / HolderSponsorship` to
`UnsupportedCommand` (`:128-132`). The vocabulary is deliberately wider than the shipped
semantics — which is the right shape, but note the vocabulary describes the *kernel's*
actions, and the kernel does not ship (§0).

---

## 6. What the browser consumes

`poa-web/src/galley-runtime.js` (733 ln, transport + validation) and
`galley-controller.js` (616 ln, DOM only). Mounted from `poa-web/src/app.js:86`.
Tests: `galley-runtime.test.mjs`, `galley-controller.test.mjs`,
`galley-accessibility.test.mjs`, `galley-fixtures.mjs`.

The split is strict and worth copying verbatim:

- **runtime** owns every `refuse(...)`; it exports pure normalizers
  (`normalizeGalleySession :314`, `normalizeGalleyStatus :355`,
  `normalizeGalleyUnsignedTurn :376`), a read projection (`projectGalleyWatch :398`), a
  durable intent journal (`createGalleyPendingIntentJournal :520`) and a transport
  (`createGalleyTransport :655`);
- **controller** never parses and never decides — it renders `projectGalleyWatch`'s output
  and calls `transport.*`.

Validation the browser genuinely performs:

- `exact(name, value, keys)` (`:77`) — exact key-set equality on every object, same
  discipline as Lean's `exactKeys`;
- prototype check — only `Object.prototype` or `null` (`:72`), so a prototype-polluted
  payload refuses;
- `resolveSameOriginGalleyEndpoint` (`:630`) + `credentials:"same-origin"`,
  `redirect:"error"`, `cache:"no-store"` (`:638-651`);
- coherence: `publicPlayCount === publicPlayers.length`, `sponsorshipCount === sponsors.length`
  (`:253`); replay window forms the journal suffix (`:284-291`); event sequences strictly
  increasing and the last event digest equals both `replay.head_digest` and `semantic_head`
  (`:369`);
- `checkGalleyPreparationPostcardSha256` (`:463`) — the postcard bytes really are what the
  server said, checked *before the signer ever sees them*;
- `checkGalleyReceiptPostcardSha256` (`:453`) — labelled, correctly, "Adjacent transport
  checksum only; this is not canonical Dregg receipt verification".

What the browser explicitly does **not** do, and says so in the rendered UI
(`galley-controller.js:385`): verify quorum finality, verify the canonical receipt, or
recompute any Lean digest. It carries no reducer. `projectGalleyWatch` even refuses the
incoherent case where a player is both recorded and offered an action (`:405`).

The durable pending-intent journal (`localStorage`, key `poa.galley.pending-intents.v2`)
stores **coordinates only** — `federation_id, daily_id, aggregate_id, intent_id,
preparation_digest, final_turn_hash, prepared_at_sequence, expires_after_sequence` — never
state. `reconcile` (`:572`) refuses to infer anything when `replay.audited` is false. This
is the correct answer to "the tab closed mid-signature" and should be copied wholesale.

Signer contract: `window.dregg.getActiveIdentity() → {publicKeyHex, profileName?}` and
`window.dregg.signTurnV3(postcardBytes, federationIdBytes) → {submitted, queued?, turnId?,
outboxId?, error?, receipt?, nodeResult?}` (`:178`). The extension is **not in this repo**.

Looseness worth noting: `daily_id` and `aggregate_id` are validated as `opaque()` (bounded
printable, ≤256) rather than `digest()` (`:302-303`), although the node always emits hex64.

---

## 7. The write path, and where it re-judges

`node/src/blocklace_sync.rs:7683` — after PQ admission and before any executor mutation:

1. `classify_finalized_galley(&signed)` (`poa_galley_api.rs:75`) scans **every** effect
   including inside `ExerciseViaCapability` and `PipelinedSend` (`:93-106`) — because
   pipeline resolution later promotes the inner action to a new root, so a reserved carrier
   must not become visible only *after* classification. Two reserved markers → `Multiple`.
   Then it re-derives the command with `command_from_exact_galley_signed_turn` and refuses
   if the scan and the exact carrier disagree (`:121`).
2. Galley + Signal, and Galley + exact-FNSP-v3, are **disjoint unsupported routes** and
   refuse rather than silently dropping one weld (`blocklace_sync.rs:7745`, `:7760`).
3. `preflight_active_poa_galley_public_perform_v1` (`poa_galley_authority.rs:959`) — a full
   independent Lean view, requiring the token to be offered exactly once at the current
   head. Its error type is split on purpose (`:163`): `StaleAction` is a deterministic
   rejection every replica reaches; `AuthorityUnavailable` stays retryable.
4. `commit_finalized_poa_galley_public_perform_v1` → `commit_log.rs:1596` builds a
   `PoaGalleyRawWeld`, and at `commit_log.rs:2753`, **inside the single commit writer**:
   re-load the active world and policy, mint the unforgeable
   `ValidatedPoaGalleyFinalityWeldV1` (`commit_log.rs:120`, no public constructor),
   `derive_poa_finalized_public_perform_v1` (`poa_galley_authority.rs:390`),
   then `prepare_poa_galley_public_event_batch_v1_in` (`:583`) — which calls Lean
   **twice more**, once for the view (to confirm the action really was offered) and once for
   the command (to obtain the event) — then calls the Lean EventBatch planner and stages
   the batch atomically with the commit record, receipt and cursor.

Count: **one player command triggers at least five separate `judgeFFI` invocations** —
`/status` read, `post_command` re-read, preflight, apex view (`:630`), apex command
(`:681`) — plus one per subsequent `/status` poll, each a full replay from genesis over
≤64 events. That is the cost of "Lean is the only judge". It is affordable at these bounds;
it is a real number an organ with a longer history must budget for.

---

## 8. Where authority stops, hop by hop

| hop | may decide | may **not** decide |
|---|---|---|
| authored content | the whole `PolicyWire` (ids, service amounts, target, anchors) | anything about a transition |
| ActivatedContentRuntime (Lean) | that a manifest binds this world and yields a valid policy + genesis projection | **which world is active** — that stays with the same-writer `WorldActivation` audit (`ActivatedContentRuntime.lean:10-12`) |
| persist / activated content | that the sealed frame replays to the same Lean answer | policy semantics — no Rust parser exists |
| `judgeFFI` (Lean) | the entire transition, the offered action set, every digest | nothing about identity, finality, or storage |
| persist / galley authority | that the durable history, the world, the receipts and Lean's answer all agree; refuse on any disagreement | it never *computes* a transition and never accepts a caller-supplied projection, head, or `audited` bit |
| node HTTP | reshaping, the actor header as personalization, preparing an **unsigned** turn | write authority — `post_command` mutates nothing; player identity comes only from the signed envelope |
| browser | shape, coherence, same-origin, two SHA-256 checks, presentation | any state transition, any player record not present in a node-audited response, canonical receipt verification, finality |
| wallet extension | consent, the signature, submission | the turn's contents — it signs bytes the node produced and the page verified |
| finalizer + commit apex | classification, PQ admission, atomicity | the Galley semantics — it asks Lean again, in its own writer |

---

## 9. Where the template is Galley-specific — the generalization list

**G1 — the Rust wire mirror is hand-maintained and order-load-bearing.**
Ten `struct Galley*Wire` in `poa_galley_authority.rs:1599-1730` whose *declaration order*
must equal Lean's `*.toJson` order, plus four hand-written policy `format!` strings in
tests. A second organ doubles this. The generalized answer is one Lean-emitted schema (or a
fingerprint test that pins each Rust struct's `serde_json` output against the Lean encoder's
output for a fixture) — not a second hand-copied mirror.

**G2 — the `public-play` / `perform` rename.** One concept in four spellings across the four
layers. A generic organ layer should carry the Lean payload `kind` through the HTTP surface
unchanged and let the carrier tag be the only numeric encoding.

**G3 — `audited: true` is a literal.** `poa_galley_api.rs:367`. No path emits `false`, yet
the whole browser loop branches on it. Either compute it or delete it; a boolean that cannot
be false is not a gate.

**G4 — the stream kind `9` and the `1`-event batch shape.** `GALLEY_STREAM_KIND = 9` is
spelled in Lean (`…Runtime.lean:41`), in persist (`:56`), and in the kernel's
`streamSpec` (`GalleyMaintenanceDaily.lean:447`). Kind must become a per-organ registry with
a collision refusal, not a constant copied into three files. Note also that
`prepare_poa_galley_public_event_batch_v1_in` hardcodes a **one-event batch** (`event_index: 0`,
single-element vectors, `:691-743`); the EventBatch V2 substrate supports more, the Galley
adapter does not.

**G5 — one action kind, one command shape.** `post_command` constructs only
`GalleyPlayerCommandV1::Perform` (`poa_galley_api.rs:481`), and the response type has no
field for command parameters. An organ with a *choice* (Bazaar's offers, NightWatch's
targets) needs the prepare request to carry an argument beyond `action_token`, and needs
Lean's `ActionTokenWire` preimage to bind it. Today `tokenPreimage` binds
`beneficiary` and `authority_commitment` and nothing else parameter-shaped.

**G6 — the one-token-per-head concurrency model.** `expires_after_sequence == sequence`
means exactly one player command can be in flight per daily. This is fine for a single
station and wrong for any organ where players act concurrently. Generalizing means a token
whose expiry spans a window plus a per-player nullifier — the machinery exists in Lean
(`grantNullifier`, `spentGrantNullifiers`) but is only wired for the unreachable sponsor path.

**G7 — the holder-sponsor half-path.** `BetaHolderSealWire`, `AdmittedBetaSponsor`,
`authorityMatchesB`, `sponsorAction` and `decodeBetaHolderSeal` are complete in Lean
(`…Runtime.lean:239-825, 998-1030`) and unreachable: `judgeFFI` passes `none`, the FFI
sponsor entry point returns a hard error (`poa_galley_ffi.rs:49`), and
`runAdmittedBetaSponsorWire` is proved to return `""` for all inputs (`:1044`). This is
honestly built and honestly disabled — but it is ~250 lines of Lean and two Rust functions
that a reader will mistake for a working path. Either wire the atomically-consumable wallet
capability or delete it.

**G8 — no Runtime boundary module.** `GalleyMaintenanceDailyBoundary.lean` ratchets the
*kernel's* privacy. The Runtime — the thing that actually ships — has no equivalent, so
nothing prevents a future edit from making `reduce`, `nextEvent` or `AdmittedBetaSponsor.mk`
public. Every organ's Runtime should get a `*RuntimeBoundary.lean` on day one.

**G9 — the SDK path constant disagrees with the node's.**
`sdk/src/poa_galley.rs:17` says `/node/api/poa/galley/v1`; `poa_galley_api.rs:25` says
`/api/poa/galley/v1`. One is the Caddy-facing path and one is the origin path, and neither
name says which. Rename or delete one.

**G10 — the receipt-chain scan is O(chain).** `load_galley_receipts_in`
(`poa_galley_authority.rs:1169`) walks the entire `RECEIPT_CHAIN` table to resolve each
event's receipt, and refuses above 65 536 rows (`:65`) because there is no
`receipt_hash → dense index` table. Every organ that wants to show receipts inherits this
ceiling. The generalized fix is the index, and it is one table.

---

## 10. The blocker a copying lane will hit first

**Nothing installs a Galley world on a running node.** The three installers —
`install_poa_world_curator_pin_v1`, `install_poa_world_activation_v1`,
`install_poa_activated_content_v1` — are `pub`, and every call site in the repo is inside
`#[cfg(test)]`:

```
node/src/poa_galley_api.rs:606,624,627        (test helper install_live_world)
persist/src/commit_log.rs:4492,4503,5167,5170,5199   (tests)
persist/src/poa_activated_content.rs:618,637,640,643,…  (tests)
persist/src/poa_world_activation.rs:1142,1198,…         (tests)
```

There is **no HTTP route and no CLI subcommand** that installs a PoA world activation or an
activated-content manifest. The one PoA operator ceremony that exists — `dregg-node
init-poa-signal` (`node/src/lib.rs:355`, `node/src/poa_signal_genesis.rs`) — installs the
*Signal* head and calls neither `install_poa_world_activation_v1` nor
`install_poa_activated_content_v1`; `grep -n "install_" node/src/poa_signal_genesis.rs`
returns nothing. The string `poa.galley-maintenance-daily.policy.v1` appears
in the repo **only inside test `format!`s** (4 sites). No authored production policy JSON
exists anywhere.

So on the live validator, `observe_active_poa_galley_v1` fails at step 1 with
`"PoA world has no installed content manifest"` (`poa_activated_content.rs:166`) →
`GalleyApiError::Backend` → **503 `poa-galley-observation-unavailable`** → the browser
renders "GALLEY SEALED". `latest_height = 0` is consistent with this: not "nobody played",
but "the organ has never been openable".

This is the memory's **uncalled-initializer class**: a documented, fully-audited,
test-exercised cold start that production never invokes. The fix is one named installer at
the operator boundary — a `dregg-node poa-galley-activate --manifest … --curator-key …`
subcommand or an admin route behind the existing curator pin — plus a real authored policy
component. It is small, and it is the difference between the whole traced path being live
and being a test fixture.
