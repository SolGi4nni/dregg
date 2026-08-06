# The Galley layer contract — the PoA organ template

Traced end to end 2026-08-05 against HEAD. Every claim below is anchored to `file:line`.
Galley is the only PoA kernel with a complete Lean → player path, so it is the template.
This document states what each hop is allowed to decide and — just as important — the
places where the template is Galley-specific and a second organ would have to generalize.

**Read §0 before you copy anything.** It records a twin that existed until 2026-08-05,
what deleting it cost, and the check every other organ still has to pass.

---

## 0. There was a second Galley. It is deleted.

**Resolved 2026-08-05 — one state machine.** Until that day there were two independent
Lean state machines with "Galley" in the name, sharing exactly one identifier and no
type, relation or theorem:

| | `GalleyMaintenanceDaily.lean` (2003 ln, **DELETED**) | `GalleyMaintenanceDailyRuntime.lean` |
|---|---|---|
| Reducer | `reduce`, private | `reduce`, public |
| State | `State` — phases `ballot / maintenance / completed / outputRecorded` | `ProjectionWire` — no phases, one `sequence` counter |
| Actions | `participant / openMaintenance / perform / visitCommons / recordFinalizedOutput` | payload kinds `"public-play"` / `"holder-sponsor"` |
| `@[export]` | **none** | `dregg_poa_galley_daily_judge` |
| Reached by Rust | **never** | always |

Deleted with it: `GalleyMaintenanceDailyBoundary.lean` (186 ln), `GalleyCommons.lean`
(2760 ln — a *third*, settled-credit commons economy, reachable only as a type parameter
of the kernel's uncallable `provisionCapabilities`), `GalleyCommonsBoundary.lean` (162 ln).
**5,111 lines, 135 pins** (85 `#assert_axioms` + 50 `#assert_compiled`).

### Why deletion and not a refinement theorem

A simulation between the two would have had to be *stated*, and every honest statement of
it was blocked:

- the Runtime's sponsor transition adds `policy.sponsorService` to the only progress
  variable it has, while the kernel's sponsorship provably moved nothing
  (`dregg_sponsorship_preserves_chamber_power`) — a **contradiction** under any relation
  mapping progress to progress, not a gap;
- a kernel commons visit paid `choice.localService` or `0` by capacity; the Runtime pays a
  policy constant with no capacity, no rotation and no authored alternative;
- `perform` and `recordFinalizedOutput` had no Runtime counterpart, and the Runtime's four
  anchor roots had no kernel counterpart;
- the only kernel state a public importer could name was `genesisState spec` (phase
  `.ballot`); the Runtime's genesis corresponds to a kernel state in `.maintenance`, which
  is reachable only through a passed two-chamber ballot or the **private** `State.mk`. A
  refinement would have had to quantify over a `DailySpec` and a `CommonsPolicy` that no
  authored content and no emitted `PolicyWire` constructs — the identity-carrier vacuity
  shape — and over `ActivatedDaily`, whose `HostInitializer.mk` had **zero construction
  sites in the repository** (verified by grep at HEAD).

### What proof coverage was lost — measured, not estimated

Counted at HEAD: 24 `#assert_axioms` + 25 `#assert_compiled` in
`GalleyMaintenanceDaily.lean`, 14 `#assert_axioms` in its boundary module, 27 + 25 in
`GalleyCommons.lean`, 20 in *its* boundary module. Sorted by what they actually
established:

1. **Parametric theorems over an uninhabited premise (no coverage lost).**
   `PersistedDailyTransition.same_successor`, `…deployment_scoped`,
   `DurableDailyLoad.revisionZero_same_genesis`,
   `OutputRegistryGenesisCertificate.same_root`, and their output-registry twins are all
   `∀ persistence : DailyPersistenceCASContract / OutputRegistryPersistenceContract, …`.
   **No value of either contract type existed anywhere in the tree**, nor of
   `DailyCanonicalSerializer` / `GalleyCommons.CanonicalSerializer`, so `faithful` was
   never discharged and the CAS/genesis-uniqueness results held of nothing. They also
   could not be inhabited across the FFI: `loadedAt` / `createGenesis` / `rootedAt` /
   `compareAndSwap` are `Prop`-valued host predicates and a `String → String` export
   cannot receive a `Prop`. The durability, CAS and receipt resolution they modelled are
   done for real, with independent re-checks at five hops, in `persist/` (§7).
2. **Case tests over private fixtures (real, and about a game nobody plays).**
   `three_step_daily_replays_to_one_exact_finalized_output`,
   `full_commons_choice_gives_authored_neighborly_alternative`,
   `one_commons_visit_per_player_is_enforced`,
   `authored_commons_strategies_have_distinct_outcomes`,
   `deployment_registry_refuses_reused_receipt_hash`, and ~20 more `native_decide` facts
   about `fixtureSpec`. These were genuine checks of a genuine design; they constrained no
   byte any node, browser or wallet ever sees.
3. **Two parametric theorems that were neither vacuous nor fixture-bound** —
   `dregg_sponsorship_preserves_chamber_power` (over every admitted grant and pre-state)
   and `successful_commons_visit_preserves_power`. These are the real loss. Their
   *subject matter* — that a service acknowledgement moves no narrative authority — now
   exists on the shipped side as `judge_output_preserves_advantage_anchors` (§2.6), which
   is strictly better placed because it is stated about the emitted `OutputWire`.
4. **The 13 privacy teeth** (`State.mk` / `initialState` / the five `*Step`s / the
   post-ballot fixture are private). Not lost — **moved**:
   `GalleyMaintenanceDailyRuntimeBoundary.lean` is the same ratchet over the module that
   ships, which is also the closure of **G8** below.

`MAX_LOCAL_SERVICE = 100` now lives in `…Runtime.lean`. Value unchanged, so no emitted
policy, fixture or pinned digest moves arithmetically.

### The check this section still exists for

Every other organ's Runtime/Wire layer starts in the position Galley was in. When a lane
says "the kernel reaches the node", the check is: *does the `@[export]`'d function's call
graph reach the kernel's reducer?* And the second check, which Galley failed until the
same commit: *is there a theorem tying the exported answer to that reducer, or only
theorems about the reducer?* See §2.6.

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

Proved facts **about the reducer**:
- `reduce_preserves_advantage_anchors` — `powerRoot/lootRoot/canonRoot/canonRevision` are
  identical across any accepted transition.
- `reduce_holder_sponsor_bounded` — sponsor service ≤ 100 and anchors unchanged.
- `receiptOf_has_no_advantage_delta` — the three deltas are literally `0`.
- `no_authority_cannot_form_holder_payload` — with `authority = none`, which is what the
  export passes, the sponsor branch cannot form a payload.

⚑ **Proved facts about the EMITTED OUTPUT** — added 2026-08-05, and the reason the list
above is now usable. Every fact in that list is about `reduce`; the judge obtains its
successor through `EventSourcing.applyEvent` and, until these theorems, could have
published *any* projection with all four of them still green. A consumer sees an
`OutputWire`, not a `Reducer`.

- `judge_command_projection_is_reduce` — for an accepted command emitting `event`,
  `reduce policy input.claimed_projection event.payload = some output.projection`. The
  published successor **is** the reducer's.
- `judge_view_projection_is_claimed` — a view answer emits no event and republishes the
  caller's `claimed_projection` byte-identically.
- `judge_output_preserves_advantage_anchors` — the four anchors of `output.projection`
  equal the four anchors of `input.claimed_projection`, in **both** modes. This is the
  one to cite; it is the only form of the anchor claim stated over what the wire carries.
- `EventSourcing.applyEvent_projection_is_reduce` — the generic law the three above rest
  on, available to every other organ's Runtime.

Refutation the weld catches: give the command branch a successor the reducer did not
return (`localServiceTotal + 1`, say) and `judge_command_projection_is_reduce` goes red.
Measured before it existed, that mutation passed every other check in the module —
`fixture_public_command_accepted` tests only `.isSome`, `fixture_public_output_redecodes`
re-decodes a tampered projection happily, and
`fixture_beta_sponsor_accepted_without_advantage` inspects only the four anchors.

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
semantics — which is the right shape, but note that four of the five tags were named after
the **deleted** kernel's actions (`PublicVote`, `OpenMaintenance`, `VisitCommons`) or after
its structurally-unreachable sponsor path. After §0 they name nothing in Lean at all. A
carrier tag whose semantics do not exist is not harmful — every one of them refuses — but
it is now a vocabulary with no referent, and the next carrier edit should collapse it to
`Perform` or say why not.

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
spelled in Lean (`…Runtime.lean:41`) and in persist (`:56`). (It was spelled a *third*
time in the deleted kernel's `streamSpec`, where nothing checked the two agreed.) Kind
must become a per-organ registry with a collision refusal, not a constant copied into two
files. Note also that
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

**G8 — no Runtime boundary module. ✅ CLOSED 2026-08-05 for Galley; open for every other
organ.** `GalleyMaintenanceDailyBoundary.lean` ratcheted the *deleted kernel's* privacy;
the Runtime had no equivalent, so nothing prevented a future edit from making `nextEvent`,
`validatedPrefix?`, the raw `parse*` decoders or `AdmittedBetaSponsor.mk` public.
`GalleyMaintenanceDailyRuntimeBoundary.lean` is now that ratchet, over the module the
export actually runs: six `fail_if_success` theorems covering the sponsor-authority
constructor, the action-token minters, the unchecked transition surface, the raw parsers
(the ones that skip the re-encode equality of §2.5), the adversarial fixtures, and the
encoder internals. It is globbed into `PathOfAngelsGuards` because nothing imports a
boundary module — a ratchet in no build target is not a ratchet. **Every organ's Runtime
should get a `*RuntimeBoundary.lean` on day one, and it must be in a build target.**

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

> **CLOSED 2026-08-05 for Galley.** `node/src/poa_galley_genesis.rs` +
> `dregg-node poa-galley-world-preview` / `dregg-node init-poa-galley-world` now call the
> three installers at the operator boundary, and
> `poa/artifacts/galley/epoch-1/{policy,manifest}.json` is the authored production
> component (`scripts/poa-galley-content.py`). **The class is not closed** — the section
> below is kept because every *other* organ is still in exactly this position, and
> because the diagnosis is what a copying lane needs. See §10.1 for what is now live and
> what is still missing.

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

### 10.1 The ceremony that closes it, and what it does not close

`node/src/poa_galley_genesis.rs`. Two subcommands, because the node must never mint a
curator signature:

```
dregg-node poa-galley-world-preview  --data-dir … --deployment-manifest … --genesis …
    --main-data-dir … --poag1-manifest … --content-envelope … --curator-key-pin …
    --content-manifest poa/artifacts/galley/epoch-1/manifest.json
    --content-session 504f412d47414c4c45592d310000000000000000000000000000000000000000
    --expected-content-epoch 1 --expected-activation-counter 5 --world-counter 1
        → POA-WORLD-ACTIVATION-PREVIEW-V1 {world, signing_message, signing_message_sha256}

  curator signs `signing_message` with the pinned Ed25519 key
        → POA-WORLD-ACTIVATION-ENVELOPE-V1 (schema, world, counter, predecessor_head,
          kind, rollback_target, curator_key, signature)

dregg-node init-poa-galley-world  … --signed-activation activation.sig.json
        → install_poa_world_curator_pin_v1 → install_poa_world_activation_v1
          → install_poa_activated_content_v1 → both reopen audits
          → load_authenticated_poa_galley_policy_v1 (the organ is open)
```

The world identity is **derived, never accepted**: `federation_id` from the verified
deployment manifest, `activation_digest` from the verified POAG1 content-epoch envelope,
`content_root` from SHA-256 of the manifest file, `content_epoch` from the envelope. A
curator signature over any other world refuses before the store is opened.

What is still open:

- **`content_session` has no independent source.** It is an operator flag that must equal
  the manifest's `scope.content_session`; Lean refuses the install otherwise. Checking it
  in the node would mean a second manifest grammar in Rust, so it is not checked there.
- **The ceremony is offline.** It opens `dregg.redb` directly, so the node must be stopped.
  There is still no admin route, and a live world rotation therefore still costs a restart.
- **No other organ has one.** This is one installer for one organ, not the generic operator
  boundary G1–G10 keep pointing at.
- **`rules_digest` is provenance, not a binding.** The authored policy sets it to SHA-256 of
  `GalleyMaintenanceDailyRuntime.lean` at authoring time. It is bound into every
  action-token preimage and verified against nothing at runtime; editing that file makes
  the artifact stale, and re-emitting it changes `content_root` and needs a new signed
  activation.

  ⚑ **IT IS STALE RIGHT NOW.** `poa/artifacts/galley/epoch-1/policy.json` carries
  `rules_digest = fe40fcf02db8ea6a660dce4eae418e75a2983c8d27aee91445e96126c2c6291b`, which
  was SHA-256 of `…Runtime.lean` before the §0 deletion. That file changed in the same
  commit (import block, `MAX_LOCAL_SERVICE`, the three weld theorems), so the digest no
  longer matches its own declared source. **Re-emit, after the tree builds green:**

  ```
  scripts/poa-galley-content.py …                    # new rules_digest, component_sha256, content_root
  dregg-node poa-galley-world-preview …              # new signing_message
  <curator signs>                                    # new POA-WORLD-ACTIVATION-ENVELOPE-V1
  dregg-node init-poa-galley-world … --signed-activation activation.sig.json
  ```

  Cost of not doing it: nothing refuses — that is the whole point of "provenance, not a
  binding" — so a stale `rules_digest` is silently baked into every action-token preimage
  a player signs against. The organ has never been installed on the live validator
  (`latest_height = 0`, §10), so nothing deployed carries the old value.
