# Telegram game authority epochs: implementation and residual report

**Date:** 2026-07-21
**Scope:** the shared game-session spine and the production Telegram adapter
**Posture:** greenfield. Security defects are ordinary defects; no compatibility promise justifies accepting a stale or ambiguously addressed state-changing action.

## Result

Telegram game buttons are no longer `{turn, arg}` instructions that a later world can reinterpret. Every rendered game action now carries an opaque 45-byte callback derived from the complete `GameActionRef`: offering, session, stable host incarnation, monotone session generation, exact action payload including text, and observed pre-state head. On a press, Telegram reconstructs the *current* bound view and accepts only a callback that equals one currently offered reference. The common spine checks the authority epoch and state head again immediately before execution.

The production bot now owns two durable records under `TELEGRAM_SESSION_DIR`:

1. the existing game move logs, which reconstruct concrete offering state; and
2. `game-epochs/host-incarnation.v1` plus `game-epochs/session-generations.v1`, which say which deployment and which lifetime of `(offering, session)` that state belongs to.

Both stores are required at boot. The shipped binary no longer permits an unopenable move-log store to degrade to memory while retaining durable routing authority.

This closes the captured-action/reused-address failure for ordinary Telegram game turns. A callback captured from generation 1 cannot land after the same human session address is closed and freshly opened as generation 2. A callback captured immediately before an ordinary process restart *can* land after replay resumes the same generation and state head; that is continuity, not replay across a different world.

## Authority and persistence model

`dreggnet-catalog/src/game_epoch.rs` supplies `GameEpochLedger`, a small frontend-neutral custody component:

- `GameHostIncarnation` is generated from the operating-system RNG, rejects the all-zero sentinel, and is retained across ordinary restarts.
- Generations are indexed by the full `(offering, session)` address. The first fresh open is generation 1. A close retains the last number but marks it inactive. A later fresh open increments it with checked arithmetic.
- A durable host session reported as already open/resumed must already have an active generation. Missing custody is a refusal, not an implicit generation-1 adoption. Only the explicitly non-durable in-memory constructor may adopt an existing test/custom-host session.
- Incarnation and generation files are versioned, exact-length/fully-consumed encodings. Truncation, trailing bytes, zero generations, invalid flags, invalid addresses, and duplicate records are refused without reinitialization.
- Mutations write a fresh temporary file, `fsync` it, atomically rename it over the target, and `fsync` the containing directory before publishing the new state in memory.

The ledger deliberately does **not** claim to be a distributed lock service. One deployment process is the writer for a ledger and its move-log store. Multi-process active/active hosting remains a separate federation/lease problem.

### Crash ordering

Open proceeds as concrete host open/persist, then generation persist. If the process dies between those steps, the next boot finds a concrete durable session without an active generation and refuses to route it. If generation persistence returns an error during the same process, Telegram closes the newly opened concrete session before returning the error.

Close proceeds as concrete host close, then generation retirement. If the process dies or persistence fails between those steps, the next genuinely fresh open still receives `previous + 1`, because `newly_opened` always advances the recorded generation even when the old record remained marked active. An old callback therefore cannot be revived by either crash window.

The record format and ordering defend against partial writes and address reuse. They do not yet coordinate two concurrent writers; operators must not point two bot processes at the same directory.

## Adapter cut

The production path is concentrated in these files:

- `dreggnet-catalog/src/game_spine.rs` adds `execute_bound_asserted_game_turn`. It preserves the original `Outcome` required by Telegram while also constructing the bound `GameResult`/receipt, so the adapter does not double-execute or bypass the common spine.
- `dreggnet-telegram/src/api.rs` and `src/lib.rs` permit one validated callback payload per rendered action. Callback count must equal action count and every payload must be 1–64 bytes.
- `dreggnet-telegram/src/host.rs` binds open, status, render, ordinary button press, free-text completion, restart resume, and close/reopen to `GameEpochLedger` and the bound inspection/execution APIs.
- `dreggnet-telegram/src/runtime.rs` exposes `try_durable_telegram_host`, the strict move-log constructor used by production. The older permissive constructor remains for callers that explicitly request an in-memory/demo fallback.
- `dreggnet-telegram/src/bin/dreggnet-telegram-bot.rs` opens the epoch ledger and strict move-log host before starting the bot host threads. Either failure terminates startup.

The callback is `g.` followed by unpadded base64url of the full 32-byte `routing_preimage_id`; it is 45 bytes and therefore fits Telegram's 64-byte ceiling without truncating or maintaining a token side table. The raw `Action` list remains in `TelegramFrontend` for rendering/introspection, but a real game-message callback must use the opaque wire value. The legacy codec is accepted for menu and read-only verify controls, and for synthetic message-less `/act`/Mini-App-style value entry only after the adapter finds a live action template and mints a new fully bound reference at the current head.

## Hostile and continuity tests

The new focused tests are intentionally built over a tiny deterministic one-move offering so authority behavior is tested without silently opting into an unaudited PQ fallback:

- `dreggnet-catalog/tests/game_epoch.rs`
  - restart retains the same incarnation and live generation;
  - close/reopen increments the generation and a captured generation-1 command cannot mutate generation 2;
  - a durable existing session without epoch custody fails closed;
  - corrupt incarnation and trailing generation bytes are refused rather than replaced.
- `dreggnet-telegram/tests/bound_game_epoch.rs`
  - a captured Telegram callback cannot cross close/reopen and causes no turn-count mutation;
  - a clean restart over the same move-log and epoch directories retains incarnation, generation, callback identity, and execution authority.
- `dreggnet-telegram/tests/runtime_shell.rs`
  - the production strict constructor refuses a path that cannot be opened as a durable store;
  - restart scenarios now retain the same epoch ledger and replay the exact opaque callback rather than relying on legacy `{turn, arg}` reinterpretation.

Existing message-routing and Descent tests were updated to inspect the actual opaque button wire while continuing to assert raw action ordering, locked presentation, per-message routing, verifier visibility, and executor-owned legality.

Focused remote results:

- `cargo nextest run -p dreggnet-catalog --test game_epoch`: **4 passed**.
- `cargo nextest run -p dreggnet-telegram --test bound_game_epoch`: **2 passed**.
- `cargo check -p dreggnet-telegram --all-targets`: **passed** on the final strict-constructor and compatibility-test tree.

The broader remote Telegram compatibility attempt reached the test binaries but aborted at ML-DSA key generation because the remote `srot` lane lacked the verified Lean PQ archive and `dregg-pq` correctly refused the unaudited `fips204` fallback. No environment override was set. That is an infrastructure gate failure, not a test assertion failure, and it must not be reported as a green suite.

## Exact remaining `LegacyUnbound` and non-bound surfaces

This cut hardens the ordinary Telegram game-turn path; it is not a claim that every frontend and every operation is epoch-bound.

1. **Web catalog and Telegram Mini App execution.** `dreggnet-web/src/game_session.rs::session_rail` constructs `GameSessionRef::new`, which is explicitly `LegacyUnbound`, for presentation chrome. More importantly, web and Mini App POST handlers execute through their existing catalog/signed-turn paths and do not yet possess durable `GameEpochLedger` custody. The Telegram launch URL names key/session, not host incarnation/generation. Identity is authenticated on the Mini App edge, but this new lifetime binding does not automatically transfer to that independent web host.
2. **Telegram binary proof operations.** Bound inspection already yields `GameOperationRef`s, but `preflight_operation`/`apply_operation` still rediscover raw `BinaryOperationDescriptor`s and invoke by `(key, session, operation name)`. The upload route needs an opaque operation token or equivalent request-bound reference, then `execute_bound_asserted_game_command(GameCommand::Operation)` (or the signed equivalent) at application time.
3. **Generic game-spine compatibility APIs.** `GameSessionRef::new`, `inspect_game_session`, `execute_asserted_game_command`, and `execute_signed_game_turn` intentionally remain legacy-only migration APIs. Bound callers use `GameSessionRef::bound` and the `*_bound_*` entry points. Tests still exercise both forms; new deployment adapters should not acquire new legacy call sites.
4. **Other frontends.** Discord, WeChat, native/no-viewer, and any direct engine surface have not been given durable host-incarnation/session-generation custody by this cut. Most do not yet consume the common game spine at all, so grep-zero for `LegacyUnbound` is not sufficient evidence of safety.
5. **Read-only verification.** Telegram's standing `/verify` control still routes directly to the current offering verifier by message/session. It does not mutate state and therefore is not an action-replay authority, but its report does not yet carry the host incarnation and generation as a first-class receipt field.
6. **Non-game Telegram offerings and per-player RPG services.** These continue through the raw offering protocol. They are outside `game_kind` and outside the authority claim made here; any state-changing surface that needs the same reused-address protection must adopt its own bound address or be promoted into the common spine.

## Next deployable cuts

The highest-leverage continuation is to bind binary operations, because those are precisely the private proof/FHE/MPC uploads whose consequences matter most. Mint operation callbacks/tickets from the complete current `GameOperationRef`, re-resolve at apply time, execute through the bound common spine, and add captured-upload tests across head change and close/reopen.

Then give the web/Mini App catalog a durable ledger and include its incarnation/generation in status, form/action tokens, and signed-turn challenges. The authority may be shared with Telegram only if both surfaces truly address the same concrete host/store and have a single-writer or explicit coordination protocol; matching human session strings is not enough.

Finally, repeat the adapter pattern for Discord and the native/no-viewer surfaces, and decide whether one deployment incarnation is frontend-local or federation-wide. The data type supports either, but operations must choose and persist the authority rather than infer it from a route name.
