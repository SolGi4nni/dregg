# Re-genesis runbook — 2026-08-08 (batched ceremony)

Authored by the ceremony-prep lane. **Everything `[auto]` below was dry-run; the actual output is
quoted inline.** Steps marked `[CUSTODY — orchestrator]` were not executed: they need key material,
the live store, or an outward-facing act.

- Authored against HEAD **`dde642177`**. The tree is shared and HEAD moved twice while this was
  written (`8a336a74e` → `dde642177`); **re-measure §1 before starting.**
- Every verification below reads **an artifact**, never an exit code. Where a step's only evidence
  would be an exit code, that is said out loud.

---

## 0. Read this first: two facts that change the shape of the ceremony

**(a) The POAG1 bundle in the repo is already internally inconsistent, at HEAD, committed.**
`8a336a74e` (the biased-modulo fix) re-emitted four game descriptors under `poa/artifacts/poag1/games/`
and did **not** touch `manifest.json` or `manifest.sig.json`. Measured:

| artifact | manifest pins | file on disk |
|---|---|---|
| `games/black-box-reconstruction.json` | 8107 | **9080** |
| `games/relay-repair.json` | 122003 | **122179** |
| `games/salvage-lock.json` | 635203 | **635427** |
| `games/signal-triangulation.json` | 52260 | **52484** |

Consequence, measured: `node --test poa-web/tests/*.test.mjs` is **33 tests red** at HEAD, every one
of them `ArtifactRefusal … code: 'byte-length'`. This is not a hazard the ceremony must avoid — it is
the state the ceremony **repairs**. Do not "fix" it separately; it is repaired by §5.

**(b) `poa/artifacts/poag1-pending/` is also stale.** The freshly emitted pending descriptors differ
from the checked-in ones (`vent-crawl` 31353 → 31601, `deck-descent` 3395622 → 3395852,
`artificer-logic` 5103296 → 5103515). The delta is the `symbol_draw` block — the same `SeedDraw`
rejection-sampling declaration the modulo fix added. `poa-web/tests/bundle-enrolment.test.mjs` is
**green anyway** (4/4, measured): it compares pending *paths*, never pending *bytes*. So this drift is
invisible to the gate and must be swept by hand in §5.

---

## 1. Preconditions — re-measure these, do not trust this table

```sh
cd /Users/ember/dev/breadstuffs
git rev-parse --short HEAD
jq -r '.missions[0].federation_id' poa/artifacts/poag1/catalog.json
jq -r '.content_epoch, .counter' poa/artifacts/poag1/manifest.sig.json
grep -n 'POA_EXPECTED_CONTENT_EPOCH\|POA_EXPECTED_CURATOR_COUNTER' poa-web/src/trust-config.js
grep -n 'CANONICAL_STATE_SCHEMA_EPOCH: u64' persist/src/lib.rs
```

Measured 2026-08-08 at `dde642177`:

| thing | value |
|---|---|
| outgoing federation id | `70b7fa4cfbc3921bef2e1ddb1a42869c8dcef27539179c9cbdf6a6e6b1d07c1b` |
| outgoing deployment id | `4db835cc36cd0d3b722e742334dc1dde9557601fe1334c7499ab023de4d6d45d` |
| outgoing genesis sha256 | `f7010ca2acf705a9d941cc27ae500b4274e958ec9529b364b8b678c3ce3ccdea` |
| signed content epoch / counter | `1` / `8` |
| web trust pins | epoch `1`, counter `8` |
| `CANONICAL_STATE_SCHEMA_EPOCH` | **26** |
| `signal_claim_fee_v1()` | **1702** (measured, §4.2) |
| epoch-1 deployment funding | `generic_genesis_value_issued: false` — **unfunded** |

---

## 2. Phase A — pre-ceremony gates. All `[auto]`, all dry-run, none need keys

Run these **before** touching anything. They establish that everything except the bundle/manifest
mismatch of §0 is sound.

### A1 `[auto]` — the checked-in deployment record still authenticates

```sh
node scripts/poa-devnet-manifest.mjs verify-public \
  --root poa/deployments/epoch-1 --main-data-dir "$HOME/.dregg"
```

**Dry-run output (green):**
```
verified PoA deployment 4db835cc36cd0d3b722e742334dc1dde9557601fe1334c7499ab023de4d6d45d (federation 70b7fa4cfbc3921bef2e1ddb1a42869c8dcef27539179c9cbdf6a6e6b1d07c1b)
```
**Verify from the artifact:** the two hex values printed must equal `poa-devnet.json`'s
`deployment_id` and `federation_id`. This re-derives `deployment_id` from the genesis bytes; it does
not read them out of the file.

### A2 `[auto]` — galley epoch-1 content is byte-exact

```sh
python3 scripts/poa-galley-content.py check
```
**Dry-run output:** `poa galley content artifacts are byte-exact` (exit 0).

### A3 `[auto]` — the multiplexed epoch-2 world is byte-exact

⚠ **The obvious invocation fails two different ways.** From `metatheory/` it dies on relative paths
(`no such file or directory: poa/artifacts/galley/epoch-1/manifest.json`); via
`lake --dir=metatheory env` it dies with `incompatible header` on the olean. The working form
resolves `LEAN_PATH` in `metatheory/` and then runs `lean` **from the repo root**:

```sh
cd /Users/ember/dev/breadstuffs/metatheory
LP=$(lake env printenv LEAN_PATH); LEANBIN=$(lake env printenv PATH | tr ':' '\n' | grep -m1 'lean.*bin')
cd /Users/ember/dev/breadstuffs
LEAN_PATH="$LP" POA_EPOCH2_MODE=check "$LEANBIN/lean" --run \
  metatheory/Dregg2/Games/PathOfAngels/AngelsEpoch2WorldEmitMain.lean
```
**Dry-run output:** `poa epoch-2 multiplexed-world artifacts are byte-exact`.

⚠ **This check is wired into no CI script.** `grep -r POA_EPOCH2 scripts/ .github/` is empty;
`scripts/test-poa.sh` has no epoch-2 line. Until it does, `poa/artifacts/angels-epoch-2/` can drift
silently. Run it by hand at every phase boundary below.

### A4 `[auto]` — schema-epoch ledger reconstructs

```sh
python3 scripts/check-schema-epoch-log.py
```
**Dry-run output:** `constant=26 · 73 event rows (48 epoch-bearing, last=26) · 14 ledger rows · git history 14 distinct values` → `OK`.

### A5 `[auto]` — bundle enrolment (pinned ∪ pending == what Lean emits)

```sh
node --test poa-web/tests/bundle-enrolment.test.mjs
```
**Dry-run output:** `pass 4, fail 0`. See §0(b): it does not compare pending bytes.

### A6 `[auto]` — extension unit suite

```sh
cd extension && npm test
```
**Dry-run output:** `tests 152 · pass 152 · fail 0`. Includes the two-independent-sources gate
(`extension/test/poa-signal.test.mjs:35-46`) that compares `POA_SIGNAL_FEDERATION_HEX` against
`poa/deployments/epoch-1/poa-devnet.json`'s `federation_id`. **This is the gate that goes red the
moment §3 lands and stays red until §4.3 — that is correct and expected.**

### A7 `[auto]` — the two known-red gates, recorded so their redness is not new information

```sh
bash scripts/check-wasm-freshness.sh extension --kind no-modules
```
**Dry-run output: RED, as expected.**
```
built at:     2026-08-07T19:40:29Z  (git 685a62a3234e0c55f3a8939f51a20d2812459e80, kind no-modules)
WASM FRESHNESS: RED — the bundle is STALE.
  built from source  472a82496c84f8d3b4f99608568d00d77ff359955fb1e5710a481f703b6475db
  tree is now        cfa3a615caf5cc9967e5dfabe6f3853b8ad7fb25448635eb17f25abc3077a4c1
```
Legs 1–5 (provenance present, schema v2, wasm sha, glue sha, bundle kind) pass; only leg 6, the
source fingerprint, is red. §7 closes it.

```sh
unzip -p extension/dist/dregg-cipherclerk-chrome.zip dregg_wasm.js | grep -c cell_id_for_pubkey
unzip -p extension/dist/dregg-cipherclerk-chrome.zip dregg_wasm.js | grep -c build_poa_signal_claim_turn
```
**Dry-run output: `0` and `3`.** The zip loaded (positive control 3) and does **not** carry
`cell_id_for_pubkey`. This is the brief's claim, confirmed at the artifact, not from a build log.

---

## 3. Phase B — the re-genesis `[CUSTODY — orchestrator]`

**Nothing here can be dry-run.** It draws key material and it is the irreversible act of the ceremony.

### B1 `[CUSTODY]` — build the node with Lean linked in

```sh
DREGG_REQUIRE_LEAN=1 cargo build --release -p dregg-node --bin dregg-node
```
On hbox, via `~/dev/dregg-infra/poa/dev-deploy.sh build` (wraps it in `swarm-build`).
**Verify from the artifact, not the exit code:**
```sh
nm -g target/release/dregg-node | grep -c 'poa_signal\|path_of_angels'   # must be > 0
sha256sum target/release/dregg-node                                      # record it; §B4 needs it
```
A node built **without** `DREGG_REQUIRE_LEAN=1` links a stub and produces a genesis nothing else
agrees with. *(Prep note: the binary built for §4.2's fee probe was built without that flag and must
not be reused here.)*

### B2 `[CUSTODY]` — decide the player grant, priced at ceremony time

Read the fee **now**, from the binary you just built — never from this document:
```sh
./target/release/dregg-node genesis --validators 1 \
  --deployment-domain pathofangels.network/federation/v1 --no-demo-economy \
  --player-grant 1 --output /tmp/fee-probe-throwaway 2>&1 | grep 'claim fee'
```
Measured 2026-08-08: **`1702`** (it was 870 before the Signal claim event went 4 lanes → 17). The
refusal fires at `node/src/genesis.rs:377-384`, **before** `create_dir_all` at `:403`, so the probe
writes nothing — confirmed: the `--output` path did not exist afterwards.

⚠ **Do not pipe this through `head`.** SIGPIPE kills the process before the refusal prints. Use
`grep`, and expect it to take minutes (the ML-DSA/ML-KEM Lean cores install at startup).

Choose `POA_PLAYER_GRANT` as a multiple of the measured fee — "N turns", stated in the commit.
`dev-deploy.sh genesis` does not set it and inherits `1000000` (`scripts/poa-devnet.sh:40`); at 1702
that is ~587 turns.

### B3 `[CUSTODY]` — genesis into a **fresh, empty** root

```sh
export POA_BIN="$PWD/target/release/dregg-node"
export POA_ROOT=<fresh EMPTY dir>            # e.g. .../pathofangels/solo-epoch-3
export POA_MAIN_DATA_DIR="$HOME/.dregg"
export POA_VALIDATORS=1 POA_HTTP_BASE=8423 POA_GOSSIP_BASE=9423
export POA_NODE_HOSTS='10.10.1.10'
export POA_PLAYER_GRANT=<from B2>
scripts/poa-devnet.sh genesis
```
⚠ `scripts/poa-devnet.sh:267-269` refuses a non-empty root, and `dev-deploy.sh:73-84` refuses if
`$CEREMONY_ROOT` exists at all ("a federation root is immutable"). **Use a new root name.**

**Key material this DRAWS (0600, OS CSPRNG, sole copies):**
- `$POA_ROOT/bundle/node-{0..N}.key` — validator seeds
- `$POA_ROOT/bundle/player-grant.key` — the grant secret (`node/src/genesis.rs:631-648`)

Wells (`issuer-well.key`, `fee-well.key`) are **derived** via `auxiliary_genesis_key`; the player
grant deliberately is **not** — `refuse_derivable_player_grant()` (`node/src/genesis.rs:272`) runs
over the bytes about to be written and over the bytes a node reads at boot recovery. Nothing
published re-derives the seed. **Lose `player-grant.key` and the only remedy is another re-genesis.**

**Verify from the artifact:**
```sh
jq -r '.federation_id, .deployment_id, .genesis_sha256, .policy.generic_genesis_value_issued' \
  "$POA_ROOT/poa-devnet.json"
stat -f '%Sp %z' "$POA_ROOT/bundle/player-grant.key"     # must be -rw------- and 32
```
`generic_genesis_value_issued` must now be **`true`**. `assertPublicManifestShape`
(`scripts/poa-devnet-manifest.mjs:566`) enforces it **both ways** — a funded descriptor that says
`false`, or an unfunded one that says `true`, is refused.

**Rollback:** delete the new `$POA_ROOT` and keep serving epoch-1. Rollback is only free **until
§8** — once the node is seeded and restarted on the new genesis, the old chain's state is gone
(`persist`'s epoch gate refuses, never migrates) and going back means re-seeding from the retained
epoch-1 root. **Retain the epoch-1 root until the ceremony is signed off.**

### B4 `[CUSTODY]` — re-seal `release-lock.json` **by hand**

⚠ **`release-lock.json` has no generator.** Only verifiers exist
(`scripts/poa-follower-package.mjs:126-171`, `scripts/poa-devnet.sh:210-226`,
`dregg-infra/poa/join-node.sh:20`). Every field is re-typed:

- `epoch` → bump
- `deployment.{federation_id, deployment_id, genesis_sha256}` → from B3
- `release.node_sha256` → from B1
- `release.source_commit` → the ceremony commit
- `files[].sha256` → `shasum -a 256 poa-devnet.json bundle/genesis.json`

**Verify from the artifact:** re-run `scripts/poa-devnet.sh verify` (or `dregg-infra/poa/release-gate.sh`),
which recomputes every `files[].sha256` rather than trusting it.

---

## 4. Phase C — propagate the new federation id

The id lives in **29 files**. Most are derived; only a short list is hand-edited. Measured
occurrence counts at HEAD:

### C1 `[auto]` — the hand-edited sources. **Edit these, then regenerate everything else.**

| file | line | note |
|---|---|---|
| `metatheory/Dregg2/Games/PathOfAngels/NetworkGenesis.lean` | 377 | bare literal |
| `metatheory/Dregg2/Games/PathOfAngels/NightWatchCampaignContent.lean` | 99 | bare literal |
| `metatheory/Dregg2/Games/PathOfAngels/AngelsEpoch2World.lean` | 234 | embeds the **whole deployment JSON** — `deployment_id` and `genesis_sha256` move too |
| `extension/src/poa-signal.ts` | 27 | `POA_SIGNAL_FEDERATION_HEX` |
| `poa-curator/tests/cli.rs` | 114 | |
| `poa-curator/tests/snapshots/epoch-1-unsigned.json` | 8 | |
| `extension/test/poa-companion-v3.test.mjs` | 26 | |
| `dregg-lean-ffi/tests/fixtures/poa-network-genesis-{canon,config,input,output}-v1.json` | — | 4 files, 7 occurrences total |
| `poa/deployments/epoch-1/release-lock.json` | — | §B4 |

**`poa-curator/src/companion.rs` is NOT on this list — brief claim confirmed.** It reads the id from
the deployment kit via `deployed_identity()` (`poa-curator/src/companion.rs:481-490`), which loads
`poa/deployments/epoch-1/poa-devnet.json`. The docblock names the exact wound this closed
("a typed copy would keep a test green against a dead federation — which is exactly what happened
until 2026-08-05"). Nothing to edit there.

**`POA_SIGNAL_NODE_URL` stays — brief claim confirmed, with a caveat.** It is
`https://node.pathofangels.network` (`extension/src/poa-signal.ts:4`) and nothing ties it to chain
identity; `poa-devnet.json` names no public URL at all. ⚠ Its only test
(`extension/test/poa-signal.test.mjs:26`) compares the constant to a hand-typed copy of itself —
exactly the "one source quoted twice" shape the *federation* assertion was repaired away from. It
will stay green whatever happens. Not this ceremony's job, but worth a follow-up card.

### C2 `[auto]` — regenerate the derived artifacts

```sh
python3 scripts/poa-galley-content.py emit        # reads federation_id from the deployment (:214)
```
Night watch **needs the curator-drawn slot secret** — see §6.

**Verify from the artifact:**
```sh
grep -rl <OLD_FED_HEX> --exclude-dir=.git --exclude-dir=target --exclude-dir=.lake . | sort
```
must return **nothing** (except deliberately retained history). Re-run with the new hex and compare
the file list to the 29 above; a file that gained or lost the id is a surprise worth reading.

### C3 `[auto]` — extension test-build output

`extension/test/.build/poa-signal.mjs` is esbuild output (gitignored); `npm test`'s pretest
regenerates it. No edit.

---

## 5. Phase D — re-emit and re-sign POAG1. **The load-bearing phase.**

### D1 `[auto]` — the emit pipeline. **Fully dry-run; here is what it produces.**

The whole of `scripts/check-poag1-artifacts.sh` was replicated into a scratch tree with a
**placeholder** federation id (`dede…de`). Timings on this laptop: `lake build` 1.2 s warm,
descriptors phase **11 s**, artifacts and bundle phases seconds each.

**⚑ Only `catalog.json` carries the federation id** — measured: 28 occurrences in `catalog.json`,
**0** in `schema.json` and **0** in all seven descriptors. Therefore the following are **final now**
and will not move at ceremony time unless a Lean source changes:

```
source_digest  sha256:8a236275803d305c7e4fda4c4335ad7068e66ec6a78139f3d695ab7e47ee73ac
content_root   sha256:6149ba272d96cb0df41ed3c907e63c19285ec0665f5c8359d6b9b492a360ca41
schema.json    2051 B  sha256:1e69a41c296ead4ced4ec631051a5f594e1410448528ac710cddbf114791e684
```
| descriptor | bytes | sha256 |
|---|---|---|
| `games/artificer-logic.json` | 5103515 | `746557faa265894ac328b1aafd1f4f324f41811b64104d26fc7cad47b3403ddd` |
| `games/black-box-reconstruction.json` | 9080 | `21b89323b1041cc5f8eb3589c3ca51647a5349cd24723c2978c12e1356193a70` |
| `games/deck-descent.json` | 3395852 | `e45b0503629715a6a83bcb4b6a9f091d459ccacb1c6c4eed719f348533258db1` |
| `games/relay-repair.json` | 122179 | `63d65efc79cef856c4dd0b3ef0a3b30ccdcdb96a79c918a422d94b012868922a` |
| `games/salvage-lock.json` | 635427 | `b01d993a0f35434d22e0e42c44ac9047abbde710b67c5a82ec25286d69792b56` |
| `games/signal-triangulation.json` | 52484 | `b89d72fa3af6e64ac127f3ca6efe5ff3da0e0494ae843b05110798783614e5a2` |
| `games/vent-crawl.json` | 31601 | `247fff82b6162c6688c48760e79c0b93ff9d5929d127ecfe40be1840722d4949` |

The four descriptors already in `poa/artifacts/poag1/games/` are **byte-identical** to the fresh
emission (verified with `cmp`) — only `manifest.json` was stale. `catalog.json` emits at **12768 B**
regardless of which federation id is used (a hex id is always 64 chars), so **only its sha256 is
unknown before the ceremony**, and `manifest.json`'s bytes follow from it.

Run mode, once the new deployment kit exists:
```sh
POA_ROOT=$POA_ROOT POA_MAIN_DATA_DIR=$POA_MAIN_DATA_DIR \
  scripts/check-poag1-artifacts.sh --update
```
`--update` re-emits into `poa/artifacts/poag1/`, **deletes `manifest.sig.json`** (`:300-301`) and
prints `POAG1 release status: UNSIGNED`.

⚠ **Brief correction:** `POA_ARTIFICER_SHA256` / `POA_VENTCRAWL_SHA256` / `POA_DECKDESCENT_SHA256`
are **not** operator inputs. The script computes them itself from the descriptors phase
(`artificer_sha="$(sha_file …)"`). They have no defaults *in the Lean emitter*, which is why the
script must pass all nine. The operator supplies only `POA_ROOT` / `POA_DEVNET_MANIFEST`,
`POA_MAIN_DATA_DIR`, and — in `check` mode — `POA_CONTENT_EPOCH` and `POA_CURATOR_COUNTER`.

**Verify from the artifact:** compare `poa/artifacts/poag1/manifest.json`'s nine rows against the
table above; seven of the nine sha256 values and all nine byte counts are predicted here. If a
descriptor sha differs, a Lean source moved and §5's source digest is wrong too.

### D2 `[auto]` — sweep the stale pending tree

`poa/artifacts/poag1-pending/` must be refreshed from the same emission (§0(b)). After `--update`
the three pending descriptors are no longer in `poa/artifacts/poag1/` — they moved into the signed
bundle — so `poag1-pending/` should be **emptied**, not refreshed, once all seven are enrolled.
`bundle-enrolment.test.mjs:97` iterates `POAG1_PENDING_ARTIFACTS`, which becomes empty in §6, so the
loop is vacuous and the directory is dead. **Delete it and say so in the commit.**

### D3 `[CUSTODY — orchestrator]` — curator-sign the bundle

```sh
cargo run --manifest-path poa-curator/Cargo.toml -- sign-content \
  --secret <CURATOR SECRET>            # 32 raw bytes, 0600, O_NOFOLLOW; dev-deploy.sh:43
  --pin poa/config/curator-key.json \
  --manifest poa/artifacts/poag1/manifest.json \
  --deployment "$POA_ROOT/poa-devnet.json" \
  --epoch 2 --counter <N>
```
`poa/config/curator-key.json` is the **public** pin (`POA-CURATOR-KEY-V1`, `curator_pubkey` only) —
safe to read and distribute. The secret is at `/home/hbox/pathofangels/keys/development-curator-v3.key`
on the build host; `poa-curator/src/main.rs:654` opens it with `O_NOFOLLOW` and refuses any
group/other permission bit.

**Counter:** current is 8. The next signature must be **9** (`main.rs:545-547` refuses a secret that
does not derive the pin; the counter itself is an external release pin, not read from the envelope).
**Epoch:** the epoch-2 world (§6) requires `content_epoch: 2`, so sign at **epoch 2, counter 9**.

`sign-content` writes `manifest.sig.json` with `atomic_write_new` (**refuse-overwrite**) and
self-verifies before writing.

**Verify from the artifact:**
```sh
jq -r '.content_epoch, .counter, .curator_pubkey, .manifest_sha256' poa/artifacts/poag1/manifest.sig.json
shasum -a 256 poa/artifacts/poag1/manifest.json     # must equal manifest_sha256 minus the sha256: prefix
cargo run --manifest-path poa-curator/Cargo.toml -- verify-content \
  --pin poa/config/curator-key.json --manifest poa/artifacts/poag1/manifest.json \
  --deployment "$POA_ROOT/poa-devnet.json" --epoch 2 --counter 9
```

**Rollback:** re-signing at the same counter is refused by `atomic_write_new`. To redo, delete
`manifest.sig.json` and re-sign — but if the old envelope has already been served, **advance the
counter instead**; the browser treats an old counter as `counter-rollback`
(`poa-web/src/content-epoch.js:93-94`).

---

## 6. Phase E — the web pins. **SAME COMMIT as §5. This ordering is load-bearing.**

⚠ **If the pins widen before the bundle ships, the deployed client refuses the deployed bundle and
the terminal blacks out.** `validateManifest` refuses on artifact **count, order, path and media
type**; a client pinning 9 artifacts against a 6-artifact manifest throws
`POAG1 artifact count does not match the Lean bundle` at load, in the browser, with no earlier
warning. The reverse (bundle ships first, pins later) refuses just as hard. **They must land
together.**

### E1 `[auto]` — `poa-web/src/poag1.js`

Move the three pending paths into `POAG1_EXPECTED_ARTIFACTS` **in path-ascending position** and leave
`POAG1_PENDING_ARTIFACTS` empty. The emitted order is measured, and **`artificer-logic` takes the
first game slot** — it sorts before `black-box-reconstruction`:

```
schema.json
catalog.json
games/artificer-logic.json          ← moved in, FIRST game
games/black-box-reconstruction.json
games/deck-descent.json             ← moved in
games/relay-repair.json
games/salvage-lock.json
games/signal-triangulation.json
games/vent-crawl.json               ← moved in, last
```
Also update the `⚠ SIX` docblock at `poag1.js:14` — it will say six when the answer is nine.

### E2 `[auto]` — `poa-web/src/mission-catalog.js` `GAME_SPECS`

Append three rows. Values read from the dry-run catalog and descriptors (all three are
`instance.disclosure: "oracle-only"`):

| missionId | gameId | title | engineModule | ruleset | disclosure | actionLimit | fixtureId |
|---|---|---|---|---|---|---|---|
| 5 | `deck-descent` | Deck Descent | `Dregg2.Games.PathOfAngels.DeckDescent` | `descent-v1` | `oracle-only` | 9 | `descent-solved-preview-v1` |
| 6 | `artificer-logic` | Artificer Logic | `Dregg2.Games.PathOfAngels.ArtificerLogic` | `artificer-v1` | `oracle-only` | 5 | `artificer-solved-preview-v1` |
| 7 | `vent-crawl` | Vent Crawl | `Dregg2.Games.PathOfAngels.VentCrawl` | `push-your-luck-v1` | `oracle-only` | 6 | `vent-solved-preview-v1` |

⚠ `GAME_SPECS` order is **mission order**, not path order — rows are indexed against
`catalog.missions[index]` (`mission-catalog.js:154`). Append 5, 6, 7 in that order; do **not** sort
them by path.

⚠ Two refusal messages at `mission-catalog.js:139-140` say "the exact four-mission set". The
comparison is `=== GAME_SPECS.length`, so it stays correct — the **prose** goes stale. Fix it.

### E3 `[auto]` — `poa-web/src/trust-config.js`

```js
export const POA_EXPECTED_CONTENT_EPOCH = 2;    // was 1
export const POA_EXPECTED_CURATOR_COUNTER = 9;  // was 8
```
These two are the **external** rollback pins; `authenticateContentEpoch` refuses
`epoch-pin-missing` / `counter-pin-missing` if absent and `epoch-rollback` / `counter-rollback` if
they disagree with the envelope. They must match §D3 exactly.

### E4 `[auto]` — prose that names counter 8 or four games

`poa-web/tests/pending-descriptors.mjs:14`, `poa-web/tests/blackbox-fixture.mjs:3`,
`poa-web/tests/game-rack.test.mjs:149`, `poa-web/tests/artifact-loader.test.mjs:36` (test **name**
"the counter-8 four-game bundle"), `poa-web/src/poag1.js:15`.

### E5 `[auto]` — verify the whole phase from the artifact

```sh
node --test poa-web/tests/*.test.mjs
```
**Must go from 33 red (§0(a)) to 0 red.** That transition is the evidence this phase worked; a green
exit code on a subset is not.

```sh
POA_ROOT=$POA_ROOT POA_MAIN_DATA_DIR=$POA_MAIN_DATA_DIR \
POA_CONTENT_EPOCH=2 POA_CURATOR_COUNTER=9 scripts/check-poag1-artifacts.sh
```
Ends with `POAG1 curator signature authenticated (activation=…)` then a line naming the federation
and all nine digests. It runs the **same** strict parser and Web Crypto verifier the browser uses.

---

## 7. Phase F — the epoch-2 multiplexed world

`poa/artifacts/angels-epoch-2/` (created by `09b2cb1b3`, the only commit touching it) carries **both**
organs — `poa.galley-maintenance-daily.policy.v1` and `poa.night-watch-campaign.config.v1` — in one
`POA-ACTIVATED-CONTENT-MANIFEST-1` so neither evicts the other. It is **not installed**; the install
rides this ceremony.

### F1 — prerequisite: the epoch-2 POAG1 envelope

This is §D3 signed at `--epoch 2`. `world.json:10` has `activation_digest: null` precisely because
the digest is derived from that envelope at install. Without it,
`poa-galley-world-preview --expected-content-epoch 2` refuses at
`node/src/poa_galley_genesis.rs:323-325`. **§D3 strictly precedes §F2.**

### F2 `[CUSTODY — orchestrator]` — the preview

The subcommand is on **`dregg-node`**, not a separate binary. ⚠ The brief's flag names are
approximate; the real ones are `--world-counter`, `--kind`, `--predecessor-head`
(`node/src/lib.rs:455-505`, 16 flags):

```sh
dregg-node poa-galley-world-preview \
  --data-dir <…> --deployment-manifest "$POA_ROOT/poa-devnet.json" \
  --genesis "$POA_ROOT/bundle/genesis.json" --main-data-dir "$POA_MAIN_DATA_DIR" \
  --poag1-manifest poa/artifacts/poag1/manifest.json \
  --content-envelope poa/artifacts/poag1/manifest.sig.json \
  --curator-key-pin poa/config/curator-key.json \
  --content-manifest poa/artifacts/angels-epoch-2/manifest.json \
  --content-session 504f412d414e47454c532d320000000000000000000000000000000000000000 \
  --expected-content-epoch 2 --expected-activation-counter 9 \
  --world-counter 2 --kind advance \
  --predecessor-head <SEE F3> --output <…>
```
⚠ `--content-manifest` is refused unless `text.trim() == text` — **a trailing newline fails it**
(`poa_galley_genesis.rs:359`). `poa/artifacts/angels-epoch-2/manifest.json` has none today; do not
let an editor add one.

⚠ `--expected-activation-counter` is the **POAG1 envelope** counter (9). `--world-counter` is the
**world activation** counter (2). Different numbers; the brief's bare `counter=2` is the latter.

### F3 `[CUSTODY]` — `predecessor_head`: **there is no way to read it off a running node**

It is `sha256(canonical_json(signed envelope))` per
`persist/src/poa_world_activation.rs:161-163`. ⚠ **It is not `sha256(activation.sig.json)`** — the
canonical `JsonEnvelope` form drops the top-level `schema` field the on-disk document carries.

No HTTP route and no CLI subcommand prints it. The only path is the store:
```
PersistentStore::load_poa_active_world_v1()  →  prepared()  →  record()  →  envelope_digest()
```
(the chain `persist/tests/poa_epoch2_multiplexed_world.rs:169-174` uses). **The orchestrator must
supply this value**, either by reading `dregg.redb` programmatically or by recomputing the canonical
(schema-less) JSON of the retained epoch-1 envelope. **This is a real tooling gap — a one-line
`dregg-node` subcommand that prints it would remove a hand-computation from the critical path.**

⚠ `world.json:19` records that every derived-label digest in the epoch-2 artifacts is the **epoch-1**
derivation. **Do not re-run `scripts/poa-galley-content.py` with `CONTENT_EPOCH = 2`** — it would
recompute the preimages with `2` and start a different daily.

### F4 `[CUSTODY]` — night-watch re-emit needs the drawn slot secret

```sh
umask 077; openssl rand -hex 32 > <path OUTSIDE any repo>/night-watch-slot-N.secret
cd metatheory && POA_NIGHT_WATCH_SECRET_FILE=<that path> \
  lake env lean --run Dregg2/Games/PathOfAngels/NightWatchCampaignContentEmitMain.lean
```
The emitter refuses the published rehearsal secret. Check mode (`POA_NIGHT_WATCH_MODE=check`) needs
no secret and is already in `scripts/test-poa.sh:79-83`.

---

## 8. Phase G — rebuild and reship wasm + extension `[auto]` build, `[CUSTODY]` publish

### G1 `[auto]` — rebuild

```sh
bash scripts/build-web-artifacts.sh                     # both bundles, ~20 min
# or the extension alone:
cd extension && npm run build && ./build.sh wasm && ./build.sh package
```
`build.sh package` hard-fails if `dregg_wasm.js`, `dregg_wasm_bg.wasm` or
`dregg-wasm-provenance.json` is missing, and gates both archives. ⚠ **Never set
`DREGG_WASM_SKIP_VERIFY=1`** — the script's own message says "Do not ship them."

### G2 `[auto]` — verify from the artifact, not the build log

```sh
Z=extension/dist/dregg-cipherclerk-chrome.zip
unzip -p "$Z" dregg_wasm.js | grep -c cell_id_for_pubkey        # must be > 0   (was 0)
unzip -p "$Z" dregg_wasm.js | grep -c build_poa_signal_claim_turn  # positive control, was 3
bash scripts/check-wasm-freshness.sh extension --kind no-modules
bash scripts/check-wasm-freshness.sh extension/dist/dregg-cipherclerk-chrome.zip --kind no-modules
```
The freshness gate must go **green** (leg 6 recomputes the wasm32 source fingerprint over ~1946
files). ⚠ Note what it explicitly **does not** answer: it never checks that a particular export is
present. It would not have caught the missing `cell_id_for_pubkey`. The `unzip -p | grep -c` above is
the only thing that does.

### G3 `[auto]` — ⚑ two standing assertions **flip red on rebuild** and must move in the same commit

Both read **`extension/dregg_wasm.js`** — which is **tracked in git**, so G1 produces a tracked-file
diff — and assert the **absence** of `cell_id_for_pubkey` as a deliberate wall. Verified at source:

- `poa-web/tests/judged-session.test.mjs:523-525`
  ```js
  assert.ok(!glue.includes("cell_id_for_pubkey"),
    "the shipped glue exports cell_id_for_pubkey now — claim-cell-underivable has FALLEN, move it to FALLEN_WALLS");
  ```
  Its positive controls at `:531-534` (`build_poa_signal_claim_turn` must be present in both glue and
  source) exist so the negative cannot pass vacuously — keep them when you move the wall.
- `extension/tests/e2e/judged-signal-session.spec.ts:580-581` —
  `expect(source).toContain('pub fn cell_id_for_pubkey'); expect(glue).not.toContain('cell_id_for_pubkey');`

Plus the `CUSTODY_BLOCKERS` entry at `poa-web/src/judged-session.js:432-465`. ⚠ Its recorded blocker
("the wasm32 workspace does not compile … `Effect::Deshield` … ZERO in HEAD") is **stale as written**:
`Deshield` appears 13× in `turn/src/action.rs` at HEAD. Whether wasm32 actually compiles is
**unverified — I did not build it**, and that is the first thing G1 will find out.

**Rollback:** the previous zips are on disk (mtime Aug 7 15:40) but are the stale ones the ceremony
exists to replace; there is nothing worth rolling back to. Copy them aside before G1 anyway — they
are gitignored and a rebuild overwrites them in place.

### G4 `[CUSTODY]` — publish

Copy into `site/extension/` (done by `build-web-artifacts.sh:114-116`) and publish. Outward-facing;
orchestrator's call.

---

## 9. Phase H — deploy `[CUSTODY — orchestrator]`

```sh
~/dev/dregg-infra/poa/dev-deploy.sh build     # hbox, swarm-build, DREGG_REQUIRE_LEAN=1
~/dev/dregg-infra/poa/dev-deploy.sh seed      # push genesis.json + node.key to $DATA_DIR (umask 077)
~/dev/dregg-infra/poa/dev-deploy.sh ship      # stream binary → workhorse, restart dregg-poa.service
~/dev/dregg-infra/poa/dev-deploy.sh status
```
⚠ `seed` is **outside** the routine `build && ship` loop and is required after a re-genesis.

**Verify from the artifact, not `is-active`:** the memory of this exact failure is that a content
lane shipped fresh web against a 189-commit-stale node for 27 hours with `healthy: true` and
`latest_height: 0`. So:
```sh
curl -s https://node.pathofangels.network/api/poa/signal/<NEW_FED_HEX>/status | jq
```
`authority_id` **and** `federation_id` must both equal the new hex — that is exactly what the
extension checks at `extension/src/background.ts:3518-3530` before it will post a claim. Then confirm
`latest_height` advances across two samples. `healthy: true` alone means nothing.

**Rollback:** re-seed from the retained epoch-1 root and re-ship. Irreversible once the epoch-1 root
is deleted — **do not delete it in this ceremony.**

---

## 10. Ordering hazards — what breaks if done out of order

| # | Constraint | What breaks |
|---|---|---|
| 1 | **Web pins (§6) land in the SAME COMMIT as the re-signed bundle (§5)** | Widen first → deployed client pins 9 artifacts, deployed manifest has 6, `POAG1 artifact count does not match the Lean bundle` at load → **terminal blacks out**. Ship first → client pins 6 against 9, same refusal. |
| 2 | **`sign-content --epoch 2` (§D3) strictly precedes `poa-galley-world-preview` (§F2)** | The preview derives `activation_digest` from that envelope; without it, refusal at `poa_galley_genesis.rs:323-325`. `world.json` ships `activation_digest: null` by design. |
| 3 | **Genesis (§B3) precedes the POAG1 emit (§D1)** | `check-poag1-artifacts.sh` refuses without an authenticated deployment manifest — POAG1 emission is post-genesis and the mission `federation_id` is checked against it (`catalog_federations != federation_id` → exit 1). |
| 4 | **`trust-config.js` counter (§E3) == `sign-content --counter` (§D3)** | Off by one either way → `counter-rollback` in the browser. Epoch likewise → `epoch-rollback`. |
| 5 | **`--world-counter` (2) ≠ `--expected-activation-counter` (9)** | Two different counters. Swapping them refuses, but reading the brief's bare `counter=2` as the envelope counter would silently target the wrong envelope. |
| 6 | **Fee measured at ceremony time (§B2), never a literal** | 870 → 1702 already. A grant priced at a stale fee produces a deployment that boots `healthy: true` and refuses every claim. `genesis.rs:359-384` refuses `grant < fee`, so a *too small* grant is caught — but "N turns" computed from a stale fee is not. |
| 7 | **`DREGG_REQUIRE_LEAN=1` on the genesis binary (§B1)** | A stub-linked node genesises a chain nothing else agrees with. |
| 8 | **Fresh `POA_ROOT` (§B3)** | Both `poa-devnet.sh:267-269` and `dev-deploy.sh:73-84` refuse a pre-existing root. Not a silent failure, but it stops the ceremony mid-flight. |
| 9 | **G3's two assertions flip red in the same commit as G1's rebuild** | Otherwise the rebuild lands and two suites go red for a reason that reads like a regression. |
| 10 | **Retain the epoch-1 root and `player-grant.key` until sign-off** | `player-grant.key` has no derivation; `persist`'s epoch gate refuses rather than migrates. Deleting either makes §B3 and §H irreversible. |

---

## 11. What could not be dry-run, and exactly what the orchestrator must supply

| step | why not | what is needed |
|---|---|---|
| §B1 build | 10 min build done **without** `DREGG_REQUIRE_LEAN=1` (fee probe only) | a Lean-linked release build; record its sha256 |
| §B3 genesis | draws validator seeds and the player-grant secret; irreversible | a fresh empty `POA_ROOT`; the chosen `POA_PLAYER_GRANT` |
| §B4 release-lock | no generator exists — hand-sealed | all six field groups re-typed, then `poa-devnet.sh verify` |
| §D3 sign-content | curator secret (`/home/hbox/pathofangels/keys/development-curator-v3.key`) | the secret path; epoch 2; counter 9 |
| §F2 preview | needs the new deployment kit **and** the epoch-2 envelope | the outputs of §B3 and §D3 |
| §F3 `predecessor_head` | **no RPC and no CLI prints it**; only a store read | the digest, read via `load_poa_active_world_v1() → prepared() → record() → envelope_digest()`, or recomputed over the canonical schema-less JSON of the retained epoch-1 envelope |
| §F4 night-watch emit | needs a curator-drawn slot secret | `openssl rand -hex 32` under `umask 077`, outside any repo |
| §G1 wasm build | ~20 min; wasm32 compilability is **unverified** | run it; `Effect::Deshield` may or may not build under wasm32 — the recorded blocker is stale |
| §G4 / §H | outward-facing and irreversible | orchestrator's call |
| nextest-based gates | not run to completion — a concurrent lane held the build-directory lock, then the unlocked run went into a cold multi-crate compile | ⚠ **The blocker is STALE, and this is now measured twice.** The reported "`.config/nextest.toml` is BROKEN, exit 96 on every profile" (from `f5be8e906`'s message) does not reproduce: `tomllib` parses the file and `profile.default.overrides[2]` contains **no** stray `#`; and `cargo nextest list -p dregg-sdk` got **past config load into `Compiling …`**, which it cannot do with an invalid filterset. Nothing here blocks the ceremony. |

### Not a ceremony step: `CANONICAL_STATE_SCHEMA_EPOCH`

**Do not bump it for the shielded roll.** Measured: it is **26** (`persist/src/lib.rs:900`), and 26
*is* the shielded cutover epoch — bumped once by `5f33b6b43` for the value link, and both the 2-out
split and the deshield off-ramp deliberately rode it. `c4ed2af2a` touched `persist/src/lib.rs` but
**only appended prose** to the epoch-26 docblock (`git log -S 'CANONICAL_STATE_SCHEMA_EPOCH: u64 = 26'`
returns exactly one commit). `b991ff4d1` says it outright: *"`CANONICAL_STATE_SCHEMA_EPOCH`
deliberately NOT bumped — no persisted shape, no accumulator, no journal-entry kind."* The brief's
"at least one lane said do not over-bump for me" is confirmed at source.

Bump only if a **new** persisted shape lands *after* a store has actually been stamped 26. The gate
(`enforce_canonical_state_schema_epoch`, `persist/src/lib.rs:1005`) **refuses, never migrates**.

### Not a ceremony step: `scripts/emit-descriptors.sh`

A shielded VK roll touches **zero** descriptor JSON, **zero** `*_FP` constant, and does not move
`dregg-epoch`'s `registry_fp` / `descriptor_set_tag`. There is **no numeric shielded VK-epoch
constant anywhere in the repo** — "VK epoch" here is a flag-day noun. The three relations
(value link, 2-out split, deshield) are pinned by three independent Lean goldens
(`ShieldedTransferValueLinkEmit.lean`, `…2OutEmit.lean`, `ShieldedDeshieldValueLinkEmit.lean`), each
held by a `#assert_compiled` theorem in its own file. Re-emitting one is `lake build Dregg2`, not a
script run.

⚠ One record is arguably stale: `docs/VK-REGEN-LOG.md:83` (ledger row 26) describes only the value
link, not the split's `link_proof` move or `SUPPORTED_OUTPUTS`. The gate passes anyway — it compares
only numbers, and says so in its own `DOES NOT ANSWER` text. Correcting the row is a ceremony
decision, not a red.
