# dregg in 15 minutes

The hands-on path, entirely local: run a node, sign a real turn, run the guided
demo, drive a governance ceremony on the real executor, and run the site in your
browser. There is no public server — everything below runs on `localhost` from a
clean checkout. Every command was run successfully against this tree; outputs are
pasted (truncated) as the expected result.

What you need: this repo and `cargo`. `python3` and `curl` for the raw HTTP bits.
Docker for the site section.

**Verified vs marshal-only — read this first.** dregg's whole point is that the
node's state producer IS the *verified Lean executor*. But that executor links a
~180 MB native archive (`dregg-lean-ffi/libdregg_lean.a`, the "Lean seed") that is
**gitignored** — a fresh clone does **not** have it. So there are two build modes:

- **verified** (`state_producer:"lean"`): the node runs the proved Lean function.
  Needs the seed **and** the elan/Lean toolchain on PATH. Get the seed the fast
  way — `./scripts/fetch-lean-seed.sh` downloads a prebuilt one in minutes — or
  the slow way, `./scripts/bootstrap.sh` (compiles it from source; mathlib is
  NOT the cost — its prebuilt oleans arrive in minutes via the cloud cache — the
  long part is the leanc compile of the Dregg2 closure, ~30–90 min on a beefy
  box).
- **marshal-only** (`state_producer:"rust"`): a plain `cargo build` with **no
  seed** builds this — the node would run the *un-verified* Rust executor. It is
  fine for UI/dev, but it is **not** the verified node. The node **refuses to
  start** in this mode unless you explicitly opt in with
  `DREGG_ALLOW_UNVERIFIED_CONSENSUS=1` — fail-closed: an unverified node is a
  deliberate choice, never a silent default.

The one-command path that does the right thing (fetch seed → build → run →
report which mode you got) is **`./scripts/run-node-10min.sh`**. The sections
below are the same steps by hand. Full detail: `docs/LEAN-SEED-ARTIFACT.md` and
`docs/BUILD-LEAN-LINKED-NODE.md`.

---

## 1. Run a node (on localhost)

### The verified path (the point of dregg)

```sh
# 1. elan + the pinned Lean toolchain on PATH (installs in minutes; NO mathlib compile):
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh    # then re-open your shell
# (Linux/Ubuntu: the gpui link also needs the xkbcommon X11 dev symlink: apt install libxkbcommon-x11-dev)
# 2. fetch the prebuilt Lean seed for your platform (minutes, not the hours-long bootstrap):
./scripts/fetch-lean-seed.sh
# 3. build the node, FAILING LOUD if it would silently degrade to marshal-only:
DREGG_REQUIRE_LEAN=1 cargo build -p dregg-node
```

If no seed release has been cut yet, step 2 fails loud and tells you your two
options (bootstrap from source, or cut a release — `docs/LEAN-SEED-ARTIFACT.md`).
The `DREGG_REQUIRE_LEAN=1` in step 3 guarantees you can never *think* you built a
verified node when you didn't — the build panics with the exact missing piece
instead of quietly shipping the Rust executor.

### Lay down a chain, then run against it

A node does **not** bootstrap its own chain, so `init` mints one: a one-validator
`genesis.json` (validator key, faucet supply, fee/issuer wells, and the consensus
clock policy `run` refuses to start without), plus a `node.key` that IS that
committee's member key.

```sh
./target/debug/dregg-node init --data-dir /tmp/my-dregg
./target/debug/dregg-node run  --data-dir /tmp/my-dregg --enable-faucet --port 8421 &
```

`init` will not overwrite: a data dir that already holds a `genesis.json` is left
alone, and one holding a `node.key` with no `genesis.json` is refused rather than
handed a solo chain — that is the shape of a validator waiting for its
federation's committee descriptor, and quietly starting it on a private chain of
its own would look like success while it talked to nobody.

Two failures this replaces, both of which shipped:

- Until 2026-07-26 `init` wrote only an empty store and a random `node.key`, and
  `run` then exited with `blocklace requires consensus_genesis_unix_seconds +
  consensus_time_mode in the shared genesis.json` — after ~13 seconds of
  starbridge seeding, so it read as a hang. The documented workaround was
  `dregg-node genesis --validators 1 --output <dir>` followed by copying
  `genesis.json` and `node-0.key` across; that still works and is what you want
  for a multi-node committee, but it is no longer needed for a solo node. (It
  also missed `agent-alice.key`, which made the node skip all ten starbridge
  factory cells at boot.)
- The key is not interchangeable. The node signs every attested state root with
  its `node.key`, and the durable commit refuses a root whose author is not in
  the genesis committee — so a `node.key` from anywhere else lets the node boot
  and produce blocks while **every turn fails to commit**, forever, with
  `integrity error: faithful note-root attestation has no valid author signature`
  repeating in the log.

For a real committee, `dregg-node genesis --validators N` is still the command;
`demo/multi-node-devnet/start_devnet.sh` shows that shape for six nodes.

**Already running a node? Pass `--gossip-port` as well.** It defaults to 9420 for
every node, and a second node that cannot bind it does not fail — blocklace logs
`failed to create PeerNode for blocklace gossip: Address already in use` and
returns, and the node then serves HTTP forever with `consensus_live:false`,
`block_count:0`, and every faucet grant accepted and never applied.

### Unlock it — nothing finalizes until you do

```sh
curl -s -X POST http://localhost:8421/cipherclerk/unlock \
  -H 'content-type: application/json' -d '{"passphrase":"pick-a-passphrase"}'
```

A locked node answers reads and accepts submissions, but it cannot **sign**, and
signing is what finalization needs: until the first unlock it produces no blocks
(`dag_height:0`, `healthy:false`) and no turn — not even a faucet grant — ever
lands. The first unlock SETS the passphrase on a fresh node and returns the
bearer token §3 uses.

### The marshal-only path (un-verified, fine for UI/dev)

If you just want to click around and don't need the verified executor, skip the
seed entirely — the genesis/key/unlock steps above are unchanged:

```sh
cargo build -p dregg-node
DREGG_ALLOW_UNVERIFIED_CONSENSUS=1 \
./target/debug/dregg-node run  --data-dir /tmp/my-dregg --enable-faucet --port 8421 &
```

(Without the env var, a seedless build refuses to start rather than silently
serving the un-verified executor — see the note above.)

### Check it either way

```sh
curl -s http://localhost:8421/status
```

```json
{"healthy":true,"peer_count":0,"latest_height":0,"dag_height":1,"block_count":1,
 "consensus_live":true,"federation_mode":"solo","state_producer":"lean",
 "lean_producer":true,"full_turn_proving":false,
 "producer_root_agreeing_effects":18,"producer_covered_effects":18}
```

`state_producer:"lean"` / `lean_producer:true` is the point: the node executes
turns by calling the verified Lean function, not a Rust reimplementation. A
marshal-only node instead reads `state_producer:"rust"` / `lean_producer:false`
here (and logged `MARSHAL-ONLY BUILD OVERRIDDEN` on startup). (`full_turn_proving`
is off
by default — the per-turn STARK is on the hot path; pass `--prove-turns` to turn
it on, which is what an audit-grade node runs.)

`healthy` is exactly three things: the store is readable, the consensus task is
attached (`consensus_live`), and the local DAG holds at least one block. A solo
node satisfies all three — but the third only **after the unlock above**: block
production signs, so a still-locked node reads `healthy:false` / `dag_height:0`
with `consensus_live:true`, and that is the fingerprint of "you have not unlocked
it yet", not of a broken node. What stays `0` on a quiet unlocked node is
`latest_height` (the ATTESTED-ROOT height), which advances on turn-bearing
finality, not on heartbeats; `dag_height` is the honest "how tall is the chain".

`producer_root_agreeing_effects` is the SWAP-SAFE count (the verified producer
runs AND its root provably equals Rust's). `GET /api/node/producer` breaks out
the wider MAPPABLE set (`mappable_effects`) — a bigger number about a weaker
property. `producer_covered_effects` is a deprecated alias of the swap-safe
count, kept while a shipped client still reads it.

Faucet a cell. NOTE: a cell id is a commitment to a public key
(`id == derive_raw(pubkey, blake3("default"))`), so a bare *random* id is
**unspendable** — the faucet credits it (a real verified turn you can watch
land), but no one holds its key to sign a spend. To fund a cell you can ACT as,
faucet `derive_raw(<your pubkey>, blake3("default"))` — `dregg id create` (§2)
makes the key and `dregg cell inspect` shows the id; §3 does it for the node
operator's own cell, and `dregg demo` (§4) drives that same operator cell end to
end. (`dregg demo` funds the NODE's identity, not a client key of yours.)

```sh
CID=$(python3 -c "import secrets;print(secrets.token_hex(32))")
curl -s -X POST http://localhost:8421/api/faucet \
  -H 'content-type: application/json' \
  -d "{\"recipient\":\"$CID\",\"amount\":1000}"
```

```json
{"success":true,"tx_hash":"5573392f…","amount":1000,"turn_hash":"64c6392a…"}
```

`success:true` means the grant was ADMITTED and handed to consensus, not that
the balance has moved: the faucet turn is applied by FINALIZATION (the same
`execute_finalized_turn` every node runs), which lands a moment later. Read the
cell back — poll if you are quick:

```sh
curl -s http://localhost:8421/api/cell/$CID
```

```json
{"id":"…","found":true,"balance":1000,"nonce":0,…}
```

`found` is the field that says whether the rest mean anything: `GET
/api/cell/{id}` answers `200` with a zero-valued cell for an id the ledger does
not hold, and `found:false` is the only thing distinguishing that from a real
empty cell.

A grant to a cell no node has seen lands in a **zero-pk landing stub**: the
recipient's public key is not carried over consensus, so every node materializes
the identical keyless cell at that id from the turn's data alone. The **first
signed turn from the key that derives the id CLAIMS it** — binding that Ed25519
key and the ML-DSA-65 key the same envelope proves possession of, and carrying
the granted balance over verbatim. That is why the faucet's `public_key` field is
optional and why a funded cell reads back with a zero `public_key` until its
owner acts.

## 2. Get the CLI

```sh
cargo build -p dregg-cli
export PATH="$PWD/target/debug:$PATH"           # or invoke ./target/debug/dregg
export DREGG_NODE_URL=http://localhost:8421
dregg node status
```

```text
=== Node Status ===
  Health: HEALTHY
  URL: http://localhost:8421
  Federation mode: solo
  State producer: LEAN (verified, 18 effects)
  Full-turn proving: off
  Attested height: 0
  DAG height: 1
  Peers: 0
```

(`State producer` prints `producer_root_agreeing_effects` — the SWAP-SAFE count
from §1, not the wider mappable set. `Attested height` stays `0` until a
turn-bearing block finalizes.)

`dregg doctor` health-checks the whole client surface; `dregg --help` lists the
verbs (id, cell, turn, name, polis, voting, bounty, cap, proof, …).

Give yourself a named identity (a fresh Ed25519 key in
`~/.dregg/profiles/<name>.json`, mode 0600 — the SDK picks the active one up
automatically via `AgentRuntime::from_active_profile`):

```sh
dregg id create ember
dregg id use ember
dregg id list
```

```text
=== Identity Profiles ===
| * ember | 72cf3c9bcc58...466e6b |
  Active: ember (persistent default)
```

`DREGG_PROFILE=<name>` overrides the persistent default per-shell.

## 3. Sign a real turn

Reads are public; **writes need the node's bearer token** (the node signs turns
with its operator cipherclerk). On your own node you obtain one by unlocking the
cipherclerk — `dregg demo --passphrase` does exactly that for you, so the
simplest path to "I signed a real turn" is the demo in §4. To do it by hand,
unlock the cipherclerk and submit one effect (write a field of the operator's own
cell — `agent` is advisory; the node derives the real signer from its
cipherclerk):

```sh
# unlock sets the passphrase on a fresh node and returns a bearer token:
export DREGG_API_TOKEN=$(curl -s -X POST http://localhost:8421/cipherclerk/unlock \
  -H 'content-type: application/json' -d '{"passphrase":"pick-a-passphrase"}' \
  | python3 -c 'import json,sys;print(json.load(sys.stdin)["bearer_token"])')

AGENT=$(curl -s http://localhost:8421/api/node/identity \
  | python3 -c 'import json,sys;print(json.load(sys.stdin)["agent_cell"])')
NODE_PK=$(curl -s http://localhost:8421/api/node/identity \
  | python3 -c 'import json,sys;print(json.load(sys.stdin)["public_key"])')

# fund the operator cell so it can pay the turn's fee (skip if already funded).
# The grant lands in a zero-pk landing stub (§1); the operator's FIRST signed
# turn — the one just below, and step 4 of `dregg demo` — claims it. `public_key`
# is accepted but only affects the `amount:0` materialization path, so passing it
# on a FUNDED grant changes nothing.
curl -s -X POST http://localhost:8421/api/faucet -H 'content-type: application/json' \
  -d "{\"recipient\":\"$AGENT\",\"amount\":5000,\"public_key\":\"$NODE_PK\"}" >/dev/null

curl -s -X POST http://localhost:8421/api/turns/submit \
  -H "Authorization: Bearer $DREGG_API_TOKEN" -H 'content-type: application/json' \
  -d "{\"agent\":\"$AGENT\",\"nonce\":0,\"fee\":1000,\"memo\":\"hello from the quickstart\",
       \"actions\":[{\"effects\":[{\"kind\":\"set_field\",\"index\":0,\"value\":\"42\"}]}]}"
```

```json
{"accepted":true,"turn_hash":"8dae2ff1…","proof_status":"proof_pending",
 "has_witness":false,"witness_count":0,"error":null}
```

Watch the receipt land:

```sh
curl -s http://localhost:8421/api/receipts          # the chain, newest first
dregg turn status 8dae2ff1…
```

```text
=== Turn Receipt ===
  Turn hash: 8dae2ff1...fff8
  Finality: tentative
  Chain index: …
  Actions: 1
  Pre-state: 6bc3a65e…
  Post-state: abd79a4a…
  Witnessed: yes
```

The receipt — committed, chained, witnessed — IS your proof the turn ran on the
verified path; `dregg turn status` reads `Proof: present`, `Witnessed: yes`. With
`full_turn_proving` off, the witness lands immediately and the proof stays
`proof_pending`. Start the node with `--prove-turns` and a worker attaches a real
per-turn STARK to the committed receipt a moment later (the `Proof: present`,
`Witness count: 1` you then read). Note the per-cell pre/post state roots in the
receipt are only populated when proving is on — a non-proving node leaves them as
placeholders (the cell state itself updates either way; read it back with
`dregg cell inspect`).

The federation-attested read surface a *light client* fetches — `GET
/federation/roots` (committee-signed state roots), `GET /checkpoint/latest`
(finalized checkpoints), and the standalone full-turn STARK bytes at `GET
/api/turn/{hash}/proof` — are produced by **blocklace finalization across a
federation**, so they are empty / `404` on a solo node by design. To see them
populated, boot the local multi-node federation in §9.

## 4. The guided demo — a full app lifecycle, one command

`dregg demo` drives the whole nameservice machine — unlock → fund → register →
resolve → transfer → revoke — each step a real signed turn on the verified commit
path. It unlocks the cipherclerk itself, so no token dance:

```sh
dregg --node-url http://localhost:8421 demo --passphrase pick-a-passphrase
```

```text
=== Step 2: Unlocking the cipherclerk ===
OK: Cipherclerk unlocked (bearer token acquired).
=== Step 3: Funding the operator cell ===
OK: Faucet accepted a 10000-computron grant; waiting for it to finalize.
OK: Operator cell holds 10000 computrons on the ledger (4600 needed for this run).
=== Step 4: Registering 'alice.dregg' ===
OK: Registration committed     Turn: f555b665…
  Applied on the ledger (cell nonce 1).
=== Step 5: Resolving 'alice.dregg' ===
OK: 'alice.dregg' is bound and active
=== Step 6: Transferring 'alice.dregg' to bob ===
OK: Transfer committed
  Applied on the ledger (cell nonce 2).
=== Step 7: Revoking 'alice.dregg' (one-way) ===
OK: Revocation committed
  Applied on the ledger (cell nonce 3).
ERROR: REVOKED — this name has been tombstoned (one-way).
=== Demo complete ===
OK: A full nameservice lifecycle ran end-to-end on the verified commit path.
```

(The `REVOKED` line at the end is the demo's final resolve showing the tombstone
it just wrote — the point of step 7, not a failure.)

The first unlock SETS the passphrase on a fresh node; the demo acquires the
bearer token itself.

**What every "Applied on the ledger" line is doing.** `accepted:true` from
`/api/turns/submit` means the turn was admitted and ordered, not that it ran —
application happens at finalization, and a turn can be refused *there*, after the
HTTP surface has already answered. Steps 6 and 7 used to print `committed` while
the node's log recorded `finalized SignedTurn failed agent-scoped receipt
continuity before mutation (deterministic rejection recorded)` for both, and
nothing moved: same nonce, same balance, same slots, green demo. Each step now
waits for the agent cell's nonce to advance before the next one is narrated. The
nonce it prints is the evidence.

The demo is re-runnable: it recycles its own tombstone and tops the cell up from
the faucet when it is short. The faucet allows one grant per cell per minute, so
a run that needs a top-up can pause for up to that long before step 4.

## 5. Drive a governance ceremony (polis)

The polis council machine — charter, proposal, M-of-N approvals, threshold
certification, execute-exactly-once — runs end-to-end on the real **embedded**
executor (no node, no server) in one example binary:

```sh
cargo run -p dregg-sdk --example polis_ceremony
```

```text
charter             : 2-of-3
treasury funded     : 100 computrons
[propose] state=Proposed approvals=0/2 certified=false
[approve] state=Proposed approvals=1/2 certified=false
certify at 1-of-2   : EXECUTOR REJECTED (as it must) — program constraint violated: affine sum 1 > 0
[certify] state=Approved approvals=2/2 certified=true
[execute] state=Executed approvals=2/2 certified=true
grantee balance     : 100 (treasury paid exactly once)
```

Every rule there is enforced by the cell program the factory installs — the SDK
builds turns, the EXECUTOR rejects the bad ones. Also try
`cargo run -p dregg-sdk --example hello_receipt_chain` — the smallest possible
"what is a receipt" loop. (`sdk/tests/*_e2e.rs` are the full tooth-by-tooth
executable specifications.)

## 6. Run the site locally (playground · explorer · starbridge)

The same executor compiles to wasm and runs in your tab. Build the wasm package,
then build and serve the site. The site builds in Docker (`node:22`); mount the
**repo root** — the build regenerates its ontology/predicate catalogs from the
Lean sources in `metatheory/`.

```sh
# 1. the in-browser executor (writes the package the site loads):
cd wasm && wasm-pack build --target web --out-dir ../site/pkg --release && cd ..

# 2. build + serve the site:
docker run --rm -d -p 3000:3000 -v "$PWD:/repo" -w /repo/site node:22 \
  sh -c "npm install --no-audit --no-fund && npm run build && npx serve dist"
```

Then:

- **<http://localhost:3000/playground/#turn-workbench>** — stage a turn by verb,
  read the verified-Lean explanation, RUN it on the real in-browser wasm
  executor, then PROVE it: a real EffectVM STARK, produced and self-verified in
  your browser.
- **<http://localhost:3000/explorer/>** — open Settings and point it at your
  `http://localhost:8421` node to browse live cells/receipts with witness status
  and per-cell time travel.
- **<http://localhost:3000/starbridge/>** — the workbench/inspector. It boots an
  EMPTY in-browser world: use the **Start here** strip (seed a sandbox world →
  run a transfer turn → click the receipt).

## 7. Subscribe to the receipt stream (reactivity)

Every receipt the node commits is broadcast live at `/api/events/stream`
(Server-Sent Events — plain curl works; `-N` disables buffering):

```sh
curl -N "$DREGG_NODE_URL/api/events/stream"
# filter to one cell and/or effect kind:
curl -N "$DREGG_NODE_URL/api/events/stream?cell=<hex-cell-id>&kind=set_field"
```

```text
event: receipt
id: 9
data: {"chain_index":9,"turn_hash":"8dae2ff1…","cells":["…"],
       "kinds":["set_field"],"finality":"tentative",…}
```

Each event's `id` is the receipt-chain index; reconnect with a `Last-Event-ID:`
header to resume. From the SDK the same feed is
`dregg_sdk::events::NodeEvents::new(url).subscribe(filter)` — a reconnecting
`Stream` of the public `Receipt` noun.

## 8. Inspect what you made

```sh
dregg cell inspect <cell-id>                  # state, nonce, program, c-list
dregg name resolve you.dregg --cell <cell>    # the name machine, decoded
dregg polis council --cell <proposal-cell>    # the council machine, decoded
dregg turn status <turn-hash>                 # receipt, finality, witness
```

and in a browser at `http://localhost:3000/explorer/cell/<id>` (also
`…/explorer/receipt/<hash>`, `…/explorer/tx/<turn-hash>`).

## 9. The federation read surface (the light-client verify)

A solo node commits and witnesses turns, but the *federation-attested* artifacts a
light client reads — committee-signed state roots, finalized checkpoints, and the
standalone full-turn STARK — only exist once a committee finalizes blocks. Boot a
local federation (two federations of three nodes each) to see them populated. This
needs only the already-built `dregg-node` binary plus `jq`:

```sh
cargo build -p dregg-node -p dregg-verifier        # the verifier is used by scenarios
cd demo/multi-node-devnet
./start_devnet.sh                                   # boots 6 nodes on 127.0.0.1:7811-7813, :7821-7823
```

The attested read surface is then live off any node (F1 node-1 is `:7811`):

```sh
curl -s http://127.0.0.1:7811/federation/roots      # committee-signed state roots (+ signatures)
curl -s http://127.0.0.1:7811/checkpoint/latest     # latest finalized checkpoint (+ qc votes)
```

The endpoints respond immediately; `roots` is an empty array `[]` on a freshly
booted, idle federation and fills as the committee finalizes blocks under activity.
The scenario scripts drive that activity and assert the surface end-to-end (all
green on this tree):

```sh
./scenarios/federation_attestation.sh               # committee-signed roots, tamper rejected
./run_all_scenarios.sh                              # cross-fed handoff, attestation, transfer, …
./stop_devnet.sh                                    # SIGTERM, then SIGKILL after 5s
```

From an SDK this is the read-only `AttestedQuery` noun (no identity, no signing) —
`attestedRoots()` / `checkpoint()` / `turnProof(hash)` in `@dregg/sdk` and
`dregg.AttestedQuery` in the Python binding. Verifying a STARK or a threshold
signature is a Rust/wasm operation; the pure-TS/Python `AttestedQuery` surfaces the
artifacts to verify, it does not return a checked verdict on its own.
`demo/multi-node-devnet/README.md` documents the topology and each scenario.

## Where next

- `starbridge-apps/` — the app layer (nameservice, polis, privacy-voting,
  bounty-board, identity, …); each crate's `lib.rs` documents its machine and
  what the substrate enforces. `dregg voting` / `dregg bounty` drive the
  voting/bounty machines on a node whose genesis seeds those cells.
- `sdk/` — `AgentRuntime` (embedded executor), factories, polis builders;
  `sdk/tests/*_e2e.rs` are executable specifications.
- `metatheory/` — the verified Lean implementation the node runs.
- `starbridge-v2/` — deos, the native cockpit (`cd starbridge-v2 && cargo build`).

## Notes

- The node's HTTP API binds `127.0.0.1` by default. To reach it from another
  host, pass `--bind 0.0.0.0` and add a `--cors-origin` for any browser origin.
- The `--enable-faucet` switch is for local dev nodes only; it lets anyone draw from the
  genesis faucet cell. A production node leaves it off.
- The embedded-executor crates (the SDK examples, `starbridge-v2`, the proof
  suites) are slow to compile in debug — the first `cargo run` of an example
  takes a few minutes. They link the Lean archive.
