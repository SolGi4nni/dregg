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
./target/debug/dregg-node init --data-dir /tmp/my-dregg
./target/debug/dregg-node run  --data-dir /tmp/my-dregg --enable-faucet --port 8421 &
```

If no seed release has been cut yet, step 2 fails loud and tells you your two
options (bootstrap from source, or cut a release — `docs/LEAN-SEED-ARTIFACT.md`).
The `DREGG_REQUIRE_LEAN=1` in step 3 guarantees you can never *think* you built a
verified node when you didn't — the build panics with the exact missing piece
instead of quietly shipping the Rust executor.

### The marshal-only path (un-verified, fine for UI/dev)

If you just want to click around and don't need the verified executor, skip the
seed entirely:

```sh
cargo build -p dregg-node
./target/debug/dregg-node init --data-dir /tmp/my-dregg
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
{"healthy":false,"peer_count":0,"latest_height":0,"dag_height":0,"block_count":0,
 "consensus_live":false,"federation_mode":"solo","state_producer":"lean",
 "lean_producer":true,"full_turn_proving":false,"producer_covered_effects":21}
```

`state_producer:"lean"` / `lean_producer:true` is the point: the node executes
turns by calling the verified Lean function, not a Rust reimplementation. A
marshal-only node instead reads `state_producer:"rust"` / `lean_producer:false`
here (and logged `MARSHAL-ONLY BUILD OVERRIDDEN` on startup). (`full_turn_proving`
is off
by default — the per-turn STARK is on the hot path; pass `--prove-turns` to turn
it on, which is what an audit-grade node runs.)

`healthy:false` / `consensus_live:false` is **expected on a solo node** —
`healthy` requires a finalized blocklace block (`consensus_live && block_count >
0`), and a single node has no committee to finalize one. Turns still commit and
witness on the verified path (you are about to watch one land); block finality
and the federation-attested read surface arrive with the multi-node federation in
§9.

Faucet a cell. NOTE: a cell id is a commitment to a public key
(`id == derive_raw(pubkey, token)`), so a bare *random* id is **unspendable** —
the faucet credits it (a real verified turn you can watch land), but no one holds
its key to sign a spend. To fund a cell you OWN, use `dregg demo` (§4), which
generates your keypair, derives your agent cell, and funds that.

```sh
CID=$(python3 -c "import secrets;print(secrets.token_hex(32))")
curl -s -X POST http://localhost:8421/api/faucet \
  -H 'content-type: application/json' \
  -d "{\"recipient\":\"$CID\",\"amount\":1000}"
```

```json
{"success":true,"tx_hash":"5573392f…","amount":1000,"turn_hash":"64c6392a…"}
```

Read the cell back:

```sh
curl -s http://localhost:8421/api/cell/$CID
```

```json
{"id":"…","found":true,"balance":1000,"nonce":0,…}
```

## 2. Get the CLI

```sh
cargo build -p dregg-cli
export PATH="$PWD/target/debug:$PATH"           # or invoke ./target/debug/dregg
export DREGG_NODE_URL=http://localhost:8421
dregg node status
```

```text
=== Node Status ===
  Health: UNHEALTHY          # expected on a solo node — see §1; turns still commit
  Federation mode: solo
  State producer: LEAN (verified, 21 effects)
  DAG height: 0
```

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
# IMPORTANT: include public_key on the FIRST faucet call that touches this cell.
# A faucet call without it materializes the cell with a ZERO public key, the
# faucet never rewrites an existing cell's key, and every signed turn on this
# data dir then fails with "Ed25519 signature verification failed" — including
# the turn below and every step of `dregg demo` (§4).
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
OK: Funded 5000 computrons.
=== Step 4: Registering 'alice.dregg' ===
OK: Registration committed     Turn: 16a4cbe4…
=== Step 6: Transferring 'alice.dregg' to bob ===
OK: Transfer committed
=== Step 7: Revoking 'alice.dregg' (one-way) ===
OK: Revocation committed
=== Demo complete ===
OK: A full nameservice lifecycle ran end-to-end on the verified commit path.
```

The first unlock SETS the passphrase on a fresh node; the demo acquires the
bearer token itself.

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
